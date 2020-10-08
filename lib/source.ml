open Identifier

module Syntax = struct

    type path =
        | IdentP of Ident.t             (* identifier *)
        | DotP of path * string         (* access to a module component *)
        | AppP of path * path
        | DollarP of path * string

    let rec path_equal p1 p2 =
        match (p1, p2) with
        | (IdentP id1, IdentP id2) -> Ident.equal id1 id2
        | (DotP(r1, field1), DotP(r2, field2)) ->
            path_equal r1 r2 && field1 = field2
        | (AppP(fun1, arg1), AppP(fun2, arg2)) ->
            path_equal fun1 fun2 && path_equal arg1 arg2
        | (DollarP(r1, field1), DollarP(r2, field2)) ->
            path_equal r1 r2 && field1 = field2
        | (_, _) -> false

    (* Section 2.3: Substitutions *)

    (* module type SUBST =
        sig
            type t
            val identity: t
            val add: Ident.t -> path -> t -> t
            val path: path -> t -> path
        end *)

    (* module Subst : SUBST = *)
    module Subst =
        struct
            type t = path Ident.tbl
            let identity = Ident.emptytbl
            let add = Ident.add
            let rec path p sub =
                match p with
                | IdentP id -> (try Ident.find id sub with Not_found -> p)
                | DotP(root, field) -> DotP(path root sub, field)
                | AppP(p1, p2) -> AppP(path p1 sub, path p2 sub)
                | DollarP(root, field) -> DollarP(path root sub, field)
        end


    type level = int

    module Core =
        struct
            type term =
                | IntE of int                           (* integer constants *)
                | StrE of string                        (* string constants *)
                | BoolE of bool                         (* boolean constants *)
                | Longident of path                      (* id or mod.mod...id *)
                | FunE of Ident.t * term             (* fun id -> expr *)
                | AppE of term * term                   (* expr(expr) *)
                | LetE of Ident.t * term * term           (* let id = expr in expr *)
                | LetRecE of Ident.t * term * term      (* let rec id = expr in expr *)
                | IfE of term * term * term             (* if expr then expr else expr *)
                | MatchE of term * (pattern * term) list    (* match expr with pattern -> expr | ... *)
                | CodE of term                          (* <expr> *)
                | EscE of term                          (* ~expr *)
                | RunE of term                          (* run expr *)
                | DollarE of path * string              (* path$field *)
            and pattern =
                | VarPat of Ident.t                     (* id *)
                | ConsPat of pattern * Ident.t          (* pattern :: pattern *)
                | PairPat of pattern * pattern          (* pattern, pattern *)
                | WildPat                               (* _ *)
            type simple_type =
                | Var of type_variable                   (* 'a, 'b *)
                | Typeconstr of path * simple_type list  (* constructed type *)
            and type_variable =
                { mutable repres: simple_type option;    (* representative, for union-find *)
                    mutable level: int }                 (* binding level, for generalization *)

            let ident_eq = Ident.create "=="
            let ident_neq = Ident.create "<>"
            let ident_lt = Ident.create "<"
            let ident_lteq = Ident.create "<="
            let ident_gt = Ident.create ">"
            let ident_gteq = Ident.create ">="
            let ident_conj = Ident.create "&&"
            let ident_disj = Ident.create "||"
            let ident_plus = Ident.create "+"
            let ident_minus = Ident.create "-"
            let ident_star = Ident.create "*"
            let ident_slash = Ident.create "/"
            let ident_comma = Ident.create ","
            let ident_fst = Ident.create "fst"
            let ident_snd = Ident.create "snd"

            let val_ids = [
                ident_eq; ident_neq; ident_lt; ident_lteq; ident_gt; ident_gteq; 
                ident_conj; ident_disj;
                ident_plus; ident_minus; ident_star; ident_slash;
                ident_comma; ident_fst; ident_snd
            ]

            let ident_arrow = Ident.create "->"
            let path_arrow = IdentP ident_arrow
            let arrow_type t1 t2 = Typeconstr(path_arrow, [t1;t2])

            let path_star = IdentP ident_star
            let star_type t1 t2 = Typeconstr(path_star, [t1;t2])

            let ident_int = Ident.create "int"
            let path_int = IdentP ident_int
            let int_type = Typeconstr(path_int, [])
            
            let ident_bool = Ident.create "bool"
            let path_bool = IdentP ident_bool
            let bool_type = Typeconstr(path_bool, [])

            let ident_string = Ident.create "string"
            let path_string = IdentP ident_string
            let string_type = Typeconstr(path_string, [])

            let ident_code = Ident.create "code"
            let path_code = IdentP ident_code
            let code_type t = Typeconstr(path_code, [t])

            let ident_csp = Ident.create "%"
            let path_csp = IdentP ident_csp
            let csp_type t = Typeconstr(path_csp, [t])

            let ident_dollar = Ident.create "$"
            let path_dollar = IdentP ident_dollar
            let dollar_type t1 t2 = Typeconstr(path_dollar, [t1;t2])

            let ident_list = Ident.create "list"
            let path_list = IdentP ident_list
            let list_type t = Typeconstr(path_list, [t])

            let type_ids = [
                ident_arrow; ident_star; ident_list;
                ident_int; ident_bool; ident_string; 
                ident_code; ident_csp; ident_dollar
            ]

            type val_type =
                { quantif: type_variable list;           (* quantified variables *)
                    body: simple_type }                  (* body of type scheme *)
            type def_type =
                { params: type_variable list;            (* list of parameters *)
                    defbody: simple_type }               (* body of type definition *)
            type kind = { arity: int }

            let rec subst_type subst = function
                | Var {repres = None} as ty -> ty
                | Var {repres = Some ty} -> subst_type subst ty
                | Typeconstr(p, tl) ->
                    Typeconstr(Subst.path p subst, List.map (subst_type subst) tl)
            let subst_valtype vty subst =
                { quantif = vty.quantif;
                    body = subst_type subst vty.body }
            let subst_deftype def subst =
                { params = def.params;
                    defbody = subst_type subst def.defbody }
            let subst_kind kind subst = kind
        end

    module Mod = 
        struct
            module Core = Core

            type type_decl =
                { kind: Core.kind;
                    manifest: Core.def_type option }          (* abstract or manifest *)
            type mod_type =
                | Signature of signature                    (* sig ... end *)
                | FunS of Ident.t * mod_type * mod_type     (* functor(X: mty) mty *)
                | CodS of mod_type                          (* mty mcod *)
            and signature = specification list
            and specification =
                | ValS of Ident.t * Core.val_type      (* val x: ty *)
                | TypeS of Ident.t * type_decl           (* type t :: k [= ty] *)
                | ModS of Ident.t * mod_type          (* module X: mty *)
            type mod_term =
                | Longident of path                         (* X or X.Y.Z *)
                | Structure of structure                    (* struct ... end *)
                | FunM of Ident.t * mod_type * mod_term     (* functor (X: mty) mod *)
                | AppM of mod_term * mod_term               (* mod1(mod2) *)
                | Constraint of mod_term * mod_type         (* (mod : mty) *)
                | CodM of mod_term                          (* <<mod>> *)
                | EscM of mod_term                          (* ~~mod *)
                | RunM of mod_term * mod_type               (* Runmod(mod : mty) *)
                | DollarM of path * string                  (* path$field *)
            and structure = definition list
            and definition =
                | LetM of Ident.t * Core.term               (* let x = expr *)
                | LetRecM of Ident.t * Core.term            (* let x = expr *)
                | TypeM of Ident.t * Core.kind * Core.def_type   (* type t :: k = ty *)
                | ModM of Ident.t * mod_term                (* module X = mod *)

            let subst_typedecl decl sub =
                { kind = Core.subst_kind decl.kind sub;
                    manifest = match decl.manifest with
                            | None -> None
                            | Some dty -> Some(Core.subst_deftype dty sub) }
            let rec subst_modtype mty sub =
                match mty with
                | Signature sg -> Signature(List.map (subst_sig_item sub) sg)
                | FunS(id, mty1, mty2) ->
                    FunS(id, subst_modtype mty1 sub, subst_modtype mty2 sub)
                | CodS(mty) -> CodS(subst_modtype mty sub)
            and subst_sig_item sub = function
                | ValS(id, vty) -> ValS(id, Core.subst_valtype vty sub)
                | TypeS(id, decl) -> TypeS(id, subst_typedecl decl sub)
                | ModS(id, mty) -> ModS(id, subst_modtype mty sub)
        end

end