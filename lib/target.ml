open Identifier

module Syntax = struct

    type path =
        | IdentP of Ident.t             (* identifier *)
        | DotP of path * string         (* access to a module component *)
        | AppP of path * path           (* functor application *)

    module Core = 
        struct
            type term =
                | IntE of int                           (* integer constants *)
                | StrE of string                        (* string constants *)
                | BoolE of bool                         (* boolean constants *)
                | Longident of path                     (* id or mod.mod...id *)
                | FunE of Ident.t * term                (* fun id -> expr *)
                | AppE of term * term                   (* expr(expr) *)
                | LetE of Ident.t * term * term         (* let id = expr in expr *)
                | LetRecE of Ident.t * term * term      (* let rec id = expr in expr *)
                | IfE of term * term * term             (* if expr then expr else expr *)
                | MatchE of term * (pattern * term) list    (* match expr with pattern -> expr | ... *)
                | CodE of term                          (* <expr> *)
                | EscE of term                          (* ~expr *)
                | RunE of term                          (* run expr *)
                | GenletE of term                       (* genlet expr *)
            and pattern =
                | VarPat of Ident.t                     (* id *)
                | ConsPat of pattern * Ident.t          (* pattern :: pattern *)
                | PairPat of pattern * pattern          (* pattern, pattern *)
                | WildPat 
            type simple_type =
                | Var of type_variable                  (* 'a, 'b *)
                | Typeconstr of path * simple_type list (* constructed type *)
            and type_variable =
                { mutable repres: simple_type option;   (* representative, for union-find *)
                    mutable level: int }                (* binding level, for generalization *)
            type val_type =
                { quantif: type_variable list;          (* quantified variables *)
                    body: simple_type }                 (* body of type scheme *)
            type def_type =
                { params: type_variable list;           (* list of parameters *)
                    defbody: simple_type }              (* body of type definition *)
            type kind = { arity: int }

            let code_path = IdentP (Ident.create "code")
            let code_type t = Typeconstr(code_path, [t])
        end

    module Mod =
        struct
            type mod_term =
                | Longident of path                             (* X or X.Y.Z *)
                | Structure of structure                        (* struct ... end *)
                | FunM of Ident.t * mod_type * mod_term         (* functor (X: mty) mod *)
                | AppM of mod_term * mod_term                   (* mod1(mod2) *)
                | Constraint of mod_term * mod_type             (* (mod : mty) *)
            and structure = definition list
            and definition =
                | LetM of Ident.t * Core.term                   (* let x = expr *)
                | LetRecM of Ident.t * Core.term                (* let x = expr *)
                | TypeM of Ident.t * Core.kind * Core.def_type  (* type t :: k = ty *)
                | ModM of Ident.t * mod_term                    (* module X = mod *)
            and toplevel =
                | SignatureDec of Ident.t * mod_type
                | StructureDec of Ident.t * mod_term
                | LetDec of Ident.t * Core.term
                | LetRecDec of Ident.t * Core.term
                | TypeDec of Ident.t * Core.kind * Core.def_type
            and mod_type =
                | LongidentS of path                            (* X or X.Y.Z *)
                | Signature of signature                        (* sig ... end *)
                | FunS of Ident.t * mod_type * mod_type         (* functor(X: mty) mty *)
                | SharingS of mod_type * mod_constraint         (* mty with constraint *)
            and signature = specification list
            and specification =
                | ValS of Ident.t * Core.val_type               (* val x: ty *)
                | TypeS of Ident.t * type_decl                  (* type t :: k [= ty] *)
                | ModS of Ident.t * mod_type                    (* module X: mty *)
            and mod_constraint =
                | TypeC of Ident.t * Core.def_type              (* type t = ty *)
            and type_decl =
                { kind: Core.kind;
                    manifest: Core.def_type option }            (* abstract or manifest *)
        end

end


module Print = struct

    open Printf
    open Syntax
    open Mod
    open Core

    let indent = ref 0
    let indent_incr () = indent := !indent + 2
    let indent_decr () = indent := !indent - 2
    let i (s : string) = sprintf "%s%s" (String.make !indent ' ') s

    let rec f: Syntax.Mod.toplevel list -> string =
        fun toplevel_list -> 
            String.concat "\n" @@ List.map toplevel toplevel_list
    
    and toplevel = function
        | SignatureDec (id, mty) -> sprintf "module type %s = %s" (Ident.name id) (mod_type mty)
        | StructureDec (id, modl) -> sprintf "module %s = %s" (Ident.name id) (mod_term modl)
        | LetDec (id, term) -> sprintf "let %s = %s" (Ident.name id) (core_term term)
        | LetRecDec (id, term) -> sprintf "let rec %s = %s" (Ident.name id) (core_term term)
        | TypeDec (id, kind, dty) -> sprintf "type %s = %s" (Ident.name id) (def_type dty)

    and path = function
        | IdentP id     -> Ident.name id
        | DotP (p, s)   -> sprintf "%s.%s" (path p) s
        | AppP (p1, p2) -> sprintf "%s(%s)" (path p1) (path p2)

    and mod_term = function
        | Longident p            -> path p
        | Structure str          -> let s1 = "struct" in
                                    indent_incr ();
                                    let s2 = structure str in
                                    indent_decr ();
                                    let s3 = i @@ "end" in
                                    s1^s2^s3
        | FunM (id, mty, body)   -> sprintf "(functor (%s : %s) -> %s)" (Ident.name id) (mod_type mty) (mod_term body)
        | AppM (funct, arg)      -> sprintf "%s(%s)" (mod_term funct) (mod_term arg)
        | Constraint (modl, mty) -> sprintf "(%s : %s)" (mod_term modl) (mod_type mty)

    and structure str =
        if List.length str = 0 then " "
        else sprintf "\n%s\n" (String.concat "\n" @@ List.map definition str)
    and definition = function
        | LetM(id, term)       -> i @@ sprintf "let %s = %s" (Ident.name id) (core_term term)
        | LetRecM(id, term)    -> i @@ sprintf "let rec %s = %s" (Ident.name id) (core_term term)
        | TypeM(id, kind, dty) -> i @@ sprintf "type %s = %s" (Ident.name id) (def_type dty)
        | ModM(id, modl)       -> i @@ sprintf "module %s = %s" (Ident.name id) (mod_term modl)

    and mod_type = function
        | LongidentS p        -> path p 
        | Signature sg        -> let s1 = "sig" in
                                 indent_incr ();
                                 let s2 = signature sg in
                                 indent_decr ();
                                 let s3 = i @@ "end" in
                                 s1^s2^s3
        | FunS (id, arg, res) -> sprintf "(functor (%s : %s) -> %s)" (Ident.name id) (mod_type arg) (mod_type res)
        | SharingS (mty, c)   -> sprintf "%s with %s" (mod_type mty) (mod_constraint c)
    
    and signature sg =
        if List.length sg = 0 then " "
        else sprintf "\n%s\n" (String.concat "\n" @@ List.map specification sg)
    and specification = function
        | ValS (id, vty)   -> i @@ sprintf "val %s: %s" (Ident.name id) (val_type vty)
        | TypeS (id, decl) -> begin match type_decl decl with
                              | None    -> i @@ sprintf "type %s" (Ident.name id)
                              | Some ty -> i @@ sprintf "type %s = %s" (Ident.name id) ty
                              end
        | ModS (id, mty)   -> i @@ sprintf "module %s: %s"(Ident.name id) (mod_type mty)
    
    and mod_constraint = function
        | TypeC (id, dty) -> sprintf "type %s = %s" (Ident.name id) (def_type dty)

    and type_decl decl =
        match decl.manifest with
        | None     -> None
        | Some dty -> Some (def_type dty)

    and core_term = function
        | IntE c                  -> string_of_int c
        | StrE s                  -> sprintf "\"%s\"" s
        | BoolE b                 -> if b then "true" else "false"
        | Longident p             -> path p
        | FunE (id, term)         -> sprintf "(fun %s -> %s)" (Ident.name id) (core_term term)
        | AppE (AppE (Longident (IdentP id), arg1), arg2) when is_binop id -> 
            sprintf "(%s %s %s)" (core_term arg1) (Ident.name id) (core_term arg2)
        | AppE (funct, arg)       -> sprintf "(%s %s)" (core_term funct) (core_term arg)
        | LetE (id, arg, body)    -> sprintf "let %s = %s in %s" (Ident.name id) (core_term arg) (core_term body)
        | LetRecE (id, arg, body) -> sprintf "let rec %s = %s in %s" (Ident.name id) (core_term arg) (core_term body)
        | IfE (t1, t2, t3)        -> sprintf "if %s then %s else %s" (core_term t1) (core_term t2) (core_term t3)
        | MatchE (t, cs)          -> sprintf "match %s with %s" (core_term t) (pattern_clauses cs)
        | CodE term               -> sprintf ".<%s>." (core_term term)
        | EscE term               -> sprintf ".~(%s)" (core_term term)
        | RunE term               -> sprintf "Runcode.run (%s)" (core_term term)
        | GenletE term            -> sprintf "genlet %s" (core_term term)
    and is_binop id =
        List.mem (Ident.name id) [","; "+"; "-"; "*"; "/"; "=="; "<>"; "<"; "<="; ">"; ">="; "&&"; "||"]
    and pattern_clauses cs =
        String.concat " | " @@ List.map pattern_clause cs
    and pattern_clause (pat, term) =
        sprintf "%s -> %s" (pattern pat) (core_term term)
    and pattern = function
        | VarPat id -> Ident.name id
        | ConsPat (hd_ptn, tl_id) -> sprintf "%s::%s" (pattern hd_ptn) (Ident.name tl_id)
        | PairPat (p1, p2) -> sprintf "(%s, %s)" (pattern p1) (pattern p2)
        | WildPat -> "_"

    and core_type = function
        | Var tvar           -> type_variable tvar
        | Typeconstr (p, []) -> path p
        | Typeconstr (IdentP id, [t1;t2]) when Ident.name id = "->" ->
            sprintf "(%s) -> %s" (core_type t1) (core_type t2)
        | Typeconstr (IdentP id, [t1;t2]) when Ident.name id = "*" ->
            sprintf "(%s) * %s" (core_type t1) (core_type t2)
        | Typeconstr (IdentP id, [t]) when Ident.name id = "code" ->
            sprintf "(%s) code" (core_type t)
        | Typeconstr (IdentP id, [t]) when Ident.name id = "list" ->
            sprintf "(%s) list" (core_type t)
        | Typeconstr (p, [t]) ->
            sprintf "%s %s" (core_type t) (path p)
        | Typeconstr (p, th::tl) ->
            sprintf "(%s) %s" (String.concat ", " @@ List.map core_type tl) (path p)

    and type_variable tvar =
        match tvar.repres with
        | None    -> ""
        | Some ty -> core_type ty

    and val_type vty =
        core_type vty.body
            
    and def_type dty =
        core_type dty.defbody

end