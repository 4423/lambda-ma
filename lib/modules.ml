exception Error of string
let error s = raise(Error s)

open Syntax

module rec Env :
    sig
        type binding =
            | Value of Mod.Core.val_type
            | Type of Mod.type_decl
            | Module of Mod.mod_type
        type t = binding Ident.tbl
        (* type t *)
        val empty: t
        val add_value: Ident.t -> Mod.Core.val_type -> t -> t
        val add_type: Ident.t -> Mod.type_decl -> t -> t    
        val add_module: Ident.t -> Mod.mod_type -> t -> t    
        val add_spec: Mod.specification -> t -> t
        val add_signature: Mod.signature -> t -> t
        val find_value: path -> t -> Mod.Core.val_type
        val find_type: path -> t -> Mod.type_decl
        val find_module: path -> t -> Mod.mod_type
    end
    =
    struct
        type binding =
            | Value of Mod.Core.val_type
            | Type of Mod.type_decl
            | Module of Mod.mod_type
        type t = binding Ident.tbl
        let empty = Ident.emptytbl
        let add_value id vty env = Ident.add id (Value vty) env
        let add_type id decl env = Ident.add id (Type decl) env
        let add_module id mty env = Ident.add id (Module mty) env
        let add_spec item env =
            match item with
            | Mod.ValS(id, vty) -> add_value id vty env
            | Mod.TypeS(id, decl) -> add_type id decl env
            | Mod.ModS(id, mty) -> add_module id mty env
        let add_signature = List.fold_right add_spec
        let rec find path env =
            match path with
            | IdentP id ->
                Ident.find id env
            | DotP(root, field) ->
                begin
                match find_module root env with
                | Mod.Signature sg -> find_field root field Subst.identity sg
                | _ -> error "structure expected in dot access"
                end
            | AppP(p1, p2) ->
                match (find_module p1 env, find_module p2 env) with
                | (Mod.FunS(id, mty1, mty2), mty3) -> 
                    begin
                    try
                        ModTyping.modtype_match env mty1 mty3;
                        Module mty2
                    with _ ->
                        error "type of path application is incorrect"
                    end
                | _ -> error "functor expected in path application"
        and find_field p field subst = function
            | [] -> error "no such field in structure"
            | Mod.ValS(id, vty) :: rem ->
                if Ident.name id = field
                then Value(Mod.Core.subst_valtype vty subst)
                else find_field p field subst rem
            | Mod.TypeS(id, decl) :: rem ->
                if Ident.name id = field
                then Type(Mod.subst_typedecl decl subst)
                else find_field p field
                        (Subst.add id (DotP(p, Ident.name id)) subst) rem
            | Mod.ModS(id, mty) :: rem ->
                if Ident.name id = field
                then Module(Mod.subst_modtype mty subst)
                else find_field p field
                        (Subst.add id (DotP(p, Ident.name id)) subst) rem
        and find_value path env =
            match find path env with
            Value vty -> vty | _ -> error "value field expected"   
        and find_type path env =
            match find path env with
            Type decl -> decl | _ -> error "type field expected"   
        and find_module path env =
            match find path env with
            Module mty -> mty | _ -> error "module field expected"   
    end

and CoreTyping :
    sig
        (* Typing functions *)
        val type_term: Env.t -> Core.term -> Core.val_type
        val kind_deftype: Env.t -> Core.def_type -> Core.kind
        val check_valtype: Env.t -> Core.val_type -> unit
        val check_kind: Env.t -> Core.kind -> unit
        (* Type matching functions *)
        val valtype_match: Env.t -> Core.val_type -> Core.val_type -> bool
        val deftype_equiv: Env.t -> Core.kind -> Core.def_type -> Core.def_type -> bool
        val kind_match: Env.t -> Core.kind -> Core.kind -> bool
        val deftype_of_path: path -> Core.kind -> Core.def_type
        (* Functions to eliminate dependencies on a particular identifier,
            as described in section 5.5 *)
        val nondep_valtype: Env.t -> Ident.t -> Core.val_type -> Core.val_type
        val nondep_deftype: Env.t -> Ident.t -> Core.def_type -> Core.def_type
        val nondep_kind:    Env.t -> Ident.t -> Core.kind -> Core.kind

        (* 外部から使うために追加。 open してもシグネチャに書いてある関数しか使えない *)
        val typerepr: Core.simple_type -> Core.simple_type
        val ident_arrow: Ident.t
        val ident_int: Ident.t
        val ident_star: Ident.t
        val int_type: Core.simple_type
        val arrow_type: Core.simple_type -> Core.simple_type -> Core.simple_type
        val path_arrow: path
        val path_star: path
        val newvar: unit -> Core.type_variable
        val begin_def: unit -> unit
        val end_def: unit -> unit
        val generalize: Core.simple_type -> Core.val_type
        val unify: Env.t -> Core.simple_type -> Core.simple_type -> unit
    end
    = 
    struct
        open Core

        let rec typerepr = function
            | Var({repres = Some ty} as var) ->
                let r = typerepr ty in var.repres <- Some r; r
            | ty -> ty

        let current_level = ref 0
        let begin_def() = incr current_level
        let end_def() = decr current_level
        let newvar() = {repres = None; level = !current_level}
        let unknown() = Var(newvar())

        let rec subst_vars subst ty =
            match typerepr ty with
            | Var var as tyvar ->
                begin try List.assq var subst with Not_found -> tyvar end
            | Typeconstr(p, tl) -> Typeconstr(p, List.map (subst_vars subst) tl)

        exception Cannot_expand
        let expand_manifest env path args =
            match Env.find_type path env with
            | {Mod.manifest = None} ->
                raise Cannot_expand
            | {Mod.manifest = Some def} ->
                subst_vars (List.combine def.params args) def.defbody

        (* Expand abbreviations in ty1 and ty2 until their top constructor match *)
        let rec scrape_types env ty1 ty2 =
            let repr1 = typerepr ty1 and repr2 = typerepr ty2 in
            match (repr1, repr2) with
            | (Typeconstr(path1, args1), Typeconstr(path2, args2)) ->
                if path_equal path1 path2 then
                    (repr1, repr2)
                else begin
                    try
                    scrape_types env (expand_manifest env path1 args1) repr2
                    with Cannot_expand ->
                    try
                        scrape_types env repr1 (expand_manifest env path2 args2)
                    with Cannot_expand ->
                        (repr1, repr2)
                end
            | (Typeconstr(path, args), _) ->
                begin try
                    scrape_types env (expand_manifest env path args) repr2
                with Cannot_expand ->
                    (repr1, repr2)
                end
            | (_, Typeconstr(path, args)) ->
                begin try
                    scrape_types env repr1 (expand_manifest env path args)
                with Cannot_expand ->
                    (repr1, repr2)
                end
            | (_, _) -> (repr1, repr2)

        let rec occur_check var ty =
            match typerepr ty with
            | Var var' -> if var == var' then error "cycle in unification"
            | Typeconstr(p, tl) -> List.iter (occur_check var) tl

        let rec update_levels level_max ty =
            match typerepr ty with
            | Var v -> if v.level > level_max then v.level <- level_max
            | Typeconstr(p, tl) -> List.iter (update_levels level_max) tl

        let rec unify env t1 t2 =
            match scrape_types env t1 t2 with
            | (r1, r2) when r1 == r2 -> ()
            | (Var v, r2) ->
                occur_check v r2;
                update_levels v.level r2;
                v.repres <- Some r2
            | (r1, Var v) ->
                occur_check v r1;
                update_levels v.level r1;
                v.repres <- Some r1
            | (Typeconstr(path1, args1), Typeconstr(path2, args2))
            when path1 = path2 ->
                List.iter2 (unify env) args1 args2
            | (_, _) ->
                error "type constructor mismatch in unification"

        let generalize ty =
            let rec gen_vars vars ty =
                match typerepr ty with
                | Var v ->
                    if v.level > !current_level && not (List.memq v vars)
                    then v :: vars
                    else vars
                | Typeconstr(path, tl) ->
                    List.fold_left gen_vars vars tl in
            { quantif = gen_vars [] ty; body = ty }

        let trivial_scheme ty =
            { quantif = []; body = ty }

        let instance vty =
            match vty.quantif with
            | [] -> vty.body
            | vars -> subst_vars (List.map (fun v -> (v, unknown())) vars) vty.body

        let ident_arrow = Ident.create "->"
        let path_arrow = IdentP ident_arrow
        let arrow_type t1 t2 = Typeconstr(path_arrow, [t1;t2])
        let ident_int = Ident.create "int"
        let path_int = IdentP ident_int
        let int_type = Typeconstr(path_int, [])
        let ident_star = Ident.create "*"
        let path_star = IdentP ident_star

        let rec infer_type env = function
            | Constant n -> int_type
            | Longident path -> instance (Env.find_value path env)
            | FunE(param, body) ->
                let type_param = unknown() in
                let type_body =
                infer_type (Env.add_value param (trivial_scheme type_param) env) 
                            body in
                arrow_type type_param type_body
            | AppE(funct, arg) ->
                let type_funct = infer_type env funct in
                let type_arg = infer_type env arg in
                let type_result = unknown() in
                unify env type_funct (arrow_type type_arg type_result);
                type_result
            | LetE(ident, arg, body) ->
                begin_def();
                let type_arg = infer_type env arg in
                end_def();
                infer_type (Env.add_value ident (generalize type_arg) env) body

        let rec check_simple_type env params ty =
        match typerepr ty with
            | Var v ->
                if not (List.memq v params) then error "free type variable"
            | Typeconstr(path, tl) ->
                let arity = (Env.find_type path env).Mod.kind.arity in
                if List.length tl <> arity then error "arity error";
                List.iter (check_simple_type env params) tl

        let kind_deftype env def =
            check_simple_type env def.params def.defbody;
            {arity = List.length def.params}

        let check_valtype env vty =
            check_simple_type env vty.quantif vty.body

        let check_kind env kind = ()

        let type_term env term =
            begin_def();
            let ty = infer_type env term in
            end_def();
            generalize ty

        let valtype_match env vty1 vty2 =
            let rec filter ty1 ty2 =
                match scrape_types env ty1 ty2 with
                | (Var v, ty2) ->
                    if List.memq v vty2.quantif
                    then false
                    else (v.repres <- Some ty2; true)
                | (Typeconstr(path1, tl1), Typeconstr(path2, tl2)) ->
                    path1 = path2 && List.for_all2 filter tl1 tl2
                | (_, _) -> false in
            filter (instance vty1) vty2.body

        let deftype_equiv env kind def1 def2 =
            let rec equiv ty1 ty2 =
                match scrape_types env ty1 ty2 with
                | (Var v1, Var v2) -> v1 == v2
                | (Typeconstr(path1, args1), Typeconstr(path2, args2)) ->
                    path1 = path2 && List.for_all2 equiv args1 args2
                | (_, _) -> false in
            let subst =
                List.map2 (fun v1 v2 -> (v2, Var v1)) def1.params def2.params in
            equiv def1.defbody (subst_vars subst def2.defbody)

        let kind_match env kind1 kind2 =
            kind1.arity = kind2.arity

        let deftype_of_path path kind =
            let rec make_params n =
                if n <= 0 then [] else newvar() :: make_params (n-1) in
            let params = make_params kind.arity in
            { params = params;
                defbody = Typeconstr(path, List.map (fun v -> Var v) params) }

        (* Elimination of dependencies on a given module identifier
        by repeated expansion of type paths rooted at that identifier.
        Those functions are used only with the relaxed typing rule
        for functor applications described in section 5.5 and implemented
        in the file modules.ml.extended *)

        let rec is_rooted_at id = function
            | IdentP id' -> Ident.equal id id'
            | DotP(p, s) -> is_rooted_at id p
            | AppP(p1, p2) -> is_rooted_at id p1 && is_rooted_at id p2

        let rec nondep_type env id ty =
        match typerepr ty with
            | Var v as tvar -> tvar
            | Typeconstr(path, args) ->
                if is_rooted_at id path then begin
                    try
                    nondep_type env id (expand_manifest env path args)
                    with Cannot_expand ->
                    raise Not_found
                end else
                    Typeconstr(path, List.map (nondep_type env id) args)

        let nondep_valtype env id vty =
            { quantif = vty.quantif; body = nondep_type env id vty.body }
        let nondep_deftype env id def =
            { params = def.params; defbody = nondep_type env id def.defbody }
        let nondep_kind env id kind =
            kind
    end

and ModTyping :
    sig
        val type_module: Env.t -> Mod.mod_term -> Mod.mod_type
        (* 公開する必要ある？ しかも引数の個数が違う *)
        (* val type_definition: Env.t -> Mod.definition -> Mod.specification *)
        val modtype_match: Env.t -> Mod.mod_type -> Mod.mod_type -> unit
    end
    =
    struct
        module CT = CoreTyping
        open Mod
        
        let rec modtype_match env mty1 mty2 =
            match (mty1, mty2) with
            | (Signature sig1, Signature sig2) ->
                let (paired_components, subst) =
                pair_signature_components sig1 sig2 in
                let ext_env = Env.add_signature sig1 env in
                List.iter (specification_match ext_env subst) paired_components
            | (FunS(param1,arg1,res1), FunS(param2,arg2,res2)) ->
                let subst = Subst.add param1 (IdentP param2) Subst.identity in
                let res1' = Mod.subst_modtype res1 subst in
                modtype_match env arg2 arg1;
                modtype_match (Env.add_module param2 arg2 env) res1' res2
            | (_, _) ->
                error "module type mismatch"
        and pair_signature_components sig1 sig2 =
            match sig2 with
            | [] -> ([], Subst.identity)
            | item2 :: rem2 ->
                let rec find_matching_component = function
                    [] -> error "unmatched signature component"
                | item1 :: rem1 ->
                    match (item1, item2) with
                        (ValS(id1, _), ValS(id2, _))
                        when Ident.name id1 = Ident.name id2 ->
                        (id1, id2, item1)
                    | (TypeS(id1, _), TypeS(id2, _))
                        when Ident.name id1 = Ident.name id2 ->
                        (id1, id2, item1)
                    | (ModS(id1, _), ModS(id2, _))
                        when Ident.name id1 = Ident.name id2 ->
                        (id1, id2, item1)
                    | _ -> find_matching_component rem1 in
                let (id1, id2, item1) = find_matching_component sig1 in
                let (pairs, subst) = pair_signature_components sig1 rem2 in
                ((item1, item2) :: pairs, Subst.add id2 (IdentP id1) subst)
        and specification_match env subst = function
            | (ValS(_, vty1), ValS(_, vty2)) ->
                if not (CT.valtype_match env vty1 (Core.subst_valtype vty2 subst))
                then error "value components do not match"
            | (TypeS(id, decl1), TypeS(_, decl2)) ->
                if not (typedecl_match env id decl1
                                        (Mod.subst_typedecl decl2 subst))
                then error "type components do not match"
            | (ModS(_, mty1), ModS(_, mty2)) ->
                modtype_match env mty1 (Mod.subst_modtype mty2 subst)
        and typedecl_match env id decl1 decl2 =
            CT.kind_match env decl1.kind decl2.kind &&
            (match (decl1.manifest, decl2.manifest) with
            (_, None) -> true
            | (Some typ1, Some typ2) ->
                CT.deftype_equiv env decl2.kind typ1 typ2
            | (None, Some typ2) ->
                CT.deftype_equiv env decl2.kind
                                (CT.deftype_of_path (IdentP id) decl1.kind) typ2)

        (* Section 2.10: Strengthening of module types *)

        let rec strengthen_modtype path mty =
            match mty with
            | Signature sg -> Signature(List.map (strengthen_spec path) sg)
            | FunS(id, arg, res) ->
                FunS(id, arg, strengthen_modtype (AppP(path, IdentP id)) res)
        and strengthen_spec path item =
            match item with
            | ValS(id, vty) -> item
            | TypeS(id, decl) ->
                let m = match decl.manifest with
                    | None -> Some(CT.deftype_of_path
                                            (DotP(path, Ident.name id)) decl.kind)
                    | Some ty -> Some ty 
                in TypeS(id, {kind = decl.kind; manifest = m})
            | ModS(id, mty) ->
                ModS(id, strengthen_modtype (DotP(path, Ident.name id)) mty)

        (* Section 5.5: Elimination of dependencies on a given identifier *)

        let rec nondep_modtype env param = function
            | Signature sg -> Signature(nondep_signature env param sg)
            | FunS(id, arg, res) ->
                FunS(id, nondep_modtype env param arg,
                        nondep_modtype (Env.add_module id arg env) param res)
        and nondep_signature env param = function
            | [] -> []
            | item :: rem ->
                let rem' = nondep_signature (Env.add_spec item env) param rem in
                match item with
                | ValS(id, vty) -> 
                    ValS(id, CT.nondep_valtype env param vty) :: rem'
                | TypeS(id, decl) ->
                    let manifest' = 
                        match decl.manifest with
                        | None -> None
                        (* TODO: パスではない引数は抽象型にしてもいいと思い変更したが要確認 *)
                        | Some ty -> Some(CT.nondep_deftype env param ty) in
                        (* | Some ty -> None in *)
                    let decl' =
                        {kind = CT.nondep_kind env param decl.kind;
                            manifest = manifest'} in
                    TypeS(id, decl') :: rem'
                | ModS(id, mty) ->
                    ModS(id, nondep_modtype env param mty) :: rem'

        (* Continuation of section 2.8: Type-checking the module language *)

        let rec check_modtype env = function
            | Signature sg -> check_signature env [] sg
            | FunS(param, arg, res) ->
                check_modtype env arg;
                check_modtype (Env.add_module param arg env) res
        and check_signature env seen = function
            | [] -> ()
            | ValS(id, vty) :: rem ->
                if List.mem (Ident.name id) seen
                then error "repeated value name";
                CT.check_valtype env vty;
                check_signature env (Ident.name id :: seen) rem
            | TypeS(id, decl) :: rem ->
                if List.mem (Ident.name id) seen
                then error "repeated type name";
                CT.check_kind env decl.kind;
                begin match decl.manifest with
                    None -> () 
                | Some typ ->
                    if not (CT.kind_match env (CT.kind_deftype env typ)
                                                decl.kind)
                    then error "kind mismatch in manifest type specification"
                end;
                check_signature (Env.add_type id decl env)
                                (Ident.name id :: seen) rem
            | ModS(id, mty) :: rem ->
                if List.mem (Ident.name id) seen 
                then error "repeated module name";
                check_modtype env mty;
                check_signature (Env.add_module id mty env) 
                                (Ident.name id :: seen) rem

        let rec type_module env = function
            | Longident path ->
                strengthen_modtype path (Env.find_module path env)
            | Structure str ->
                Signature(type_structure env [] str)
            | FunM(param, mty, body) ->
                check_modtype env mty;
                FunS(param, mty,
                    type_module (Env.add_module param mty env) body)
            | AppM(funct, arg) ->
                (* The relaxed typing rule for functor applications,
                    as described in section 5.5 *)
                begin
                match type_module env funct with
                | FunS(param, mty_param, mty_res) ->
                    let mty_arg = type_module env arg in
                    modtype_match env mty_arg mty_param;
                    begin
                    match arg with
                    | Longident path ->
                        subst_modtype mty_res
                                    (Subst.add param path Subst.identity)
                    | _ ->
                        try
                            let mty_res' = nondep_modtype (Env.add_module param mty_arg env)
                                            param mty_res in
                            (* 結果型の型コンポーネントのうち自由変数が含まれているマニフェスト型を抽象型にする *)
                            eliminate_module env mty_res'
                        with Not_found ->
                            error "cannot eliminate dependency in application"
                    end
                | _ -> error "application of a non-functor"
                end
            | Constraint(modl, mty) ->
                check_modtype env mty;
                modtype_match env (type_module env modl) mty;
                mty
        and type_structure env seen = function
            | [] -> []
            | stritem :: rem ->
                let (sigitem, seen') = type_definition env seen stritem in
                sigitem :: type_structure (Env.add_spec sigitem env) seen' rem
        and type_definition env seen = function
            | LetM(id, term) ->
                if List.mem (Ident.name id) seen
                then error "repeated value name";
                (ValS(id, CT.type_term env term), Ident.name id :: seen)
            | ModM(id, modl) ->
                if List.mem (Ident.name id) seen
                then error "repeated module name";
                (ModS(id, type_module env modl), Ident.name id :: seen)
            | TypeM(id, kind, typ) ->
                if List.mem (Ident.name id) seen
                then error "repeated type name";
                CT.check_kind env kind;
                if not (CT.kind_match env (CT.kind_deftype env typ) kind)
                then error "kind mismatch in type definition";
                (TypeS(id, {kind = kind; manifest = Some typ}),
                Ident.name id :: seen)

        and eliminate_module env = function
            | Signature sg -> Signature(eliminate_signature env sg)
            | FunS(param, arg, res) ->
                FunS(param, 
                    eliminate_module env arg, 
                    eliminate_module (Env.add_module param arg env) res)
        and eliminate_signature env = function
            | [] -> []
            | ValS(id, vty) as v :: rem ->
                v :: eliminate_signature env rem
            | TypeS(id, decl) :: rem ->
                let decl' = 
                    begin match decl.manifest with
                    | None -> decl
                    | Some typ ->
                        try
                            (* typ に自由変数が含まれていないかを kind_deftype でチェック *)
                            CT.kind_deftype env typ;
                            decl
                        with Not_found ->
                            { kind = decl.kind; manifest = None }
                    end in
                TypeS(id, decl') :: eliminate_signature (Env.add_type id decl env) rem
            | ModS(id, mty) as m :: rem ->
                m :: eliminate_signature (Env.add_module id mty env) rem
    end




(* 以下コピペして適宜モジュール名を変更しただけ *)




module type SCOPE =
    sig
        type t
        val empty: t
        val enter_value: Ident.t -> t -> t
        val enter_type: Ident.t -> t -> t
        val enter_module: Ident.t -> t -> t
        val value_path: path -> t -> path
        val type_path: path -> t -> path
        val module_path: path -> t -> path
    end

module Scope : SCOPE =
    struct
        type t =
            { values: (string * Ident.t) list;
                types: (string * Ident.t) list;
                modules: (string * Ident.t) list }
        let empty = { values = []; types = []; modules = [] }
        let enter_value id sc =
            { values = (Ident.name id, id) :: sc.values;
                types = sc.types; modules = sc.modules }
        let enter_type id sc =
            { types = (Ident.name id, id) :: sc.types;
                values = sc.values; modules = sc.modules }
        let enter_module id sc =
            { modules = (Ident.name id, id) :: sc.modules;
                values = sc.values; types = sc.types }
        let scope_value id sc =
            try List.assoc (Ident.name id) sc.values
            with Not_found -> error("unbound value " ^ Ident.name id)
        let scope_type id sc =
            try List.assoc (Ident.name id) sc.types
            with Not_found -> error("unbound type " ^ Ident.name id)
        let scope_module id sc =
            try List.assoc (Ident.name id) sc.modules
            with Not_found -> error("unbound module " ^ Ident.name id)
        let rec scope_path scope_ident path sc =
            match path with
            | IdentP id -> IdentP(scope_ident id sc)
            | DotP(root, field) -> DotP(scope_path scope_module root sc, field)
        let value_path = scope_path scope_value
        let type_path = scope_path scope_type
        let module_path = scope_path scope_module
    end

module Scoping =
    struct
        open Core
        let rec scope_term sc = function
            | Constant n -> Constant n
            | Longident path -> Longident(Scope.value_path path sc)
            | FunE(id, body) ->
                FunE(id, scope_term (Scope.enter_value id sc) body)
            | AppE(t1, t2) -> AppE(scope_term sc t1, scope_term sc t2)
            | LetE(id, t1, t2) ->
                LetE(id, scope_term sc t1, scope_term (Scope.enter_value id sc) t2)
        let rec scope_simple_type sc = function
            | Var v -> Var v
            | Typeconstr(path, args) ->
                Typeconstr(Scope.type_path path sc,
                            List.map (scope_simple_type sc) args)
        let scope_valtype sc vty =
            { quantif = vty.quantif; body = scope_simple_type sc vty.body }
        let scope_deftype sc def =
            { params = def.params; defbody = scope_simple_type sc def.defbody }
        let scope_kind sc kind = kind
    end

module ModScoping =
    struct
        module CS = Scoping
        open Mod
        let scope_typedecl sc decl =
            { kind = CS.scope_kind sc decl.kind;
                manifest = match decl.manifest with
                            None -> None
                        | Some ty -> Some(CS.scope_deftype sc ty) }
        let rec scope_modtype sc = function
            | Signature sg -> Signature(scope_signature sc sg)
            | FunS(id, arg, res) ->
                FunS(id, scope_modtype sc arg,
                            scope_modtype (Scope.enter_module id sc) res)
        and scope_signature sc = function
            | [] -> []
            | ValS(id, vty) :: rem ->
                ValS(id, CS.scope_valtype sc vty) ::
                scope_signature (Scope.enter_value id sc) rem
            | TypeS(id, decl) :: rem ->
                TypeS(id, scope_typedecl sc decl) ::
                scope_signature (Scope.enter_type id sc) rem
            | ModS(id, mty) :: rem ->
                ModS(id, scope_modtype sc mty) ::
                scope_signature (Scope.enter_module id sc) rem
        let rec scope_module sc = function
            | Longident path -> Longident(Scope.module_path path sc)
            | Structure str -> Structure(scope_structure sc str)
            | FunM(id, arg, body) ->
                FunM(id, scope_modtype sc arg,
                        scope_module (Scope.enter_module id sc) body)
            | AppM(m1, m2) -> AppM(scope_module sc m1, scope_module sc m2)
            | Constraint(m, mty) ->
                Constraint(scope_module sc m, scope_modtype sc mty)
        and scope_structure sc = function
            | [] -> []
            | LetM(id, v) :: rem ->
                LetM(id, CS.scope_term sc v) ::
                scope_structure (Scope.enter_value id sc) rem
            | TypeM(id, kind, dty) :: rem ->
                TypeM(id, CS.scope_kind sc kind, CS.scope_deftype sc dty) ::
                scope_structure (Scope.enter_type id sc) rem
            | ModM(id, m) :: rem ->
                ModM(id, scope_module sc m) ::
                scope_structure (Scope.enter_module id sc) rem
    end


module MLPrint =
    struct
        open Format
        open Core
        open Mod

        let variable_names = ref ([] : (type_variable * string) list)

        let reset_names () = variable_names := []

        let rec print_path = function
            | IdentP id ->
                print_string (Ident.name id)
            | DotP(root, field) ->
                print_path root; print_string "."; print_string field
            | AppP(p1, p2) ->
                print_path p1; print_string "("; print_path p2; print_string ")"

        let rec print_simple_type ty =
        match CoreTyping.typerepr ty with
            | Var v ->
                let name =
                    try
                    List.assq v !variable_names
                    with Not_found ->
                    let n = List.length !variable_names + 1 in
                    let s = String.make 1 (Char.chr(97 + n)) in
                    variable_names := (v, s) :: !variable_names;
                    s in
                print_string "'"; print_string name
            | Typeconstr(path, [t1;t2]) when path = CoreTyping.path_arrow ->
                print_simple_type t1; print_string " -> ";
                print_simple_type t2
            | Typeconstr(path, [t1;t2]) when path = CoreTyping.path_star ->
                print_simple_type t1; print_string " * ";
                print_simple_type t2
            | Typeconstr(path, []) ->
                print_path path
            | Typeconstr(path, [t]) ->
                print_simple_type t; print_string " "; print_path path
            | Typeconstr(path, t1::tl) ->
                print_string "(";
                print_simple_type t1;
                List.iter (fun t -> print_string ", "; print_simple_type t) tl;
                print_string ") "; print_path path

        let print_valtype vty =
        reset_names(); print_simple_type vty.body

        let print_deftype id dty =
        reset_names();
        print_simple_type
            (Typeconstr(IdentP id, List.map (fun v -> Var v) dty.params));
        print_string " ="; print_space();
        print_simple_type dty.defbody

        let print_typedecl id decl =
        match decl.manifest with
            | None ->
                reset_names();
                print_simple_type
                    ((CoreTyping.deftype_of_path (IdentP id) decl.kind).defbody)
            | Some dty ->
                print_deftype id dty

        let rec print_modtype = function
            | Signature sg ->
                open_hvbox 2;
                print_string "sig";
                List.iter
                    (fun item -> print_space(); print_signature_item item) sg;
                print_break 1 (-2);
                print_string "end";
                close_box()
            | FunS(param, arg, body) ->
                open_hvbox 2;
                print_string "functor("; print_string(Ident.name param);
                print_string ": "; print_modtype arg; print_string ")";
                print_space(); print_string "-> "; print_modtype body;
                close_box()
        and print_signature_item = function
            | ValS(id, vty) ->
                open_hvbox 2;
                print_string "val "; print_string(Ident.name id);
                print_string ":"; print_space(); print_valtype vty;
                close_box()
            | TypeS(id, decl) ->
                open_hvbox 2;
                print_string "type "; print_typedecl id decl;
                close_box()
            | ModS(id, mty) ->
                open_hvbox 2;
                print_string "module "; print_string(Ident.name id);
                print_string ":"; print_space(); print_modtype mty;
                close_box()
    end
