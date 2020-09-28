open Identifier
open Source.Syntax
open Error

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
        val find_value_dollar: path -> string -> t -> Mod.Core.val_type
        val find_type_dollar: path -> string -> t -> Mod.type_decl
        val find_module_dollar: path -> string -> t -> Mod.mod_type
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
                begin
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
                end
            | DollarP(root, field) ->
                find_dollar root field env
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
        
        and find_dollar root field env =
            match find_module root env with
            | Mod.CodS(Mod.Signature sg) ->
                find_field_dollar root field Subst.identity sg
            | _ -> error "signature mcod expected in dollar access"
        and find_field_dollar p field subst = function
            | [] -> error "no such field in structure"
            | Mod.ValS(id, vty) :: rem ->
                if Ident.name id = field
                then Value(Mod.Core.subst_valtype vty subst)
                else find_field_dollar p field subst rem
            | Mod.TypeS(id, decl) :: rem ->
                if Ident.name id = field
                then Type(Mod.subst_typedecl decl subst)
                else find_field_dollar p field
                        (Subst.add id (DollarP(p, Ident.name id)) subst) rem
            | Mod.ModS(id, mty) :: rem ->
                if Ident.name id = field
                then Module(Mod.subst_modtype mty subst)
                else find_field_dollar p field
                        (Subst.add id (DollarP(p, Ident.name id)) subst) rem
        and find_value_dollar root field env =
            match find_dollar root field env with
            Value vty -> vty | _ -> error "value field expected"
        and find_type_dollar root field env =
            match find_dollar root field env with
            Type decl -> decl | _ -> error "type field expected"
        and find_module_dollar root field env =
            match find_dollar root field env with
            Module mty -> mty | _ -> error "module field expected"
    end

and CoreTyping :
    sig
        (* Typing functions *)
        val type_term: level -> Env.t -> Core.term -> Core.val_type
        val type_term_rec: level -> Env.t -> Ident.t -> Core.term -> Core.val_type
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

        let rec infer_type lv env = function
            | IntE n -> int_type
            | StrE s -> string_type
            | BoolE b -> bool_type
            | Longident path -> instance (Env.find_value path env)
            | FunE(param, body) ->
                let type_param = unknown() in
                let type_body =
                infer_type lv (Env.add_value param (trivial_scheme type_param) env) 
                            body in
                arrow_type type_param type_body
            | AppE(funct, arg) ->
                let type_funct = infer_type lv env funct in
                let type_arg = infer_type lv env arg in
                let type_result = unknown() in
                unify env type_funct (arrow_type type_arg type_result);
                type_result
            | LetE(ident, arg, body) ->
                begin_def();
                let type_arg = infer_type lv env arg in
                end_def();
                infer_type lv (Env.add_value ident (generalize type_arg) env) body
            | LetRecE(ident, arg, body) ->
                begin_def();
                let type_param = unknown() in
                let env' = Env.add_value ident (trivial_scheme type_param) env in
                let type_arg = infer_type lv env' arg in
                end_def();
                infer_type lv (Env.add_value ident (generalize type_arg) env) body
            | IfE(cond, t1, t2) ->
                let type_cond = infer_type lv env cond in
                unify env type_cond bool_type;
                let type_t1 = infer_type lv env t1 in
                let type_t2 = infer_type lv env t2 in
                unify env type_t1 type_t2;
                type_t1
            | CodE t ->
                if lv > 0 then error "brackets are allowed only at level 0"
                else
                let ty = infer_type (lv+1) env t in
                code_type ty
            | EscE t ->
                if lv < 1 then error "escape is allowed only at level 1"
                else
                let ty = infer_type (lv-1) env t in
                begin
                match ty with
                | Typeconstr(path, [t]) when path = path_code -> t
                | Var {repres = Some(Typeconstr(path, [t])) } when path = path_code -> t
                | _ -> error "escape for non-code value"
                end
            | RunE t ->
                if lv > 0 then error "run is allowed only at level 0"
                else
                let ty = infer_type lv env t in
                begin
                match ty with
                | Typeconstr(path, [t]) when path = path_code -> t
                | Var {repres = Some(Typeconstr(path, [t])) } when path = path_code -> t
                | _ -> error "run for non-code value"
                end
            | DollarE(root, field) ->
                if lv > 0 then error "dollar access is allowed only at level 0"
                else code_type @@ instance (Env.find_value_dollar root field env)

        let rec check_simple_type env params ty =
        match typerepr ty with
            | Var v ->
                if not (List.memq v params) then error "free type variable"
            | Typeconstr(path, tl) when path = path_dollar ->
                let arity_dollar = (Env.find_type path env).Mod.kind.arity in
                if arity_dollar <> 2 then error "arity error";
                let t1 = List.nth tl 0 in
                let t2 = List.nth tl 1 in
                let (root, field) = match (t1, t2) with
                | (Typeconstr(root, []), Typeconstr(IdentP id, [])) -> root, Ident.name id
                in
                let arity_field = (Env.find_type_dollar root field env).Mod.kind.arity in
                if arity_field <> 0 then error "arity error"
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

        let type_term lv env term =
            begin_def();
            let ty = infer_type lv env term in
            end_def();
            generalize ty

        let type_term_rec lv env ident term =
            begin_def();
            let type_param = unknown() in
            let env' = Env.add_value ident (trivial_scheme type_param) env in
            let ty = infer_type lv env' term in
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
            | DollarP _ -> error "unexpected dollar access"

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
        val type_module: level -> Env.t -> Mod.mod_term -> Mod.mod_type
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
            | (CodS mty1, CodS mty2) ->
                modtype_match env mty1 mty2
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
            | CodS mty -> CodS(strengthen_modtype path mty)
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
            | CodS mty -> CodS(nondep_modtype env param mty)
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
            | CodS mty -> check_modtype env mty
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

        let rec type_module lv env = function
            | Longident path ->
                strengthen_modtype path (Env.find_module path env)
            | Structure str ->
                Signature(type_structure lv env [] str)
            | FunM(param, mty, body) ->
                if lv > 0 then error "functor definitions are allowed only at level 0"
                else
                check_modtype env mty;
                FunS(param, mty,
                    type_module lv (Env.add_module param mty env) body)
            | AppM(funct, arg) ->
                (* The relaxed typing rule for functor applications,
                    as described in section 5.5 *)
                if lv > 0 then error "functor applications are allowed only at level 0"
                else
                begin
                match type_module lv env funct with
                | FunS(param, mty_param, mty_res) ->
                    let mty_arg = type_module lv env arg in
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
                modtype_match env (type_module lv env modl) mty;
                mty
            | CodM(modl) ->
                if lv > 0 then error "brackets are allowed only at level 0"
                else
                let mty = type_module (lv+1) env modl in
                begin
                match mty with
                | CodS _ -> error "nested brackets"
                | _ -> CodS(mty)
                end
            | EscM(modl) ->
                if lv < 1 then error "escape is allowed only at level 1"
                else
                let mty_code = type_module (lv-1) env modl in
                begin
                match mty_code with
                | CodS mty -> mty
                | _ -> error "an escape may appear only within brackets"
                end
            | RunM(modl, mty) ->
                if lv > 0 then error "Runmod is allowed only at level 0"
                else
                check_modtype env mty;
                let mty_code = type_module lv env modl in
                begin
                match mty_code with
                | CodS mty' -> 
                    modtype_match env mty' mty;
                    mty
                | _ -> error "a code of a module is expected for an argument of Runmod"
                end
            | DollarM(root, field) ->
                if lv > 0 then error "dollar access is allowed only at level 0"
                else
                    let mty = Env.find_module_dollar root field env in
                    CodS(strengthen_modtype root mty)
        and type_structure lv env seen = function
            | [] -> []
            | stritem :: rem ->
                let (sigitem, seen') = type_definition lv env seen stritem in
                sigitem :: type_structure lv (Env.add_spec sigitem env) seen' rem
        and type_definition lv env seen = function
            | LetM(id, term) ->
                if List.mem (Ident.name id) seen
                then error "repeated value name";
                (ValS(id, CT.type_term lv env term), Ident.name id :: seen)
            | LetRecM(id, term) ->
                if List.mem (Ident.name id) seen
                then error "repeated value name";
                (ValS(id, CT.type_term_rec lv env id term), Ident.name id :: seen)
            | ModM(id, modl) ->
                if List.mem (Ident.name id) seen
                then error "repeated module name";
                (ModS(id, type_module lv env modl), Ident.name id :: seen)
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
            | CodS mty -> CodS(eliminate_module env mty)
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

let init_env = ref Env.empty

let enter_type id decl =
    init_env := Env.add_type id decl !init_env

let enter_val id ty =
    init_env := Env.add_value id ty !init_env

let _ =
    let open Core in
    enter_type ident_arrow {Mod.kind = {arity = 2}; Mod.manifest = None};
    enter_type ident_star {Mod.kind = {arity = 2}; Mod.manifest = None};
    enter_type ident_int {Mod.kind = {arity = 0}; Mod.manifest = None};
    enter_type ident_bool {Mod.kind = {arity = 0}; Mod.manifest = None};
    enter_type ident_string {Mod.kind = {arity = 0}; Mod.manifest = None};
    enter_type ident_code {Mod.kind = {arity = 1}; Mod.manifest = None};
    enter_type ident_csp {Mod.kind = {arity = 1}; Mod.manifest = None};
    enter_type ident_dollar {Mod.kind = {arity = 2}; Mod.manifest = None};
    List.iter
        (fun id ->
            enter_val id
            { quantif = [];
              body = arrow_type int_type (arrow_type int_type bool_type)})
        [ident_eq; ident_neq; ident_lt; ident_lteq; ident_gt; ident_gteq]; 
    List.iter
        (fun id ->
            enter_val id
            { quantif = [];
              body = arrow_type int_type (arrow_type int_type int_type)})
        [ident_plus; ident_minus; ident_star; ident_slash]; 
    let alpha = CoreTyping.newvar() and beta = CoreTyping.newvar() in
    let talpha = Var alpha and tbeta = Var beta in
    enter_val ident_comma
        { quantif = [alpha;beta];
          body = arrow_type talpha (arrow_type tbeta
                    (Typeconstr(path_star, [talpha; tbeta]))) };
    enter_val ident_fst
        { quantif = [alpha;beta];
          body = arrow_type
                    (Typeconstr(path_star, [talpha; tbeta])) talpha };
    enter_val ident_snd
        { quantif = [alpha;beta];
          body = arrow_type
                    (Typeconstr(path_star, [talpha; tbeta])) tbeta }

let f : Mod.mod_term -> Mod.mod_type = 
        fun modl -> ModTyping.type_module 0 !init_env modl