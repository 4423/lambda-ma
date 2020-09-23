open Syntax
open Error

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

module type STAGED_SCOPE =
    sig
        type t
        val empty: t
        val enter_value: Ident.t -> int -> t -> t
        val enter_type: Ident.t -> int -> t -> t
        val enter_module: Ident.t -> int -> t -> t
        val value_path: path -> int -> t -> path
        val type_path: path -> int -> t -> path
        val module_path: path -> int -> t -> path
    end

module StagedScope : STAGED_SCOPE =
    struct
        type t = Scope.t array
        let max_level = 2
        let empty = 
            let res = Array.make max_level Scope.empty in
            for i = 0 to max_level - 1 do
                res.(i) <- Scope.empty
            done;
            res
        let check_level lv =
            if lv >= max_level 
            then error "exceeded maximum stage level"
            else if lv < 0
            then error "exceeded minimum stage level"
        let enter_value id lv sc =
            check_level lv;
            sc.(lv) <- Scope.enter_value id sc.(lv);
            sc
        let enter_type id lv sc =
            check_level lv;
            sc.(lv) <- Scope.enter_type id sc.(lv);
            sc
        let enter_module id lv sc =
            check_level lv;
            sc.(lv) <- Scope.enter_module id sc.(lv);
            sc
        let value_path path lv sc =
            check_level lv;
            Scope.value_path path sc.(lv)
        let type_path path lv sc =
            check_level lv;
            Scope.type_path path sc.(lv)
        let module_path path lv sc =
            check_level lv;
            Scope.module_path path sc.(lv)
    end

module Scoping =
    struct
        module Scope = StagedScope
        open Core
        let rec scope_term lv sc = function
            | Constant n -> Constant n
            | Longident path -> Longident(Scope.value_path path lv sc)
            | FunE(id, body) ->
                FunE(id, scope_term lv (Scope.enter_value id lv sc) body)
            | AppE(t1, t2) -> AppE(scope_term lv sc t1, scope_term lv sc t2)
            | LetE(id, t1, t2) ->
                LetE(id, scope_term lv sc t1, scope_term lv (Scope.enter_value id lv sc) t2)
            | LetRecE(id, t1, t2) ->
                LetRecE(id, 
                    scope_term lv (Scope.enter_value id lv sc) t1, 
                    scope_term lv (Scope.enter_value id lv sc) t2)
            | CodE t ->
                CodE(scope_term (lv+1) sc t)
            | EscE t ->
                EscE(scope_term (lv-1) sc t)
            | RunE t ->
                RunE(scope_term lv sc t)
        let rec scope_simple_type lv sc = function
            | Var v -> Var v
            | Typeconstr(path, args) ->
                Typeconstr(Scope.type_path path lv sc,
                            List.map (scope_simple_type lv sc) args)
        let scope_valtype lv sc vty =
            { quantif = vty.quantif; body = scope_simple_type lv sc vty.body }
        let scope_deftype lv sc def =
            { params = def.params; defbody = scope_simple_type lv sc def.defbody }
        let scope_kind lv sc kind = kind
    end

module ModScoping =
    struct
        module CS = Scoping
        module Scope = StagedScope
        open Mod
        let scope_typedecl lv sc decl =
            { kind = CS.scope_kind lv sc decl.kind;
                manifest = match decl.manifest with
                            None -> None
                        | Some ty -> Some(CS.scope_deftype lv sc ty) }
        let rec scope_modtype lv sc = function
            | Signature sg -> Signature(scope_signature lv sc sg)
            | FunS(id, arg, res) ->
                FunS(id, scope_modtype lv sc arg,
                            scope_modtype lv (Scope.enter_module id lv sc) res)
            | CodS mty -> CodS(scope_modtype (lv+1) sc mty)
        and scope_signature lv sc = function
            | [] -> []
            | ValS(id, vty) :: rem ->
                ValS(id, CS.scope_valtype lv sc vty) ::
                scope_signature lv (Scope.enter_value id lv sc) rem
            | TypeS(id, decl) :: rem ->
                TypeS(id, scope_typedecl lv sc decl) ::
                scope_signature lv (Scope.enter_type id lv sc) rem
            | ModS(id, mty) :: rem ->
                ModS(id, scope_modtype lv sc mty) ::
                scope_signature lv (Scope.enter_module id lv sc) rem
        let rec scope_module lv sc = function
            | Longident path -> Longident(Scope.module_path path lv sc)
            | Structure str -> Structure(scope_structure lv sc str)
            | FunM(id, arg, body) ->
                FunM(id, scope_modtype lv sc arg,
                        scope_module lv (Scope.enter_module id lv sc) body)
            | AppM(m1, m2) -> AppM(scope_module lv sc m1, scope_module lv sc m2)
            | Constraint(m, mty) ->
                Constraint(scope_module lv sc m, scope_modtype lv sc mty)
            | CodM(m) -> CodM(scope_module (lv+1) sc m)
            | EscM(m) -> EscM(scope_module (lv-1) sc m)
            | RunM(m, mty) -> RunM(scope_module lv sc m, scope_modtype lv sc mty)
        and scope_structure lv sc = function
            | [] -> []
            | LetM(id, v) :: rem ->
                let c = LetM(id, CS.scope_term lv sc v) in
                c :: scope_structure lv (Scope.enter_value id lv sc) rem
            | LetRecM(id, v) :: rem ->
                let c = LetRecM(id, CS.scope_term lv (Scope.enter_value id lv sc) v) in
                c :: scope_structure lv (Scope.enter_value id lv sc) rem
            | TypeM(id, kind, dty) :: rem ->
                let c = TypeM(id, CS.scope_kind lv sc kind, CS.scope_deftype lv sc dty) in
                c :: scope_structure lv (Scope.enter_type id lv sc) rem
            | ModM(id, m) :: rem ->
                let c = ModM(id, scope_module lv sc m) in
                c :: scope_structure lv (Scope.enter_module id lv sc) rem
    end
