open Syntax
open Modules

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
