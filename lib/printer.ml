open Identifier
open Typing
open Format
open Source.Syntax
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
    | DollarP(root, field) ->
        print_path root; print_string "$"; print_string field

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
    | Typeconstr(path, [t1;t2]) when path = path_arrow ->
        print_simple_type t1; print_string " -> ";
        print_simple_type t2
    | Typeconstr(path, [t1;t2]) when path = path_star ->
        print_simple_type t1; print_string " * ";
        print_simple_type t2
    | Typeconstr(path, [t]) when path = path_code ->
        print_simple_type t; print_string " code"
    | Typeconstr(path, [t]) when path = path_csp ->
        print_string ".%"; print_simple_type t
    | Typeconstr(path, [t1;t2]) when path = path_dollar ->
        print_simple_type t1; print_string "$";
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
        print_signature sg;
        print_break 1 (-2);
        print_string "end";
        close_box()
    | FunS(param, arg, body) ->
        open_hvbox 2;
        print_string "functor("; print_string(Ident.name param);
        print_string ": "; print_modtype arg; print_string ")";
        print_space(); print_string "-> "; print_modtype body;
        close_box()
    | CodS mty ->
        print_modtype mty; print_string " mcod"
and print_signature sg =
    List.iter (fun item -> print_space(); print_signature_item item) sg
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

let f: mod_type -> unit = function
    | Signature(sg) -> 
        print_signature sg;
        Format.print_newline()