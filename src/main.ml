open Syntax
open Modules
open CoreTyping
open Scope
open Error

let init_scope = ref Scope.empty
let init_env = ref Env.empty

let enter_type id decl =
  init_scope := Scope.enter_type id !init_scope;
  init_env := Env.add_type id decl !init_env

let enter_val name ty =
  let id = Ident.create name in
  init_scope := Scope.enter_value id !init_scope;
  init_env := Env.add_value id ty !init_env

let _ =
  let ident_bool = Ident.create "bool" in
  let path_bool = IdentP ident_bool in
  let bool_type = Core.Typeconstr(path_bool, []) in
  enter_type ident_arrow {Mod.kind = {Core.arity = 2}; Mod.manifest = None};
  enter_type ident_star {Mod.kind = {Core.arity = 2}; Mod.manifest = None};
  enter_type ident_int {Mod.kind = {Core.arity = 0}; Mod.manifest = None};
  enter_type ident_bool {Mod.kind = {Core.arity = 0}; Mod.manifest = None};
  enter_val "false" { Core.quantif = []; Core.body = bool_type };
  enter_val "true" { Core.quantif = []; Core.body = bool_type };
  List.iter
    (fun name ->
        enter_val name
          { Core.quantif = [];
            Core.body = arrow_type int_type (arrow_type int_type bool_type)})
    ["+"; "-"; "*"; "/"; "=="; "<>"; "<"; "<="; ">"; ">="];
  let alpha = newvar() and beta = newvar() in
  let talpha = Core.Var alpha and tbeta = Core.Var beta in
  enter_val ","
    { Core.quantif = [alpha;beta];
      Core.body = arrow_type talpha (arrow_type tbeta
                  (Core.Typeconstr(path_star, [talpha; tbeta]))) };
  enter_val "fst"
    { Core.quantif = [alpha;beta];
      Core.body = arrow_type
                  (Core.Typeconstr(path_star, [talpha; tbeta])) talpha };
  enter_val "snd"
    { Core.quantif = [alpha;beta];
      Core.body = arrow_type
                  (Core.Typeconstr(path_star, [talpha; tbeta])) tbeta };
  enter_val "conditional"
    { Core.quantif = [alpha];
      Core.body = arrow_type bool_type
                          (arrow_type talpha (arrow_type talpha talpha)) }

let parse lexbuf =
  Parser.main Lexer.token lexbuf

let parse_file filepath = 
  let ichannel = open_in filepath in
  let lexbuf = Lexing.from_channel ichannel in
  try parse lexbuf with
  | Parsing.Parse_error ->
      close_in ichannel;
      let s = Printf.sprintf "Syntax error at char %d" (Lexing.lexeme_start lexbuf) in
      error s
  | Lexer.Lexical_error msg ->
      close_in ichannel;
      let s = Printf.sprintf "Lexical error: %s, around character %d" 
                  msg (Lexing.lexeme_start lexbuf) in
      error s

let main() =
  try
    let prog = parse_file "./test/example.mml" in
    let scoped_prog = ModScoping.scope_module !init_scope prog in
    let mty = ModTyping.type_module !init_env scoped_prog in
    match mty with Mod.Signature(sg) ->  MLPrint.print_signature sg;
    Format.print_newline();
    exit 0
  with
    Error s ->
      prerr_string "Error: "; prerr_string s; prerr_newline(); exit 2

let _ = main()
