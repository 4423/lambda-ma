open Error

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
    let scoped_prog = Scope.f prog in
    let mty = Typing.f scoped_prog in
    Printer.f mty;
    let translated_prog = Translation.f scoped_prog in
    print_string @@ Target.Print.f translated_prog;
    exit 0
  with
    Error s ->
      prerr_string "Error: "; prerr_string s; prerr_newline(); exit 2

let _ = main()
