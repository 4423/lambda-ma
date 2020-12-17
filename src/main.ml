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

let usage () =
  Printf.printf "usage: %s <file> \n" (Sys.argv.(0))

let main () =
  try
    if (Array.length Sys.argv) <> 2 then usage ()
    else
      let path = Sys.argv.(1) in
      print_string @@ Target.Print.f @@ Translation.f @@ Scope.f @@ parse_file path
  with
    Error s ->
      prerr_string "Error: "; prerr_string s; prerr_newline(); exit 2

let _ = main ()
