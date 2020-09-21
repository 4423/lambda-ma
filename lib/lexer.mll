(*  A modular module system.
    The lexical analyzer for mini-ML.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. *)

{
(* Auxiliary Caml code *)

exception Lexical_error of string

open Parser             (* "parser" provides the type for tokens. *)

(* The table of keywords and infixes *)

let keyword_table = (Hashtbl.create 17 : (string, token) Hashtbl.t)

let _ = List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok)
 ["function", FUNCTION;
  "fun", FUNCTION;
  "let", LET;
  "rec", REC;
  "struct", STRUCT;
  "end", END;
  "functor", FUNCTOR;
  "val", VALUE;
  "type", TYPE;
  "module", MODULE;
  "sig", SIG;
  "in", IN;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "match", MATCH;
  "with", WITH;
  ]

(* End of auxiliary Caml definitions *)
}

let whitespace = [' ' '\t' '\n' '\r']
let digit      = ['0'-'9']
let hex        = '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
let oct        = '0' ['o' 'O'] ['0'-'7']+
let bin        = '0' ['b' 'B'] ['0'-'1']+
let char       = ['\x20'-'\x7e']
let lower      = ['a'-'z']
let upper      = ['A'-'Z']
let alpha      = (lower | upper)
let var        = (lower | "_") (alpha | "_" | digit)*
let con        = (upper) (alpha | "_" | digit)*

(* Lexer rules *)

rule token = parse
  | whitespace+
            { token lexbuf }
  (*
  | var
            { let s = Lexing.lexeme lexbuf in
              try Hashtbl.find keyword_table s
              with Not_found -> VAR s }
  | con
            { let s = Lexing.lexeme lexbuf in
              try Hashtbl.find keyword_table s
              with Not_found -> CON s }
  *)
  | [ 'A'-'Z' 'a'-'z' '\192'-'\214' '\216'-'\246' '\248'-'\254' ]
    [ 'A'-'Z' 'a'-'z' '\192'-'\214' '\216'-'\246' '\248'-'\254'
      '0'-'9' '_' '\'' ] *
            { let s = Lexing.lexeme lexbuf in
              try
                Hashtbl.find keyword_table s
              with Not_found ->
                IDENT s }
  | digit+ | hex | oct | bin
            { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | "(*"
            { comment lexbuf; token lexbuf }
  
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | "."     { DOT }
  | ";"     { SEMICOLON }
  | ";;"    { SEMISEMI }
  | "->"    { ARROW }
  | "="     { EQUAL }
  | ","     { COMMA }
  | "'"     { QUOTE }
  | ":"     { COLON }
  | "*"     { STAR }
  | "+"     { PLUS }
  | "-"     { MINUS }
  | "/"     { SLASH }
  | "=="    { EQUALEQUAL }
  | "<>"    { LESSGREATER }
  | "<"     { LESS }
  | ">"     { GREATER }
  | "<="    { LESSEQUAL }
  | ">="    { GREATEREQUAL }
  | "::"    { COLCOL }
  | "&&"    { CONJ }
  | "|"     { BAR }
  | "||"    { DISJ }
  | "true"  { TRUE }
  | "false" { FALSE }
  | "not"   { NOT }
  | "and"   { AND }
  | eof     { EOF }

  | "mcod"  { MCOD }
  | ".<<"   { LMCOD }
  | ">>."   { RMCOD }
  | ".~~"   { MESC }
  | "$"     { DOLLAR }
  | "Runmod"  { MRUN }
  | "code"  { CODE }
  | ".<"    { LCOD }
  | ">."    { RCOD }
  | ".~"    { ESC }
  | ".%"    { CSP }
  | "Runcode.run" { RUN }

  | "\"" (char+ as lexeme) "\""
      { STR (lexeme) }

  | _       { raise(Lexical_error "illegal character") }

and comment = parse
    "*)"
            { () }
  | "(*"
            { comment lexbuf; comment lexbuf }
  | eof
            { raise (Lexical_error "comment not terminated") }
  | _
            { comment lexbuf }

