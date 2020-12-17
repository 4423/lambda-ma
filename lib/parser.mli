type token =
  | VAR of (string)
  | CON of (string)
  | STR of (string)
  | INT of (int)
  | ARROW
  | COLON
  | COMMA
  | DOT
  | ELSE
  | END
  | EOF
  | EQUAL
  | EQUALEQUAL
  | FUNCTION
  | FUNCTOR
  | GREATER
  | GREATEREQUAL
  | IF
  | IN
  | LESS
  | LESSEQUAL
  | LESSGREATER
  | LET
  | REC
  | LIDENT
  | LPAREN
  | MINUS
  | MODULE
  | PLUS
  | QUOTE
  | RPAREN
  | SEMICOLON
  | SEMISEMI
  | SIG
  | SLASH
  | STAR
  | STRUCT
  | THEN
  | TYPE
  | VALUE
  | MATCH
  | WITH
  | COLCOL
  | CONJ
  | BAR
  | DISJ
  | TRUE
  | FALSE
  | NOT
  | AND
  | MCOD
  | LMCOD
  | RMCOD
  | MESC
  | DOLLAR
  | MRUN
  | CODE
  | LCOD
  | RCOD
  | ESC
  | CSP
  | RUN
  | RECAPP

val implementation :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Source.Syntax.Mod.mod_term
val phrase :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Source.Syntax.Mod.definition
val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Source.Syntax.Mod.toplevel list
