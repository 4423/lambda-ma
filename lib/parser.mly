/*  A modular module system.
    The parser for mini-ML.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. */

%{

open Identifier
open Syntax
open Modules
open CoreTyping

let variables = ref ([] : (string * Core.type_variable) list)

let reset_type_variables () =
  variables := []

let find_type_variable name =
  try
    List.assoc name !variables
  with Not_found ->
    let v = newvar() in
    variables := (name, v) :: !variables;
    v

let binop op arg1 arg2 =
  Core.AppE(AppE(Longident(IdentP(Ident.create op)), arg1), arg2)
let ternop op arg1 arg2 arg3 =
  Core.AppE(AppE(AppE(Longident(IdentP(Ident.create op)), arg1), arg2), arg3)

%}

%token <string> VAR      // "<identifier>"
%token <string> CON      // "<identifier>"
%token <string> STR      // "<string>"
%token <int> INT

%token ARROW
%token COLON
%token COMMA
%token DOT
%token ELSE
%token END
%token EOF
%token EQUAL
%token EQUALEQUAL
%token FUNCTION
%token FUNCTOR
%token GREATER
%token GREATEREQUAL
%token IF
%token IN
%token LESS
%token LESSEQUAL
%token LESSGREATER
%token LET
%token REC               // "rec"
%token LIDENT
%token LPAREN
%token MINUS
%token MODULE
%token PLUS
%token QUOTE
%token RPAREN
%token SEMICOLON
%token SEMISEMI
%token SIG
%token SLASH
%token STAR
%token STRUCT
%token THEN
%token TYPE
%token VALUE
%token MATCH             // "match"
%token WITH              // "with"
%token COLCOL            // "::"
%token CONJ              // "&&"
%token BAR               // "|"
%token DISJ              // "||"
%token TRUE              // "true"
%token FALSE             // "false"
%token NOT               // "not"
%token AND               // "and"
%token MCOD              // "mcod"
%token LMCOD             // ".<<"
%token RMCOD             // ">>."
%token MESC              // ".~~"
%token DOLLAR            // "$"
%token MRUN              // "Runmod"
%token CODE              // "code"
%token LCOD              // ".<"
%token RCOD              // ">."
%token ESC               // ".~"
%token CSP               // ".%"
%token RUN               // "Runcode.run"

%right ARROW
%right COMMA
%right LESSGREATER LESS LESSEQUAL GREATER GREATEREQUAL
%right PLUS MINUS
%right STAR SLASH

%start implementation
%type <Syntax.Mod.mod_term> implementation
%start phrase
%type <Syntax.Mod.definition> phrase

%start main
%type <Syntax.Mod.mod_term> main

%%

/* Paths */

path:
  | CON           { IdentP(Ident.create $1) }
  | path DOT CON  { DotP($1, $3) }
;
path_var:
  | VAR           { IdentP(Ident.create $1) }
  | path DOT VAR  { DotP($1, $3) }
;

/* Value expressions for the core language */

valexpr:
    valexpr1                          { $1 }
  | valexpr COMMA valexpr             { binop "," $1 $3 }
  | valexpr PLUS valexpr              { binop "+" $1 $3 }
  | valexpr MINUS valexpr             { binop "-" $1 $3 }
  | valexpr STAR valexpr              { binop "*" $1 $3 }
  | valexpr SLASH valexpr             { binop "/" $1 $3 }
  | valexpr EQUALEQUAL valexpr        { binop "==" $1 $3 }
  | valexpr LESSGREATER valexpr       { binop "<>" $1 $3 }
  | valexpr LESS valexpr              { binop "<" $1 $3 }
  | valexpr LESSEQUAL valexpr         { binop "<=" $1 $3 }
  | valexpr GREATER valexpr           { binop ">" $1 $3 }
  | valexpr GREATEREQUAL valexpr      { binop ">=" $1 $3 }
  | FUNCTION VAR ARROW valexpr      { Core.FunE(Ident.create $2, $4) }
  | LET VAR valbind IN valexpr      { Core.LetE(Ident.create $2, $3, $5) }
  | LET REC VAR valbind IN valexpr     { Core.LetRecE(Ident.create $3, $4, $6) }
  | IF valexpr THEN valexpr ELSE valexpr { ternop "conditional" $2 $4 $6 }
  | LCOD valexpr RCOD                 { Core.CodE($2) }
  | ESC valexpr                       { Core.EscE($2) }
  | RUN valexpr                       { Core.RunE($2) }
;
valexpr1:
    valexpr0 { $1 }
  | valexpr1 valexpr0 { Core.AppE($1, $2) }
;
valexpr0:
    path_var  { Core.Longident($1) }
  | INT  { Core.Constant $1 }
  | LPAREN valexpr RPAREN { $2 }
;
valbind:
    EQUAL valexpr     { $2 }
  | VAR valbind     { Core.FunE(Ident.create $1, $2) }
;

/* Type expressions for the core language */

simpletype:
    QUOTE VAR             { Core.Var(find_type_variable $2) }
  | simpletype ARROW simpletype { Core.Typeconstr(path_arrow, [$1; $3]) }
  | simpletype STAR simpletype  { Core.Typeconstr(path_star, [$1; $3]) }
  | path_var                    { Core.Typeconstr($1, []) }
  | simpletype path_var         { Core.Typeconstr($2, [$1]) }
  | LPAREN simpletypelist RPAREN path_var { Core.Typeconstr($4, List.rev $2) }
  | simpletype CODE             { Core.Typeconstr(path_code, [$1]) }
  | CSP simpletype              { Core.Typeconstr(path_csp, [$2]) }
;
simpletypelist:
    simpletype { [$1] }
  | simpletypelist COMMA simpletype { $3::$1 }
;

valuedecl:
    colon_begin_scheme simpletype
            { reset_type_variables(); end_def(); generalize $2 }
;
colon_begin_scheme: /* Hack to perform side effects before reading the type */
    COLON   { begin_def(); reset_type_variables() }
;

/* Type definitions and declarations */

typedecl:
    typeparams VAR        { ($2, {Core.arity = List.length $1}) }
;
typedef:
    typeparams VAR EQUAL simpletype
      { reset_type_variables();
        ($2, {Core.arity = List.length $1}, {Core.params = $1; Core.defbody = $4}) }
;
typeparams:
    /* nothing */               { [] }
  | typeparam                   { [$1] }
  | LPAREN typeparamlist RPAREN { List.rev $2 }
;
typeparamlist:
    typeparam                       { [$1] }
  | typeparamlist COMMA typeparam   { $3 :: $1 }
;
typeparam:
    QUOTE VAR { find_type_variable $2 }
;
typeinfo:
    typedef   { let (id, kind, def) = $1 in
                (id, {Mod.kind = kind; Mod.manifest = Some def})}
  | typedecl  { let (id, kind) = $1 in
                (id, {Mod.kind = kind; Mod.manifest = None}) }
;

/* Value expressions for the module language */

modulexpr:
    path                              { Mod.Longident $1 }
  | STRUCT structure END              { Mod.Structure(List.rev $2) }
  | FUNCTOR LPAREN CON COLON moduletype RPAREN ARROW modulexpr
                                      { Mod.FunM(Ident.create $3, $5, $8) }
  | modulexpr LPAREN modulexpr RPAREN { Mod.AppM($1, $3) }
  | LPAREN modulexpr RPAREN           { $2 }
  | modulexpr COLON moduletype        { Mod.Constraint($1, $3) }
  | LMCOD modulexpr RMCOD             { Mod.CodM($2) }
  | MESC modulexpr                    { Mod.EscM($2) }
  | MRUN LPAREN modulexpr COLON moduletype RPAREN { Mod.RunM($3, $5) }
;
structure:
    /*nothing*/                       { [] }
  | structure structure_item opt_semi { $2 :: $1 }
;
structure_item:
    LET VAR valbind           { Mod.LetM(Ident.create $2, $3) }
  | LET REC VAR valbind           { Mod.LetRecM(Ident.create $3, $4) }
  | TYPE typedef                  { let (id, kind, def) = $2 in
                                    Mod.TypeM(Ident.create id, kind, def) }
  | MODULE CON COLON moduletype EQUAL modulexpr
                     { Mod.ModM(Ident.create $2, Mod.Constraint($6, $4)) }
  | MODULE CON EQUAL modulexpr   { Mod.ModM(Ident.create $2, $4) }
;
opt_semi:
    /* nothing */ { () }
  | SEMICOLON { () }
;

/* Type expressions for the module language */

moduletype:
    SIG signature END               { Mod.Signature(List.rev $2) }
  | FUNCTOR LPAREN CON COLON moduletype RPAREN ARROW moduletype
                                    { Mod.FunS(Ident.create $3, $5, $8) }
  | moduletype MCOD                 { Mod.CodS($1) }
  | LPAREN moduletype RPAREN        { $2 }
;
signature:
    /*nothing*/                       { [] }
  | signature signature_item opt_semi { $2 :: $1 }
;
signature_item:
    VALUE VAR valuedecl             { Mod.ValS(Ident.create $2, $3) }
  | TYPE typeinfo    { let (id, def) = $2 in Mod.TypeS(Ident.create id, def) }
  | MODULE CON COLON moduletype     { Mod.ModS(Ident.create $2, $4) }
;

/* Toplevel entry point */

phrase:
    structure_item SEMISEMI           { $1 }
  | EOF                               { raise End_of_file }
;

main:
  | structure EOF   { Structure (List.rev $1) }
;

/* Sep. comp. entry point */

implementation:
    modulexpr EOF                     { $1 }
;
