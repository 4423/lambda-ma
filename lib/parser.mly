/*  A modular module system.
    The parser for mini-ML.

    Copyright 1999 Xavier Leroy.
    This file is distributed under the GNU Public Licence. */

%{

open Identifier
open Source.Syntax
open Source.Syntax.Core

let rec typerepr = function
  | Var({repres = Some ty} as var) ->
      let r = typerepr ty in var.repres <- Some r; r
  | ty -> ty

let current_level = ref 0
let begin_def() = incr current_level
let end_def() = decr current_level
let newvar() = {repres = None; level = !current_level}

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

%}

%token <string> VAR      // "<identifier>"
%token <string> CON      // "<identifier>"
%token <string> STR      // "<string>"
%token <int> INT         // "<int>"

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
%token RECAPP            // "recapp"

%right ARROW
%right COMMA
%right LESSGREATER LESS LESSEQUAL GREATER GREATEREQUAL
%right PLUS MINUS
%right STAR SLASH
%left VAR CON STR INT TRUE FALSE UNIT LPAREN MCOD LMCOD MESC MRUN LCOD CODE ESC RUN DOLLAR

%start implementation
%type <Source.Syntax.Mod.mod_term> implementation
%start phrase
%type <Source.Syntax.Mod.definition> phrase

%start main
%type <Source.Syntax.Mod.toplevel list> main

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
  | valexpr CONJ valexpr              { binop "&&" $1 $3 }
  | valexpr DISJ valexpr              { binop "||" $1 $3 }
  | FUNCTION VAR ARROW valexpr      { Core.FunE(Ident.create $2, $4) }
  | LET VAR valbind IN valexpr      { Core.LetE(Ident.create $2, $3, $5) }
  | LET REC VAR valbind IN valexpr     { Core.LetRecE(Ident.create $3, $4, $6) }
  | IF valexpr THEN valexpr ELSE valexpr { Core.IfE($2, $4, $6) }
  | MATCH valexpr WITH clauselist     { Core.MatchE ($2, $4) }
;
valexpr1:
    valexpr0 { $1 }
  | valexpr1 valexpr0 { Core.AppE($1, $2) }
;
valexpr0:
    path_var  { Core.Longident($1) }
  | INT                   { Core.IntE $1 }
  | STR                   { Core.StrE $1 }
  | TRUE                  { Core.BoolE(true) }
  | FALSE                 { Core.BoolE(false) }
  | LCOD valexpr RCOD     { Core.CodE($2) }
  | ESC valexpr0          { Core.EscE($2) }
  | RUN valexpr0          { Core.RunE($2) }
  | path DOLLAR VAR       { Core.DollarE($1, $3) }
  | LPAREN valexpr RPAREN { $2 }
;
valbind:
    EQUAL valexpr     { $2 }
  | VAR valbind     { Core.FunE(Ident.create $1, $2) }
;

clauselist:
  | clauselist BAR clauselist { $1 @ $3 }
  | clause                    { $1 :: [] }
;
clause:
  | pattern ARROW valexpr  { $1, $3 }
;
pattern:
  | pattern COLCOL VAR      { ConsPat ($1, Ident.create $3) }
  | pattern COMMA pattern   { PairPat ($1, $3) }
  | simplepattern           { $1 }
;
simplepattern:
  | LPAREN pattern RPAREN   { $2 }
  | VAR                     { match $1 with
                              | "_" -> WildPat
                              | x0  -> VarPat (Ident.create x0) }
;

/* Type expressions for the core language */

simpletype:
    QUOTE VAR             { Core.Var(find_type_variable $2) }
  | simpletype ARROW simpletype { Core.Typeconstr(Core.path_arrow, [$1; $3]) }
  | simpletype STAR simpletype  { Core.Typeconstr(Core.path_star, [$1; $3]) }
  | path_var                    { Core.Typeconstr($1, []) }
  | simpletype path_var         { Core.Typeconstr($2, [$1]) }
  | LPAREN simpletypelist RPAREN path_var { Core.Typeconstr($4, List.rev $2) }
  | simpletype CODE             { Core.Typeconstr(Core.path_code, [$1]) }
  | CSP simpletype              { Core.Typeconstr(Core.path_csp, [$2]) }
  | path DOLLAR VAR             { Core.dollar_type 
                                    (Core.Typeconstr($1, [])) 
                                    (Core.Typeconstr(IdentP(Ident.create $3), [])) }
  | LPAREN simpletype RPAREN    { $2 }
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
  | path DOLLAR CON                   { Mod.DollarM($1, $3) }
  | RECAPP INT modulexpr modulexpr    { Mod.RecAppM($2, $3, $4) }
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
  | path                            { Mod.LongidentS $1 }
  | SIG signature END               { Mod.Signature(List.rev $2) }
  | FUNCTOR LPAREN CON COLON moduletype RPAREN ARROW moduletype
                                    { Mod.FunS(Ident.create $3, $5, $8) }
  | moduletype MCOD                 { Mod.CodS($1) }
  | moduletype WITH modconstraint   { Mod.SharingS($1, $3) }
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
modconstraint:
  | TYPE typedef  { let (id, _, def) = $2 in Mod.TypeC(Ident.create id, def) }
;

/* Toplevel entry point */

toplevel_list:
  |                                     { [] }
  | toplevel_list toplevel opt_semisemi { $2 :: $1}
;
opt_semisemi:
  |          { () }
  | SEMISEMI { () }
;
toplevel:
  | MODULE TYPE CON EQUAL moduletype  { Mod.SignatureDec(Ident.create $3, $5)}
  | MODULE CON COLON moduletype EQUAL modulexpr
                    { Mod.StructureDec(Ident.create $2, Mod.Constraint($6, $4)) }
  | MODULE CON EQUAL modulexpr        { Mod.StructureDec(Ident.create $2, $4) }
  | LET VAR valbind                   { Mod.LetDec(Ident.create $2, $3) }
  | LET REC VAR valbind               { Mod.LetRecDec(Ident.create $3, $4) }
  | TYPE typedef                      { let (id, kind, def) = $2 in
                                          Mod.TypeDec(Ident.create id, kind, def) }
;
phrase:
    structure_item SEMISEMI           { $1 }
  | EOF                               { raise End_of_file }
;

main:
  | toplevel_list EOF { List.rev $1 }
;

/* Sep. comp. entry point */

implementation:
    modulexpr EOF                     { $1 }
;
