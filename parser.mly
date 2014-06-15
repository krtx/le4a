%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token LBRACKET RBRACKET SEMICOLON
%token RARROW
%token FUN DFUN

%token <Syntax.id> BAND BOR
%token IF THEN ELSE TRUE FALSE
%token LET REC IN AND
%token MATCH WITH VBAR
%token UNDERSCORE WHEN AS

%token <Syntax.id> CONS
%token <Syntax.id> MOD
%token <Syntax.id> OR
%token <Syntax.id> LAND LOR LXOR
%token <Syntax.id> LSL LSR ASR

%token <Syntax.id> EQUAL EQUALOP VBAROP
%token <Syntax.id> LCHEVRON RCHEVRON AT CARET AMPERSAND AMPERSANDOP
%token <Syntax.id> PLUS HYPHEN ASTERISK ASTERISKTWO
%token <Syntax.id> SLASH DOLLAR PERCENT

%token <int> INTV
%token <Syntax.id> ID

%token EOF

%nonassoc IN
%right RARROW
%nonassoc ELSE
%nonassoc AS
%nonassoc VBAR
%right BOR OR
%right BAND AMPERSAND
%left EQUALOP EQUAL LCHEVRON RCHEVRON VBAROP AMPERSANDOP DOLLAR
%right AT CARET
%right CONS
%left PLUS HYPHEN
%left ASTERISK SLASH PERCENT MOD LAND LOR LXOR
%right ASTERISKTWO LSL LSR ASR

%start toplevel lines
%type <Syntax.program> toplevel
%type <Syntax.program list> lines

%%

lines :
  | line EOF { $1 }

line :
  | { [] }
  | Statement { [$1] }
  | Statement SEMISEMI line { $1 :: $3 }

toplevel :
  | Statement SEMISEMI { $1 }

Statement :
  | Expr { Exp $1 }
  | LetDecList { Decl ($1) }
  | LetRecDecList { RecDecl ($1) }

LetDecList :
  | LetDec { [$1] }
  | LetDecList LetDec { $1 @ [$2] }

LetRecDecList :
  | LetRecDec { [$1] }
  | LetRecDecList LetRecDec { $1 @ [$2] }

LetDec :
  | LET BindList { $2 }

LetRecDec :
  | LET REC BindList { $3 }

BindList :
  | Bind { [$1] }
  | BindList AND Bind { $1 @ [$3] }

Bind :
  | Symbols EQUAL Expr { ($1, $3) }

Expr :
  | SimpleExpr { $1 }
  | Expr BOR Expr { AppExp (Var $2, [$1; $3]) }
  | Expr OR Expr { AppExp (Var $2, [$1; $3]) }
  | Expr BAND Expr { AppExp (Var $2, [$1; $3]) }
  | Expr AMPERSAND Expr { AppExp (Var $2, [$1; $3]) }
  | Expr EQUALOP Expr { AppExp (Var $2, [$1; $3]) }
  | Expr VBAROP Expr { AppExp (Var $2, [$1; $3]) }
  | Expr EQUAL Expr { AppExp (Var $2, [$1; $3]) }
  | Expr LCHEVRON Expr { AppExp (Var $2, [$1; $3]) }
  | Expr RCHEVRON Expr { AppExp (Var $2, [$1; $3]) }
  | Expr AMPERSANDOP Expr { AppExp (Var $2, [$1; $3]) }
  | Expr DOLLAR Expr { AppExp (Var $2, [$1; $3]) }
  | Expr AT Expr { AppExp (Var $2, [$1; $3]) }
  | Expr CARET Expr { AppExp (Var $2, [$1; $3]) }
  | Expr PLUS Expr { AppExp (Var $2, [$1; $3]) }
  | Expr HYPHEN Expr { AppExp (Var $2, [$1; $3]) }
  | Expr ASTERISK Expr { AppExp (Var $2, [$1; $3]) }
  | Expr SLASH Expr { AppExp (Var $2, [$1; $3]) }
  | Expr PERCENT Expr { AppExp (Var $2, [$1; $3]) }
  | Expr MOD Expr { AppExp (Var $2, [$1; $3]) }
  | Expr LAND Expr { AppExp (Var $2, [$1; $3]) }
  | Expr LOR Expr { AppExp (Var $2, [$1; $3]) }
  | Expr LXOR Expr { AppExp (Var $2, [$1; $3]) }
  | Expr ASTERISKTWO Expr { AppExp (Var $2, [$1; $3]) }
  | Expr LSL Expr { AppExp (Var $2, [$1; $3]) }
  | Expr LSR Expr { AppExp (Var $2, [$1; $3]) }
  | Expr ASR Expr { AppExp (Var $2, [$1; $3]) }
  | Expr CONS Expr { ConsExp ($1, $3) }
  | IF Expr THEN Expr ELSE Expr { IfExp ($2, $4, $6) }
  | MATCH Expr WITH PatternMatchList { MatchExp ($2, $4) }
  | MATCH Expr WITH VBAR PatternMatchList { MatchExp ($2, $5) }
  | FUN Symbols RARROW Expr { FunExp ($2, $4) }
  | DFUN Symbols RARROW Expr { DFunExp ($2, $4) }
  | LET BindList IN Expr { LetExp ($2, $4) }
  | LET REC BindList IN Expr { LetRecExp ($3, $5) }
  | SimpleExpr SimpleExprList { AppExp ($1, $2) }

SimpleExpr :
  | Const { $1 }
  | LPAREN Expr RPAREN { $2 }
  | LBRACKET List RBRACKET { $2 }

InfixOp:
  | BOR { $1 } | OR { $1 } | BAND { $1 } | AMPERSAND { $1 } | EQUALOP { $1 } | VBAROP { $1 } | EQUAL { $1 } | LCHEVRON { $1 } | RCHEVRON { $1 } | AMPERSANDOP { $1 } | DOLLAR { $1 } | AT { $1 } | CARET { $1 } | PLUS { $1 } | HYPHEN { $1 } | ASTERISK { $1 } | SLASH { $1 } | PERCENT { $1 } | MOD { $1 } | LAND { $1 } | LOR { $1 } | LXOR { $1 } | ASTERISKTWO { $1 } | LSL { $1 } | LSR { $1 } | ASR { $1 }

SimpleExprList :
  | SimpleExpr { [$1] }
  | SimpleExprList SimpleExpr { $1 @ [$2] }

Const :
  | INTV { ILit $1 }
  | TRUE { BLit true }
  | FALSE { BLit false }
  | Symbol { Var $1 }

PatternMatchList :
  | PatternMatch { [$1] }
  | PatternMatchList VBAR PatternMatch { $1 @ [$3] }

PatternMatch :
  | Pattern RARROW Expr { ($1, BLit true, $3) }
  | Pattern WHEN Expr RARROW Expr { ($1, $3, $5) }

Pattern :
  | UNDERSCORE { Wildcard }
  | Symbol { PVar $1 }
  | INTV { PILit $1 }
  | TRUE { PBLit true }
  | FALSE { PBLit false }
  | LPAREN Pattern RPAREN { $2 }
  | Pattern VBAR Pattern { POr ($1, $3) }
  | Pattern AS Symbol { PAs ($1, $3) }
  | Pattern CONS Pattern { PCons ($1, $3) }
  | LBRACKET PList RBRACKET { $2 }

PList :
  | { PNil }
  | Pattern { PCons ($1, PNil) }
  | Pattern SEMICOLON PList { PCons ($1, $3) }
      
Symbols :
  | Symbol { [$1] }
  | Symbols Symbol { $1 @ [$2] }

Symbol :
  | ID { $1 }
  | LPAREN InfixOp RPAREN { $2 }

List :
  | { NilExp }
  | Expr { ConsExp ($1, NilExp) }
  | Expr SEMICOLON List { ConsExp ($1, $3) }

