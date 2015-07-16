%{
  open Form
%}
%type <Form.prog> prog
%type <Form.form> form
%start form
%token <string> IDENT
%token SEQ CHOICE ITER CPAR TEST
%token BOT TOP NEG CONJ DISJ IMP EQUIV
%token DIAM_O DIAM_C BOX_O BOX_C
%token PAREN_O PAREN_C
%token EOL
%left EQUIV
%right IMP
%left DISJ
%left CONJ
%left DIAM_O DIAM_C BOX_O BOX_C
%nonassoc CPAR
%left CHOICE
%right SEQ
%left ITER
%left NEG
%%
form:
        fexp EOL { $1 }
  | EOL fexp EOL { $2 }
;
fexp:
    IDENT                   { Var $1 }
  | PAREN_O fexp PAREN_C    { $2 }
  | BOT                     { Bot }
  | TOP                     { top }
  | NEG fexp                { neg $2 }
  | fexp CONJ fexp          { conj $1 $3 }
  | fexp DISJ fexp          { disj $1 $3 }
  | fexp IMP fexp           { imp $1 $3 }
  | fexp EQUIV fexp         { conj (imp $1 $3) (imp $3 $1) }
  | DIAM_O prog DIAM_C fexp { diam $2 $4 }
  | BOX_O prog BOX_C fexp   { Box ($2, $4) }
;
prog:
    IDENT                   { Atom $1 }
  | PAREN_O prog PAREN_C    { $2 }
  | prog SEQ prog           { Seq ($1, $3) }
  | TEST fexp               { Test $2 }
  | prog CHOICE prog        { Choice ($1, $3) }
  | ITER prog               { Iter $2 }
  | prog CPAR prog          { CPar ($1, $3) }
;
