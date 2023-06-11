
%token <int> INT
%token PLUS MINUS TIMES DIV
%token LPAREN RPAREN
%token EOL

%start <int> main
%type  <int> expr

%%

main:
| LPAREN expr RPAREN
    { 42 }

expr:
| i = INT
    { i }

(* "relation" ignore *)
(* "(" "rule"  body  head ")"
"(" "fact"  fact  ")" *)

