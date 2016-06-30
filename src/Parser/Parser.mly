%{
  open Eval
%}

%token EOF
%token DOT
%token COMMA
%token LPAR
%token RPAR
%token LBRACK
%token RBRACK
%token EQ
%token AND
%token OR

%token SCHEME
%token ENCODING
%token PREDICATE
%token BOOL_FORM
%token ATTRIBUTES
%token REPETITIONS
%token AND_GATES
%token NATTRS

%token KEY
%token CT
%token MPK
%token MSK

%token BEGIN_CT
%token END_CT

%token <int> INT
%token <string> NAME

/************************************************************************/
/* Priority & associativity */

%left AND OR

/************************************************************************/
/* Production types */

%type <Eval.pp_cmd list> pp_cmds
%type <Eval.mpk_cmd list> mpk_cmds
%type <Eval.msk_cmd> msk_cmd
%type <Eval.eval_policy> policy_cmd
%type <string list> sk_attrs
%type <Eval.sk_cmd> sk_cmd
%type <Eval.ct_cmd> ct_cmd

/************************************************************************/
/* Start productions */

%start pp_cmds
%start mpk_cmds
%start msk_cmd
%start policy_cmd
%start sk_attrs
%start sk_cmd
%start ct_cmd

%%

/************************************************************************/
/* Types */

name_list :
| LBRACK; ns = separated_list(COMMA, NAME); RBRACK; { ns }
;

predicate :
| BOOL_FORM; LPAR; r = INT; REPETITIONS; COMMA; b = INT; AND_GATES; COMMA; n = INT; NATTRS; RPAR;  { BoolForm(r,b,n) }
;

pp_cmd :
| SCHEME; EQ; s = NAME; DOT;               { Scheme(s) }
| ENCODING; EQ; s = NAME; DOT;             { Encoding(s) }
| PREDICATE; EQ; p = predicate; DOT;       { Predicate(p) }
| ATTRIBUTES; EQ; attrs = name_list; DOT;  { Attributes(attrs) }
;

pp_cmds : cs = list(pp_cmd); EOF; { cs };

mpk_cmd :
| MPK; EQ; s = NAME; DOT;  { Mpk(s) }
| cmd = pp_cmd             { Pp(cmd) }
;

mpk_cmds : cs = list(mpk_cmd); EOF; { cs };

msk_cmd : MSK; EQ; s = NAME; DOT; { Msk(s) };

policy :
| s = NAME;                      { Eval_leaf(s) }
| p1 = policy; OR; p2 = policy   { Eval_OR(p1,p2) }
| p1 = policy; AND; p2 = policy  { Eval_AND(p1,p2) }
| LPAR; p = policy; RPAR;        { p }
;

policy_cmd : p = policy; EOF; { p };

sk_attrs : l = name_list; EOF; { l };

sk_cmd :
| KEY; EQ; s = NAME; DOT;              { Sk(s) }
;

ct_cmd : BEGIN_CT; CT; EQ; s = NAME; DOT; END_CT; { Ct(s) };
