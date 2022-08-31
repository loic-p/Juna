%token<string> IDENT CONS
%token<int> INTLITERAL
%token<string> STRING
%token FUN IN LET REC MATCH WITH TYPE FORALL END
%token ARROW DARROW EQ LPAREN RPAREN COMMA PIPE COLON STAR DIV UNDERSCORE
%token<RawLambda.binop> ADDOP
%token<RawLambda.cmpop> CMPOP
%token EOF

%start<RawLambda.type_decl_ list * RawLambda.term> entry

%{

open RawLambda

%}

%%

(* -------------------------------------------------------------------------- *)

(* The file should start with some type declarations, then a term.
   No type declaration are allowed in the middle of a term *)

entry:
  a = list(decl_type_) t = any_term EOF
    { (a, t) }

(* -------------------------------------------------------------------------- *)

(* Type syntax *)
(* Parsing a type should return a type_p value *)

atomic_type:
| a = IDENT
  { TL.BaseType (TL.TypeVar.Named a ) }
| LPAREN a = any_type RPAREN
  { a }

applicative_type:
| a = atomic_type
  { a }
| a = IDENT b = nonempty_list(atomic_type)
  { TL.Inst (a, b) }

multiplicative_type:
| a = applicative_type
  { a }
| a = multiplicative_type STAR b = applicative_type
  { TL.Prod (a, b) }

any_type:
| a = multiplicative_type
  { a }
| a = applicative_type ARROW b = any_type
  { TL.Arrow (a, b) }

(** Type declaration **)
(* specific introduction rule *)

cons :
  a = CONS
  { a }

intro_type_:
| a = cons COLON u = gen_type_
  { (a, u) }

intro_type:
  a = placed(intro_type_)
  { a }

(* all the introduction rules of a declaration *)

intro_rules:
  option(PIPE) a = separated_list(PIPE, intro_type)
  { a }

(* list of placed type argument names *)

type_args:
  a = list(placed(IDENT))
  { a }

decl_type_:
  TYPE t = placed(IDENT) a = type_args EQ c = intro_rules END
  { (t, a, c) }


(* gen_type is used for annotation in let constructions *)

gen_type_:
| a = any_type
  { ([], a) }  
| FORALL t = nonempty_list(IDENT) COMMA a = any_type
  { (typenames_of_strings t , a) }

gen_type :
  a = placed(gen_type_)
  { a }

(* term syntax *)
(* patterns used for pattern matching *)

atomic_pattern_:
| UNDERSCORE
  { TDL.ThrowawayPt } 
| a = IDENT
  { TDL.VarPt a }
| LPAREN a = pattern RPAREN
  { TDL.ThrowawayPt } 
| LPAREN a = pattern COMMA b = pattern RPAREN
  { TDL.TuplePt (a, b) }

atomic_pattern :
  a = placed(atomic_pattern_)
  { a }

pattern_:
| a = atomic_pattern_
  { a }
| a = cons b = list(atomic_pattern)
  { TDL.ConsPt (a, b) }

pattern:
  p = placed(pattern_)
  { p }

(* clauses of a match statement *)

clause_:
  a = pattern DARROW b = any_term
  { (a, b) }

match_clauses_:
  option(PIPE) a = separated_list(PIPE, clause_)
  { a }

atomic_term_:
| LPAREN t = any_term RPAREN
    { t.TDL.value }
| LPAREN t = any_term COMMA u = any_term RPAREN
    { Tuple (t, u) }
| MATCH t = any_term WITH a = match_clauses_ END
    { Match (t, a) }
| x = IDENT
    { Var x }
| i = INTLITERAL
    { Lit i }
| s = STRING
    { String s }

arg_term_ :
| a = atomic_term_
  { a }
| k = cons
  { Cons (k, []) }

arg_term :
  a = placed(arg_term_)
  { a }

atomic_term :
  a = placed(atomic_term_)
  { a }

cons_term_ :
  k = cons l = list(arg_term)
  { Cons (k, l) }

application_term_:
| t = atomic_term_
    { t }
| t = application_term l = arg_term
    { App (t, l) }

application_term :
  a = placed(application_term_)
  { a }

applicative_term_ :
| t = cons_term_
    { t }
| t = application_term_
    { t }

applicative_term :
  a = placed(applicative_term_)
  { a }

%inline multiplicative_term_:
  t = left_associative_level(applicative_term_, STAR { OpMul } | DIV { OpDiv }, mkbinop)
    { t }

additive_term_:
  t = left_associative_level(multiplicative_term_, ADDOP, mkbinop)
    { t }

additive_term :
  t = placed(additive_term_)
    { t }

%inline compared_term_:
| t1 = additive_term op = CMPOP t2 = additive_term
  { CmpOp (t1, op, t2) }
| t = additive_term_
  { t }

any_term_:
| t = compared_term_
    { t }
| FUN x = nonempty_list(IDENT) ARROW t = any_term
    { Lam (x, t) }
| LET mode = recursive x = IDENT COLON a = gen_type EQ t1 = any_term IN t2 = any_term
    { Let (mode, x, Hint (a.TDL.value, a.TDL.place), t1, t2) }
| LET mode = recursive x = IDENT EQ t1 = any_term IN t2 = any_term
    { Let (mode, x, NoHint, t1, t2) }

%inline any_term:
  t = placed(any_term_)
    { t }

(* -------------------------------------------------------------------------- *)

(* An infix-left-associative-operator level in a hierarchy of arithmetic
   expressions. *)

(* [basis] is the next lower level in the hierarchy.
   [op] is the category of binary operators.
   [action] is a ternary sequencing construct. *)

left_associative_level(basis, op, action):
| t = basis
| t = action(
        left_associative_level(basis, op, action),
        op,
        basis
      )
    { t }

(* -------------------------------------------------------------------------- *)

(* A ternary sequence whose semantic action builds a [BinOp] node. *)

%inline mkbinop(term1, op, term2):
  t1 = placed(term1) op = op t2 = placed(term2)
    { BinOp (t1, op, t2) }

(* -------------------------------------------------------------------------- *)

(* A [let] construct carries an optional [rec] annotation. *)

recursive:
| REC { Recursive }
|     { NonRecursive }

(* -------------------------------------------------------------------------- *)

(* A term is annotated with its start and end positions, for use in error
   messages. *)

%inline placed(X):
  x = X
    { { TDL.place = ($startpos, $endpos); TDL.value = x } }

(* -------------------------------------------------------------------------- *)

(* In a right-flexible list, the last delimiter is optional, i.e., [delim] can
   be viewed as a terminator or a separator, as desired. *)

(* There are several ways of expressing this. One could say it is either a
   separated list or a terminated list; this works if one uses right recursive
   lists. Or, one could say that it is a separated list followed with an
   optional delimiter; this works if one uses a left-recursive list. The
   following formulation is direct and seems most natural. It should lead to
   the smallest possible automaton. *)

right_flexible_list(delim, X):
| (* nothing *)
    { [] }
| x = X
    { [x] }
| x = X delim xs = right_flexible_list(delim, X)
    { x :: xs }

(* In a left-flexible list, the first delimiter is optional, i.e., [delim] can
   be viewed as an opening or as a separator, as desired. *)

(* Again, there are several ways of expressing this, and again, I suppose the
   following formulation is simplest. It is the mirror image of the above
   definition, so it is naturally left-recursive, this time. *)

reverse_left_flexible_list(delim, X):
| (* nothing *)
    { [] }
| x = X
    { [x] }
| xs = reverse_left_flexible_list(delim, X) delim x = X
    { x :: xs }

%inline left_flexible_list(delim, X):
  xs = reverse_left_flexible_list(delim, X)
    { List.rev xs }
