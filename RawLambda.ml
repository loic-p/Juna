(*** Intermediate language after parsing ***)

module TL = TypeLambda
module TDL = TypeDeclLambda
  
(* Indentifiers for constructors of a given type. *)

type type_cons = 
  string 

and type_var =
  string TDL.placed

(* Rule for type introduction.
   Contains the name of the rule and its type.

   A a_1 ... a_k : t_1 -> ... -> t_k 
     -> t u_1 ... u_n 
*)
  
and type_intro =
  (type_cons * TL.gen_type) TDL.placed

(* Declaration of a type.
   First the name of the type, then the names of its arguments, then the introduction rules. 

   type t a_1 ... a_k =
   | R_1
   | ...
   | R_n
*)
  
and type_decl_ =
  type_var * (type_var list) * (type_intro list)

(* Type annotations for term variables *)
(* Polymorphic types introduce forall quantifiers *)
  
and type_hint =
  | NoHint
  | Hint of TL.gen_type * Error.place
  
(** Term syntax **)
(* Variables for terms. *)

and term_var =
  string

(* Token for let bindings. Each one can be marked as recursive or not. *)

and recursive =
  | Recursive
  | NonRecursive

(* The four standard integer arithmetic operations.
   Will extend with fancier operations, but lets keep it simple for now. *)

and binop = TL.binop =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv

(* Comparisons. Give them two integers, they will return a boolean *)

and cmpop = TL.cmpop =
  | CmpGt
  | CmpGe
  | CmpLt
  | CmpLe
  | CmpEq

(* Standard lambda-calculus syntax, plus 
   - integer literals
   - binary operations
   - tuples
   - algebraic datatypes
   - pattern matching.
 *)
  
and term_ =
  | Var of term_var
  | Lam of (term_var list) * term
  | App of term * term
  | Cons of type_cons * (term list)
  | Match of term * ((TDL.pattern * term) list)
  | Lit of int
  | String of string
  | BinOp of term * binop * term
  | CmpOp of term * cmpop * term
  | Tuple of term * term
  | Let of recursive * term_var * type_hint * term * term

(* Every abstract syntax tree node of type [term] is annotated with a place,
   that is, a position in the source code. This allows us to produce a good
   error message when a problem is detected. *)

and term =
  term_ TDL.placed

(* not sure what is this. Probably useful somewhere. *)
  
let typenames_of_strings : string list -> TL.TypeVar.t list =
  fun l ->
  List.map (fun x -> TL.TypeVar.Named x) l

(* The following annotation requests the automatic generation of a [show_]
   function for each of the types defined above. For instance, the function
   [show_term], of type [term -> string], converts a term to a string. These
   functions can be useful during debugging. Running with [--debug] causes
   every intermediate abstract syntax tree to be displayed in this way. *)

[@@deriving show { with_path = false }]
