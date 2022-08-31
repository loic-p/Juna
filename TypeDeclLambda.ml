(*** Intermediate language after type declaration checking ***)

module TL = TypeLambda
module Tmap = TL.TypeMap
module Smap = Map.Make (String)
          
(** Term syntax **)
(* Variables for terms. *)

type term_var =
  string

(* Token for let bindings. Each one can be marked as recursive or not. *)

and recursive = TL.recursive =
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

and type_cons =
  string

(* Patterns are either
   - a wildcard
   - a single variable
   - a pair of patterns (not implemented yet) 
   - a constructor applied to some patterns
   - an annotated version of a pattern *)
  
and pattern_ =
  | ThrowawayPt
  | VarPt of term_var
  | TuplePt of pattern * pattern
  | ConsPt of type_cons * (pattern list)
  | AnnotatedPt of pattern * TL.type_t

and pattern =
  pattern_ placed

and type_hint =
  | NoHint
  | Hint of TL.gen_type * Error.place

(* Standard lambda-calculus syntax, plus some cool things *)

and term_ =
  | Var of term_var
  | Lam of term_var * term
  | App of term * term
  | Cons of type_cons * (term list)
  | Match of term * ((pattern * term) list)
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
  term_ placed

(* A value of type ['a placed] can be thought of as a value of type ['a]
   decorated with a place. *)
  
and 'a placed = {
  place: Error.place;
  value: 'a
  }

[@@deriving show { with_path = false }]
              
type type_subst = TL.type_t Tmap.t
type binding = Rigid | Wobbly
type identifier = Atom.atom

(* These are used in the type inference phase. More or less everything one
   should know during the inference :
   - vars are known variables with type, wobbliness, and a unique name
   - maps and subst are used to refine the types with known info
   - typs are the type families defined by the programmer
   - cons are the type introduction rules defined by the programmer *)
                
type env =
  { vars : (binding * identifier * TL.gen_type) Smap.t ;
    maps : type_subst ;
    typs : TL.type_info Smap.t ;
    cons : TL.intro_rule Smap.t ;
    subs : type_subst }

(* The following annotation requests the automatic generation of a [show_]
   function for each of the types defined above. For instance, the function
   [show_term], of type [term -> string], converts a term to a string. These
   functions can be useful during debugging. Running with [--debug] causes
   every intermediate abstract syntax tree to be displayed in this way. *)


