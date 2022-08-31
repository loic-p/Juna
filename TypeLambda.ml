(*** Intermediate language after type inference ***)

(** Type syntax **)
(* Variables for types. *)

module TypeVar =
  struct
    type t =
      | Named of string
      | Fresh of int

    [@@deriving show { with_path = false }]

    let compare = Pervasives.compare
  end

module TypeMap = Map.Make (TypeVar)
module Smap = Map.Make (String)

type type_family = string

[@@deriving show { with_path = false }]

(* A type is either:
  - a type variable
  - a product of two types
  - an instance of a type family
  - an arrow type *)
                 
type type_t =
  | BaseType of TypeVar.t
  | Prod of type_t * type_t
  | Inst of type_family * (type_t list)
  | Arrow of type_t * type_t

[@@deriving show { with_path = false }]
           
(* Arity is always good to know *)

type type_info =
  { arity : int }
           
type type_cons =
  string

(* Rule for type introduction.
   - gen_param are the phantom parameters that do not appear outside of the rule
   - args are the type of the arguments that the rule requires
   - result is the instance of the constructed type
   - total_type is more or less args -> result *)
  
type intro_rule =
  { gen_param : TypeVar.t list ;
    args : type_t list ;
    result : type_family * (type_t list) ;
    total_type : type_t }

(* Type annotations for term variables *)
(* Generalized types introduce forall quantifiers *)
  
type gen_type =
  (TypeVar.t list) * type_t

[@@deriving show { with_path = false }]
  
(** Term syntax **)
(* Variables for terms. *)

type term_var =
  Atom.atom

(* Token for let bindings. Each one can be marked as recursive or not. *)

type recursive =
  | Recursive
  | NonRecursive

(* The four standard integer arithmetic operations.
   Will extend with fancier operations, but lets keep it simple for now. *)

type binop =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv

(* Comparisons. Give them two integers, they will return a boolean *)

type cmpop =
  | CmpGt
  | CmpGe
  | CmpLt
  | CmpLe
  | CmpEq

(* Patterns are either
   - a wildcard
   - a single variable
   - a pair of patterns (not implemented yet) 
   - a constructor applied to some patterns
   - an annotated version of a pattern *)
  
type pattern_ =
  | ThrowawayPt
  | VarPt of term_var
  | TuplePt of pattern * pattern
  | ConsPt of type_cons * (pattern list)

and pattern =
  pattern_ annotated

(* Standard lambda-calculus syntax, plus some cool things *)

and clause =
  pattern * term

and term_ =
  | Var of term_var
  | Lam of term_var * term
  | App of term * term
  | Cons of type_cons * (term list)
  | Match of term * (clause list)
  | Lit of int
  | String of string
  | BinOp of term * binop * term
  | CmpOp of term * cmpop * term
  | Tuple of term * term
  | Let of recursive * term_var * term * term

(* Every abstract syntax tree node of type [term] is annotated with a place,
   that is, a position in the source code. This allows us to produce a good
   error message when a problem is detected. *)

and term =
  term_ annotated

(* A value of type ['a placed] can be thought of as a value of type ['a]
   decorated with a place. *)
  
and 'a annotated = {
    typ : type_t ;
    place : Error.place ;
    value : 'a
  }

type program =
  term * Atom.atom Smap.t * unit Smap.t

(* All the predefinite data. Types, introduction rules and variables *)
  
(* The fundamental types *)
let basetype_int : type_t =
  Inst ("int", [])

let basetype_bool : type_t =
  Inst ("bool", [])

let basetype_unit : type_t =
  Inst ("unit", [])

let basetype_string : type_t =
  Inst ("string", [])

(* Intro rules for bool and unit *)
let basecons_bool : intro_rule =
  { gen_param = [] ;
    args = [] ;
    result = ("bool", []) ;
    total_type = basetype_bool }

let basecons_unit : intro_rule =
  { gen_param = [] ;
    args = [] ;
    result = ("unit", []) ;
    total_type = basetype_unit }

(* builtin functions *)
let basevar_printint : Atom.atom * gen_type =
  (Atom.fresh "print_int", ([], Arrow (basetype_int, basetype_unit)))

let basevar_printstring : Atom.atom * gen_type =
  (Atom.fresh "print_string", ([], Arrow (basetype_string, basetype_unit)))

let basevar_fst : Atom.atom * gen_type =
  let tv1 = TypeVar.Named "0a" in
  let tv2 = TypeVar.Named "0b" in
  (Atom.fresh "fst", ([tv1 ; tv2], Arrow (Prod (BaseType tv1, BaseType tv2), BaseType tv1)))

let basevar_snd : Atom.atom * gen_type =
  let tv1 = TypeVar.Named "1a" in
  let tv2 = TypeVar.Named "1b" in
  (Atom.fresh "snd", ([tv1 ; tv2], Arrow (Prod (BaseType tv1, BaseType tv2), BaseType tv2)))

let base_types =
  [ basetype_int ;
    basetype_bool ;
    basetype_unit ;
    basetype_string ]

let base_cons =
  [ ("True", basecons_bool, -2) ;
    ("False", basecons_bool, -3) ;
    ("Unit", basecons_unit, -4) ]

let base_vars =
  [ ("print_int", basevar_printint) ;
    ("print_string", basevar_printstring) ;
    ("fst", basevar_fst) ;
    ("snd", basevar_snd) ]

(* The following annotation requests the automatic generation of a [show_]
   function for each of the types defined above. For instance, the function
   [show_term], of type [term -> string], converts a term to a string. These
   functions can be useful during debugging. Running with [--debug] causes
   every intermediate abstract syntax tree to be displayed in this way. *)




(* Visualisation b/c these preprocessor are not that practical and
   I ended up displayint types a LOT *)

let parenthesise (s, p) =
  if p then "(" ^ s ^ ")" else s

let string_of_atom (x : Atom.atom) : string =
  Printf.sprintf "%s_%d" (Atom.hint x) (Atom.identity x)
  
(* Converts a typevar to a string *)
let string_of_typevar : TypeVar.t -> string =
  function
  | TypeVar.Named s -> s
  | TypeVar.Fresh i -> "type_" ^ (string_of_int i)
       
(* Converts a type to a string for pretty errors *)
let string_of_type : type_t -> string =
  fun t ->
  let rec aux t =
    match t with
    | BaseType t -> (string_of_typevar t, false)
    | Prod (t1, t2) ->
       let s1 = parenthesise (aux t1) in
       let s2 = parenthesise (aux t2) in
       (s1 ^ " * " ^ s2, true)
    | Arrow (t1, t2) ->
       let s1 = parenthesise (aux t1) in
       let s2 = fst (aux t2) in
       (s1 ^ " -> " ^ s2, true)
    | Inst (t, tl) ->
       let l = List.map (fun x -> parenthesise (aux x)) tl in
       let paren = List.length tl > 0 in
       (List.fold_left (fun b a -> b ^ " " ^ a) t l, paren)
  in
  fst (aux t)

(* Same for a type family *)
let string_of_typescheme : gen_type -> string =
  fun (g, t) ->
  if List.length g = 0 then
    string_of_type t
  else
    let aux a b =
      b ^ " " ^ string_of_typevar a
    in
    let s = List.fold_right aux g "Forall" in
    s ^ ", " ^ string_of_type t

let string_of_pattern : pattern -> string =
  fun pat ->
  let rec aux pat =
    match pat.value with
    | ThrowawayPt -> ("_", false)
    | VarPt tv -> (string_of_atom tv, false)
    | TuplePt (p1, p2) ->
       let s1 = fst (aux p1) in
       let s2 = fst (aux p2) in
       ("(" ^ s1 ^ " , " ^ s2 ^ ")", false)
    | ConsPt (c, pl) ->
       let pl' = List.map (fun x -> parenthesise (aux x)) pl in
       let paren = List.length pl > 0 in
       (List.fold_left (fun b a -> b ^ " " ^ a) c pl', paren)
  in
  let pat' = parenthesise (aux pat) in
  let typ = string_of_type pat.typ in
  pat' ^ ":" ^ typ

let string_of_binop : binop -> string =
  function
  | OpAdd -> " + "
  | OpSub -> " - "
  | OpMul -> "*"
  | OpDiv -> "/"

let string_of_cmpop : cmpop -> string =
  function
  | CmpGe -> " >= "
  | CmpGt -> " > "
  | CmpLe -> " <= "
  | CmpLt -> " < "
  | CmpEq -> " = "

let rec string_of_clause : int option -> clause -> string =
  fun indent (pat, t) ->
  let nexti = match indent with None -> None | Some n -> Some (n+1) in
  let nl = match indent with None -> " " | Some n -> "\n" ^ (String.make (2*n + 2) ' ') in
  let t' = fst (string_of_term_ nexti t) in
  let pat' = string_of_pattern pat in
  "| " ^ pat' ^ " =>" ^ nl ^ t'
  
and string_of_term_ indent t =
  match t.value with
  | Var tv ->
     let s = string_of_atom tv in
     (s, true)
  | Lam (tv, t) ->
     begin
       let tvs = string_of_atom tv in
       match indent with
       | None ->
          let ts = parenthesise (string_of_term_ None t) in
          ("fun " ^ tvs ^ " -> " ^ ts, true)
       | Some n ->
          let nl = "\n" ^ (String.make (2*n) ' ') in
          let ts = fst (string_of_term_ (Some (n+1)) t) in
          ("fun " ^ tvs ^ " ->" ^ nl ^ "  " ^ ts, true)
     end
  | App (t1, t2) ->
     let s1 = string_of_term_ None t1 in
     let s2 = string_of_term_ None t2 in
     ((parenthesise s1) ^ " " ^ (parenthesise s2), true)
  | Cons (tc, l) ->
     let l' = List.map (fun x -> parenthesise (string_of_term_ None x)) l in
     let paren = List.length l > 0 in
     (List.fold_left (fun b a -> b ^ " " ^ a) tc l', paren)
  | Match (t, clauses) ->
     begin
       let ts = parenthesise (string_of_term_ None t) in
       let typs = string_of_type t.typ in
       match indent with
       | None ->
          let clauses' = List.map (string_of_clause indent) clauses in
          let cls = List.fold_left (fun b a -> b ^ " " ^ a) "" clauses' in
          ("match " ^ ts ^ ":" ^ typs ^ " with " ^ cls, true)
       | Some n ->
          let clauses' = List.map (string_of_clause indent) clauses in
          let nl = "\n" ^ (String.make (2*n) ' ') in
          let cls = match clauses' with
            | [] -> "Empty match ???"
            | hd::tl -> List.fold_left (fun b a -> b ^ nl ^ a) hd tl
          in
          ("match " ^ ts ^ ":" ^ typs ^ " with " ^ nl ^ cls, true)
     end
  | Lit i ->
     (string_of_int i, false)
  | String s ->
     ("\"" ^ s ^ "\"", false)
  | BinOp (t1, o, t2) ->
     let os = string_of_binop o in
     let s1 = string_of_term_ None t1 in
     let s2 = string_of_term_ None t2 in
     ((parenthesise s1) ^ os ^ (parenthesise s2), true)
  | CmpOp (t1, o, t2) ->
     let os = string_of_cmpop o in
     let s1 = string_of_term_ None t1 in
     let s2 = string_of_term_ None t2 in
     ((parenthesise s1) ^ os ^ (parenthesise s2), true)
  | Tuple (t1, t2) ->
     let s1 = fst (string_of_term_ None t1) in
     let s2 = fst (string_of_term_ None t2) in
     ("(" ^ s1 ^ " , " ^ s2 ^ ")", false)
  | Let (recc, tv, t1, t2) ->
     begin
       let tvs = string_of_atom tv in
       let typs = string_of_type t1.typ in
       match indent with
       | None ->
          let s1 = fst (string_of_term_ None t1) in
          let s2 = fst (string_of_term_ None t2) in
          ("let " ^ tvs ^ " : " ^ typs ^ " = " ^ s1 ^ " in " ^ s2, true)
       | Some n ->
          let nl = "\n" ^ (String.make (2*n) ' ') in
          let s1 = fst (string_of_term_ (Some (n+1)) t1) in
          let s2 = fst (string_of_term_ indent t2) in
          ("let " ^ tvs ^ " : " ^ typs ^ " =" ^ nl ^ "  " ^ s1 ^ nl ^ "in" ^ nl ^ s2, true)
     end
  
and string_of_term : term -> string =
  fun t ->
  fst (string_of_term_ (Some 0) t)
  
                                             
