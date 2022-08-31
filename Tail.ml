(* This intermediate language describes the result of the CPS transformation.
   It is a lambda-calculus where the ordering of computations is explicit and
   where every function call is a tail call.

   The following syntactic categories are distinguished:

   1. "Values" include variables, integer literals, and applications of the
      primitive integer operations to values. Instead of "values", they could
      also be referred to as "pure expressions". They are expressions whose
      evaluation terminates and has no side effect, not even memory
      allocation.

   2. "Blocks" include lambda-abstractions. Even though lambda-abstractions
      are traditionally considered values, here, they are viewed as
      expressions whose evaluation has a side effect, namely, the allocation
      of a memory block.

   3. "Terms" are expressions with side effects. Terms always appear in tail
      position: an examination of the syntax of terms shows that a term can be
      viewed as a sequence of [LetVal], [LetBlo] and [Print] instructions,
      terminated with either [Exit] or [TailCall]. This implies, in
      particular, that every call is a tail call.

   In contrast with the surface language, where every lambda-abstraction has
   arity 1, in this calculus, lambda-abstractions of arbitrary arity are
   supported. A lambda-abstraction [Lam] carries a list of formal arguments
   and a function call [TailCall] carries a list of actual arguments. Partial
   applications or over-applications are not supported: it is the programmer's
   responsibility to ensure that every function call provides exactly as many
   arguments as expected by the called function. *)

module TL = TypeLambda
module Smap = Map.Make(String)

type variable =
  Atom.atom

and cons =
  string

and binop = TL.binop =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv

and cmpop = TL.cmpop =
  | CmpGt
  | CmpGe
  | CmpLt
  | CmpLe
  | CmpEq
  
and value =
  | VVar of variable
  | VLit of int
  | VBinOp of value * binop * value

and block =
  | Lam of variable list * term
  | CmpOp of value * cmpop * value
  | Cons of cons * value list
  | Pair of value * value
  | String of string

(* Terms include the following constructs:

   - The primitive operation [Exit] stops the program.

   - The tail call [TailCall (v, vs)] transfers control to the function [v]
     with actual arguments [vs]. (The value [v] should be a function and its
     arity should be the length of [vs].)

   - The term [Print (v, t)] prints the value [v], then executes the term [t].
     (The value [v] should be a primitive integer value.)

   - The term [LetVal (x, v, t)] binds the variable [x] to the value [v], then
     executes the term [t].

   - The term [LetBlo (x, b, t)] allocates the memory block [b] and binds the
     variable [x] to its address, then executes the term [t]. *)

and pattern = 
  | ThrowawayPt
  | VarPt of variable
  | TuplePt of pattern * pattern
  | ConsPt of cons * (pattern list)
         
and clause =
  pattern * term

and term =
  | Exit
  | Print_int of variable
  | Print_string of variable
  | TailCall of variable * value list
  | LetVal of variable * value * term
  | LetBlo of variable * block * term
  | LetBloRec of variable * variable * block * term
  | Match of variable * clause list

[@@deriving show { with_path = false }]
           
type program =
  term * Atom.atom Smap.t * unit Smap.t

(* -------------------------------------------------------------------------- *)

(* Constructor functions. *)

let vvar x =
  VVar x

let vvars xs =
  List.map vvar xs

(* -------------------------------------------------------------------------- *)

(* Computing the free variables of a value, block, or term. *)

open Atom.Set

let base_values =
  let aux (_, (i , _)) b =
    add i b
  in
  List.fold_right aux TL.base_vars empty

let rec fv_value (v : value) =
  match v with
  | VVar x ->
     if mem x base_values then
       empty
     else
       singleton x
  | VLit _ ->
     empty
  | VBinOp (v1, _, v2) ->
     union (fv_value v1) (fv_value v2)

and fv_values (vs : value list) =
  union_many fv_value vs

and fv_lambda (xs : variable list) (t : term) =
  diff (fv_term t) (of_list xs)

and fv_block (b : block) =
  match b with
  | Lam (xs, t) ->
     fv_lambda xs t
  | String _ ->
     empty
  | Pair (v1, v2) ->
     union (fv_value v1) (fv_value v2)
  | Cons (_, l) ->
     let l' = List.map fv_value l in
     List.fold_right union l' empty
  | CmpOp (v1, _, v2) ->
     union (fv_value v1) (fv_value v2)

and fv_pat (p : pattern) =
  match p with
  | ThrowawayPt ->
     empty
  | VarPt v ->
     singleton v
  | TuplePt (p1, p2) ->
     union (fv_pat p1) (fv_pat p2)
  | ConsPt (_, l) ->
     let l' = List.map fv_pat l in
     List.fold_right union l' empty

and fv_clause (pat, term) =
  diff (fv_term term) (fv_pat pat)

and fv_term (t : term) =
  match t with
  | Exit ->
      empty
  | TailCall (v, vs) ->
      union (fv_values vs) (singleton v)
  | LetVal (x, v1, t2) ->
      union
        (fv_value v1)
        (remove x (fv_term t2))
  | Print_string v ->
     singleton v
  | Print_int v ->
     singleton v
  | LetBlo (x, b1, t2) ->
      union
        (fv_block b1)
        (remove x (fv_term t2))
  | LetBloRec (x, v, b1, t2) ->
      union
        (remove v (fv_block b1))
        (remove x (fv_term t2))
  | Match (v, clauses) ->
     let l = List.map fv_clause clauses in
     let f = List.fold_right union l empty in
     union f (singleton v)
