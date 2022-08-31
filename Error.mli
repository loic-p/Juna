open Lexing

(* A place is a pair of a start position and an end position. *)

type place =
  position * position

(* [set_filename lexbuf filename] updates [lexbuf] to record the
   fact that the current file name is [filename]. This file name
   is later used in error messages. *)

val set_filename: lexbuf -> string -> unit

(* [place lexbuf] produces a pair of the current token's start and
   end positions. This function is useful when reporting an error
   during lexing. *)

val place: lexbuf -> place

(* [error place format ...] displays an error message and exits.
   The error message is located at [place]. The error message
   is composed based on [format] and the extra arguments [...]. *)

val error: place -> string -> 'a

(* specific error handlers *)

exception Type_error of place * string
  
val redefinition : string -> place -> 'a
val type_gen : string -> place -> 'a
val gadt_cons_type : string -> place -> 'a
val type_arity : string -> int -> place -> 'a
val cons_arity : string -> int -> place -> 'a
val type_unbound : string -> place -> 'a
val unexpected_function : string -> place -> 'a
val unexpected_pair : string -> place -> 'a
val expected_arrow : place -> 'a
val unmatching_type : string -> string -> place -> 'a
val var_unbound : string -> place -> 'a
val cons_unbound : string -> place -> 'a
val deep_matching : place -> 'a
val escape : place -> 'a
val pattern_redef : string -> place -> 'a
val pattern_ill_formed : place -> 'a
val too_much_args : string -> place -> 'a
val gadt_weird_param : string -> place -> 'a

val pp_place: Format.formatter -> place -> unit                                            
