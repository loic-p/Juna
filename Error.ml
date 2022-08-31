open Lexing

type place =
  position * position

let place lexbuf : place =
  lexbuf.lex_start_p, lexbuf.lex_curr_p

let line p : int =
  p.pos_lnum

let column p : int =
  p.pos_cnum - p.pos_bol

let show place : string =
  let startp, endp = place in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d"
    startp.pos_fname
    (line startp)
    (column startp)
    (endp.pos_cnum - startp.pos_bol) (* intentionally [startp.pos_bol] *)

let display header place str =
  Printf.fprintf stderr "%s:\n" (show place);
  Printf.fprintf stderr "%s\n" (header ^ str ^ "\n%!") ;
  exit 1

let error place format =
  display
    "Error: "
    place format ;
  failwith "Terminated."

let set_filename lexbuf filename =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename }


(* Specific error handlers *)

exception Type_error of place * string

let redefinition name place =
  raise (Type_error (place, name ^ " already exists and should not be redefined."))

let type_gen name place =
  raise (Type_error (place, name ^ " already exists and should not be generalized on."))

let gadt_cons_type name place =
  raise (Type_error (place, "The type of an introduction rule should be an arrow type\
                            whith an instance of " ^ name ^ " as codomain."))

let type_arity name arity place =
  raise (Type_error (place, "The type " ^ name ^ " expects " ^
                             (string_of_int arity) ^ " type arguments."))

let cons_arity name arity place =
  raise (Type_error (place, "The type constructor " ^ name ^ " expects " ^
                             (string_of_int arity) ^ " type arguments."))

let type_unbound name place =
  raise (Type_error (place, "The type name " ^ name ^ " is unbound here."))

let unexpected_function expected place =
  raise (Type_error (place, "A " ^ expected ^ " was expected, but the given \
                                              term is a function."))

let unexpected_pair expected place =
  raise (Type_error (place, "A " ^ expected ^ " was expected, but the given \ 
                                              term is a pair."))

let expected_arrow place =
  raise (Type_error (place, "This term isn't typed as an arrow and can therefore \
                            not be applied."))
  
let unmatching_type : string -> string -> place -> 'a =
  fun t1 t2 place ->
  raise (Type_error (place, "The types " ^ t1 ^ " and " ^ t2 ^ " are incompatible."))

let var_unbound name place =
  raise (Type_error (place, "The variable " ^ name ^ " is unbound here."))

let cons_unbound name place =
  raise (Type_error (place, "The constructor " ^ name ^ " is unbound here."))

let deep_matching place =
  raise (Type_error (place, "Unfortunately, deep pattern matching isn't supported yet.\
                            I hope I will be able to do it. Sorry :("))

let escape place =
  raise (Type_error (place, "TODO"))

let pattern_redef name place =
  raise (Type_error (place, "The variable " ^ name ^ " appears twice in the same pattern."))

let pattern_ill_formed place =
  raise (Type_error (place, "This pattern is ill-formed"))

let too_much_args name place =
  raise (Type_error (place, "The variable " ^ name ^ " is applied to too many arguments."))

let gadt_weird_param name place =
  raise (Type_error (place, "The type " ^ name ^ " cannot have a parameter with its own name."))


let pp_place formatter _place =
  Format.fprintf formatter "<>"
