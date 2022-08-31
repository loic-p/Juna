(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top
module TL = TypeLambda

module Imap = Map.Make(struct type t = int let compare = compare end)
module Smap = Map.Make(String)
type funinfo = T.tag * Atom.atom * int * int
type funlist = { decl : T.function_declaration list ;
                 tags : funinfo list  }

(* Generation of fresh identifiers to make sure no conflicts happen *)
let fresh_tag : unit -> T.tag =
  let x = ref 0 in
  fun () -> x := !x + 1 ; !x - 1

let fresh_cons_tag : unit -> T.tag =
  let x = ref (-100) in (* -1 is for pair, -2 for True, -3 for False, -4 for Unit *)
  fun () -> x := !x - 1 ; !x + 1

(* We will have a "main switch" that calls defunctionalized functions
   for every number of parameters. This function keeps track of which
   number of parameters we need, and returns the name of the appropriate
   switch when asked. *)
let mainswitch =
  let names = ref Imap.empty in
  fun n ->
  if Imap.mem n (!names) then
    Imap.find n (!names)
  else
    let name = Atom.fresh ("switch_" ^ (string_of_int n) ^ "_args") in
    names := Imap.add n name (!names) ;
    name

(* temporary function b/c i'm not brave enough to try deep pattern matching 
   before the deadline *)
let force_variable : S.pattern -> T.variable =
  function
  | S.ThrowawayPt -> Atom.fresh "throwaway"
  | S.VarPt v -> v
  | _ -> failwith "Deep pattern matching :( \nI am sorry but this is not implemented :( :("

(* Nothing interesting *)
let rec translate_val : S.value -> T.value =
  function
  | S.VVar var -> T.VVar var
  | S.VLit i -> T.VLit i
  | S.VBinOp (v1, o, v2) ->
     let v1' = translate_val v1 in
     let v2' = translate_val v2 in
     T.VBinOp (v1', o, v2')

(* Lambda abstraction translation is the most interesting part here.
   Every lambda abstraction is defunctionalized and translated to
   an algebraic data type with a tag used to call it. *)
let rec translate_block : funlist -> T.tag Smap.t -> S.variable -> Atom.Set.t -> S.block ->
                          funlist * T.block =
  fun f cons_tags var bnd bl ->
  match bl with
  | S.Lam (args, body) ->
     let free = Atom.Set.elements (Atom.Set.diff (S.fv_lambda args body) bnd) in
     let freeval = List.map (fun x -> T.VVar x) free in
     let (f2, body') = translate f cons_tags body in
     let tag = fresh_tag () in
     let fname = Atom.fresh ((TL.string_of_atom var)^ "_fun") in
     let func = T.Fun (fname, free@args, body') in
     let f3 = { decl = func::f2.decl ;
                tags = (tag, fname, List.length free, List.length args)::f2.tags } in
     let bl' = T.Cons (tag, freeval) in
     (f3, bl')
  | S.Pair (v1, v2) ->
     let v1' = translate_val v1 in
     let v2' = translate_val v2 in
     (f, T.Cons (-1, [v1' ; v2']))
  | S.Cons (cons, args) ->
     let args' = List.map translate_val args in
     let tag = Smap.find cons cons_tags in
     (f, T.Cons (tag, args'))
  | S.String s ->
     (f, T.String s)
  | S.CmpOp (v1, o, v2) ->
     let v1' = translate_val v1 in
     let v2' = translate_val v2 in
     (f, T.CmpOp (v1', o, v2'))

(* Converts Tail to Top. Note that almost every block will terminate
   by a tail call to a switch. *)
and translate : funlist -> T.tag Smap.t -> S.term ->
                funlist * T.term =
  fun f cons_tags t ->
  match t with
  | S.Exit ->
     (f, T.Exit)
  | S.TailCall (var, args) -> 
     (f, T.TailCall (mainswitch (List.length args), (T.VVar var)::args))
  | S.LetVal (var, value, t) ->
     let (f', t') = translate f cons_tags t in
     let value' = translate_val value in
     (f', T.LetVal (var, value', t'))
  | S.LetBlo (var, block, t) ->
     let (f', t') = translate f cons_tags t in
     let (f'', block') = translate_block f' cons_tags var Atom.Set.empty block in
     (f'', T.LetBlo (var, block', t'))
  | S.LetBloRec (var, prev, block, t) ->
     let (f', t') = translate f cons_tags t in
     let (f'', block') = translate_block f' cons_tags var Atom.Set.empty block in
     (f'', T.LetBloRec (var, prev, block', t'))
  | S.Print_int (var) ->
     let id = fst TL.basevar_printint in
     let block = T.Cons (-1, []) in
     let t = T.TailCall (mainswitch 1, [T.VVar var ; T.VVar id]) in
     (f, T.LetBlo (id, block, t))
  | S.Print_string (var) ->
     let id = fst TL.basevar_printstring in
     let block = T.Cons (-2, []) in
     let t = T.TailCall (mainswitch 1, [T.VVar var ; T.VVar id]) in
     (f, T.LetBlo (id, block, t))
  | S.Match (var, clauses) ->
     let aux clause (f, clauses) =
       let (f', clause') = translate_clause f cons_tags clause in
       (f', clause'::clauses)
     in
     let (f', clauses') = List.fold_right aux clauses (f, []) in
     (f', T.Swi (var, clauses'))

(** TODO **)
(* deep pattern matching *)
and translate_clause : funlist -> T.tag Smap.t -> S.clause ->
                       funlist * T.branch =
  fun f cons_tags (pat, t) ->
  let (f', t') = translate f cons_tags t in
  let br = match pat with
    | S.ThrowawayPt -> T.BrDefault t'
    | S.VarPt v -> T.BrVar (v, t')
    | S.TuplePt (p1, p2) ->
       let v1 = force_variable p1 in
       let v2 = force_variable p2 in
       T.Branch (-1, [v1 ; v2], t')
    | S.ConsPt (c, pl) ->
       let tag = Smap.find c cons_tags in
       let vars = List.map force_variable pl in
       T.Branch (tag, vars, t')
  in
  (f', br)

(* This function, when given a list of all the defunctionalized
   functions in the program, orders them according to their number
   of parameters, so that each one can be part of the corresponding
   switch. *)
let separate_switches : funinfo list -> (int * funinfo list) list =
  fun l ->
  let rec aux = function
    | [] -> Imap.empty
    | hd::tl ->
       let (_, _, _, n) = hd in
       let m = aux tl in
       if Imap.mem n m then
         let l = Imap.find n m in
         Imap.add n (hd::l) m
       else
         Imap.add n [hd] m
  in
  let m = aux l in
  Imap.fold (fun k a b -> (k, a)::b) m []

(* Constructs a switch that calls the defunctionalized functions *)
let construct_switch : int * funinfo list -> T.function_declaration =
  fun (n, f) ->
  let name = mainswitch n in
  let cal = Atom.fresh "callee" in
  let arg = List.init n (fun _ -> Atom.fresh "argswitch") in
  let argv = List.map (fun x -> T.VVar x) arg in
  let aux (tag, name, n, _) =
    let free = List.init n (fun _ -> Atom.fresh "freearg") in
    let freev = List.map (fun x -> T.VVar x) free in
    T.Branch (tag, free, T.TailCall (name, freev@argv))
  in
  let branches = List.map aux f in
  let body = T.Swi (cal, branches) in
  T.Fun (name, cal::arg, body)

(* Calls the previous function for every number of parameters *)
let construct_switches : funlist -> T.function_declaration list =
  fun f ->
  let ss = separate_switches f.tags in
  let s = List.map construct_switch ss in
  s@f.decl

(* We need to put the base functions in the switches. This is the place
   where we do it. *)
let base_functions : funlist =
  let s1 = Atom.fresh "print_int_fun" in
  let s2 = Atom.fresh "print_string_fun" in
  let a1 = Atom.fresh "print_arg" in
  let a2 = Atom.fresh "print_cont" in
  let print_int_decl =
    T.Fun (s1, [a1 ; a2], T.Print_int (a1, T.TailCall (mainswitch 1, [T.VVar a2 ; T.VLit 0])))
  in
  let print_string_decl =
    T.Fun (s2, [a1 ; a2], T.Print_string (a1, T.TailCall (mainswitch 1, [T.VVar a2 ; T.VLit 0])))
  in
  let print_int_tag = (-1, s1, 0, 2) in
  let print_string_tag = (-2, s2, 0, 2) in
  let decl = [ print_int_decl ; print_string_decl ] in
  let tags = [ print_int_tag ; print_string_tag ] in
  { decl = decl ;
    tags = tags }

let base_cons : T.tag Smap.t =
  let aux (n, _, t) b =
    Smap.add n t b
  in
  List.fold_right aux TL.base_cons Smap.empty

(* Some info about type introduction rules *)
  
let gen_cons_tags : unit Smap.t -> T.tag Smap.t =
  fun m ->
  let aux k _ m =
    if Smap.mem k base_cons then
      Smap.add k (Smap.find k base_cons) m
    else
      Smap.add k (fresh_cons_tag ()) m
  in
  Smap.fold aux m Smap.empty

(* Main defunctionalization program. *)
  
let defun_prog : S.program -> T.program =
  fun (t, _, cons) ->
  let cons_tags = gen_cons_tags cons in
  let (f, t) = translate base_functions cons_tags t in
  (construct_switches f, t)
