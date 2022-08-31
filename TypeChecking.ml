(** Checking of full typing **)
(* Reads TypeLambda *)
(* TODO : Deep pattern matching ??? *)

module TL = TypeLambda
module Smap = Map.Make(String)
module Tmap = TypeLambda.TypeMap
module UF = UnionFind

type eq = TL.type_t * TL.type_t

type env =
  { vars : TL.type_t Smap ;
    typs : TL.type_info Tmap ;
    cons : TL.intro_rule Smap ;
    equa : eq list }

type label =
  | BaseType of TL.TypeVar.t
  | Prod
  | Inst of TL.TypeVar.t
  | Arrow
  | Nothing
  
type ltbl = (label * (int list), int) Hashtbl.t

let fresh_type_name =
  let x = ref 0 in
  fun () -> x := !x + 1 ; TL.TypeVar.Fresh (!x)

let fresh_integer =
  let r = ref 0 in
  fun () -> r := !r + 1 ; !r - 1
          
(* Fills the given hash table with the nodes included in t,
   and returns the number of the root node *)
let rec hashtable_of_type (tbl : ltbl) t =
  let key = match t with
  | TL.BaseType tv ->
     (BaseType tv, [])
  | TL.Arrow (t1, t2) ->
     let i1 = hashtable_of_type tbl t1 in
     let i2 = hashtable_of_type tbl t2 in
     (Arrow, [i1 ; i2])
  | TL.Prod (t1, t2) ->
     let i1 = hashtable_of_type tbl t1 in
     let i2 = hashtable_of_type tbl t2 in
     (Prod, [i1 ; i2])
  | TL.Inst (tv, tl) ->
     let il = List.map (hashtable_of_type tbl) tl in
     (Inst tv, il)
  in
  if Hashtbl.mem tbl key then
    Hashtbl.find tbl key
  else
    (let i = fresh_integer () in
     Hashtbl.add tbl key i ; i)

(* Builds a graph representing the types t1, t2, and all of those
   appearing in rel. Returns the graph, the relations in it and the
   nodes corresponding to t1 and t2 *)
let graph_of_types t1 t2 rel =
  let tbl = Hashtbl.create 10 in
  let aux tbl (t3, t4) =
    (hashtable_of_type tbl t3, hashtable_of_type t4)
  in
  let i1 = hashtable_of_type tbl t1 in
  let i2 = hashtable_of_type tbl t2 in
  let rel_i = List.map (aux tbl) rel in
  let n = Hashtbl.length tbl in
  let empty_node = { UF.label = Nothing ;
                     UF.rank = 0 ;
                     UF.parent = 0 ;
                     UF.children = []} in
  let graph = Array.make n empty_node in
  assert (n = fresh_integer ()) ;
  let aux g (lbl, children) i =
    g.(i) <- { UF.label = lbl ;
               UF.rank = 0 ;
               UF.parent = i ;
               UF.children = children }
  in
  Hashtbl.iter (aux graph) tbl ;
  (graph, rel_i, i1, i2)


(* Check equality between t1 and t2 in the environment env. In
   the absence of equations, it reduces to basic equality. *)
let type_eq env t1 t2 =
  if List.length env.equa = 0 then
    t1 = t2
  else
    let (graph, rel, i1, i2) = graph_of_types t1 t2 env.equa in
    UF.decide_equality graph rel i1 i2
    
    
(* Printable types 
   Warning: possible confusion between string and format *)
let string_of_type (t : TL.type_t) =
  let parenthesise (s, p) =
    if p then "(" ^ s ^ ")" else s
  in
  let string_of_type_var t = function
    | Named s -> s
    | Fresh i -> "fresh_" ^ (string_of_int i)
  in
  let rec aux t =
    match t.value with
    | BaseType t -> (string_of_type_var t, false)
    | Prod (t1, t2) ->
       let s1 = parenthesise (aux t1) in
       let s2 = parenthesise (aux t2) in
       (s1 ^ " * " ^ s2, true)
    | Arrow (t1, t2) ->
       let s1 = parenthesise (aux t1) in
       let s2 = aux t2 in
       (s1 ^ " -> " ^ s2, true)
    | Inst (t, tl) ->
       let l = List.map (fun x -> parenthesise (aux x)) tl in
       (List.fold_left (fun b a -> b ^ " " ^ a) (string_of_type_var t) l, true)
  in
  aux t

(* predicate env |- t.value : t.typ *)

let rec check_term (e : env)
      (t : TL.term)
  match t.value with
  | TL.Var tv ->
     begin
       try
         let typ = Smap.find tv e.vars in
         if not (subtype env t.typ typ) then
           Error.instanciation t.typ typ t.place
       with
         _ -> Error.var_unbound tv t.place
     end
  | TL.Lam (tv, t') ->
     begin   
       match t.typ with
       | Arrow (typ1, typ2) ->
          if not (type_eq e typ2 t'.typ) then
            Error.unmatching_type typ2 t'.typ t.place
          else
            let e' = { e with
                       vars = Smap.add tv typ1 e.vars} in
            check_term e' t'
       | _ -> Error.unexpected_function (string_of_type t.typ) t'.place
     end
  | TL.App (t1, t2) ->
     begin
       match t1.typ with
       | Arrow (typ1, typ2) ->
          if not (type_eq e typ1 t2.typ) then
            Error.unmatching_type typ1 t2.typ t.place
          else if not (type_eq e typ2 t.typ) then
            Error.unmatching_type typ2 t.typ t.place
          else
            (check_term e t1 ;
             check_term e t2)
       | _ -> Error.expected_arrrow t1.place
     end
  | TL.Cons tc tl ->
     begin
       try
         let info = Smap.find tc e.cons in
         if List.length tl <> List.length info.args then
           Error.cons_arity tc (List.length info.args) (List.length tl)
         else
           (List.map (check_term e) tl ;
            let expected = build_abstraction_type info.args info.typ in
            let obtained = build_abstraction_type tl t.typ in
            if not (subtype env obtained expected) then
              Error.instanciation obtained expected t.place)
       with
       |  _ -> Error.cons_unbound tc place
     end
  | TL.Match (t', tl) ->
     check_term e t' ;
     let aux typ1 typ2 (x : TL.clause) =
       match x.typ with
       | Arrow (typ1', typ2') ->
          if not (type_eq e typ1' typ1) then
            Error.unmatching_type typ1' typ1 x.place
          else if not (type_eq e typ2' typ2) then
            Error.unmatching_type typ2' typ2 x.place
          else
            check_clause x
       | _ -> failwith "Unexpected error (code : TypeChecking.1), please report."
     in
     List.map (aux t'.typ t.typ) tl
  | TL.Lit i ->
     if not (type_eq e t.typ type_int) then
       Error.unmatching_type type_int t.typ t.place
  | TL.BinOp (t1, b, t2) ->
     (if not (type_eq e t1.typ type_int) then
        Error.unmatching_type type_int t1.typ t.place
      else if not (type_eq e t2.typ type_int) then
        Error.unmatching_type type_int t2.typ t.place
      else if not (type_eq e t.typ type_int) then
        Error.unmatching_type type_int t.typ t.place) ;
     (check_term e t1 ;
      check_term e t2)
  | TL.Tuple (t1, t2) ->
     begin
       match t.typ with
       | TL.Prod (typ1, typ2) ->
          (if not (type_eq e t1.typ typ1) then
             Error.unmatching_type t1.typ typ1 t1.place
           else if not (type_eq e t2.typ typ2) then
             Error.unmatching_type t2.typ typ2 t2.place) ;
          (check_term e t1 ;
           check_term e t2)
       | _ -> Error.unexpected_pair t.place
     end
  | TL.Let (r, tv, gtyp, t1, t2) ->
     let e' = { e with
                vars = Smap.add tv typ e.vars } in
     let (gen, typ) = gtyp in
     let type_var_info = { arity = 0 ; gadt = false } in
     let aux1 = fun b a -> Tmap.add a type_var_info b in
     let aux2 en = {en with
                     typs = List.fold_left aux1 en.typs gen} in
     let en = if r then aux2 e' else aux2 e in
     check_term en t1 ;
     (if not (type_eq en t1.typ typ) then
        Error.unmatching_type t1.typ typ t1.place) ;
     (if not (type_eq e t2.typ t.typ) then
        Error.unmatching_type t2.typ t.typ t2.place) ;
     check_term e' t2

(* checks a match clause typing *)
     
and check_clause (e : env)
          (c : TL.clause) =
  let (pt, t) = c.value in
  let (phantoms, e') = check_pattern e pt in
  (** PHANTOMS SHOULD NOT ESCAPE HERE **)
  (* since they have been generated with fresh names, this should not be a problem *)
  check_term e' t

(* dirty copy-paste from TypeDeclCheck, modified to work with TypeLambda *)  
(* creates a new instance of a type introduction rule, that is a version
   witch fresh generalized parameters names *)

let rec replace_type_name (newer : TL.TypeVar.t)
          (older : TL.TypeVar.t)
          (t : TL.type_t) =
  match t with
  | TL.BaseType tv ->
     if tv = older then
       TL.BaseType newer
     else
       t
  | TL.Prod (t1, t2) ->
     let t1' = replace_type_name newer older t1 in
     let t2' = replace_type_name newer older t2 in
     TL.Prod (t1', t2')
  | TL.Inst (tv, tl) ->
     let tv' = if tv = older then newer else tv in
     let tl' = List.map (replace_type_name newer older) tl in
     TL.Inst (tv', tl')
  | TL.Arrow (t1, t2) ->
     let t1' = replace_type_name newer older t1 in
     let t2' = replace_type_name newer older t2 in
     TL.Arrow (t1', t2')

let new_instance (rule : TL.intro_rule) =
  let aux a (b, c) =
    let fresh = fresh_type_name () in
    let b' = { b with
               typ = replace_type_name fresh a b.typ ;
               args = List.map (replace_type_name fresh a) b.args } in
    (b', fresh::c)
  in
  List.fold_right aux (rule, []) rule.gen_param
  
(* checks that a pattern has the given type, and returns the pair :
   - generalized type variables that one should not let escape
   - new environment with updated types (including generalized ones), 
     instanciated variables and type equations *)

let generate_equations t1 t2 =
  match t1, t2 with
  | Inst (typ1, tl1), Inst (typ2, tl2) ->
     if typ1 <> typ2 then
       failwith "Unexpected error (code : TypeChecking.3), please report."
     else
       begin
         try List.combine tl1 tl2 with
         | _ -> failwith "Unexpected error (code : TypeChecking.4), please report."
       end
  | _ -> failwith "Unexpected error (code : TypeChecking.2), please report."
  
let rec check_pattern e p =
  match p.value with
  | ThrowawayPt -> ([], e)
  | VarPt vt ->
     let e' = { e with
                vars = Smap.add vt p.typ e.vars } in
     ([], e')
  | TuplePt (p1, p2) ->
     Error.deep_matching p.place
  | ConsPt (tc, pl) ->
     begin
       try
         let rule = Smap.find tc e.cons in
         let (rule, phantoms) = new_instance rule in
         if List.length rule.args <> List.length pl then
           Error.cons_arity tc (List.length rule.args) p.place
         else if not (subtype e rule.typ p.typ) then
           Error.unmatching_types rule.typ p.typ p.place
         else
           let l = List.combine pl rule.args in
           let type_var_info = { arity = 0 ; gadt = false } in
           let aux1 = fun b a -> Tmap.add a type_var_info b in
           let aux2 b a =
             match a with
             | (ThrowawayPt, typ) -> b
             | (VarPt vt, typ) -> Smap.add vt typ b 
             | _ -> Error.deep_matching p.place
           in
           let e' = { e with
                      typs = List.fold_left aux1 e.typs phantoms ;
                      vars = List.fold_left aux2 e.vars l ;
                      equa = (generate_equations rule.typ p.typ) @ e.equa } in
           (phantoms, e')
       with
       | _ -> Error.cons_unbound tc p.place
     end
