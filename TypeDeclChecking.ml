(** Checking of type declarations **)
(* Translates from RawLambda to TypeDeclLambda *)

module RL = RawLambda
module TL = TypeLambda
module TDL = TypeDeclLambda
module Smap = Map.Make(String)
           
type type_name = TL.TypeVar.t
type type_dict = TL.type_info Smap.t
type intro_dict = TL.intro_rule Smap.t
               
(* Closure that generates fresh type variables *)

let fresh_type_name =
  let x = ref 0 in
  fun () -> x := !x - 1 ; TL.TypeVar.Fresh (!x)
         
(* Base GADTs with arity *)

let base_t_dict : type_dict =
  let aux b a =
    match a with
    | TL.Inst (n, l) -> Smap.add n {TL.arity = List.length l} b
    | _ -> b
  in
  List.fold_left aux Smap.empty TL.base_types

(* Base introduction rules *)
  
let base_i_dict : intro_dict =
  List.fold_left (fun a (n, m, _) -> Smap.add n m a)
    Smap.empty
    TL.base_cons

(* Base variables *)
  
let base_vars : (TDL.binding * Atom.atom * TL.gen_type) Smap.t =
  let aux b (n, m) =
    Smap.add n (TDL.Rigid, fst m, snd m) b
  in
  List.fold_left aux Smap.empty TL.base_vars
            
(* First, we need to check that GADTs are well constructed *)

(* since they can be mutually recursive, we start by constructing a dictionnary
of their names with arity. We also check that there is no redefinition *)
            
let rec get_type_names (td : RL.type_decl_ list) (dict : type_dict) =
  match td with
  | [] -> dict
  | (v, l, _)::tl ->
     if Smap.mem v.TDL.value dict then
       Error.redefinition v.TDL.value v.TDL.place
     else
       let info = { TL.arity = List.length l } in
       let dict' = Smap.add v.TDL.value info dict in
       get_type_names tl dict'

(* Now we can check that definition are actually correct *)

(* Checks that parameter that are generalized on in a type introduction rule 
   are legitimate and returns a new typing context *)
    
let check_gen_param (place : Error.place)
      (g_param : type_name list)
      (v_dict : type_name Smap.t) =
  let rec aux g_param l v_dict =
    match g_param with
    | [] -> (v_dict, l)
    | (TL.TypeVar.Named hd)::tl ->
       if Smap.mem hd v_dict then
         Error.type_gen hd place
       else
         let id = fresh_type_name () in
         let v_dict' = Smap.add hd id v_dict in
         aux tl (id::l) v_dict'
  | _::tl ->
     aux tl l v_dict
  in
  aux g_param [] v_dict

(* Checks that a type is well formed in the type context given by t_dict 
   and returns it *)
    
let rec check_type (place : Error.place)
          (t_dict : type_dict)
          (v_dict : type_name Smap.t)
          (t : TL.type_t) =
  match t with
  | TL.BaseType (TL.TypeVar.Named v) ->
     if Smap.mem v v_dict then
       let id = Smap.find v v_dict in
       TL.BaseType id
     else if Smap.mem v t_dict then
       let info = Smap.find v t_dict in
       if info.TL.arity > 0 then
         Error.type_arity v info.TL.arity place
       else
         TL.Inst (v, [])
     else
       Error.type_unbound v place
  | TL.BaseType v ->
     TL.BaseType v
  | TL.Prod (t1, t2) ->
     let t1' = check_type place t_dict v_dict t1 in
     let t2' = check_type place t_dict v_dict t2 in
     TL.Prod (t1', t2')
  | TL.Inst (tv, tl) ->
     begin
       try
         let info = Smap.find tv t_dict in
         if info.TL.arity <> List.length tl then
           Error.type_arity tv info.TL.arity place
         else
           let tl' = List.map (check_type place t_dict v_dict) tl in
           TL.Inst (tv, tl')
       with
       | _ -> Error.type_unbound tv place
     end
  | TL.Arrow (t1, t2) ->
     let t1' = check_type place t_dict v_dict t1 in
     let t2' = check_type place t_dict v_dict t2 in
     TL.Arrow (t1', t2')

(* The same for a polymorphic type scheme *)
     
let check_type_scheme : Error.place -> type_dict -> TL.gen_type ->
                        TL.gen_type =
  fun place t_dict (params, t) ->
  let aux1 a b =
    match a with
    | TL.TypeVar.Named n -> n::b
    | _ -> b
  in
  let aux2 a (d, p) =
    if Smap.mem a d then
      Error.redefinition a place
    else
      let id = fresh_type_name () in
      let d' = Smap.add a id d in
      (d', id::p)
  in
  let param_names = List.fold_right aux1 params [] in
  let (v_dict, params') = List.fold_right aux2 param_names (Smap.empty, []) in
  let t' = check_type place t_dict v_dict t in
  (params', t')

(* Check that the type of an introduction rule is well formed and appropriate
   and returns it *)

let rec check_intro_type (parent : string * int)
          (place : Error.place)
          (t_dict : type_dict)
          (v_dict : type_name Smap.t)
          (t : TL.type_t) =
  let (typename, arity) = parent in
  match t with
  | TL.Arrow (t1, t2) ->
     let t1' = check_type place t_dict v_dict t1 in
     let t2' = check_intro_type parent place t_dict v_dict t2 in
     TL.Arrow (t1', t2')
  | TL.BaseType (TL.TypeVar.Named tv) ->
     if tv <> typename then
       Error.gadt_cons_type typename place
     else if arity <> 0 then
       Error.type_arity typename arity place
     else
       TL.Inst (tv, [])
  | TL.Inst (tv, tl) ->
     begin
       if tv <> typename then
         Error.gadt_cons_type typename place
       else if List.length tl <> arity then
         Error.type_arity typename arity place
       else
         let args = List.map (check_type place t_dict v_dict) tl in
         TL.Inst (tv, args)
     end
  | _ -> Error.gadt_cons_type typename place

(* Some decurrification of an arrow type.
   Converts a_1 -> ... -> a_n -> b to [a_1 ; ... ; a_n], b *)
       
let rec decompose_type : TL.type_t -> TL.type_t list * TL.type_t =
  function
  | TL.Arrow (t1, t2) ->
     let (args, result) = decompose_type t2 in
     (t1::args, result)
  | t -> ([], t)

(* Checks a type introduction rule and returns a list of generalized type parameters,
   along with the type of the constructor *)

let check_gadt_intro ((typename, arity) : string * int)
      (t_dict : type_dict)
      (v_dict : type_name Smap.t)
      (i_dict : intro_dict)
      (i : RL.type_intro) =
  let (cons, t) = i.TDL.value in
  if Smap.mem cons i_dict then
    Error.redefinition cons i.TDL.place
  else
    let (g_param, t2) = t in
    let (v_dict', g_param') = check_gen_param i.TDL.place g_param v_dict in
    let t3 = check_intro_type (typename, arity) i.TDL.place t_dict v_dict' t2 in
    let (args, result) = decompose_type t3 in
    let result' = match result with TL.Inst (a, b) -> (a, b) | _ -> failwith "Why" in
    let info = { TL.gen_param = g_param' ;
                 TL.args = args ;
                 TL.result = result' ;
                 TL.total_type = t3 } in
    Smap.add cons info i_dict
  
(* Checks a whole type introduction and adds it to the GADT map ; also adds type
   introduction rules to the appropriate map. Finally returns *)
    
let check_type_decl (t_dict : type_dict)
      (i_dict : intro_dict)
      ((t, tv, ti) : RL.type_decl_) =
  let aux a (b : RL.type_var) =
    if b.TDL.value = t.TDL.value then
      Error.gadt_weird_param b.TDL.value b.TDL.place
    else
      let id = fresh_type_name () in
      Smap.add b.TDL.value id a
  in
  let vars_dict = List.fold_left aux Smap.empty tv in
  let info = (t.TDL.value, List.length tv) in
  List.fold_left
    (check_gadt_intro info t_dict vars_dict)
    i_dict
    ti

(* bring it all together to check the full type declarations *)
  
let check_types (t : RL.type_decl_ list) =
  let t_dict = get_type_names t base_t_dict in
  let i_dict = List.fold_left (check_type_decl t_dict) base_i_dict t in
  (t_dict, i_dict)

(* There is also some basic translation of terms.
   Functions of several arguments are converted to functions with one
   argument, and type hints are verified/translated. *)

let rec translate_clause t_dict (pat, term) =
  let term' = translate t_dict term in
  (pat, term')

and translate : type_dict -> RL.term -> TDL.term =
  fun t_dict term ->
  let value =
    match term.TDL.value with
    | RL.Var tv -> TDL.Var tv
    (* currifying *)
    | RL.Lam (l, t) ->
       let aux a b =
         { TDL.value = TDL.Lam (a, b) ;
           TDL.place = term.TDL.place }
       in
       let t' = translate t_dict t in
       let term' = List.fold_right aux l t' in
       term'.TDL.value
    | RL.App (t1, t2) ->
       let t1' = translate t_dict t1 in
       let t2' = translate t_dict t2 in
       TDL.App (t1', t2')
    | RL.Cons (c, l) ->
       let l' = List.map (translate t_dict) l in
       TDL.Cons (c, l')
    | RL.Match (t, clauses) ->
       let clauses' = List.map (translate_clause t_dict) clauses in
       let t' = translate t_dict t in
       TDL.Match (t', clauses')
    | RL.Lit i -> TDL.Lit i
    | RL.String s -> TDL.String s
    | RL.BinOp (t1, o, t2) ->
       let t1' = translate t_dict t1 in
       let t2' = translate t_dict t2 in
       TDL.BinOp (t1', o, t2')
    | RL.CmpOp (t1, o, t2) ->
       let t1' = translate t_dict t1 in
       let t2' = translate t_dict t2 in
       TDL.CmpOp (t1', o, t2')
    | RL.Tuple (t1, t2) ->
       let t1' = translate t_dict t1 in
       let t2' = translate t_dict t2 in
       TDL.Tuple (t1', t2')
    (* translating type hints *)
    | RL.Let (r, tv, h, t1, t2) ->
       let t1' = translate t_dict t1 in
       let t2' = translate t_dict t2 in
       let h' = match h with
         | RL.Hint (tau, place) ->
            let tau' = check_type_scheme place t_dict tau in
            TDL.Hint (tau', place)
         | RL.NoHint -> TDL.NoHint
       in
       let r' = if r = RL.Recursive then TDL.Recursive else TDL.NonRecursive in
       TDL.Let (r', tv, h', t1', t2')
  in
  { TDL.place = term.TDL.place ;
    TDL.value = value }

(* Main function to bring it all together *)
  
let check_program : RL.type_decl_ list * RL.term -> TDL.env * TDL.term =
  fun (tdecl, term) ->
  let (t_dict, i_dict) = check_types tdecl in
  let env = { TDL.vars = base_vars ;
              TDL.maps = TL.TypeMap.empty ;
              TDL.typs = t_dict ;
              TDL.cons = i_dict ;
              TDL.subs = TL.TypeMap.empty } in
  let term' = translate t_dict term in
  (env, term')


