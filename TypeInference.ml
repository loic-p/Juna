(** Infer unannotated types **)
(* Translates from TypeDeclLambda to TypeLambda *)
(* TODO : Deep pattern matching ??? *)
(* WARNING : Consider applying substitutions every time a TL.term is constructed *)
(* WARNING : At some point you should substitute in environments ???? *)

module TL = TypeLambda
module TDL = TypeDeclLambda
module Smap = Map.Make(String)
module Tmap = TypeLambda.TypeMap

type typevar = TL.TypeVar.t
type type_subst = TL.type_t Tmap.t
type binding = TDL.binding = Rigid | Wobbly
type identifier = Atom.atom

(* These are used in the type inference phase. More or less everything one
   should know during the inference :
   - vars are known variables with type, wobbliness, and a unique name
   - maps and subst are used to refine the types with known info
   - typs are the type families defined by the programmer
   - cons are the type introduction rules defined by the programmer *)
                
type env = TDL.env =
  { vars : (binding * identifier * TL.gen_type) Smap.t ;
    maps : type_subst ;
    typs : TL.type_info Smap.t ;
    cons : TL.intro_rule Smap.t ;
    subs : type_subst }

(* These are used when typing pattern matching. Some variation on env. 
   The only interesting feature is tr_phan, which are the types that
   one should not let escape *)

type triple =
  { tr_phan : typevar list * typevar list ;
    tr_vars : (binding * identifier * TL.type_t) Smap.t ;
    tr_maps : type_subst ;
    tr_subs : type_subst }

type compatibility =
  | Compatible of env
  | Incompatible of TL.type_t * TL.type_t

exception Too_many_args

let debug = ref false





          
(* ========================================================================== *)
(*                               Printing                                     *)
(* ========================================================================== *)


let print_debug : string -> unit =
  fun s ->
  if !debug then
    print_string s
  else
    ()
          
let print_env : env -> unit =
  fun e ->
  Smap.iter (fun k _ -> print_debug (k ^ " ")) e.vars ;
  print_debug "\ntype families : " ;
  Smap.iter (fun k _ -> print_debug (k ^ " ")) e.typs ;
  print_debug "\ntype constructors : " ;
  Smap.iter (fun k _ -> print_debug (k ^ " ")) e.cons ;
  print_debug "\n\nsubstitution :\n" ;
  Tmap.iter (fun k b -> print_debug ((TL.string_of_typevar k) ^ " : " ^
                                       (TL.string_of_type b) ^ "\n")) e.subs ;
  print_debug "\nvariables :\n" ;
  Smap.iter (fun k (_, id, t) ->
      print_debug (k ^ " : " ^ (TL.string_of_atom id) ^ " : " ^
                     (TL.string_of_typescheme t) ^ "\n")) e.vars






(* ========================================================================== *)
(*                               Misc                                         *)
(* ========================================================================== *)


(* union of two string maps, giving priority to the second argument *)
let s_union : 'a Smap.t -> 'a Smap.t -> 'a Smap.t =
  fun a b ->
  Smap.union (fun _ _ x -> Some x) a b

(* union of two typevar maps, giving priority to the second argument *)
let t_union : 'a Tmap.t -> 'a Tmap.t -> 'a Tmap.t =
  fun a b ->
  Tmap.union (fun _ _ x -> Some x) a b

(* returns the difference of two maps as a list *)
let map_diff : 'a Tmap.t -> 'a Tmap.t -> typevar list =
  fun m1 m2 ->
  let aux key _ l =
    if Tmap.mem key m2 then l else key::l
  in
  Tmap.fold aux m1 []

(* restricts the bindings of f so that they are contained in those of g *)
let restrict : 'a Tmap.t -> 'b Tmap.t -> 'a Tmap.t =
  fun f g ->
  let aux tv t b =
    if Tmap.mem tv g then
      Tmap.add tv t b
    else
      b
  in
  Tmap.fold aux f Tmap.empty

(* membership predicate for a list *)
let rec elem : 'a -> 'a list -> bool =
  fun a l ->
  match l with
  | [] -> false
  | hd::tl -> if a = hd then true else elem a tl
  
(* naive inclusion predicate for lists *)
let rec contained : 'a list -> 'a list -> bool =
  fun a b ->
  match a with
  | [] -> true
  | hd::tl -> if elem hd b then contained tl b else false

(* returns a duplicate in l *)
let duplicate : 'a list -> 'a option =
  fun l ->
  let rec aux1 a = function
    | [] -> None
    | hd::tl -> if hd = a then Some a else aux1 a tl
  in
  let rec aux2 = function
    | [] -> None
    | hd::tl ->
       begin
         match aux1 hd tl with
         | Some a -> Some a
         | None -> aux2 tl
       end
  in
  aux2 l

(* intersection between a type list and a substitution domain *)
let rec inter : TL.type_t list -> type_subst -> 'a option =
  fun l s ->
  match l with
  | [] -> None
  | hd::tl ->
     begin
      match hd with
      | TL.BaseType tv ->
         if Tmap.mem tv s then Some tv else inter tl s
      | _ -> inter tl s
     end  

(* Like List.combine, but with three lists *)
let rec triple_combine : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list =
  fun l1 l2 l3 ->
  match l1, l2, l3 with
  | [], [], [] -> []
  | h1::t1, h2::t2, h3::t3 -> (h1, h2, h3)::(triple_combine t1 t2 t3)
  | _ -> failwith "Incompatible length"





    
(* ========================================================================== *)
(*                           Free type variables                              *)
(* ========================================================================== *)
    
(* check if v is a free type variable of t *)
let rec is_ftv : TL.type_t -> typevar -> bool =
  fun t v ->
  match t with
  | TL.BaseType tv -> tv = v
  | TL.Prod (t1, t2) -> (is_ftv t1 v) || (is_ftv t2 v)
  | TL.Inst (_, tl) ->
     List.fold_left (fun b a -> is_ftv a v || b) false tl
  | TL.Arrow (t1, t2) -> (is_ftv t1 v) || (is_ftv t2 v)

(* gets the free type variables of t that do not appear in bound
   and return them as a map *)
let get_ftv_map : TL.type_t -> unit Tmap.t =
  fun t ->
  let rec aux f = function
    | TL.BaseType tv -> Tmap.add tv () f
    | TL.Prod (t1, t2) -> aux (aux f t2) t1
    | TL.Arrow (t1, t2) -> aux (aux f t2) t1
    | TL.Inst (_, tl) -> List.fold_left aux f tl
  in
  aux (Tmap.empty) t

(* gets the free type variables of t that do not appear in bound
   and return them as a list *)
let get_ftv_list : TL.type_t -> typevar list =
  fun t ->
  List.map fst (Tmap.bindings (get_ftv_map t))

let rec get_ftvl : TL.type_t list -> unit Tmap.t =
  function
  | [] -> Tmap.empty
  | hd::tl ->
     let s = get_ftvl tl in
     let s' = get_ftv_map hd in
     t_union s s'

let get_ftv_scheme : TL.gen_type -> unit Tmap.t =
  fun (gen_param, t) ->
  let ftv = get_ftv_map t in
  List.fold_right Tmap.remove gen_param ftv

(* gets the free type variables of an environment *)
let get_ftve : env -> unit Tmap.t =
  fun e ->
  let aux1 _ t m =
    t_union (get_ftv_map t) m
  in
  let aux2 _ (_, _, s) m =
    t_union (get_ftv_scheme s) m
  in
  let m = Tmap.fold aux1 e.maps Tmap.empty in
  Smap.fold aux2 e.vars m

(* auxiliary function for infer_term 
   returns a sublist of vars containing only those appearing in tl with 
   a rigid binding *)
let rec get_ftv_1 : (TL.type_t * binding) list ->
                    typevar list ->
                    typevar list =
  fun tl vars ->
  match vars with
  | [] -> []
  | hd::tail ->
     let l = List.map (fun (t, b) -> b = Rigid && is_ftv t hd) tl in
     if List.fold_right (||) l false then
       hd::(get_ftv_1 tl tail)
     else
       get_ftv_1 tl tail

let split_ftv : typevar list -> TL.type_t list -> typevar list * typevar list =
  fun tv t ->
  let s = get_ftvl t in
  let rec aux a b = function
    | [] -> (a, b)
    | hd::tl -> if Tmap.mem hd s then aux (hd::a) b tl else aux a (hd::b) tl
  in
  aux [] [] tv

let not_ftv_in : typevar list -> TL.type_t -> bool =
  fun tv t ->
  let s = get_ftv_map t in
  let rec aux = function
    | [] -> true
    | hd::tl -> if Tmap.mem hd s then false else aux tl
  in
  aux tv







  
(* ========================================================================== *)
(*                           Substitutions                                    *)
(* ========================================================================== *)

(* creates a substitution from a list of pairs *)
let subst_from_list : (typevar * TL.type_t) list -> type_subst =
  fun l ->
  let aux (tv, t) b =
    Tmap.add tv t b
  in
  List.fold_right aux l Tmap.empty          

(* applies a substitution to a type *)
let rec apply_subst : type_subst -> TL.type_t -> TL.type_t =
  fun subst t ->
  match t with
  | TL.BaseType tv ->
     if Tmap.mem tv subst then
       Tmap.find tv subst
     else
       t
  | TL.Prod (t1, t2) ->
     TL.Prod (apply_subst subst t1, apply_subst subst t2)
  | TL.Arrow (t1, t2) ->
     TL.Arrow (apply_subst subst t1, apply_subst subst t2)
  | TL.Inst (tv, tl) ->
     TL.Inst (tv, List.map (apply_subst subst) tl)

let apply_subst_scheme : type_subst -> TL.gen_type -> TL.gen_type =
  fun subst (l, t) ->
  let rec aux s = function
    | [] -> s
    | hd::tl ->
       let s' = Tmap.remove hd s in
       aux s' tl
  in
  let subst' = aux subst l in
  (l, apply_subst subst' t)
    
let apply_subst_env : type_subst -> env -> env =
  fun subst e ->
  { e with
    maps = Tmap.map (apply_subst subst) e.maps ;
    vars = Smap.map (fun (b, i, s) -> (b, i, apply_subst_scheme subst s)) e.vars }

(* Same as precedent, but specialized to substitution with one binding to avoid
   some overhead *)
let rec apply_elem_subst : typevar -> TL.type_t -> TL.type_t -> TL.type_t =
  fun tv r t ->
  match t with
  | TL.BaseType tv' -> if tv' = tv then r else t
  | TL.Prod (t1, t2) ->
     TL.Prod (apply_elem_subst tv r t1, apply_elem_subst tv r t2)
  | TL.Arrow (t1, t2) ->
     TL.Arrow (apply_elem_subst tv r t1, apply_elem_subst tv r t2)
  | TL.Inst (tf, tl) ->
     TL.Inst (tf, List.map (apply_elem_subst tv r) tl)     

(* Returns the substitution corresponding to applying t then s *)
let compose_subst : type_subst -> type_subst -> type_subst =
  fun s t ->
  let t' = Tmap.map (apply_subst s) t in
  t_union t' s
  
(* adds a new binding to a substitution, while ensuring it remains idempotent *)
let subst_add : typevar -> TL.type_t -> type_subst -> type_subst =
  fun tv t s ->
  let s' = Tmap.map (apply_elem_subst tv t) s in
  Tmap.add tv t s'     


  





  

(* ========================================================================== *)
(*                           Fresh identifiers                                *)
(* ========================================================================== *)
    
let fresh_type_name : unit -> typevar =
  let x = ref 0 in
  fun () -> x := !x + 1 ; TL.TypeVar.Fresh (!x)

let fresh_base_type : unit -> TL.type_t =
  fun () -> TL.BaseType (fresh_type_name ())

let fresh_names_and_subst : typevar list -> typevar list * type_subst =
  fun l ->
  let m = List.map (fun _ -> fresh_type_name ()) l in
  let n = List.map (fun x -> TL.BaseType x) m in
  let s = subst_from_list (List.combine l n) in
  (m, s)
            
(* returns a substitution with fresh types for all the typevars in l *)
let rec fresh_subst : typevar list -> type_subst =
  fun l ->
  match l with
  | [] -> Tmap.empty
  | hd::tl ->
     let tn = fresh_type_name () in
     let m = fresh_subst tl in
     Tmap.add hd (TL.BaseType tn) m










(* ========================================================================== *)
(*                           Unification                                      *)
(* ========================================================================== *)

(* computes a fresh most general unifier for the types t1 and t2,
   as described in Jones et al. Returns None if they are not compatible. *)
let fmgu : TL.type_t -> TL.type_t -> (type_subst) option =
  fun t1 t2 ->
  let aux1 tv t l =
    let aux (a, b) =
      (apply_elem_subst tv t a, apply_elem_subst tv t b)
    in
    List.map aux l
  in
  let rec aux2 v u lst =
    match lst with
    | [] -> Some u
    | (TL.BaseType tv1, TL.BaseType tv2)::tl when tv1 = tv2 -> aux2 v u tl
    | (TL.BaseType tv1, TL.BaseType tv2)::tl ->
       let b1 = Tmap.mem tv1 v in
       let b2 = Tmap.mem tv2 v in
       if (b1 && b2) || (not (b1 || b2)) then
         let f = TL.BaseType (fresh_type_name ()) in
         let u' = subst_add tv1 f (subst_add tv2 f u) in
         let tl' = aux1 tv1 f (aux1 tv2 f tl) in
         aux2 v u' tl'
       else if b1 then
         let u' = subst_add tv1 (TL.BaseType tv2) u in
         let tl' = aux1 tv1 (TL.BaseType tv2) tl in
         aux2 v u' tl'
       else
         let u' = subst_add tv2 (TL.BaseType tv1) u in
         let tl' = aux1 tv2 (TL.BaseType tv1) tl in
         aux2 v u' tl'
    | (TL.BaseType tv, t2)::tl ->
       if is_ftv t2 tv then
         None
       else
         let u' = subst_add tv t2 u in
         let tl' = aux1 tv t2 tl in
         aux2 v u' tl'
    | (t1, TL.BaseType tv)::tl -> aux2 v u ((TL.BaseType tv, t1)::tl)
    | (TL.Prod (ta1, ta2), TL.Prod (tb1, tb2))::tl ->
       aux2 v u ((ta1, tb1)::(ta2, tb2)::tl)
    | (TL.Arrow (ta1, ta2), TL.Arrow (tb1, tb2))::tl ->
       aux2 v u ((ta1, tb1)::(ta2, tb2)::tl)
    | (TL.Inst (tv1, tl1), TL.Inst (tv2, tl2))::tl ->
       if (tv1 = tv2) && (List.length tl1 = List.length tl2) then
         let l = List.combine tl1 tl2 in
         aux2 v u (l@tl)
       else
         None
    | _ -> None
  in
  let ftv1 = get_ftv_map t1 in
  let ftv2 = get_ftv_map t2 in
  let ftv = t_union ftv1 ftv2 in
  let u = aux2 ftv2 Tmap.empty [(t1, t2)] in
  match u with
  | Some u' -> Some (restrict u' ftv)
  | None -> None

(* Returns an environment with a substitution unifying the two types,
   or None if impossible. *)
let unify : env -> TL.type_t -> TL.type_t -> env option =
  fun e t1 t2 ->
  print_debug ("Trying to unify " ^ (TL.string_of_type t1) ^
                 " and " ^ (TL.string_of_type t2) ^ "\n") ;
  let t1' = apply_subst e.subs t1 in
  let t2' = apply_subst e.subs t2 in
  match fmgu t1' t2' with
  | Some theta ->
     print_debug "Success\n\n" ;
     Some { e with
         subs = compose_subst theta e.subs }
  | None -> print_debug "Failure\n" ; None

(* Folds a list of equalities with unify *)
let unify_list : env -> (TL.type_t * TL.type_t) list -> compatibility =
  fun e l ->
  let aux (t1, t2) b =
    match b with
    | Incompatible _ -> b
    | Compatible e ->
       begin
         match unify e t1 t2 with
         | Some e' -> Compatible e'
         | None -> Incompatible (t1, t2)
       end
  in
  List.fold_right aux l (Compatible e)








  
(* ========================================================================== *)
(*                           Type manipulations                               *)
(* ========================================================================== *)

(* Tries to see the type scheme as an instance of a type, and returns an
   environment with appropriate substitution, or None if impossible. *)
let type_inst : env -> TL.gen_type -> TL.type_t -> env option =
  fun e (gl, t1) t2 ->
  let subst = fresh_subst gl in
  let t1' = apply_subst subst t1 in
  unify e t1' t2

(* Tries to see the given type as an arrow type, returns None if impossible. *)
let arrow_type : env -> TL.type_t ->
                 (env * TL.type_t * TL.type_t) option =
  fun e t ->
  print_debug ("Unifying " ^ (TL.string_of_type t) ^ " with an arrow\n\n") ;
  match (apply_subst e.subs t) with
  | TL.Arrow (t1, t2) -> Some (e, t1, t2)
  | TL.BaseType tv ->
     let t1 = TL.BaseType (fresh_type_name ()) in
     let t2 = TL.BaseType (fresh_type_name ()) in
     let t' = TL.Arrow (t1, t2) in
     let e' = { e with
                subs = subst_add tv t' e.subs } in
     Some (e', t1, t2)
  | _ -> None

let product_type : env -> TL.type_t ->
                   (env * TL.type_t * TL.type_t) option =
  fun e t ->
  match (apply_subst e.subs t) with
  | TL.Prod (t1, t2) -> Some (e, t1, t2)
  | TL.BaseType tv ->
     let t1 = TL.BaseType (fresh_type_name ()) in
     let t2 = TL.BaseType (fresh_type_name ()) in
     let t' = TL.Prod (t1, t2) in
     let e' = { e with
                subs = subst_add tv t' e.subs } in
     Some (e', t1, t2)
  | _ -> None


(* conversion from a_0 -> a_1 -> ... -> a_n -> b to [a_0 ; ... a_n], b *)
let rec decurrify : int -> TL.type_t -> (TL.type_t list * TL.type_t) option =
  fun n t ->
  if n > 0 then
    match t with
    | TL.Arrow (t1, t2) ->
       begin
         match decurrify (n-1) t2 with
         | None -> None
         | Some (args, res) -> Some (t1::args, res)
       end
    | _ -> None
  else
    Some ([], t)
       






  
(* ========================================================================== *)
(*                                 Errors                                     *)
(* ========================================================================== *)
  
(* Pretty errors *)
let error_incompatible_types : env -> TL.type_t -> TL.type_t -> Error.place -> 'a =
  fun e a b p ->
  let a' = apply_subst e.subs a in
  let b' = apply_subst e.subs b in
  raise (Error.Type_error (p, "The types " ^ (TL.string_of_type a') ^ " and "
                        ^ (TL.string_of_type b') ^ " are incompatible."))
  (* Error.unmatching_type (TL.string_of_type a) (TL.string_of_type b) p *)

let error_instance : TL.gen_type -> TL.type_t -> Error.place -> 'a =
  fun s t p ->
  Error.unmatching_type (TL.string_of_typescheme s) (TL.string_of_type t) p






  

(* ========================================================================== *)
(*                           Type inference                                   *)
(* ========================================================================== *)
       

(* checks that all type variables are known *)
(* all in all, really looks like apply_subst *)
let rec translate_hint_aux : env -> Error.place -> TL.type_t -> TL.type_t =
  fun e place h ->
  match h with
  | TL.BaseType tv ->
     begin
       try
         Tmap.find tv e.maps
       with
       | _ -> Error.type_unbound (TL.string_of_typevar tv) place
     end
  | TL.Inst (tv, tl) ->
     begin
       try
         let ti = Smap.find tv e.typs in
         if List.length tl <> ti.TL.arity then
           Error.type_arity tv ti.TL.arity place
         else
           let tl' = List.map (translate_hint_aux e place) tl in
           TL.Inst (tv, tl')
       with
       | _ -> Error.type_unbound tv place
     end
  | TL.Arrow (t1, t2) ->
     let t1' = translate_hint_aux e place t1 in
     let t2' = translate_hint_aux e place t2 in
     TL.Arrow (t1', t2')
  | TL.Prod (t1, t2) ->
     let t1' = translate_hint_aux e place t1 in
     let t2' = translate_hint_aux e place t2 in
     TL.Prod (t1', t2')

(* basically replaces quantified type variables with fresh ones *)
(* also takes into account the bindings already present in context *)
let translate_hint : env -> Error.place -> TL.gen_type ->
                     env * TL.gen_type =
  fun e place (gen_params, typ) ->
  let (gen_params', phi) = fresh_names_and_subst gen_params in
  let eps = { e with
              maps = t_union e.maps phi } in              
  let typ' = translate_hint_aux eps place typ in
  (eps, (gen_params', typ'))

let rec infer_atomic_pattern : env -> TDL.pattern -> binding -> TL.type_t -> triple ->
                               env * TL.pattern * triple =
  fun e pat bind tau tr ->
  match pat.TDL.value with
  | TDL.ThrowawayPt ->
     let tl = { TL.typ = apply_subst e.subs tau ;
                TL.place = pat.TDL.place ;
                TL.value = TL.ThrowawayPt } in
     (e, tl, tr)
  | TDL.VarPt tv ->
     if Smap.mem tv tr.tr_vars then
       Error.pattern_redef tv pat.TDL.place
     else
       let identifier = Atom.fresh "var" in
       let tr' = { tr with
                   tr_vars = Smap.add tv (bind, identifier, tau) tr.tr_vars } in
       let tl = { TL.typ = apply_subst e.subs tau ;
                  TL.place = pat.TDL.place ;
                  TL.value = TL.VarPt identifier } in
       (e, tl, tr')
  | TDL.AnnotatedPt (pt, t) ->
     begin
       let preb = get_ftv_list t in
       let aux v l =
         if (Tmap.mem v e.maps) || (Tmap.mem v tr.tr_maps) then l else v::l
       in
       let b = List.fold_right aux preb [] in
       let b' = List.map (fun _ -> fresh_type_name ()) b in
       let beta = List.map (fun x -> TL.BaseType x) b' in
       let phi = subst_from_list (List.combine b beta) in
       let nm = t_union e.maps tr.tr_maps in
       let tr_vars' = Smap.map (fun (b, i, t) -> (b, i, ([], t))) tr.tr_vars in
       let eps = { e with
                   vars = s_union e.vars tr_vars' ;
                   maps = t_union nm phi } in
       let tau' = translate_hint_aux eps pat.TDL.place t in
       let nu1 = apply_subst tr.tr_subs tau' in
       let nu2 = if bind = Wobbly then tau else apply_subst tr.tr_subs tau in
       match unify e nu1 nu2 with
       | Some delta ->
          begin
            let c = List.map (apply_subst delta.subs) beta in
            match duplicate c, inter c tr.tr_subs, inter c tr.tr_maps with
            | Some _, _, _ -> Error.pattern_ill_formed pat.TDL.place (* give up *)
            | None, Some _, _ -> Error.pattern_ill_formed pat.TDL.place (** TODO **)
            | None, None, Some _ -> Error.pattern_ill_formed pat.TDL.place
            | None, None, None ->
               let psi = subst_from_list (List.combine b c) in
               let psi' = subst_from_list (List.combine b' c) in
               let tau'' = apply_subst psi' tau' in
               let tr' = { tr with
                           tr_maps = t_union tr.tr_maps psi } in
               infer_atomic_pattern delta pt Rigid tau'' tr'
          end
       | None -> error_incompatible_types e nu1 nu2 pat.TDL.place
     end
  | _ -> Error.deep_matching pat.TDL.place
       
(* applies infer_pattern successively to all the elements of l *)  
let infer_pattern_list : env -> (TDL.pattern * binding * TL.type_t) list -> triple ->
                         env * TL.pattern list * triple =
  fun e l tr ->
  let aux (pat, b, tau) (eps, l, tr) =
    let (eps', tl, tr') = infer_atomic_pattern eps pat b tau tr in
    (eps', tl::l, tr')
  in
  List.fold_right aux l (e, [], tr)    
  
(* Type inference for patterns *)
let infer_pattern : env -> TDL.pattern -> binding -> TL.type_t ->
                    env * TL.pattern * triple =
  fun e pat b tau ->
  let empty_triple = { tr_vars = Smap.empty ;
                       tr_maps = Tmap.empty ;
                       tr_subs = Tmap.empty ;
                       tr_phan = ([], []) } in
  match pat.TDL.value with
  | TDL.ThrowawayPt -> infer_atomic_pattern e pat b tau empty_triple
  | TDL.VarPt _ -> infer_atomic_pattern e pat b tau empty_triple
  | TDL.AnnotatedPt _ -> infer_atomic_pattern e pat b tau empty_triple
  | TDL.TuplePt _ -> Error.deep_matching pat.TDL.place
  | TDL.ConsPt (tc, pl) ->
     begin
       try
         let info = Smap.find tc e.cons in
         if List.length pl <> List.length info.TL.args then
           Error.cons_arity tc (List.length info.TL.args) pat.TDL.place
         else
           if b = Wobbly then
             begin
               let (bc, be) = split_ftv info.TL.gen_param (snd info.TL.result) in
               let (c, phic) = fresh_names_and_subst bc in
               let phie = fresh_subst be in
               let l = List.map (apply_subst phic) (snd info.TL.result) in
               let tau' = TL.Inst (fst info.TL.result, l) in
               match unify e tau tau' with
               | Some eps ->
                  let aux t = if not_ftv_in bc t then Rigid else Wobbly in
                  let m = List.map aux info.TL.args in
                  let tr = { empty_triple with
                             tr_phan = (c, bc) } in
                  let args' = List.map (apply_subst phie) info.TL.args in
                  let args'' = List.map (apply_subst phic) args' in
                  let k = triple_combine pl m args'' in
                  let (eps', tll, tr') = infer_pattern_list eps k tr in
                  let tl = { TL.typ = apply_subst eps'.subs tau;
                             TL.place = pat.TDL.place ;
                             TL.value = TL.ConsPt (tc, tll) } in
                  (eps', tl, tr')
               | None -> error_incompatible_types e tau tau' pat.TDL.place
             end
           else
             let family = fst info.TL.result in
             match tau with
             | TL.Inst (family', args) when family' = family ->
                begin
                  let (c, psi) = fresh_names_and_subst info.TL.gen_param in
                  let tres = List.map (apply_subst psi) (snd info.TL.result) in
                  match unify_list e (List.combine args tres) with
                  | Compatible e' ->
                     let tr = { empty_triple with
                                tr_phan = (c, []) ;
                                tr_subs = e'.subs } in
                     let m = List.init (List.length pl) (fun _ -> Rigid) in
                     let taui = List.map (apply_subst psi) info.TL.args in
                     let k = triple_combine pl m taui in
                     let (eps, tll, tr') = infer_pattern_list e k tr in
                     let tl = { TL.typ = apply_subst eps.subs tau ;
                                TL.place = pat.TDL.place ;
                                TL.value = TL.ConsPt (tc, tll) } in
                     (eps, tl, tr')
                  | Incompatible (t1, t2) ->
                     error_incompatible_types e t1 t2 pat.TDL.place
                end
             | _ ->
                let t = TL.Inst (fst info.TL.result, snd info.TL.result) in
                error_incompatible_types e tau t pat.TDL.place
       with
       | Error.Type_error (p, e) -> Error.error p e
       | _ -> Error.cons_unbound tc pat.TDL.place
     end

(* type inference for a match clause *)
let rec infer_clause : env -> TDL.pattern * TDL.term -> binding * binding ->
                       TL.type_t * TL.type_t ->
                       env * (TL.pattern * TL.term) =
  fun e (pat, t) (bpat, bt) (tpat, tt) ->
  let (eps, tlpat, tr) = infer_pattern e pat bpat tpat in
  let tr_vars' = Smap.map (fun (b, i, t) -> (b, i, ([], t))) tr.tr_vars in
  let u = { eps with
            vars = s_union e.vars tr_vars' ;
            maps = t_union e.maps tr.tr_maps } in
  let u' = apply_subst_env tr.tr_subs u in
  let mtt = if bt = Wobbly then tt else apply_subst tr.tr_subs tt in
  let (eps', tlt) = infer_term u' t bt mtt in
  (** TODO **)
  (* check that no phantom escapes *)
  (*
  let phantoms = (fst tr.tr_phan) @ (snd tr.tr_phan) in
  let tpat' = apply_subst eps'.subs tpat in
  let tt' = apply_subst eps'.subs tt in
   *)
  (eps', (tlpat, tlt))
  
(* infers the type of the binding for a term (Rigid or Wobbly), and also returns
   its type and an updated environment *)
and infer_binding : env -> TDL.term ->
                    env * TL.term * TL.type_t * binding =
  fun e t ->
  let typ = TL.BaseType (fresh_type_name ()) in
  let (e', tl) = infer_term e t Wobbly typ in
  let typ' = apply_subst e'.subs typ in
  let default = (e', tl, typ', Wobbly) in
  match t.TDL.value with
  (* an application should be considered rigid if all the free type variables in
     the result can be inferred rigid from the arguments *)
  (* This one is a bit too complex for my likings, TODO split it into simpler parts *)
  | TDL.App _ -> 
     begin
       let rec aux1 l t = match t.TDL.value with
         | TDL.Var tv -> Some (tv, l)
         | TDL.App (t1, t2) -> aux1 (t2::l) t1
         | _ -> None
       in
       let aux2 a (eps, terml, typl, bl) =
         let (eps', term, typ, bind') = infer_binding eps a in
         (eps', term::terml, typ::typl, bind'::bl)
       in
       let aux3 place a b =
         { TL.typ = (match b.TL.typ with 
                     | TL.Arrow (_, t2) -> t2 (* is that legitimate ? *)
                     | _ -> failwith "What") ;
           TL.place = place ; (* not really true but idc *)
           TL.value = TL.App (b, a) }
       in
       (* decurrify an application : from (...(f a_1) ... a_n-1) a_n to f (a_1, ..., a_n) *) 
       match aux1 [] t with
       | Some (tv, l) -> 
          begin
            try
              let (b, i, (gen_params, typ)) = Smap.find tv e.vars in
              if b = Wobbly then
                default
              else
                (* infer modifiers and types for all the arguments *)
                let (e', terms, typs, bl) = List.fold_right aux2 l (e, [], [], []) in
                let (args_t, res_t) =
                  match decurrify (List.length terms) typ with
                  | Some x -> x
                  | None -> raise Too_many_args
                in
                let subst = fresh_subst gen_params in
                let typ' = apply_subst subst typ in
                let (args_t', res_t') =
                  match decurrify (List.length terms) typ' with
                  | Some x -> x
                  | None -> raise Too_many_args
                in
                match unify_list e' (List.combine typs args_t') with
                | Compatible eps ->
                   let res = apply_subst eps.subs res_t' in
                   let tl = { TL.typ = apply_subst eps.subs typ' ;
                              TL.place = t.TDL.place ; (* not really but idc *)
                              TL.value = TL.Var i } in
                   let tl' = List.fold_right (aux3 t.TDL.place) terms tl in
                   (* ftv that are bound rigidly because of arguments *)
                   let ftv_args = get_ftv_1 (List.combine args_t bl) gen_params in
                   let ftv_res = get_ftv_list res_t in
                   let bind = if contained ftv_res ftv_args then Rigid else Wobbly in
                   (eps, tl', res, bind)
                | Incompatible (t1, t2) ->
                   error_incompatible_types e' t1 t2 t.TDL.place
            with
            | Too_many_args -> Error.too_much_args tv t.TDL.place
            | _ -> Error.var_unbound tv t.TDL.place
          end

       | None ->
          default
     end
  | TDL.Cons (tc, l) ->
     begin
       let aux2 a (eps, terml, typl, bl) =
         let (eps', term, typ, bind') = infer_binding eps a in
         (eps', term::terml, typ::typl, bind'::bl)
       in
       try
         let info = Smap.find tc e.cons in
         (* infer modifiers and types for all the arguments *)
         let (e', terms, typs, bl) = List.fold_right aux2 l (e, [], [], []) in
         let subst = fresh_subst info.TL.gen_param in
         let args_t' = List.map (apply_subst subst) info.TL.args in
         let res_t = TL.Inst (fst info.TL.result, snd info.TL.result) in
         let res_t' = apply_subst subst res_t in
         match unify_list e' (List.combine typs args_t') with
         | Compatible eps ->
            let res = apply_subst eps.subs res_t' in
            let tl' = { TL.typ = res ;
                        TL.place = t.TDL.place ; 
                        TL.value = TL.Cons (tc, terms) } in
            (* ftv that are bound rigidly because of arguments *)
            let ftv_args = get_ftv_1 (List.combine info.TL.args bl) info.TL.gen_param in
            let ftv_res = get_ftv_list res_t in
            let bind = if contained ftv_res ftv_args then Rigid else Wobbly in
            (eps, tl', res, bind)
         | Incompatible (t1, t2) ->
            error_incompatible_types e' t1 t2 t.TDL.place
       with
       | Error.Type_error (pl, e) -> Error.error pl e
       | _ -> Error.cons_unbound tc t.TDL.place
     end
  | TDL.Var tv ->
     begin
       try
         let (b, i, (gen_params, typ)) = Smap.find tv e.vars in
         if b = Wobbly then
           default
         else if gen_params = [] then
           let term = { TL.typ = typ ;
                        TL.place = t.TDL.place ;
                        TL.value = TL.Var i } in
           (e, term, typ, Rigid)
         else
           let subst = fresh_subst gen_params in
           let typ' = apply_subst subst typ in
           let term = { TL.typ = typ' ;
                        TL.place = t.TDL.place ;
                        TL.value = TL.Var i } in
           (e, term, typ', Wobbly)
       with
         _ -> Error.var_unbound tv t.TDL.place
     end
  | TDL.Lit i ->
     let term = { TL.typ = TL.basetype_int ;
                  TL.place = t.TDL.place ;
                  TL.value = TL.Lit i } in
     (e, term, TL.basetype_int, Rigid)
  | TDL.String s ->
     let term = { TL.typ = TL.basetype_string ;
                  TL.place = t.TDL.place ;
                  TL.value = TL.String s } in
     (e, term, TL.basetype_string, Rigid)
  | TDL.BinOp (t1, o, t2) ->
     let (eps, t1') = infer_term e t1 Rigid TL.basetype_int in
     let (eps', t2') = infer_term eps t2 Rigid TL.basetype_int in
     let term = { TL.typ = TL.basetype_int ;
                  TL.place = t.TDL.place ;
                  TL.value = TL.BinOp (t1', o, t2') } in
     (eps', term, TL.basetype_int, Rigid)
  | TDL.CmpOp (t1, o, t2) ->
     let (eps, t1') = infer_term e t1 Rigid TL.basetype_int in
     let (eps', t2') = infer_term eps t2 Rigid TL.basetype_int in
     let term = { TL.typ = TL.basetype_bool ;
                  TL.place = t.TDL.place ;
                  TL.value = TL.CmpOp (t1', o, t2') } in
     (eps', term, TL.basetype_bool, Rigid)
  | TDL.Tuple (t1, t2) ->
     let (eps, t1', typ1, b1) = infer_binding e t1 in
     let (eps', t2', typ2, b2) = infer_binding eps t2 in
     let b = if (b1 = Rigid) && (b2 = Rigid) then Rigid else Wobbly in
     let typ = apply_subst eps'.subs (TL.Prod (typ1, typ2)) in
     let term = { TL.typ = typ ;
                  TL.place = t.TDL.place ;
                  TL.value = TL.Tuple (t1', t2') } in
     (eps', term, typ, b)
  | _ -> default

and infer_gen_binding : env -> TDL.term ->
                        env * TL.term * TL.gen_type * binding =
  fun e t ->
  let (e', term, typ, b) = infer_binding e t in
  let ftv = get_ftv_map typ in
  let eps = apply_subst_env e'.subs e' in
  let non_ftv = get_ftve eps in
  let gen = map_diff ftv non_ftv in
  let (gen', subst) = fresh_names_and_subst gen in
  let typ' = apply_subst subst typ in
  let term' = { term with
                TL.typ = typ' } in
  (eps, term', (gen', typ'), b)

(* Main type inference function
   returns an updated environment and a typed term *)
and infer_term : env ->
                 TDL.term -> binding -> TL.type_t ->
                 env * TL.term =
  fun e t m tau ->
  print_debug "Starting_inference of term :\n" ;
  print_debug (TDL.show_term t) ;
  print_debug ("\n\nWith type " ^ (TL.string_of_type tau)) ;
  print_debug "\n\nIn environment :\n" ;
  print_env e ;
  print_debug "\n\n" ;
  match t.TDL.value with
  | TDL.Var tv ->
     begin
       try
         let (_, i, typ_s) = Smap.find tv e.vars in
         match type_inst e typ_s tau with
         | Some e' ->
            let tl = { TL.typ = apply_subst e'.subs tau ;
                       TL.place = t.TDL.place ;
                       TL.value = TL.Var i } in
            (e', tl)
         | None ->
            let typ_s' = apply_subst_scheme e.subs typ_s in
            let tau' = apply_subst e.subs tau in
            error_instance typ_s' tau' t.TDL.place
       with
       | Error.Type_error (pl, e) -> Error.error pl e
       | _ -> Error.var_unbound tv t.TDL.place
     end
  | TDL.Lam (tv, t') ->
     begin
       match arrow_type e tau with
       | Some (e', tau1, tau2) ->
          let pat = { TDL.value = TDL.VarPt tv ;
                      TDL.place = t.TDL.place } in
          let (eps, (_, tlt')) =
            infer_clause e' (pat, t') (m, m) (tau1, tau2) in
          let (_, identifier, _) = Smap.find tv eps.vars in
          let tl = { TL.typ = apply_subst eps.subs tau ;
                     TL.place = t.TDL.place ;
                     TL.value = TL.Lam (identifier, tlt') } in
          (eps, tl)
       | None ->
          Error.unexpected_function (TL.string_of_type tau) t.TDL.place
     end
  | TDL.App (t1, t2) ->
     let arg_typename = fresh_type_name () in
     let arg_type = TL.BaseType arg_typename in
     let fun_type = TL.Arrow (arg_type, tau) in
     let (e', tl1) = infer_term e t1 Wobbly fun_type in
     let (e'', tl2) = infer_term e' t2 Wobbly arg_type in
     let tl = { TL.typ = apply_subst e''.subs tau ;
                TL.place = t.TDL.place ;
                TL.value = TL.App (tl1, tl2) } in
     (e'', tl)
  | TDL.Cons (tc, l) ->
     begin
       try
         let info = Smap.find tc e.cons in
         if List.length l <> List.length info.TL.args then
           Error.cons_arity tc (List.length info.TL.args) t.TDL.place
         else
           let phi = fresh_subst info.TL.gen_param in
           let res_t = TL.Inst (fst info.TL.result, snd info.TL.result) in
           let res' = apply_subst phi res_t in
           let args' = List.map (apply_subst phi) info.TL.args in
           match unify e tau res' with
           | Some e' ->
              let aux (term, typ) (eps, tll) =
                let (eps', tl) = infer_term eps term Wobbly typ in
                (eps', tl::tll)
              in
              let (eps, tll) = List.fold_right aux (List.combine l args') (e', []) in
              let tl = { TL.typ = apply_subst eps.subs tau ;
                         TL.place = t.TDL.place ;
                         TL.value = TL.Cons (tc, tll) } in
              (eps, tl)
           | None ->
              error_incompatible_types e tau res' t.TDL.place
       with
       | Error.Type_error (pl, e) -> Error.error pl e
       |  _ -> Error.cons_unbound tc t.TDL.place
     end
  | TDL.Match (t', cl) ->
     let (e', tl, tpat, bind) = infer_binding e t' in
     let aux a (eps, l) =
       let (eps', c) = infer_clause eps a (bind, m) (tpat, tau) in
       (eps', c::l)
     in
     let (eps, l) = List.fold_right aux cl (e', []) in
     let tlm = { TL.typ = apply_subst eps.subs tau ;
                 TL.place = t.TDL.place ;
                 TL.value = TL.Match (tl, l) } in
     (eps, tlm)
  | TDL.Lit i ->
     begin
       match unify e tau TL.basetype_int with
       | Some e' ->
          let tl = { TL.typ = TL.basetype_int ;
                     TL.place = t.TDL.place ;
                     TL.value = TL.Lit i } in
          (e', tl)
       | None -> error_incompatible_types e tau TL.basetype_int t.TDL.place
     end
  | TDL.String s ->
     begin
       match unify e tau TL.basetype_string with
       | Some e' ->
          let tl = { TL.typ = TL.basetype_string ;
                     TL.place = t.TDL.place ;
                     TL.value = TL.String s } in
          (e', tl)
       | None -> error_incompatible_types e tau TL.basetype_string t.TDL.place
     end
  | TDL.BinOp (t1, o, t2) ->
     begin
       match unify e tau TL.basetype_int with
       | Some e' ->
          (* should i use a wobbly binding ??? *)
          let (eps, tl1) = infer_term e' t1 Rigid TL.basetype_int in
          let (eps', tl2) = infer_term eps t2 Rigid TL.basetype_int in
          let tl = { TL.typ = TL.basetype_int ;
                     TL.place = t.TDL.place ;
                     TL.value = TL.BinOp (tl1, o, tl2) } in
          (eps', tl)
       | None -> error_incompatible_types e tau TL.basetype_int t.TDL.place
     end
  | TDL.CmpOp (t1, o, t2) ->
     begin
       match unify e tau TL.basetype_bool with
       | Some e' ->
          (* should i use a wobbly binding ??? *)
          let (eps, tl1) = infer_term e' t1 Rigid TL.basetype_int in
          let (eps', tl2) = infer_term eps t2 Rigid TL.basetype_int in
          let tl = { TL.typ = TL.basetype_bool ;
                     TL.place = t.TDL.place ;
                     TL.value = TL.CmpOp (tl1, o, tl2) } in
          (eps', tl)
       | None -> error_incompatible_types e tau TL.basetype_bool t.TDL.place
     end
  | TDL.Tuple (t1, t2) ->
     begin
       match product_type e tau with
       | Some (e', tau1, tau2) ->
          let (eps, tl1) = infer_term e' t1 m tau1 in
          let (eps', tl2) = infer_term eps t2 m tau2 in
          let tl = { TL.typ = apply_subst eps'.subs tau ;
                     TL.place = t.TDL.place ;
                     TL.value = TL.Tuple (tl1, tl2) } in
          (eps', tl)
       | None ->
          Error.unexpected_pair (TL.string_of_type tau) t.TDL.place
     end
  | TDL.Let (r, tv, TDL.NoHint, t1, t2) ->
     let identifier = Atom.fresh "var" in
     let e = if r = TDL.NonRecursive then e else
               let tau = ([], fresh_base_type ()) in
               { e with
                 vars = Smap.add tv (Wobbly, identifier, tau) e.vars }
     in
     let (e', tl1, typ, bind) = infer_gen_binding e t1 in
     print_debug ("Guessed type " ^ (TL.string_of_typescheme typ) ^ " for wobbly let binding.\n\n") ;
     let eps = if r = TDL.Recursive then e' else
                 { e' with
                   vars = Smap.add tv (bind, identifier, typ) e'.vars }
     in
     let (eps', tl2) = infer_term eps t2 m tau in
     let tl = { TL.typ = apply_subst eps'.subs tau ;
                TL.place = t.TDL.place ;
                TL.value = TL.Let (r, identifier, tl1, tl2) } in
     (eps', tl)
  | TDL.Let (r, tv, TDL.Hint (typ, h_place), t1, t2) ->
     let identifier = Atom.fresh "var" in
     let (eps, ts) = translate_hint e h_place typ in
     let eps = if r = TDL.NonRecursive then eps else
                 { eps with
                   vars = Smap.add tv (Rigid, identifier, ts) eps.vars }
     in
     let (eps', tl1) = infer_gen_term eps t1 Rigid ts in
     let f = if r = TDL.Recursive then
               { eps with
                 subs = eps'.subs }
             else
               { eps with
                 vars = Smap.add tv (Rigid, identifier, ts) eps.vars ;
                 subs = eps'.subs }
     in
     let (f', tl2) = infer_term f t2 m tau in
     let tl = { TL.typ = apply_subst f'.subs tau ;
                TL.place = t.TDL.place ;
                TL.value = TL.Let (r, identifier, tl1, tl2) } in
     (f', tl)

and infer_gen_term : env ->
                     TDL.term -> binding -> TL.gen_type ->
                     env * TL.term =
  fun e t b (gen_param, tau) ->
  let phi = fresh_subst gen_param in
  let tau' = apply_subst phi tau in
  let (e', tl) = infer_term e t b tau' in
  if (** TODO **) false then (* Really important. DO IT *)
    Error.escape t.TDL.place 
  else
    (e', tl)

let get_prog_env : env -> Atom.atom Smap.t * unit Smap.t =
  fun e ->
  let cons = Smap.map (fun _ -> ()) e.cons in
  let base_vars = ["print_int"] in
  let aux a b =
    let (_, x, _) = Smap.find a e.vars in
    Smap.add a x b
  in
  let vars = List.fold_right aux base_vars Smap.empty in
  (vars, cons)

let infer_prog : bool -> env * TDL.term -> TL.program =
  fun d (e, t) ->
  debug := d ;
  let tau = fresh_base_type () in
  let (e', t') = try
      infer_term e t Wobbly tau
    with
      Error.Type_error (pl, e) -> Error.error pl e
  in
  print_debug "\n\n\n INFERENCE SUCCESSFUL \n\n\n" ;
  print_debug (TL.string_of_term t') ;
  print_debug "\n\n\n NOW STARTING PRODUCTION \n\n\n" ;
  let (base_vars, cons) = get_prog_env e' in
  (t', base_vars, cons)
