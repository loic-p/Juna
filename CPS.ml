(* The source calculus. *)
module TL = TypeLambda
(* The target calculus. *)
module T = Tail

(* Nothing is accomplished here *)
let rec translate_pattern : TL.pattern -> T.pattern =
  fun p ->
  match p.TL.value with
  | TL.ThrowawayPt -> T.ThrowawayPt
  | TL.VarPt tv -> T.VarPt tv
  | TL.TuplePt (p1, p2) ->
     let p1' = translate_pattern p1 in
     let p2' = translate_pattern p2 in
     T.TuplePt (p1', p2')
  | TL.ConsPt (c, pl) ->
     let pl' = List.map translate_pattern pl in
     T.ConsPt (c, pl')                     


(* The main CPS transform function. Returns a T.block that will
   always be a lambda absraction. *)
let rec cps_block : TL.term -> T.block =
  fun t ->
  let k = Atom.fresh "cps" in
  match t.TL.value with
  (* A variable is translated into its double negation *)
  | TL.Var tv ->
     if tv = fst TL.basevar_printint then
       T.Lam ([k], T.Print_int (k))
     else if tv = fst TL.basevar_printstring then
       T.Lam ([k], T.Print_string (k))
     else
       T.Lam ([k], T.TailCall (k, [T.VVar tv]))
  (* A lambda abstraction is more or less the same *)
  | TL.Lam (tv, t) ->
     let f = Atom.fresh "lam" in
     (* non exhaustive pattern but cps_block only produces lambda-abstractions *)
     let T.Lam (args, body) = cps_block t in 
     T.Lam ([k], T.LetBlo (f, T.Lam (tv::args, body),
                 T.TailCall (k, [T.VVar f])))
  (* An application that looks like
       t1 t2
     Will be translated into something like
       fun k ->
       let x1 = [t1] in
       x1 (fun y1 -> 
           let x2 = [t2] in x1 x2 k)
   *)
  | TL.App (t1, t2) ->
     let x1 = Atom.fresh "app" in
     let x2 = Atom.fresh "app" in
     let xt1 = Atom.fresh "app" in
     let xt2 = Atom.fresh "app" in
     let xr1 = Atom.fresh "app" in
     let xr2 = Atom.fresh "app" in
     let t1' = cps_block t1 in
     let t2' = cps_block t2 in
     let res1 = T.Lam ([x2], T.TailCall (x1, [T.VVar x2 ; T.VVar k])) in
     let res2 = T.Lam ([x1], T.LetBlo (xr1, res1,
                             T.LetBlo (xt2, t2',
                             T.TailCall (xt2, [T.VVar xr1])))) in
     T.Lam ([k], T.LetBlo (xr2, res2,
                 T.LetBlo (xt1, t1',
                 T.TailCall (xt1, [T.VVar xr2]))))

  (* A constructor that looks like
       K a b c
     will be transformed into something that looks like
       fun k ->
       let xa = [a] in
       let xb = [b] in
       let xc = [c] in
       xa (fun a -> xb (fun b -> xc (fun c -> k (K a b))))
   *)
  | TL.Cons (cons, args) ->
     let x = List.map (fun _ -> Atom.fresh "cons") args in
     let xval = List.map (fun x -> T.VVar x) x in
     let y = List.map (fun _ -> Atom.fresh "cons") args in
     let args' = List.map cps_block args in
     let xc = Atom.fresh "cons_res" in
     let rec aux1 = function
       | [] -> T.LetBlo (xc, T.Cons (cons, xval),
               T.TailCall (k, [T.VVar xc]))
       | (x1, x2)::tl ->
          let xr = Atom.fresh "cons" in
          let r = aux1 tl in
          T.LetBlo (xr, T.Lam ([x1], r),
          T.TailCall (x2, [T.VVar xr]))
     in
     let rec aux2 res = function
       | [] -> res
       | (x, arg)::rl ->
          let rest = aux2 res rl in
          T.LetBlo (x, arg, rest)
     in
     let res = aux1 (List.combine x y) in
     let res' = aux2 res (List.combine y args') in
     T.Lam ([k], res')
  (* A match that looks like
       match t with
       | p1 -> t1
       | p2 -> t2
     will be translated into something that looks like
       fun k ->
       let xt = [t] in
       xt (fun t -> match t with
                    | p1 -> let xt1 = [t1] in xt1 k
                    | p2 -> let xt2 = [t2] in xt2 k
   *)
  | TL.Match (term, clauses) ->
     let xt = Atom.fresh "match" in
     let xa = Atom.fresh "match" in
     let xr = Atom.fresh "match" in
     let aux (pt, t) =
       let xt = Atom.fresh "match" in
       let t' = cps_block t in
       let pt' = translate_pattern pt in
       (pt', T.LetBlo (xt, t',
             T.TailCall (xt, [T.VVar k])))
     in
     let clauses' = List.map aux clauses in
     let term' = cps_block term in
     let res = T.Lam ([xa], T.Match (xa, clauses')) in
     T.Lam ([k], T.LetBlo (xt, term',
                 T.LetBlo (xr, res,
                 T.TailCall (xt, [T.VVar xr]))))
  (* Obvious *)
  | TL.Lit i ->
     T.Lam ([k], T.TailCall (k, [T.VLit i]))
  | TL.String s ->
     let xs = Atom.fresh "string" in
     T.Lam ([k], T.LetBlo (xs, T.String s,
                 T.TailCall (k, [T.VVar xs])))
  (* A binary operation that looks like
       t1 o t2
     will get translated to something that looks like
       fun k ->
       let x1 = [t1] in
       let x2 = [t2] in
       x1 (fun a -> x2 (fun b -> k (a o b)))
   *)
  | TL.BinOp (t1, o, t2) ->
     let x1 = Atom.fresh "bin" in
     let x2 = Atom.fresh "bin" in
     let xr1 = Atom.fresh "bin" in
     let xr2 = Atom.fresh "bin" in
     let xa = Atom.fresh "bin" in
     let xb = Atom.fresh "bin" in
     let t1' = cps_block t1 in
     let t2' = cps_block t2 in
     let res1 = T.Lam ([xb],
                T.TailCall (k, [T.VBinOp (T.VVar xa, o, T.VVar xb)])) in
     let res2 = T.Lam ([xa], T.LetBlo (x2, t2',
                             T.LetBlo (xr1, res1,
                             T.TailCall (x2, [T.VVar xr1])))) in
     T.Lam ([k], T.LetBlo (x1, t1',
                 T.LetBlo (xr2, res2,
                 T.TailCall (x1, [T.VVar xr2]))))
  | TL.CmpOp (t1, o, t2) ->
     let x1 = Atom.fresh "cmp_fst" in
     let x2 = Atom.fresh "cmp_snd" in
     let xr = Atom.fresh "cmp_result" in
     let xr1 = Atom.fresh "cmp" in
     let xr2 = Atom.fresh "cmp" in
     let xa = Atom.fresh "cmp" in
     let xb = Atom.fresh "cmp" in
     let t1' = cps_block t1 in
     let t2' = cps_block t2 in
     let res1 = T.Lam ([xb],
                T.LetBlo (xr, T.CmpOp (T.VVar xa, o, T.VVar xb),
                T.TailCall (k, [T.VVar xr]))) in
     let res2 = T.Lam ([xa], T.LetBlo (x2, t2',
                             T.LetBlo (xr1, res1,
                             T.TailCall (x2, [T.VVar xr1])))) in
     T.Lam ([k], T.LetBlo (x1, t1',
                 T.LetBlo (xr2, res2,
                 T.TailCall (x1, [T.VVar xr2]))))
  (* More or less the same without the operation *)
  | TL.Tuple (t1, t2) ->
     let x1 = Atom.fresh "pair" in
     let x2 = Atom.fresh "pair" in
     let xr1 = Atom.fresh "pair" in
     let xr2 = Atom.fresh "pair" in
     let xa = Atom.fresh "pair" in
     let xb = Atom.fresh "pair" in
     let xp = Atom.fresh "pair" in
     let t1' = cps_block t1 in
     let t2' = cps_block t2 in
     let res1 = T.Lam ([xb],
                T.LetBlo (xp, T.Pair (T.VVar xa, T.VVar xb),
                T.TailCall (k, [T.VVar xp]))) in
     let res2 = T.Lam ([xa], T.LetBlo (x2, t2',
                             T.LetBlo (xr1, res1,
                             T.TailCall (x2, [T.VVar xr1])))) in
     T.Lam ([k], T.LetBlo (x1, t1',
                 T.LetBlo (xr2, res2,
                 T.TailCall (x1, [T.VVar xr2]))))
  | TL.Let (TL.NonRecursive, var, t1, t2) ->
     let x1 = Atom.fresh "let" in
     let x2 = Atom.fresh "let" in
     let xr = Atom.fresh "let" in
     let t1' = cps_block t1 in
     let t2' = cps_block t2 in
     let res =  T.Lam ([var], T.LetBlo (x2, t2',
                              T.TailCall (x2, [T.VVar k])))
     in
     T.Lam ([k], T.LetBlo (x1, t1',
                 T.LetBlo (xr, res,
                 T.TailCall (x1, [T.VVar xr]))))
  | TL.Let (TL.Recursive, var, t1, t2) ->
     begin
       match t1.TL.value with
       | TL.Lam (arg, body) ->
          let x1 = Atom.fresh "letrec" in
          let x2 = Atom.fresh "letrec" in
          let xr = Atom.fresh "letrec" in
          let xa = Atom.fresh "letrec" in
          let xb = Atom.fresh "letrec" in
          let xk = Atom.fresh "letrec" in
          let t2' = cps_block t2 in
          let T.Lam (args, body') = cps_block body in
          let lambda = T.Lam ([xk], T.LetBloRec (xa, var, T.Lam (arg :: args, body'),
                                   T.TailCall (xk, [T.VVar xa]))) 
          in
          let res = T.Lam ([var], T.LetBlo (x2, t2',
                                  T.TailCall (x2, [T.VVar k])))
          in
          T.Lam ([k], T.LetBlo (x1, lambda,
                      T.LetBlo (xr, res,
                      T.TailCall (x1, [T.VVar xr]))))
       | _ ->
          (** TODO **)
          (* Recursive data structures would be so cool *)
          cps_block { t with
              TL.value = (TL.Let (TL.NonRecursive, var, t1, t2)) }
     end

(* put all the pieces together *)
let cps_prog : TL.program -> T.program =
  fun (t, vars, cons) ->
  let t' = cps_block t in
  let xp = Atom.fresh "program" in
  let xm = Atom.fresh "main" in
  let x = Atom.fresh "unused" in
  let main = T.Lam ([x], T.Exit) in
  let prog = T.LetBlo (xm, main,
             T.LetBlo (xp, t',
             T.TailCall (xp, [T.VVar xm]))) in
  (prog, vars, cons)
