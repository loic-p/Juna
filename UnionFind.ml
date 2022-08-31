(* Congruence closure algorithm as described by Nelson and Oppen *)
(* Implemented via union find arrays *)

type 'a node = {
    label : 'a ;
    mutable rank : int ;
    mutable parent : int ;
    children : int (* sorted *) list
  }

let rec get_class (graph : 'a node array)
          (n : int) =
  if graph.(n).parent = n then
    n
  else
    get_class graph (graph.(n).parent)

let congruent (graph : 'a node array)
      u v =
  let rec aux l1 l2 =
    match l1, l2 with
    | [], [] -> true
    | h1::t1, h2::t2 -> get_class graph h1 = get_class graph h2 && (aux t1 t2)
    | _ -> assert false
  in
  graph.(u).label = graph.(v).label &&
    (let c_u = graph.(u).children in
     let c_v = graph.(v).children in
     List.length c_u = List.length c_v && (aux c_u c_v))

(* fusion of sorted list while removing duplicates *)
  
let rec fusion (l1 : 'a (* sorted *) list)
      (l2 : 'a (* sorted *) list) =
  match l1, l2 with
  | [], _ -> l2
  | _, [] -> l1
  | h1::t1, h2::t2 ->
     begin
       if h1 = h2 then
         fusion t1 l2
       else if h1 < h2 then
         h1 :: (fusion t1 l2)
       else
         h2 :: (fusion l1 t2)
     end

(* insertion in sorted list without duplicates *)

let rec insert (l : 'a (* sorted *) list)
          (e : 'a) =
  match l with
  | [] -> [e]
  | hd::tl ->
     begin
       if hd = e then
         l
       else if hd > e then
         e::l
       else
         hd::(insert tl e)
     end

let union (graph : 'a node array)
      (pred : int (* sorted *) list array)
      u v =
  if graph.(u).rank < graph.(v).rank then
    begin
      graph.(u).parent <- v ;
      pred.(v) <- fusion pred.(u) pred.(v)
    end
  else if graph.(u).rank > graph.(v).rank then
    begin
      graph.(v).parent <- u ;
      pred.(u) <- fusion pred.(v) pred.(u)
    end
  else
    begin
      graph.(u).rank <- graph.(u).rank + 1 ;
      graph.(v).parent <- u ;
      pred.(u) <- fusion pred.(v) pred.(u)
    end

let rec merge (graph : 'a node array)
          (pred : int (* sorted *) list array)
          u v =
  if get_class graph u = get_class graph v then
    ()
  else
    let p1 = pred.(u) in
    let p2 = pred.(v) in
    union graph pred u v ;
    merge_aux1 graph pred p1 p2

and merge_aux1 graph pred p1 p2 =
  match p1 with
  | [] -> ()
  | hd::tl ->
     begin
       merge_aux2 graph pred hd p2 ;
       merge_aux1 graph pred tl p2
     end

and merge_aux2 graph pred u p =
  match p with
  | [] -> ()
  | hd::tl ->
     begin
       (if get_class graph u <> get_class graph hd &&
            congruent graph u hd then
          merge graph pred u hd) ;
       merge_aux2 graph pred u tl
     end

let build_pred graph =
  let pred = Array.make (Array.length graph) [] in
  let rec aux pred src = function
    | [] -> ()
    | hd::tl -> pred.(hd) <- insert (pred.(hd)) src
  in
  for i = 0 to Array.length graph - 1 do
    aux pred i graph.(i).children
  done ;
  pred

let congruence_closure graph rel =
  let rec aux graph pred rel =
    match rel with
    | [] -> ()
    | (u, v)::tl ->
       begin
         merge graph pred u v ;
         aux graph pred tl
       end
  in
  aux graph (build_pred graph) rel

let decide_equality graph rel u v =
  congruence_closure graph rel ;
  get_class graph u = get_class graph v

let print_class cl =
  let rec aux = function
    | [] -> ()
    | hd::tl ->
       begin
         print_int hd ;
         print_string " " ;
         aux tl
       end
  in
  if List.length cl > 0 then
    begin
      print_string "(" ;
      aux cl ;
      print_string ")\n"
    end
  
let print_congruence graph =
  let classes = Array.make (Array.length graph) [] in
  for i = 0 to Array.length graph - 1 do
    classes.(get_class graph i) <- insert (classes.(get_class graph i)) i
  done ;
  for i = 0 to Array.length graph - 1 do
    print_class classes.(i)
  done 
    
(* test cases, reproduced from Nelson and Oppen's paper *)

(*
let () = print_string ("\nFirst test :\n")
  
let n0 = { label = "f" ; rank = 0 ; parent = 0 ; children = [1 ; 3] }
let n1 = { label = "f" ; rank = 0 ; parent = 1 ; children = [2 ; 3] }
let n2 = { label = "a" ; rank = 0 ; parent = 2 ; children = [] }
let n3 = { label = "b" ; rank = 0 ; parent = 3 ; children = [] }

let g1 = [| n0 ; n1 ; n2 ; n3 |]
let r1 = [(1, 2)]
       
let () = congruence_closure g1 r1
let () = print_congruence g1

let () = print_string ("\nSecond test :\n")

let m0 = { label = "f" ; rank = 0 ; parent = 0 ; children = [1] }
let m1 = { label = "f" ; rank = 0 ; parent = 1 ; children = [2] }
let m2 = { label = "f" ; rank = 0 ; parent = 2 ; children = [3] }
let m3 = { label = "f" ; rank = 0 ; parent = 3 ; children = [4] }
let m4 = { label = "f" ; rank = 0 ; parent = 4 ; children = [5] }
let m5 = { label = "a" ; rank = 0 ; parent = 5 ; children = [] }

let g2 = [| m0 ; m1 ; m2 ; m3 ; m4 ; m5 |]
let r2 = [(2, 5) ; (0, 5)]
       
let () = congruence_closure g2 r2
let () = print_congruence g2
 *)
