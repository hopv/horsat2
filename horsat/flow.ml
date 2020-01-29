open Grammar;;
open Utilities;;
open Automaton;;

type fc = FCvt of nameV * term * term list
            (* Flow(x) supseteq Flow(t) where t is of the form h v1 ... vk*)
        | FCvv of nameV * nameV
            (* Flow(x) supseteq Flow(y) *)
        | FCapp of nameV * int * term list
            (* FCapp(x,k,[t1;...;tl]) means there can be an application
               x u1 ... uk t1 ... tl
             *)

let merge_fcs = merge_and_unify compare

let get_vars f g =
 try
   fst (List.assoc f g.r)
 with Not_found -> assert false

let rec genC_term t g =
  let (h,ts) = decompose_term t in
  if ts=[] then []
  else
    let n = List.length ts in
    let fc1 = genC_terms ts g in
    let fc2 =
      match h with
        NT(f) -> 
         let vs = get_vars f g in
         let vs' = list_take_n vs n in
         let env = List.combine vs' ts in
          List.map 
           (fun (x,t1)-> 
              let (h,ts1)=decompose_term t1 in
              match h with
                Var(y) -> if ts1=[] then FCvv(x,y) else FCvt(x,h,ts1)
              | _ -> FCvt(x,h,ts1)) 
           env
    | T(a) -> []
    | Var(x) -> 
         [FCapp(x,0,ts)]
    | _ -> assert false
   in
     merge_fcs fc1 fc2

and genC_terms ts g =
  List.fold_left
   (fun fc t -> merge_fcs (genC_term t g) fc) [] ts

let genC_rule (f,(vs,t)) g =
  genC_term t g

let genC g: fc list =
  List.fold_left
   (fun fc r -> merge_fcs (genC_rule r g) fc) [] g.r

let print_fc fc =
  match fc with
    FCvt(x,t,ts) ->
      (print_string ("FCvt: Flow("^x^") > ");
      print_term t; print_string " ";
      List.iter (fun t->print_term t; print_string " ") ts)
  | FCvv(x,y) -> 
      print_string ("FCvv: Flow("^x^") > Flow("^y^")")
  | FCapp(x,n,ts) ->
      (print_string ("FCapp: "^x^" ");
      List.iter (fun _->print_string ".") (mk_list n ());
      List.iter (fun t->print_term t; print_string " ") ts)
let print_fcs fclist =
  List.iter
   (fun fc -> (print_fc fc; print_string "\n"))
  fclist
  
let add_flow flow x t =
  try
    let r = Hashtbl.find flow x in
    let old = !r in
    let new_flow = merge_and_unify compare old [t] in
      if List.length old =List.length new_flow then
        false
      else 
         (r := new_flow; true)
  with Not_found ->
    (Hashtbl.add flow x (ref [t]); true)

let lookup_flow flow x =
  try
     !(Hashtbl.find flow x)
  with Not_found ->
    []

let add_fcstab fcstab x fc =
  try
    let r = Hashtbl.find fcstab x in
    let (fcvv,fcapp)= !r in
    match fc with
      FCvv _ -> 
        let fcvv' = merge_fcs fcvv [fc] in
          if List.length fcvv'=List.length fcvv then false
          else (r := (fcvv', fcapp); true)
    | FCapp _ -> 
        let fcapp' = merge_fcs fcapp [fc] in
          if List.length fcapp'=List.length fcapp then false
          else (r := (fcvv, fcapp'); true)
   | _ -> assert false
  with Not_found ->
    match fc with
      FCvv _ ->  (Hashtbl.add fcstab x (ref ([fc],[])); true)
    | FCapp _ -> (Hashtbl.add fcstab x (ref ([],[fc])); true)
   | _ -> assert false


let lookup_fcstab fcstab x =
  try
    !(Hashtbl.find fcstab x)
  with Not_found -> ([],[])
    
let rec init_flow flow fcstab fcs =
  match fcs with
    [] -> ()
  | FCvt(x,t,ts)::fcs' ->
       let _ = add_flow flow x (t,ts) in
       init_flow flow fcstab fcs'
  | FCvv(x,y)::fcs' ->
     let _ =
       let _ = add_fcstab fcstab y (FCvv(x,y)) in ()
     in
       init_flow flow fcstab fcs'
  | FCapp(x,n,ts)::fcs' ->
       let _ = add_fcstab fcstab x (FCapp(x,n,ts)) in
       init_flow flow fcstab fcs'

let mkfs_flow x (h,ts) =
  FCvt(x,h,ts)
(**
   Flow(x) > Flow(y), Flow(y)>t --> Flow(x) > t
   x [n] ts1,  Flow(x)>F ts2, |ts2|=m --> Flow(x_{m+n+1}@F) > ts1
   x [n] ts1,  Flow(x)>y ts2, |ts2|=m --> y [m+n] ts1
**)
let rec propagate_flow_step fcs flow fcstab g =
  match fcs with
    [] -> []
  | FCvt(x,h,ts)::fcs' ->
        let (fcvv,fcapp) = lookup_fcstab fcstab x in
        (* Flow(y) > Flow(x), Flow(x)>t --> Flow(y) > t *)
        let fcs1 = List.fold_left
                        (fun fcs1 fc1->
                           match fc1 with
                            FCvv(y,x') -> (* x=x' *)
                             let fc2 = FCvt(y,h,ts) in
                              if add_flow flow y (h,ts) then
                                  merge_fcs fcs1 [fc2]
                              else fcs1
                          | _ -> assert false)
                      [] fcvv
           in 
        let fcs2 =
          match h with
            App(_,_)->assert false
          | T(_)-> []
          | NT(f) ->
          (* x [n] ts1,  Flow(x)>F ts2, |ts2|=m --> Flow(x_{m+n+1}@F) > ts1*)
             List.fold_left
              (fun fcs1 fc1 ->
                match fc1 with
                   FCapp(_,n,ts1) ->
                     let m = List.length ts in
                     let k = List.length ts1 in
                     let vars = get_vars f g in
                     let vars' = list_take_n (list_rem_n vars (m+n)) k in
                     let env = List.combine vars' ts1 in
                       List.fold_left 
                        (fun fcs3 (z,t1) ->
                         let (h,ts2)=decompose_term t1 in
                          match h with
                          Var(u) -> 
                            if ts2=[] then if u=z then fcs3 else
                              let fc2 = FCvv(z,u) in
                              if add_fcstab fcstab u fc2 then
                                merge_fcs fcs3 [fc2]
                              else fcs3
                            else
                              if add_flow flow z (h,ts2) then
                                merge_fcs fcs3 [FCvt(z,h,ts2)]
                              else fcs3
                        | _ -> 
                              if add_flow flow z (h,ts2) then
                                merge_fcs fcs3 [FCvt(z,h,ts2)]
                              else fcs3
                        ) fcs1 env
                  | _ -> assert false
                  ) [] fcapp
           | Var(y) ->
             (* x > y t1...tk, x ...[n] s1 ... sm -> y ...[k+n] s1...sm *)
              List.fold_left
                (fun fcs1 fc1 ->
                  match fc1 with
                   FCapp(_,n,ts1) ->
                    let k = List.length ts in
                    let fc2 = FCapp(y,k+n,ts1) in
                     if add_fcstab fcstab y fc2 then
                       merge_fcs fcs1 [fc2]
                     else fcs1
                 | _ -> assert false
                ) [] fcapp                    
           in 
           let fcs'' = merge_fcs (merge_fcs fcs1 fcs2) fcs' in
                fcs''
  | FCvv(x,y)::fcs' -> 
     (* x>y, y>t --> x>t *)
      let terms = lookup_flow flow y in
      let fcs1 = List.fold_left
                 (fun fcs1 (h,ts) -> 
                   if add_flow flow x (h,ts) then
                     merge_fcs fcs1 [FCvt(x,h,ts)]
                   else
                     fcs1)
                 [] terms
      in
      let fcs'' = merge_fcs fcs1 fcs' in
         fcs''
  | FCapp(x,n,ts)::fcs' -> 
      (* x ..[n]ts, x > y s1...sm --> y ..[m+n] ts
         x ..[n]ts, x > F s1...sm --> F ..[m+n] ts
       *)
      let terms = lookup_flow flow x in
      let fcs1 =
        List.fold_left
         (fun fcs1 (h1,ts1) ->
           match h1 with
             Var(y) ->
               let m = List.length ts1 in
               let fc2 = FCapp(y,n+m,ts) in
                 if add_fcstab fcstab y fc2 then
                   merge_fcs fcs1 [fc2]
                 else fcs1 
          | NT(f) ->
               let m = List.length ts1 in
               let k = List.length ts in
               let vs = get_vars f g in
               let vars' = list_take_n (list_rem_n vs (m+n)) k in
               let env = List.combine vars' ts in
                       List.fold_left 
                        (fun fcs3 (z,t1) ->
                         let (h,ts2)=decompose_term t1 in
                          match h with
                          Var(u) -> 
                            if ts2=[] then if u=z then fcs3 else
                              let fc2 = FCvv(z,u) in
                              if add_fcstab fcstab u fc2 then
                                merge_fcs fcs3 [fc2]
                              else fcs3
                            else
                              if add_flow flow z (h,ts2) then
                                merge_fcs fcs3 [FCvt(z,h,ts2)]
                              else fcs3
                        | _ -> 
                              if add_flow flow z (h,ts2) then
                                merge_fcs fcs3 [FCvt(z,h,ts2)]
                              else fcs3
                        ) fcs1 env
           | T(_) -> fcs1
           | _ -> assert false
          ) [] terms
       in
       let fcs'' = merge_fcs fcs1 fcs' in
           fcs''

let rec propagate_flow fcs flow fcstab g =
  let fcs' = propagate_flow_step fcs flow fcstab g in
   if fcs'=[] then flow
   else propagate_flow fcs' flow fcstab g


let print_flowterms htslist =
  List.iter
   (fun (h,ts) ->
     print_string "  ";
     print_term h;
     print_string " ";
     List.iter (fun t->print_term t;print_string " ") ts;
     print_string "\n")
    htslist

let print_flow flow =
  let flowlist = hash2list flow in
  List.iter 
  (fun (x,r) ->
     (print_string ("Flow("^x^"):\n");
      print_flowterms !r;
      print_string "\n\n"))
  flowlist


let print_fcstab fcstab =
  let fcslist = hash2list fcstab in
  List.iter
  (fun (x,r)->
     (print_string ("Constraints on "^x^":\n");
      let (fcs1,fcs2)= !r in
      print_fcs fcs1;
      print_fcs fcs2;
      print_string "\n\n"))
  fcslist

let flowtable = Hashtbl.create 100

let lookup_flowtab x =
  try
   let hts_list =  !(Hashtbl.find flowtable x) in
     hts_list 
  with
   Not_found -> []

let headtable = Hashtbl.create 1000

let rec lookup_headtab x =
  try
    Hashtbl.find headtable x
  with
   Not_found -> 
     let heads = compute_heads x in
       (Hashtbl.add headtable x heads; heads)
and compute_heads x =
  let hts_list = lookup_flowtab x in
    List.fold_left
    (fun heads (h, hs) ->
      let k = List.length hs in
      match h with
        (NT(_) | T(_)) -> merge_and_unify compare [(h,k)] heads
      | Var(y) ->
           let heads1 =
              List.map (fun (h,k1)->(h,k+k1)) (lookup_headtab y)
           in
             merge_and_unify compare heads1 heads
      | _ -> assert(false)
    )
    []
    hts_list

let print_heads g =
 (print_string "heads of terms bound to variables:\n";
  List.iter
  (fun (_,(vars,_)) ->
    List.iter 
   (fun x->
    print_string (x^": ");
    let heads = lookup_headtab x in
    List.iter (fun (h,k) -> 
         (print_term h; print_string ("::"^(string_of_int k)^", "))) heads;
    print_string ("\n"))
    vars
  )
  g.r;
  print_string "===========================\n")


(* solve_fcs: ... -> (name, (term * term list) list ref) *)
let solve_fcs fcs g =
  let fcstab = Hashtbl.create 100 in
  let _ = init_flow flowtable fcstab fcs in
  let fcs' = List.filter (function FCvt(_,_,_)->false | _ -> true) fcs in
  let _ = propagate_flow fcs' flowtable fcstab g in
  let _ = if !Flags.debugging then print_flow flowtable in
(*  let _ = print_string "===============\n" in
  let _ = print_fcstab fcstab in
*)
    flowtable

let stmap_add stmap h q =
  try
    let r = Hashtbl.find stmap h in
    let qs = merge_and_unify compare [q] !r in
      if List.length !r = List.length qs then
         false
      else (r := qs; true)
  with Not_found ->
    (Hashtbl.add stmap h (ref [q]); true)

let rec propagate_states todo stmap flow g delta =
  match todo with
    [] -> ()
  | (NT(f),q)::todo' ->
      let (_,body) = Grammar.get_def f g in
      let h = Grammar.head body in
        if stmap_add stmap h q then
          propagate_states ((h,q)::todo') stmap flow g delta
        else
          propagate_states todo' stmap flow g delta
  | (T(a),q)::todo' ->
    (try
     let (vars,_) = Grammar.get_def (Grammar.tname2ntname a) g in
     let delta' = List.filter (fun ((q',a'),_)->q=q' && a=a') delta in
     let todo1 =
      List.fold_left
      (fun todo0 (_,qs) ->
        let vqlist = List.combine vars qs in
        List.fold_left
         (fun todo2 (v,q) ->
           if not(q="top") && stmap_add stmap (Var(v)) q then
             (Var(v),q)::todo2
           else todo2)
         todo0 vqlist)
       todo' delta'
      in
        propagate_states todo1 stmap flow g delta
     with (UndefinedNonterminal _) -> propagate_states todo' stmap flow g delta
     )
   | (Var(x),q)::todo' ->
      let terms = lookup_flow flow x in
      let todo1 =
        List.fold_left 
        (fun todo0 (h, _) ->
            if stmap_add stmap h q then
              (h,q)::todo0
            else todo0)
         todo' terms
       in 
        propagate_states todo1 stmap flow g delta
   | _ -> assert false

let stmap = Hashtbl.create 400

let lookup_stmap nt =
  try
    !(Hashtbl.find stmap (NT(nt)))
  with Not_found -> []

let mk_ntstmap flow g m =
  let _ = stmap_add stmap (NT(g.s)) m.init in
  let _ = propagate_states [(NT(g.s),m.init)] stmap flow g m.delta in
    stmap

let print_stmap stmap =
  let stmaplist = hash2list stmap in
  List.iter 
  (fun (h,r) -> 
     print_term h; print_string ": ";
     List.iter (fun q -> print_string (q^" ")) !r;
     print_string "\n"
  ) stmaplist

let negate_ntstmap stmap =
 ( Hashtbl.iter
  (fun h r -> 
    let l = List.map (fun q -> "~"^q) !r in
      r := l)
  stmap;
   stmap)
