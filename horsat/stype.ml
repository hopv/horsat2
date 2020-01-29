(** check the sorts of non-terminals, print them and the order of the recursion scheme **)
(** Note: the implementation below is naive and slow **)

open Flags;;
open Utilities;;
open Grammar;;
open Automaton;;

type tvar = int
type st = STvar of (st option) ref | STbase | STfun of st * st 

let new_tvid() = ref None

let new_tvar() = STvar(new_tvid())

let rec deref_st st =
  match st with
    STvar(tref) -> 
      ( match !tref with
         None -> st
       | Some(st') -> let st1 = deref_st st' in (tref:= Some(st1); st1))
  | _ -> st

let rec arity_of_sty sty =
  let sty' = deref_st sty in
  match sty' with
    STvar _ -> 0
  | STbase -> 0
  | STfun(_,sty1) -> (arity_of_sty sty1) + 1
exception IllSorted of string
exception UnifFailure of st * st

let is_stfun sty =
  let sty' = deref_st sty in
  match sty' with
    STfun _ -> true
  | _ -> false


let subst_id = []

let rec app_subst sub st =
  match st with
     STvar v -> (try List.assoc v sub with Not_found -> st)
   | STfun(st1,st2) -> STfun(app_subst sub st1, app_subst sub st2)
   | _ -> st

let rec inst_var st =
  let st' = deref_st st in
  match st' with
     STvar vref ->  STbase
   | STfun(st1,st2) -> STfun(inst_var st1, inst_var st2)
   | _ -> st'

let comp_subst sub1 sub2 =
  let sub1' = List.map (fun (x,st) -> (x, app_subst sub2 st)) sub1 in
  let dom1 = List.map fst sub1 in
  let sub2' = List.filter (fun (x,st) -> not(List.mem x dom1)) sub2 in
    sub1'@sub2'

let rec occur v sty =
  match sty with
    STvar(v1) -> v==v1
  | STfun(sty1,sty2) -> (occur v sty1)||(occur v sty2)
  | _ -> false

let rec unify_sty sty1 sty2 =
  let sty1' = deref_st sty1 in
  let sty2' = deref_st sty2 in
   match (sty1',sty2') with
    (STvar v1, STvar v2) ->
        if v1==v2 then ()
        else v1 := Some(sty2')
  | (STvar v1, _) ->
       if occur v1 sty2'
       then raise (UnifFailure (sty1',sty2'))
       else (v1 := Some(sty2'))
  | (_, STvar v2) -> 
       if occur v2 sty1'
       then raise (UnifFailure (sty1',sty2'))
       else (v2 := Some(sty1'))
  | (STfun(st11,st12), STfun(st21,st22)) ->
      unify_sty st11 st21; unify_sty st12 st22
  | (STbase, STbase) -> ()
  | _ -> raise (UnifFailure (sty1,sty2))
  
let rec unify_all c =
  match c with
     [] -> []
  | (sty1,sty2)::c1 ->
      unify_sty sty1 sty2;
      unify_all c1

let rec stys2sty stys =
  match stys with
    [] -> new_tvar()
  | [sty] -> sty
  | sty::stys' ->
      let sty1 = stys2sty stys' in
      let _= unify_sty sty sty1 in
         sty

let rec ty2sty ty =
  let stys = List.map aty2sty ty in
    stys2sty stys
and aty2sty aty =
  match aty with
     ItyQ _ -> STbase
   | ItyFun(t1,at2) -> STfun(ty2sty t1, aty2sty at2)

let rec aty2sty' aty =
  match aty with
     ItyQ _ -> STbase
   | ItyFun([],aty') -> STfun(STbase, aty2sty' aty')
   | ItyFun(aty1::aty2,aty') -> STfun(aty2sty' aty1, aty2sty' aty')

let cte2cste cte =
  let f(c,t) = (c, try ty2sty t with 
                    UnifFailure _ -> raise (IllSorted ("The arity of "^c^" is inconsistent\n"))) in
     List.map f cte

let rec print_sty sty =
  match sty with
    STvar(tv) -> print_string ("'a")
  | STbase -> print_string "o"
  | STfun(sty1,sty2) ->
       let flag1 = is_stfun sty1 in
         (if flag1 then print_string "(" else ();
          print_sty sty1;
          if flag1 then print_string ")" else ();
          print_string " -> ";
          print_sty sty2)
         
let print_sortbinding (f, sty) =
  (print_string (" "^f^" : ");
   print_sty sty;
   print_string "\n")

let print_ste nste =
  let _ = print_string "\nSorts of non-terminals:\n" in
  let _ = print_string "======================\n" in
  let _ = List.map print_sortbinding nste in
  let _ = print_string "\n" in
    ()

let print_cste cste =
  let _ = print_string "\nSorts of terminals:\n" in
  let _ = print_string "======================\n" in
  let _ = List.map print_sortbinding cste in
  let _ = print_string "\n" in
    ()

let rec tcheck_term t vte cte nte =
  match t with
    NT(f) -> (List.assoc f nte, [])
  | T(a) -> (List.assoc a cte, [])
  | Var(v) -> (List.assoc v vte, [])
  | App(t1,t2) ->
       let (sty1, c1) = tcheck_term t1 vte cte nte in
       let (sty2, c2) = tcheck_term t2 vte cte nte in
       let sty3 = new_tvar() in
       let sty4 = STfun(sty2,sty3) in
          (sty3, (sty1,sty4)::(c2@c1))

let rec mk_functy stys sty =
  match stys with
    [] -> sty
  | sty1::stys' ->
       STfun(sty1, mk_functy stys' sty)

let tcheck_rule (f, (vars, body)) cste nste =
  let vste = List.map (fun v -> (v, new_tvar())) vars in
(**
  let _ = if !debugging then print_string ("Checking the rule for "^f^"\n") in
  let _ = if !debugging then print_ste cste in
  let _ = if !debugging then print_ste nste in
  let _ = if !debugging then print_ste vste in
**)
  let (sty,c1) = tcheck_term body vste cste nste in
  let fty1 = mk_functy (List.map snd vste) STbase in
  let fty2 = List.assoc f nste in
    (sty,STbase)::(fty1,fty2)::c1

let tcheck_rules rules cste nste =
  List.fold_left
     (fun c -> fun r -> (tcheck_rule r cste nste)@c) [] rules

let rec order_of_sty sty =
  match sty with
    STfun(sty1,sty2) -> max ((order_of_sty sty1)+1) (order_of_sty sty2)
  | _ -> 0

let order_of_nste nste =
  let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste in
  let x = list_max (fun (nt1,ord1) ->fun (nt2,ord2) -> compare ord1 ord2) ordmap in
    x

let print_order (f,ord) =
  let _ = print_string ("\nOrder of recursion scheme: "^(string_of_int ord)^"\n") in
  let _ = print_string ("Non-terminal of highest order: "^f^"\n") in
    ()

let rec mk_vste vars sty =
  match vars with
   [] -> []
 | v::vars' ->
    (match sty with
       STfun(sty1,sty') -> (v,sty1)::(mk_vste vars' sty')
     | _ -> assert false
   )

let sorttab = Hashtbl.create 1000
let register_sort_htab term sty =
  try
    Hashtbl.find sorttab term
  with Not_found ->
    (Hashtbl.add sorttab term sty; sty)
let lookup_sort term =
  try
    Hashtbl.find sorttab term
  with Not_found -> 
   (print_term term; assert false)

let rec register_sort_term term cste nste vste =
  match term with
    NT(f) -> let sty = List.assoc f nste in
              register_sort_htab term sty
  | T(a) -> let sty = List.assoc a cste in
              register_sort_htab term sty
  | Var(v) -> let sty = List.assoc v vste in
              register_sort_htab term sty
  | App(t1,t2) ->
       let sty1 = register_sort_term t1 cste nste vste in
       let sty2 = register_sort_term t2 cste nste vste in
        match sty1 with
            STfun(sty3,sty4) ->
              if sty3=sty2 then 
                register_sort_htab term sty4
              else assert false
          | _ -> assert false

let register_sort_rule (nt,(vars,term)) cste nste =
  let sty = List.assoc nt nste in
  let _ = register_sort_htab (NT(nt)) sty in
  let vste = mk_vste vars sty in
  let _ = List.iter (fun (v,sty) -> let _ = register_sort_htab (Var(v)) sty in ()) vste in
  let _ = register_sort_term term cste nste vste in
     ()

let register_sort g cste nste =
  List.iter (fun rule -> register_sort_rule rule cste nste) g.r

let tcheck g cte =
  let cste = cte2cste cte in
  let nste = List.map (fun (n,_) -> (n, new_tvar())) g.nt in
  let _ = if !debugging then print_ste cste in
  let _ = if !debugging then print_ste nste in
  let rules = g.r in
  let c = tcheck_rules rules cste nste in
  let _ =  try
                unify_all c 
             with UnifFailure _ ->
                    raise (IllSorted "Rules are not well-sorted\n")
  in
  let nste' = List.map (fun (nt,sty) -> (nt, inst_var sty)) nste in
  let cste' = List.map (fun (a,sty) -> (a, inst_var sty)) cste in
  let (f,ord) = order_of_nste nste' in
  let _ = print_ste nste' in
  let _ = print_cste cste' in
  let _ = print_order (f, ord) in
  let _ = register_sort g cste' nste' in
    flush stdout
