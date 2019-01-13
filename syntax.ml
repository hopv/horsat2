(*** syntax for parser ***)

type head = Name of string | NT of string | FD of int | CASE of int 
          | PAIR | DPAIR | FUN of string list * preterm
and preterm = PTapp of head * preterm list
type prerule = string * string list * preterm
type prerules = prerule list
type transition = (string * string) * string list
type transitions = transition list

type preformula = FConst of string 
                | FVar of int * string 
                | FAnd of preformula * preformula
                | FOr of preformula * preformula
type ata_trans = (string * string) * preformula

type automaton = Trivial of transitions 
               | Alternating of ((string * int) list) * (ata_trans list)
let rec string_of_vars vl =
  match vl with
    [] -> ""
   | v::vl' -> v^" "^(string_of_vars vl')

let rec string_of_head h =
  match h with
    Name(s) -> s
  | NT(s) -> s
  | FD(n) -> (string_of_int n)
  | CASE(n) -> "_case "^(string_of_int n)
  | PAIR -> "_cons"
  | FUN(vl, pterm) -> "_fun "^(string_of_vars vl)^" -> "^(string_of_preterm pterm)
  | DPAIR -> "_dcons"
  
and string_of_preterm pterm =
  match pterm with
    PTapp(h, pterms) ->
      (string_of_head h)^" "^(string_of_preterms pterms)
and string_of_preterms pterms =
  match pterms with
    [] -> ""
 | pt::pterms' ->
    match pt with
       PTapp(_,[]) -> (string_of_preterm pt)^" "^(string_of_preterms pterms')
     | _ -> 
            "("^(string_of_preterm pt)^") "^(string_of_preterms pterms')


let string_of_prerule (f, vl, pterm) =
   f^" "^(string_of_vars vl)^" -> "^(string_of_preterm pterm)

let rec string_of_prerules_aux prerules =
  match prerules with
    [] -> ""
  | prule::prerules' ->
     (string_of_prerule prule)^".\n"^(string_of_prerules_aux prerules')

let string_of_prerules prerules =
  "%BEGING\n"^(string_of_prerules_aux prerules)^"%ENDG\n"


let rec string_of_states qs =
  match qs with
    [] -> ""
  | q::qs' -> q^" "^(string_of_states qs')

let string_of_transition ((q,a), qs) =
  q^" "^a^" -> "^(string_of_states qs)

let rec string_of_transitions_aux trs =
  match trs with
   [] -> ""
 | tr::trs' ->
     (string_of_transition tr)^".\n"^(string_of_transitions_aux trs')
let string_of_transitions trs = 
  "%BEGINA\n"^(string_of_transitions_aux trs)^"%ENDA\n";;

let rec string_of_ata_formula = function
  | FConst s -> s
  | FVar (i,q) -> "(" ^ string_of_int i ^ "," ^ q ^ ")"
  | FAnd (f1,f2) -> "(" ^ string_of_ata_formula f1 ^ " /\\ " 
                      ^ string_of_ata_formula f2 ^ ")"
  | FOr (f1,f2) -> "(" ^ string_of_ata_formula f1 ^ " \\/ " 
                      ^ string_of_ata_formula f2 ^ ")"


let string_of_ata_rule ((q,a), fml ) =
  q ^ " " ^ a ^ " -> " ^ (string_of_ata_formula fml)

let rec string_of_ata_rules_aux trs =
  match trs with
    [] -> ""
 |  tr :: trs ->
     (string_of_ata_rule tr) ^ ".\n" ^ (string_of_ata_rules_aux trs)

let string_of_automaton = function
  | Trivial trs ->
    "%BEGINA\n"^(string_of_transitions_aux trs)^"%ENDA\n"
  | Alternating (rs,trs) ->
    "%BEGINR\n"^
      String.concat "" (List.map (fun (q,i) -> q ^" -> "^string_of_int i^".\n") rs) ^
    "%ENDR\n"^
    "%BEGINATA\n"^(string_of_ata_rules_aux trs)^"%ENDATA\n"

let ntid = ref 0
let new_ntname() =
   let x = !ntid in
   let _ = (ntid := !ntid + 1) in
     ("$FUN"^(string_of_int x))
