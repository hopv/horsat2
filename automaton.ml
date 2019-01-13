open Utilities;;
open Grammar;;

type state = string
type transfunc = ((state * nameT) * state list) list
type automaton = {alpha: terminals;
                  st: state list;
                  delta: transfunc;
                  init: state
                 }


let next_state q a m =
  List.assoc (q,a) m.delta

let size_st m = List.length (m.st)

let getalpha m =
  let alpha = 
     List.map (fun ((_,a),qs) -> (a, List.length qs)) m.delta
  in
    Utilities.delete_duplication_unsorted alpha

