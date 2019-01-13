
type t = int list ref * bool array
exception Empty
let make n = (ref [], Array.make n false)
let makeall n = (ref (Utilities.fromto 0 n), Array.make n true)
let make_fromlist n l =
   let bitmap= Array.make n false in
     List.iter (fun i -> bitmap.(i) <- true) l;
     (ref l, bitmap)
      
let rec dequeue (qref,bitmap) =
  match !qref with
    [] -> raise Empty
 | n::ns ->
     qref := ns;
     if bitmap.(n) then (bitmap.(n) <- false; n)
     else dequeue(qref,bitmap)
let print_queue (qref,bitmap) =
  List.iter (fun x->
    if bitmap.(x) then
     print_string ((string_of_int x)^",")
    else ())
  !qref;
  print_string "\n"
  
let enqueue (qref,bitmap) n =
  if bitmap.(n)=true then ()
  else
    qref := n::!qref;
    bitmap.(n) <- true

let is_empty queue =
  try
    let n = dequeue queue in
    enqueue queue n; false
  with
    Empty -> true 

let rec iter f queue =
  try
    let x = dequeue queue in
    f(x); iter f queue
  with Empty -> ()
