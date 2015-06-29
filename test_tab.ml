#use "tab.ml";;
#trace proceed_todo;;
#trace proceed_branching;;
#trace proceed_successor;;
#trace proceed_waiting;;

let test phi =
  try
    ignore (proceed_todo (init phi))
  with
    Nothing_Todo -> ()

let a = Atom "a"
let b = Atom "b"
let p = Var "p"
let q = Var "q"

let t1 = conj (Diam (a, p)) (neg (Diam (a, neg q)))
let t2 = conj (neg p) (Diam (Iter a, p))
let t3 = neg (Diam (Seq (Test p, Test (neg p)), q))
let t4 = Diam (Seq (Test p, Test q), neg p)
let t5 = Diam (Seq (Test p, Seq (a, Test q)), neg p)
let t6 = conj
  (neg (Diam (Iter a, p)))
  (Diam (Seq (Seq (Seq (Seq (Iter a, Iter b), a), Iter b), b), p))
let t7 = conj
  (neg (Diam (CPar (a, 1, b), p)))
  (Diam (CPar (a, 1, b), q))
let t8 = conj
  (neg (Diam (CPar (Iter a, 1, Iter b), p)))
  (Diam (CPar (a, 1, b), q))
(* TODO: continue *)

let () =
  print_endline "t1" ;
  test t1;
  print_endline "t2" ;
  test t2;
  print_endline "t3" ;
  test t3;
  print_endline "t4" ;
  test t4;
  print_endline "t5" ;
  test t5;
  print_endline "t6" ;
  test t6;
  print_endline "t7" ;
  test t7;
  print_endline "t8" ;
  test t8;
  ()
