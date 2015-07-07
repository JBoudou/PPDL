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
let c = Atom "c"
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
  (Diam (CPar (a, 2, b), q))
let t8 = conj
  (neg (Diam (CPar (Iter a, 1, Iter b), p)))
  (Diam (CPar (a, 2, b), q))

(* <(a ||1 (b ; [c]¬p?)) ||2 c> [[[c]¬p? ||3 T?]⊥? || T?] ⊥ *)
let t9 =
  Diam (CPar (CPar (a, 1, Seq (b, Test (Neg (Diam (c, p))))), 2, c), 
    Neg (Diam (CPar (
      Test (Neg (Diam (CPar (Test (Neg (Diam (c, p))), 3, Test top), top))),
      4, Test top), top)))

let t10 = Neg (Diam (Iter a, Neg (Diam (a, top))))

(* TODO: continue *)

let results =
  List.map (fun (name, form) ->
              print_endline name ;
              proceed_todo (init form))
           [  "t1",   t1 ;
              "t2",   t2 ;
              "t3",   t3 ;
              "t4",   t4 ;
              "t5",   t5 ;
              "t6",   t6 ;
              "t7",   t7 ;
              "t8",   t8 ;
              "t9",   t9 ;
              "t10",  t10 ;
           ]
