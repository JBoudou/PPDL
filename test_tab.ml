#load "form.cmo"
#load "tab.cmo"

open More
open Form

let a = Atom "a"
let b = Atom "b"
let c = Atom "c"
let p = Var "p"
let q = Var "q"

let t1 = conj (diam a p) (Box (a, q))
let t2 = conj (neg p) (diam (Iter a) p)
let t2b = conj (conj (neg p) (Box (a, neg p))) (diam (Iter a) p)
let t3 = Box (Seq (Test p, Test (neg p)), q)
let t4 = diam (Seq (Test p, Test q)) (neg p)
let t5 = diam (Seq (Test p, Seq (a, Test q))) (neg p)
let t6 = conj
  (Box (Iter a, neg p))
  (diam (Seq (Seq (Seq (Seq (Iter a, Iter b), a), Iter b), a)) p)
let t6b = diam (Seq (Seq (Test (neg q), Seq (a,b)) , Test p)) q
let t6c = diam (Seq (Seq (Test (neg q), Seq (Iter a, Iter b)) , Test p)) q
let t7 = conj
  (Box  (CPar (a, b), p))
  (diam (CPar (a, b)) q )
let t7b = conj
  (Box  (CPar (a, b), neg q))
  (diam (CPar (a, b)) q )
let t7c = conj
  (Box  (CPar (Iter a, b), neg q))
  (diam (CPar (a, b)) q )
let t7d = conj
  (Box  (CPar (a, Iter b), neg q))
  (diam (CPar (a, b)) q )
let t7e = conj
  (Box  (CPar (Iter a, Iter b), neg q))
  (diam (CPar (a, b)) q )
let t8 = conj
  (Box (CPar (Iter a, Iter b), p))
  (diam (CPar (a, b)) q)

(* <(a ||1 (b ; [c]¬p?)) ||2 c> [[[c]¬p? ||3 T?]⊥? || T?] ⊥ *)
let t9 =
  diam (CPar (CPar (a, Seq (b, Test (Box (c, neg p)))), c))
       (Box (CPar (
          Test (Box (CPar (Test (Box (c, neg p)), Test top), Bot)),
          Test top), Bot))

let t10 = Box (Iter a, diam a top)

let t11 = conj
  (Box (Iter a, disj (neg p) (neg q)))
  (diam (Iter a) (conj p q))

let t12 =
  let d = disj p q in
  let e = Seq (a, Test d) in
  let skip = Test top in
  let plus alpha = Seq (alpha, Iter alpha) in
  diam (plus (CPar
          (CPar
              (CPar (Seq (b, Seq (Test (Box (b, Bot)), Test d)), e),
              e),
          e)
       ))
       (Box (CPar (CPar (CPar (Test (Box (b, Bot)), skip), skip), skip), Bot))

let t13 = conj
  (Box (Iter (Seq (Iter b, Iter a)), Neg q))
  (diam (Iter (Seq (Iter a, Iter b))) q)

let t14 = diam (CPar (Seq (a,Choice (b,c)), Iter (Choice (a, b)))) p

let t15 = Box (Iter (Test (diam a top)), diam a top)

let t16 = conj
  (neg p)
  (diam (Iter (CPar (CPar (Iter a, Iter b), Test top))) p)

let t17 = diam (Iter (Test Bot)) top
let t17b = diam (Test Bot) top

let t18 = conj
  (diam (CPar (Iter a, b)) (Box (CPar (Test (Neg p), Test top), Bot)))
  (Box (CPar (Test (diam (Iter a) p), Test top), Bot))
let t18b = conj
  (diam (CPar (a, Iter b)) (Box (CPar (Test top, Test (Neg p)), Bot)))
  (Box (CPar (Test top, Test (diam (Iter b) p)), Bot))

let t19 = conj
  (Box (a, diam (Seq (Test (Box (CPar (a,b), neg p)), b)) top))
  (conj
    (diam a top)
    (diam (Seq (a, Seq (Test top, CPar (a, b)))) p)
  )

(* TODO: continue *)

let print_formula = Form.print_formula
open TForm
open Tab


#trace proceed_todo
#trace proceed_branching
#trace proceed_successor
#trace proceed_waiting


let results =
  List.map (fun phi ->
              let result = proceed_todo (init (translate phi)) in
              print_formula Format.std_formatter phi ;
              Format.pp_print_string Format.std_formatter
                (if result then " sat" else " unsat") ;
              Format.pp_print_newline Format.std_formatter () ;
              result)
           [  t1 ;
(*              t2 ;
              t2b ;
              t3 ;
              t4 ;
              t5 ;
              t6 ;
              t6b ;
              t6c ;
              t7 ;
              t7b ;
              t7c ;
              t7d ;
              t7e ;
              t8 ;
              t9 ;
              t10 ;
              t11 ;
              t12 ;
              t13 ;
              t14 ;
              t15 ;
              t16 ;
              t17 ;
              t17b ;
              t18 ;
              t18b ;
*)              t19 ;
           ]

let () =
  Format.pp_print_list Format.pp_print_bool Format.std_formatter results ;
  Format.pp_print_newline Format.std_formatter ()
