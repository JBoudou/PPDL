open Form

let a = Atom "a"
let b = Atom "b"
let q = Var "q"

let pa = CPar (Iter a, Seq (Choice (a,b), b))
let pb = CPar (Seq (a, Test q), Seq (a, b))

let fs = Box (Iter pa, diam pb top)
let fu = Box (Iter pa, conj (neg q) (diam pb q))

open Format

let out = std_formatter

;;
( print_formula out fs ;
  pp_print_newline out () ;
  print_formula out fu ;
  pp_print_newline out () );;

open Hintikka

let flcs = HSet.fischer_ladner ([], HForm.translate fs)
let flcu = HSet.fischer_ladner ([], HForm.translate fu)

let flns = HSet.neg_closure flcs
let flnu = HSet.neg_closure flcu

;;
( pp_print_int out (HSet.cardinal flcs) ;
  pp_print_string out " " ;
  pp_print_int out (HSet.cardinal flns) ;
  pp_print_newline out () ;
  pp_print_int out (HSet.cardinal flcu) ;
  pp_print_string out " " ;
  pp_print_int out (HSet.cardinal flnu) ;
  pp_print_newline out ()
)


let hins = SetHSet.filtered_subsets (HSet.is_Hintikka flcs) flns
let hinu = SetHSet.filtered_subsets (HSet.is_Hintikka flcu) flnu

;;
( pp_print_int out (SetHSet.cardinal hins) ;
  pp_print_newline out () ;
  pp_print_int out (SetHSet.cardinal hinu) ;
  pp_print_newline out ()
)
