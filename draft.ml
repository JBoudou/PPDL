let a = Form.Atom "a";;
let b = Form.Atom "b";;
let c = Form.Atom "c";;
let p = Form.Var "p";;

let phi = Form.diam (Form.CPar (Form.Seq (a,Form.Choice (b,c)), Form.Iter (Form.Choice (a, b)))) p
let tphi = TForm.translate phi

let psi = Form.diam (Form.Seq (Form.Test p, a)) p
let tpsi = TForm.translate psi

let contr = Form.diam (Form.Test p) (Form.neg p)
let tcontr = TForm.translate contr
