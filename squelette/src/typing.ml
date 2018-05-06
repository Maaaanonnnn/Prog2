open Ast

type typing_error

let print_error fmt err = failwith "boo"


let rec substi v x l = match l with
  |[] -> []
  |(d,g)::q when d=g=v-> (x, x)::(substi v x q)
  |(d,g)::q when d = v-> (x, g)::(substi v x q)
  |(d,g)::q when g = v-> (d, x)::(substi v x q)
  |_ -> failwith "impossible"
                                                
let occurcheck v typ =  let rec aux v x typ = match typ with
  |[] -> aux v x typ
  |(l,r)::q -> if (v = l || v = r) then failwith "failure"
    else aux v x q
  in
  (aux v x typ)



let rec robinson l = match l with
  |[] -> []
  |(TyVar(x),TyVar(t))::q -> if x = t then robinson q
    else failwith "failure"
  |(TyArrow(x1, x2), TyArrow(t1, t2))::q | (TyTimes(x1, x2), TyTimes(t1, t2))::q -> (t1, x2)::(x1, t2)::(robinson q)
  |(TyArrow(x1, x2), TyVar(v))::q -> occurcheck (TyVar v) q 
  |_ -> failwith "nji"




let rec typing_expr expl = match expl with
  |l, Var(v) -> TyVar v
  |l, App(el1, el2) -> TyArrow ((typing_expr el1), (typing_expr el2))
  |l, Lam(var, tyop, el) -> failwith "todo"
  |l, Pair(el1, el2) -> TyTimes(typing_expr el1, typing_expr el2)
  |l, LetIn(var, el1, el2) -> failwith "todo"
  |l, Fix(el) -> typing_expr el
  |l, Int(n) -> TyInt
  |l, Bool(b) -> TyBool
  |l, Proj(ele) -> (match ele with
        |Left(l, Pair(e1, e2)) -> typing_expr e1
        |Right(l, Pair(e1, e2)) -> typing_expr e2
        |_ -> failwith "typage impossible")    
  |l, Ite(el1, el2, el3) -> if (typing_expr el1 = TyBool) then
      (let e2 = typing_expr el2 in
      let e3 = typing_expr el3 in
       if (e2 = e3) then e2
       else
      failwith "boo")
    else
      (failwith "uncorrect type!")      
  |l, Binop(bin, el1, el2) -> if ( (typing_expr el1 = TyInt) && (typing_expr el2 = TyInt))then
      TyInt
    else
      failwith "uncorrect type!"



(*let typing_binop bin e1 e2   = match bin with
  |Plus -> gh
  |Minus -> ckdjl
  |Times -> ed
  |Div -> csjkm
  |And -> d
  |Or -> d
  |Eq -> de
  |Gt ->d
*)


                  
                  
let rec typing_ast ast = match ast with
  |l, Let(va, tyop, expl) -> typing_expr expl
  |l, LetRec(va, tyop, expl) -> typing_expr expl
