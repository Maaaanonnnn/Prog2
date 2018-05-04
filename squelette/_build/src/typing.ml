open Ast

type typing_error

let print_error fmt err = failwith "boo"

let rec typing_ast ast = match ast with
  |l, Let(va, tyop, expl) -> failwith "todo"
  |l, LetRec(va, tyop, expl) -> failwith "todo"


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
      (typing_expr el2;
       typing_expr el3)
    else
      failwith "uncorrect type!"      
  |l, Binop(bin, el1, el2) -> if ( (typing_expr el1 = TyInt) && (typing_expr el2 = TyInt))then
      TyInt
    else
      failwith "uncorrect type!"


                  
                  
