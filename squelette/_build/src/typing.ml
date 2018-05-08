open Ast
open Genlab

type typing_error

let print_error fmt err = failwith "boo"


let rec substi (v:Ast.ty) (x: Ast.ty) l = match l with
  |[] -> []
  |(d,g)::q when (d = v && g = v) -> (x, x)::(substi v x q)
  |(d,g)::q when d = v-> (x, g)::(substi v x q)
  |(d,g)::q when g = v-> (d, x)::(substi v x q)
  |_ -> failwith "impossible"


                                                
let rec occurcheck v typ =   match typ with
  |[] -> false
  |(l,r)::q -> if (v = l || v = r) then true
    else
      occurcheck v q



let rec robinson l = match l with
  |[] -> []
  |(TyVar(x),TyVar(t))::q -> if x = t then robinson q
    else failwith "failure"
  |(TyArrow(x1, x2), TyArrow(t1, t2))::q | (TyTimes(x1, x2), TyTimes(t1, t2))::q -> (t1, x2)::(x1, t2)::(robinson q)
  |(TyArrow(x1, x2), TyVar(v))::q -> if occurcheck (TyVar v) q then failwith "failure tyarrow"
    else
      substi x1 (TyVar v) l      
  |_ -> l


let rec addvartype exprl = match exprl with
  |l, Lam(var, None, el) -> l, Lam(var, Some (TyVar genlab), el)



let rec typing_expr c expl = match expl with
  |l, Var(v) -> TyVar v
  |l, App(el1, el2) -> TyArrow ((typing_expr c el1), (typing_expr c el2))
  |l, Lam(var, tyop, el) -> failwith "todo"
  |l, Pair(el1, el2) -> TyTimes(typing_expr c el1, typing_expr c el2)
  |l, LetIn(var, el1, el2) -> failwith "todo"
  |l, Fix(el) -> typing_expr c el
  |l, Int(n) -> TyInt
  |l, Bool(b) -> TyBool
  |l, Proj(ele) -> (match ele with
        |Left(l, Pair(e1, e2)) -> typing_expr c e1
        |Right(l, Pair(e1, e2)) -> typing_expr c e2
        |_ -> failwith "typage impossible")    
  |l, Ite(el1, el2, el3) -> if (typing_expr c el1 = TyBool) then
      (let e2 = typing_expr c el2 in
      let e3 = typing_expr c el3 in
       if (e2 = e3) then e2
       else
      failwith "boo")
    else
      (failwith "uncorrect type!")      
  |l, Binop(bin, el1, el2) -> if ( (typing_expr c el1 = TyInt) && (typing_expr c el2 = TyInt))then
      TyInt
    else
      failwith "uncorrect type!"
  |l, Unit -> TyUnit 



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


                  
                  
let rec typing_ast (ast: Ast.t) = failwith "g,rk" (*let tl = (match ast with
  | [] -> []
  | (l, Let(va, tyop, expl))::q ->  (match tyop with
      |None -> (typing_expr expl)::(typing_ast q)
      |Some t -> (t)::(typing_ast q) )
  | (l, LetRec(va, tyop, expl))::q -> (match tyop wi((typing_expr expl) )::typing_ast q
  ) in Ok(tl)
                                                  *)
