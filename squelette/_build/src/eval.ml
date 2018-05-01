open Ast

let projsnd (t : Utils.loc*cmd) = let a, b = t in
  b

let projsndexp (e : Utils.loc * expr) = let a, b = e in
  b

  
let evalbinop bin context (expr1 : expr loc) (expr2 : expr loc)  = match bin, projsndexp(expr1), projsndexp(expr2) with
  |Plus, Int(n1), Int(n2) -> Int(n1 + n2)
  |Minus, Int(n1), Int(n2) -> Int(n1 - n2)
  |Times, Int(n1), Int(n2) -> Int(n1*n2)
  |Div, Int(n1), Int(n2) -> Int(n1/n2)
  |And, Bool(e1), Bool(e2) -> Bool(e1 && e2)
  |Or, Bool(e1), Bool(e2) -> Bool(e1 || e2)
  |Eq, e1, e2-> Bool(e1 = e2)
  |Gt, Int(n1), Int(n2) -> Bool(n1<n2)
  |_, _, _ -> failwith "opération non définie"

    


let rec evalexpr context (expr : expr loc) = match expr with
  |_, Var(v) -> List.assoc v context
  |_, App((_,Lam(var, _, el1)), el2) -> let e2 = evalexpr context el2 in
    evalexpr ((var, e2)::context) el1
  |c, App(el1, el2) -> let e1 = evalexpr context el1 in
    evalexpr context (c, (App((c, e1), el2)))    
  |c, Lam(va, tyop, el) ->  Lam(va, tyop, el)
  |c, Pair(el1, el2) -> let e1 = evalexpr context el1 in
    let e2 = evalexpr context el2 in
    Pair((c, e1), (c, e2))
  |c, LetIn(va, el1, el2) -> let e1 = evalexpr context el1 in
    evalexpr ((va, e1)::context) el2
  |l1, Fix(l2, (Lam(va, tyop, el))) -> evalexpr ((va, Fix(l2, Lam (va, tyop, el)))::context) el
  |_, Fix(el) ->  evalexpr context el
  |_, Int(n) -> Int(n)
  |_, Bool(b) -> Bool(b)
  |_, Proj(ele) -> (match ele with
    |Left(_, Pair(e1, e2)) -> evalexpr context e1
    |Right(_, Pair(e1, e2)) -> evalexpr context e2
    |_ -> failwith "unprojectable")
  |_, Ite(el1, el2, el3) -> if (evalexpr context el1) = Bool(true) then
      evalexpr context el2
    else
      evalexpr context el3
  |l, Binop(bin, el1, el2) -> evalbinop bin context (l, (evalexpr context el1)) (l, (evalexpr context el2))



let rec eval_cmds context (cmds : cmd loc) = match cmds with
  |(l, Let(va, tyop, exprloc)) -> (va, (evalexpr context exprloc))
  |(l, LetRec(va, tyop, exprloc)) -> (va, (evalexpr context (l, (Fix (l, (Lam(va, tyop, exprloc)))))))




let eval_ast (cmds : Ast.t) = let rec aux context cmds = match cmds with
  |[] -> context
  |t::q  -> (aux ((eval_cmds context t)::context) q)
  in
  aux [] cmds


    
