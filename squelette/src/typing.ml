open Ast
open Genlab

type typing_error

let print_error fmt err = failwith "TO DO"


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
  |(TyArrow(x1, x2), TyVar(v))::q | (TyVar(v), TyArrow(x1, x2))::q -> if occurcheck (TyVar v) q then failwith "failure tyarrow"
    else
      substi x1 (TyVar v) l      
  |_ -> l

(* précise les types des variable d'une expression, permet notamment de présiser le type des lambda abstactions *)
let rec addvartype exprl = match exprl with
  |l, Lam(var, None, el) -> l, Lam(var, Some (TyVar genlab), addvartype el)
  |l, Lam(var, Some t, el) -> l, Lam(var, Some t, addvartype el)
  |l, Var(v) -> l, Var v
  |l, App(el1, el2) -> l, App(addvartype el1, addvartype el2)
  |l, Pair(el1, el2) -> l, Pair(addvartype el1, addvartype el2)
  |l, LetIn(var, el1, el2) -> l, LetIn(var, addvartype el1, addvartype el2)
  |l, Fix(el) -> l, Fix(addvartype el)
  |l, Int(n) -> l, Int(n)
  |l, Bool(b) -> l, Bool(b)
  |l, Proj(Left(ele)) -> l, Proj(Left (addvartype ele))
  |l, Proj(Right(ele)) -> l, Proj(Right (addvartype ele))
  |l, Ite(el1, el2, el3) -> l, Ite(addvartype el1, addvartype el2, addvartype el3) 
  |l, Binop(bin, el1, el2) -> l, Binop(bin, addvartype el1, addvartype el2)
  |l, Unit -> l, Unit  

(* rajoute des contraintes de type à une liste de contraintes, initialement vide *)
let rec contrainte context expl lc = match expl with
  |l, Var(v) ->  List.assoc v context, lc
  |l, Lam(var, Some t, el) -> let t', lc' = contrainte ((var,t)::context) el lc in
    TyArrow(t, t'), lc'
  |l, App(el1, el2) -> let t1, lc1 = contrainte context el1 lc in
    let t2, lc2 = contrainte context el2 lc1 in
    let v = Genlab.genlab in 
    TyVar(v), (t1, TyArrow(t2, TyVar(v)))::lc2
  |l, Pair(el1, el2) -> let t1, lc1 = contrainte context el1 lc in
    let t2, lc2 = contrainte context el2 lc1 in
    TyTimes(t1, t2), lc2
  |l, LetIn(var, el1, el2) -> let t1, lc1 = contrainte context el1 lc in
    let t2, lc2 = contrainte context el2 lc1 in
    t2, (t1, t2)::lc2
  |l, Fix(el) ->  let t1, lc1 = contrainte context el lc in
    t1, lc1
  |l, Int(n) -> TyInt, lc
  |l, Bool(b) -> TyBool, lc
  |l, Proj(Left(ele)) -> let t', lc' = contrainte context ele lc in
    t', lc
  |l, Proj(Right(ele)) ->  let t', lc' = contrainte context ele lc in
    t', lc
  |l, Ite(el1, el2, el3) ->  let t1, lc1 = contrainte context el1 lc in
    let t2, lc2 = contrainte context el2 lc1 in
    let t3, lc3 = contrainte context el3 lc2 in
    t2, (t2,t3)::(t1, TyBool)::lc3    
  |l, Binop(bin, el1, el2) -> let t1, lc1 = contrainte context el1 lc in
    let t2, lc2 = contrainte context el2 lc1 in
    TyInt, (t1, TyInt)::(t2, TyInt)::lc2
  |l, Unit -> TyUnit, lc
  |_,_ -> failwith "impossible"

(* permet d'associer les variables à leur type à partir de la liste de contraintes construite précédemment *)
let rec inter typ lcont = match typ with
  |TyVar(v) -> List.assoc (TyVar v) lcont
  |TyInt -> TyInt
  |TyBool -> TyBool
  |TyArrow(e1, e2) -> TyArrow(inter e1 lcont, inter e2 lcont)
  |TyTimes(e1, e2) -> TyTimes (inter e1 lcont, inter e2 lcont)
  |TyUnit -> TyUnit


(* permet le typage d'une expression à partir du contexte c dans lequel ses variables sont*)
let typing_expr c expl = let ex = addvartype expl in
  let ty, contr = contrainte c ex [] in
  let unif = robinson contr in
  let replace = inter ty unif in
  replace

(* type les commandes *)
let typing_commande c cmd = match cmd with
  |Let(va, tyop, expl) -> typing_expr c expl
  |LetRec(va, tyop, expl) -> typing_expr c expl
                 
                  
let rec typing_ast (ast: Ast.t) = failwith "ne marche pas" (*let tl = (match ast with
  | [] -> []
  | (l, Let(va, tyop, expl))::q ->  (match tyop with
      |None -> (typing_expr expl)::(typing_ast q)
      |Some t -> (t)::(typing_ast q) )
  | (l, LetRec(va, tyop, expl))::q -> (match tyop ((typing_expr expl) )::typing_ast q

  ) in Ok(tl)
                                                  
                                  *)
