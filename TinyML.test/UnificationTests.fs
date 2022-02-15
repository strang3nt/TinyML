module TinyML.test.unification

open NUnit.Framework
open TinyML.Ast
open TinyML.Typing

let rec printSubst (subst : subst) = 
    match subst with
    | [] -> ""
    | ((_tyvar, _ty) :: rest) -> sprintf "[%d , %s] , %s" _tyvar (pretty_ty _ty) (printSubst rest)

[<Test>]
let Test1_unify () =
    let t1 = TyName ("Int")
    let t2 = TyVar (1)
    let subst = unify t1 t2
    Assert.AreEqual(1, List.length(subst), printSubst subst) 

[<Test>]
let Test2_unify () =
    let t1 = TyArrow(TyVar(1), TyVar(2))
    let t2 = TyArrow(TyVar(3), TyVar(4))
    let subst = unify t1 t2
    Assert.AreEqual(2, List.length(subst)) 
    CollectionAssert.AreEqual(subst, [(1, TyVar(3)); (2, TyVar(4))], printSubst subst)
