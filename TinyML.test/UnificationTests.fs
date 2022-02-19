module TinyML.test.unification

open NUnit.Framework
open TinyML.test.helpers
open TinyML.Ast
open TinyML.Typing

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
    CollectionAssert.AreEqual(subst, [(1, TyVar(3)); (2, TyVar(4))], printSubst subst)

[<Test>]
let Test3_occurrence () = 
    let tyvar_ = 1
    let t1 = TyArrow(TyVar(1), TyVar(2))
    let t2 = TyTuple ([TyInt; t1])
    let t3 = TyTuple ([TyString; t2])
    let t4 = TyArrow(TyVar(3), TyVar(2))
    Assert.True((occurs tyvar_ t1))
    Assert.True((occurs tyvar_ t2))
    Assert.True((occurs tyvar_ t3))
    Assert.False((occurs tyvar_ t4))

let assert_equality_unification (t1 : ty) (t2 : ty) =
    let s = unify t1 t2
    Assert.AreEqual(t2, (apply_subst s t1), "Unifier:" + printSubst s + "\n Type 1:" + (pretty_ty t1) + "\n Type 2:" + (pretty_ty t2))

[<Test>]
let Test4_completeUnification () =
    let mutable t1 = TyArrow(TyVar(1), TyVar(2))
    let mutable t2 = TyArrow(TyVar(3), TyVar(4))
    assert_equality_unification t1 t2

    t1 <- TyVar 3
    Assert.Throws<TypeError>(fun () -> unify t1 t2 |> ignore) |> ignore

    t1 <- TyTuple ([TyVar(1); TyVar(2)])
    t2 <- TyTuple ([TyVar(3); TyVar(4)])
    assert_equality_unification t1 t2
