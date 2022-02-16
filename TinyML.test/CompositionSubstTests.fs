module TinyML.test.composesubst

open NUnit.Framework
open TinyML.test.helpers
open TinyML.Ast
open TinyML.Typing

[<Test>]
let Test1_composeSubst_diffTyVars () =
    let s1 = [(1, TyArrow(TyVar(7), TyInt)); (2, TyTuple([TyInt; TyInt])); (3, TyVar(3))]
    let s2 = [(4, TyVar(8)); (5, TyArrow(TyVar(7), TyInt)); (6, TyVar(3))]
    let v1 = [(1, TyArrow(TyVar(7), TyInt)); (2, TyTuple([TyInt; TyInt])); (3, TyVar(3)); (4, TyVar(8))]
    let v2 = compose_subst s1 s2
    CollectionAssert.AreEqual(v1, v2, printSubst v2)

let Test2_composeSubst_sameTyVars () =
    Assert.Fail("Not implemented")