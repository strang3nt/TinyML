module TinyML.Tests.Composesubst

open NUnit.Framework
open TinyML.Tests.Helpers
open TinyML.Ast
open TinyML.Typing

[<Test>]
let Test1_compositionSubst () =
    let t = TyArrow(TyVar 1, TyVar 2)
    let s1 = [(2, TyArrow(TyVar 3, TyInt))]
    let s2 = [(1, TyBool); (3, TyFloat)]
    let s3_expected = [(2, TyArrow(TyFloat, TyInt)); (1, TyBool); (3, TyFloat)]
    let s3_actual = compose_subst s1 s2
    CollectionAssert.AreEqual(s3_expected, s3_actual, "Expected " + (printSubst s3_expected) + " is different from actual " + (printSubst s3_actual))
