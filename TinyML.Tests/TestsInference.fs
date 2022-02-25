module TinyML.Tests.Inference

open NUnit.Framework
open TinyML.Tests.Helpers
open TinyML.Ast
open TinyML.Typing

let s = gamma0_scheme_env

[<Test>]
let Test1_infer () = 
    let e = LetIn ((false, "id", None, Lambda ("x", None, Lambda ("y", None, Var "x"))), App (App (Var "id", Lit (LInt 3)), Lit (LInt 4))) 
    let (t, _) = typeinfer_expr s e
    Assert.AreEqual (t, TyInt)

[<Test>]
let Test2_var_generation () =
    tyvar_reset()
    tyvar_generator() |> ignore
    tyvar_generator() |> ignore
    Assert.AreEqual (2, tyvar_generator())
