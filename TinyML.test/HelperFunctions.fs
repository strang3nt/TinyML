module TinyML.test.helpers

open TinyML.Ast
open TinyML.Typing

let rec printSubst (subst : subst) = 
    match subst with
    | [] -> ""
    | (_tyvar, _ty) :: rest -> sprintf "[%d , %s] %s" _tyvar (pretty_ty _ty) (printSubst rest)
