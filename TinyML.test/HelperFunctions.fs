module TinyML.test.helpers

open TinyML.Ast
open TinyML.Typing

let rec printSubst (s : subst) = 
    match s with
    | [] -> ""
    | (_tyvar, _ty) :: rest -> sprintf "[%d , %s] %s" _tyvar (pretty_ty _ty) (printSubst rest)
