﻿(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

(* returns the tyvar itself when there is no correspondence *)
let search_tyvar (s : subst) (t : tyvar) : ty =
    let (_, y) = 
        try List.find (fun (x, _) -> t = x) s
        with :? System.Collections.Generic.KeyNotFoundException -> (1, TyVar(t))
    y

(*
    IDEA: search for suitable substitutions of t and return updated t
    go through each term of t and search wether if each term is a tyvar and if it is indexed in s
*)
let rec apply_subst (s : subst) (t : ty): ty = 
    match t with
    | TyName (_) -> t
    | TyVar (x) -> search_tyvar s x
    | TyArrow (x, y) -> TyArrow(apply_subst s x, apply_subst s y)
    | TyTuple (x) -> TyTuple(List.map (apply_subst s) x)

(*
    check if tyvar tvar occurs in ty t if true return true else return false.
*)
let rec occurs (tvar : tyvar) (t : ty) : bool = 
    match t with
    | TyArrow (x, y) -> (occurs tvar x) || (occurs tvar y)
    | TyTuple (x::xs) -> (occurs tvar x) || (occurs tvar (TyTuple xs))
    | TyVar (x) -> tvar = x
    | _ -> false

let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName (x), TyName (y) ->
        if x = y 
        then [] 
        else type_error "unify: cannot unify different primitive types %s and %s" (pretty_ty t1) (pretty_ty t2)
    | TyTuple (x), TyTuple (y) -> 
        if List.length(x) = 0 && List.length(y) = 0
        then []
        else if List.length(x) = List.length(y)
        then 
            let s1 = unify (List.head x) (List.head y) 
            s1 @ unify
                (TyTuple (List.skip 1 x |> List.map (fun i -> apply_subst s1 i)))
                (TyTuple (List.skip 1 y |> List.map (fun i -> apply_subst s1 i)))
        else type_error "unify: tuples %s and %s have different lengths" (pretty_ty t1) (pretty_ty t2)
    | TyArrow (x, y), TyArrow (w, z) -> 
        let s1 = (unify x w)
        s1 @ (unify (apply_subst s1 y) (apply_subst s1 z))
    | TyVar(x), y -> 
        if occurs x y 
        then type_error "unify: %s occurs in %s, thus they are not unifiable" (pretty_ty t1) (pretty_ty t2)
        else if TyVar(x) = y then [] else [(x, y)]
    | _, TyVar(_) -> unify t2 t1
    | _ -> type_error "unify: %s and %s are not unifiable" (pretty_ty t1) (pretty_ty t2)

(* 
    Compose two substitutions S1 and S2 
    by applying S1 to all the substitute types in S2, 
    then add in any substitutions in S1 
    unless S2 already has a substitute for that variable.
*)
let compose_subst (s1 : subst) (s2 : subst) : subst =
    let s2_applied = List.map (fun (y, x) -> (y, apply_subst s2 x)) s1 
    let s2_filtered = List.filter (fun (x, _) -> not (List.exists (fun (y, _) -> x = y) s2_applied)) s2
    s2_applied @ s2_filtered

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

// type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))

]

let gamma0_scheme_env = List.map (fun (x, y) -> (x, Forall ([], y) )) gamma0

let mutable private tyvar_counter = -1;

let tyvar_generator = tyvar_counter <- tyvar_counter + 1; tyvar_counter

let instantiate (Forall (tyvar_list, t)) : ty =
    let sub = List.map (fun x -> (x, TyVar(tyvar_generator))) tyvar_list
    apply_subst sub t

// the list of all type variables appearing in the type that don't appear in the type environment
let generalize (env : scheme env) (t : ty) : scheme = 
    let freevars_env = Set.fold (fun set (x, y) -> Set.union set (freevars_scheme y)) Set.empty (Set.ofList env)
    let freevars_t = freevars_scheme (Forall ([], t))
    Forall (Set.toList( Set.difference freevars_t freevars_env), t)

let apply_subst_to_env (s: subst) (env : scheme env) : scheme env=
    List.map (fun (x, Forall (l, t)) -> (x, Forall (l, apply_subst s t))) env

// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, []
    | Lit (LFloat _) -> TyFloat, []
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, []
    | Lit (LBool _) -> TyBool, []
    | Lit LUnit -> TyUnit, []
    | Var x -> 
        let (_, s1) = 
            try List.find(fun (y, _) -> y = x) env
            with :? System.Collections.Generic.KeyNotFoundException -> type_error "typeinfer_expr: variable %s is not defined" x
        instantiate s1, []

    | Lambda (x, None, e)  ->
        let tyvar_ = TyVar(tyvar_generator)
        let (t2, s) = typeinfer_expr ((x, Forall ([], tyvar_)) :: env) e
        let t1 = apply_subst s tyvar_
        TyArrow (t1, t2), s

    | Lambda (x, Some t1, e) ->
        let (t2, s) = typeinfer_expr ((x, Forall ([], t1)) :: env) e
        TyArrow (t1, t2), s

    | App (e1, e2) ->
        let tyvar_ = TyVar (tyvar_generator)
        let (t1, s1) = typeinfer_expr env e1
        let (t2, s2) = typeinfer_expr (apply_subst_to_env s1 env) e2
        let s3 = unify (apply_subst s2 t1) (TyArrow (t2, tyvar_))
        let s1_s2_s3 = compose_subst s1 (compose_subst s2 s3)
        apply_subst s1_s2_s3 tyvar_, s1_s2_s3

    | Let (x, t, e1, e2) ->
        let (t1, s1) = typeinfer_expr env e1
        match t with
        | None -> ()
        | Some decl_type -> if t1 <> decl_type then type_error "typeinfer_expr: type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty decl_type ) (pretty_ty t1)
        let s = generalize (apply_subst_to_env s1 env) t1
        let env2 = apply_subst_to_env s1 ((x, s) :: env)
        let (t2, s2) = typeinfer_expr env2 e2
        t2, compose_subst s1 s2

    | LetRec (f, None, e1, e2) ->
        let env1 = (f, Forall ([], TyVar (tyvar_generator)))::env
        let (t1, s1) = typeinfer_expr env1 e1
        let env2 = apply_subst_to_env s1 ((f, (generalize (apply_subst_to_env s1 env1) t1)) :: env)
        let (t2, s2) = typeinfer_expr env2 e2
        t2, compose_subst s1 s2

    | LetRec (f, Some tf, e1, e2) -> 
        let env0 = (f, Forall ([], tf)) :: env
        let (t1, s1) = typeinfer_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "typeinfer_expr: let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "typeinfer_expr: let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typeinfer_expr env0 e2

    | _ -> unexpected_error "typeïnfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
    
// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
