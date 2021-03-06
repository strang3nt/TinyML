(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let search_tyvar (s : subst) (t : tyvar) : ty =
    match List.tryFind (fun (x, _) -> t = x) s with
    | Some (_, y) -> y
    | _ -> TyVar(t)

let rec apply_subst (s : subst) (t : ty): ty = 
    match t with
    | TyName _ -> t
    | TyVar x -> search_tyvar s x
    | TyArrow (x, y) -> TyArrow(apply_subst s x, apply_subst s y)
    | TyTuple x -> TyTuple(List.map (apply_subst s) x)

let rec occurs (tvar : tyvar) (t : ty) : bool = 
    match t with
    | TyArrow (x, y) -> (occurs tvar x) || (occurs tvar y)
    | TyTuple (x::xs) -> (occurs tvar x) || (occurs tvar (TyTuple xs))
    | TyVar x -> tvar = x
    | _ -> false

let rec unify (t1 : ty) (t2 : ty) : subst =

    match t1, t2 with

    | TyName x, TyName y when x = y -> []
    | TyName _, TyName _ -> type_error "unify: cannot unify different primitive types %s and %s" (pretty_ty t1) (pretty_ty t2)
    
    | TyTuple x, TyTuple y when List.length(x) = 0 && List.length(y) = 0 -> []
    | TyTuple x, TyTuple y when List.length(x) = List.length(y) -> 
        let s1 = unify (List.head x) (List.head y) 
        s1 @ unify
            (TyTuple (List.skip 1 x |> List.map (fun i -> apply_subst s1 i)))
            (TyTuple (List.skip 1 y |> List.map (fun i -> apply_subst s1 i)))
    | TyTuple _, TyTuple _ -> type_error "unify: tuples %s and %s have different lengths" (pretty_ty t1) (pretty_ty t2)
    
    | TyArrow (x, y), TyArrow (w, z) -> 
        (unify x w)
        |> fun s1 -> s1 @ (unify (apply_subst s1 y) (apply_subst s1 z))

    | TyVar x, y when occurs x y -> type_error "unify: %s occurs in %s, thus they are not unifiable" (pretty_ty t1) (pretty_ty t2)
    | TyVar _, y when t1 = y -> []
    | TyVar x, y -> [(x, y)]

    | _, TyVar _ -> unify t2 t1
    | _ -> type_error "unify: %s and %s are not unifiable" (pretty_ty t1) (pretty_ty t2)

let compose_subst (s1 : subst) (s2 : subst) : subst =
    s1
    |> List.map (fun (y, x) -> (y, apply_subst s2 x))
    |> fun s1_applied -> List.append s1_applied s2
    |> List.distinctBy fst

(* from a type gets type variables *)
let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

(* from a type scheme gets bounded type variables *)
let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

(*
    -------------------------------
            type inference
    -------------------------------
*)

let gamma0 : ty env = [

    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("+", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("+", TyArrow (TyInt, TyArrow (TyFloat, TyFloat)))
    ("+", TyArrow (TyFloat, TyArrow (TyInt, TyFloat)))
    
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("-", TyArrow (TyFloat, TyArrow (TyInt, TyFloat)))
    ("-", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))

    ("=", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    ("=", TyArrow (TyFloat, TyArrow (TyFloat, TyBool)))
    ("=", TyArrow (TyFloat, TyArrow (TyInt, TyBool)))
    ("=", TyArrow (TyFloat, TyArrow (TyFloat, TyBool)))

    ("<", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    ("<", TyArrow (TyFloat, TyArrow (TyFloat, TyBool)))
    ("<", TyArrow (TyFloat, TyArrow (TyInt, TyBool)))
    ("<", TyArrow (TyFloat, TyArrow (TyFloat, TyBool)))

    ("<=", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    ("<=", TyArrow (TyFloat, TyArrow (TyFloat, TyBool)))
    ("<=", TyArrow (TyFloat, TyArrow (TyInt, TyBool)))
    ("<=", TyArrow (TyFloat, TyArrow (TyFloat, TyBool)))

]

let gamma0_scheme_env : scheme env = List.map (fun (x, y) -> (x, Forall ([], y) )) gamma0

let mutable private tyvar_counter = -1;

let tyvar_generator () =
    tyvar_counter <- tyvar_counter + 1
    tyvar_counter

let tyvar_reset () = 
    tyvar_counter <- -1

let instantiate (Forall (tyvar_list, t)) : ty =
    tyvar_list
    |> List.map (fun x -> (x, TyVar(tyvar_generator())))
    |> fun sub -> apply_subst sub t

let generalize (env : scheme env) (t : ty) : scheme = 
    env
    |> Set.ofList
    |> Set.fold (fun acc (_, y) -> Set.union acc (freevars_scheme y)) Set.empty
    |> fun freevars_env -> Forall (Set.toList (Set.difference (freevars_ty t) freevars_env), t)

let apply_subst_to_env (s: subst) (env : scheme env) : scheme env =
    s
    |> List.map fst
    |> fun boundVars ->
        // remove from free variables the types I am substituting
        env
        |> List.map (fun (x, Forall (l, t)) ->
            let l = Set.difference (set l) (set boundVars) |> Set.toList 
            (x, Forall (l, apply_subst s t)))

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
        match List.tryFind(fun (y, _) -> y = x) env with
        | Some (_, s1) -> instantiate s1, []
        | _ -> type_error "typeinfer_expr: variable %s is not defined in the environment" x
        
    | Lambda (x, None, e)  ->
        let tyvar = TyVar(tyvar_generator())
        let t2, s = typeinfer_expr ((x, Forall ([], tyvar)) :: env) e
        let t1 = apply_subst s tyvar
        TyArrow (t1, t2), s

    | Lambda (x, Some t1, e) ->
        let t2, s = typeinfer_expr ((x, Forall ([], t1)) :: env) e
        TyArrow (t1, t2), s

    | App (App (Var ("+" | "-" | "=" | "<" | "<=" as x), e3), e2) ->
        let rec remove_nth pred n lst =
            match lst, n with
            | h::t, 1 when pred h -> t
            | h::t, _ when pred h -> remove_nth pred (n-1) t
            | h::t, _ -> h::remove_nth pred n t
            | _ -> []
        // let mutable s1_, s2_, s3_ = [], [], []
        let m = (List.filter (fun (y, _) -> y = x) env).Length - 1
        let tv1 = TyVar (tyvar_generator())
        let tv2 = TyVar (tyvar_generator())
        let rec overloading i =
            let env_ = if (i > 0) then remove_nth (fun ((es, _) : string * scheme) -> es = x) i env else env
            let t0, _ = typeinfer_expr env_ (Var x)
            let t1, s1 = typeinfer_expr env e3
            
            try
                let unified_s1_s0 = unify (apply_subst s1 t0) (TyArrow (t1, tv1))
                let s0_s1_unified_s1_s0 = compose_subst s1 unified_s1_s0
                let t2, s2 = typeinfer_expr (apply_subst_to_env s0_s1_unified_s1_s0 env) e2
                s0_s1_unified_s1_s0, s2, unify (apply_subst s2 (apply_subst s0_s1_unified_s1_s0 tv1)) (TyArrow (t2, tv2))
            with
                | TypeError _ when i = m -> type_error "Couldn't find compatible types for operator %s: found type %s for the left operand" x (pretty_ty t1)
                | TypeError _ -> overloading (i + 1)
        let s1, s2, s3 = overloading 0
        let s1_s2_s3 = compose_subst s1 (compose_subst s2 s3)
        apply_subst s1_s2_s3 tv2, s1_s2_s3

    | App (e1, e2) ->
        let tyvar = TyVar (tyvar_generator())
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr (apply_subst_to_env s1 env) e2 
        let s3 = unify (apply_subst s2 t1) (TyArrow (t2, tyvar))
        let s1_s2_s3 = compose_subst s1 (compose_subst s2 s3)
        apply_subst s1_s2_s3 tyvar, s1_s2_s3

    | Let(x, Some decl_type, e1, _) when fst (typeinfer_expr env e1) <> decl_type -> type_error "typeinfer_expr: type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty decl_type ) (pretty_ty (fst (typeinfer_expr env e1)))
    | Let (x, _, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s = generalize (apply_subst_to_env s1 env) t1
        let env2 = apply_subst_to_env s1 ((x, s) :: env)
        let t2, s2 = typeinfer_expr env2 e2
        t2, compose_subst s1 s2

    | LetRec (f, None, e1, e2) ->
        let env = (f, Forall ([], TyVar (tyvar_generator()))) :: env
        let t1, s1 = typeinfer_expr env e1
        let env = apply_subst_to_env s1 ((f, (generalize (apply_subst_to_env s1 env) t1)) :: env)
        let t2, s2 = typeinfer_expr env e2
        t2, compose_subst s1 s2

    | LetRec (f, Some tf, e1, e2) -> 
        let env = (f, Forall ([], tf)) :: env
        let t1, _ = typeinfer_expr env e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "typeinfer_expr: let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "typeinfer_expr: let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typeinfer_expr env e2

    // | IfThenElse (e1, _, _) when fst (typeinfer_expr (apply_subst_to_env ) e1) <> TyBool -> type_error "typeinfer_expr: if condition must be bool, but got %s" (pretty_ty (fst (typeinfer_expr env e1)))
    | IfThenElse (e1, e2, e3o) -> 
        let t1, s1 = typeinfer_expr env e1
        let s1' = unify t1 (TyBool)
        let s1 = compose_subst s1 s1'
        let env = apply_subst_to_env s1 env
        let t2, s2 = typeinfer_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "typeinfer_expr: if-then without else requires unit type in then branch, but got %s" (pretty_ty t2)
            TyUnit, compose_subst s2 s1
        | Some e3 ->
            let t3, s3 = typeinfer_expr (apply_subst_to_env s2 env) e3
            if t2 <> t3 then type_error "typeinfer_expr: type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t3, compose_subst s3 (compose_subst s2 s1)

    | Tuple el ->
        el
        |> List.fold (fun ((tl, s) : ty list * subst) (en : expr) -> 
            let tn, sn = typeinfer_expr (apply_subst_to_env s env) en in tn::tl, compose_subst s sn) 
            ([], [])
        |> fun (tr, sub) -> TyTuple tr, sub

    | BinOp (e1, op, e2) when (List.exists (fun (x, _) -> op = x) gamma0) -> typeinfer_expr env (App ((App (Var op, e1)), e2))

    | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: binary operator %s not supported" op

    | UnOp (op, _) -> unexpected_error "typeinfer_expr: unary operator %s not supported" op

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

(* 
   ------------------
    type checking
   ------------------
*)
    
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

    | Lambda (_, None, _) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
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

    | LetRec (_, None, _, _) ->
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
