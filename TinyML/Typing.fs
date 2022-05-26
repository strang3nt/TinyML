(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let search_tyvar (s : subst) (t : tyvar) : ty =
    let (_, y) = 
        try List.find (fun (x, _) -> t = x) s
        with :? System.Collections.Generic.KeyNotFoundException -> (1, TyVar(t))
    y

let rec apply_subst (s : subst) (t : ty): ty = 
    match t with
    | TyName (_) -> t
    | TyVar (x) -> search_tyvar s x
    | TyArrow (x, y) -> TyArrow(apply_subst s x, apply_subst s y)
    | TyTuple (x) -> TyTuple(List.map (apply_subst s) x)

let rec occurs (tvar : tyvar) (t : ty) : bool = 
    match t with
    | TyArrow (x, y) -> (occurs tvar x) || (occurs tvar y)
    | TyTuple (x::xs) -> (occurs tvar x) || (occurs tvar (TyTuple xs))
    | TyVar (x) -> tvar = x
    | _ -> false

let rec unify (t1 : ty) (t2 : ty) : subst =

    match t1, t2 with

    | TyName (x), TyName (y) when x = y -> []
    | TyName (_), TyName (_) -> type_error "unify: cannot unify different primitive types %s and %s" (pretty_ty t1) (pretty_ty t2)
    
    | TyTuple (x), TyTuple (y) when List.length(x) = 0 && List.length(y) = 0 -> []
    | TyTuple (x), TyTuple (y) when List.length(x) = List.length(y) -> 
        let s1 = unify (List.head x) (List.head y) 
        s1 @ unify
            (TyTuple (List.skip 1 x |> List.map (fun i -> apply_subst s1 i)))
            (TyTuple (List.skip 1 y |> List.map (fun i -> apply_subst s1 i)))
    | TyTuple (_), TyTuple (_) -> type_error "unify: tuples %s and %s have different lengths" (pretty_ty t1) (pretty_ty t2)
    
    | TyArrow (x, y), TyArrow (w, z) -> 
        let s1 = (unify x w)
        s1 @ (unify (apply_subst s1 y) (apply_subst s1 z))

    | TyVar(x), y when occurs x y -> type_error "unify: %s occurs in %s, thus they are not unifiable" (pretty_ty t1) (pretty_ty t2)
    | TyVar(x), y when t1 = y -> []
    | TyVar(x), y -> [(x, y)]

    | _, TyVar(_) -> unify t2 t1
    | _ -> type_error "unify: %s and %s are not unifiable" (pretty_ty t1) (pretty_ty t2)

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

(*
    -------------------------------
            type inference
    -------------------------------
*)

let gamma0 : ty env = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("+", TyArrow (TyInt, TyArrow (TyFloat, TyFloat)))
    ("+", TyArrow (TyFloat, TyArrow (TyInt, TyFloat)))
    ("+", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))

]

let gamma0_scheme_env : scheme env = List.map (fun (x, y) -> (x, Forall ([], y) )) gamma0

let mutable private tyvar_counter = -1;

let tyvar_generator () =
    tyvar_counter <- tyvar_counter + 1
    tyvar_counter

let tyvar_reset () = 
    tyvar_counter <- -1

let instantiate (Forall (tyvar_list, t)) : ty =
    let sub = List.map (fun x -> (x, TyVar(tyvar_generator()))) tyvar_list
    apply_subst sub t

let generalize (env : scheme env) (t : ty) : scheme = 
    let freevars_env = Set.fold (fun set (_, y) -> Set.union set (freevars_scheme y)) Set.empty (Set.ofList env)
    let freevars_t = freevars_scheme (Forall ([], t))
    Forall (Set.toList( Set.difference freevars_t freevars_env), t)

let apply_subst_to_env (s: subst) (env : scheme env) : scheme env=
    List.map (fun (x, Forall (l, t)) -> (x, Forall (l, apply_subst s t))) env // TODO: should I remove from free variables the types I am substituting?

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
        let tyvar_ = TyVar(tyvar_generator())
        let (t2, s) = typeinfer_expr ((x, Forall ([], tyvar_)) :: env) e
        let t1 = apply_subst s tyvar_
        TyArrow (t1, t2), s

    | Lambda (x, Some t1, e) ->
        let (t2, s) = typeinfer_expr ((x, Forall ([], t1)) :: env) e
        TyArrow (t1, t2), s

    | App (_) ->
        let tyvar_ = TyVar (tyvar_generator())
        let s1, s2, s3 = overload env e tyvar_
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
        let env1 = (f, Forall ([], TyVar (tyvar_generator())))::env
        let (t1, s1) = typeinfer_expr env1 e1
        let env2 = apply_subst_to_env s1 ((f, (generalize (apply_subst_to_env s1 env1) t1)) :: env)
        let (t2, s2) = typeinfer_expr env2 e2
        t2, compose_subst s1 s2

    | LetRec (f, Some tf, e1, e2) -> 
        let env0 = (f, Forall ([], tf)) :: env
        let (t1, _) = typeinfer_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "typeinfer_expr: let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "typeinfer_expr: let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typeinfer_expr env0 e2

    | IfThenElse (e1, e2, e3o) -> 
        let (t1, s1) = typeinfer_expr env e1
        if t1 <> TyBool then type_error "typeinfer_expr: if condition must be a bool, but got %s" (pretty_ty t1)
        let env1 = apply_subst_to_env s1 env
        let (t2, s2) = typeinfer_expr env1 e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "typeinfer_expr: if-then without else requires unit type in then branch, but got %s" (pretty_ty t2)
            TyUnit, compose_subst s2 s1
        | Some e3 ->
            let (t3, s3) = typeinfer_expr (apply_subst_to_env s2 env1) e3
            if t2 <> t3 then type_error "typeinfer_expr: type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t3, compose_subst s3 (compose_subst s2 s1)

    | Tuple ( el ) ->
        let (tr, sub) = List.fold (fun ((tl, s) : (ty list * subst)) (en : expr) -> 
            let (tn, sn) = typeinfer_expr (apply_subst_to_env s env) en
            tn::tl, compose_subst s sn) ([], []) el 
        TyTuple tr, sub

    | BinOp (e1, op, e2) when (List.exists (fun (x, _) -> op = x) gamma0) -> typeinfer_expr env (App ((App (Var op, e1)), e2))
    | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: binary operator %s not supported" op

    | UnOp (op, _) -> unexpected_error "typeinfer_expr: unary operator %s not supported" op

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
    
and overload (env : scheme env) (e : expr) (t : ty) : subst * subst * subst =
    match e with
    | App (App (Var x, e3), e2) -> 

        let rec remove_nth pred n lst =
            match lst, n with
            | (h::t, 1) when pred h -> t
            | (h::t, _) when pred h -> remove_nth pred (n-1) t
            | (h::t, _) -> h::remove_nth pred n t
            | _ -> []
        let mutable (s1_, s2_, s3_) = [], [], []
        let m = (List.filter (fun (y, _) -> y = x) env).Length
        let tyvar_ = TyVar (tyvar_generator())
        let mutable continueLooping = true
        let mutable i = 0 
        while continueLooping do
            let env_ = if (i > 0) then remove_nth (fun ((es, _) : string * scheme) -> es = x) i env else env
            let t0, s0 = typeinfer_expr env_ (Var x)
            let (t1, s1) = typeinfer_expr (apply_subst_to_env s0 env) e3
            let unified_s1_s0 = 
                try 
                    unify (apply_subst s1 t0) (TyArrow (t1, tyvar_))
                with
                    | TypeError _  when i = m - 1 -> reraise()
                    | TypeError _ -> []
            if not unified_s1_s0.IsEmpty then
                let s0_s1_unified_s1_s0 = compose_subst s0 (compose_subst s1 unified_s1_s0)
                let (t2, s2) = typeinfer_expr (apply_subst_to_env s0_s1_unified_s1_s0 env) e2 
                s1_ <- s0_s1_unified_s1_s0
                s2_ <- s2
                s3_ <- 
                    try 
                        unify (apply_subst s2 (apply_subst s0_s1_unified_s1_s0 tyvar_)) (TyArrow (t2, t))
                    with
                        | TypeError _  when i = m - 1 -> reraise()
                        | TypeError _ -> []
            if s3_.IsEmpty then i <- i + 1 else continueLooping <- false

        s1_, s2_, s3_
        
    | App (e1, e2) -> 
        let (t1, s1) = typeinfer_expr env e1
        let (t2, s2) = typeinfer_expr (apply_subst_to_env s1 env) e2 
        s1, s2, unify (apply_subst s2 t1) (TyArrow (t2, t))

    | _ -> unexpected_error "typeinfer_expr: overload: function can only be called with an expression type: %s received" (pretty_expr e)

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
