(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1 with
    | TyName (x) ->
        match t2 with
        | TyName (y) -> 
            if x = y 
            then [] 
            else type_error "Cannot unify different primitive types %s and %s" (pretty_ty t1) (pretty_ty t2)
        | TyVar (y) -> [(y, t1)] (* Here the substitution work the opposite way, substitute t1 with y *)
        | _ -> type_error "Cannot unify primitive type %s with %s" (pretty_ty t1) (pretty_ty t2)
    | TyVar (x) ->
        match t2 with
        | TyName (y) -> unify t2 t1
        | TyVar (y) -> [(x, t2)]
        | _ -> type_error "Cannot unify type variable %s with $s" (pretty_ty t1) (pretty_ty t2)
    | TyTuple (x1::x) ->
        match t2 with
        | TyTuple (y1::y) -> 
            if List.length(x) = List.length(y) 
            then (unify x1 y1) @ (unify (TyTuple x) (TyTuple y))
            else type_error "%s and %s have different lengths thus they are not unifiable" (pretty_ty t1) (pretty_ty t2)
        | _ -> type_error "Cannot unify Tuple type %s with non tuple type %s" (pretty_ty t1) (pretty_ty t2)
    | TyArrow (x, y) ->
        match t2 with
        | TyArrow (w, z) -> (unify x w) @ (unify y z)
        | _ -> type_error "Cannot unify Arrow type %s with non arrow type %s" (pretty_ty t1) (pretty_ty t2)
    | _ -> type_error "%s not implemented" (pretty_ty t1)

// TODO implement this
// TODO check, just a scheleton
let rec apply_subst (s : subst) (t : ty): ty = 
    match t with
    | TyVar (_) -> TyVar (check_against s t)
    | TyArrow (x, y) -> TyArrow(apply_subst s x, apply_subst s y)
    | TyTuple (x) -> TyTuple(List.map (apply_subst s) x)
    | _ -> type_error "apply_subst: cannot apply substitution to primitive type %s" (pretty_ty t)
(* check_against finds the first tyvar for which t : ty is in s : subst *)
and check_against (s : subst) (t : ty) : tyvar =
    let x, _ = List.find (fun (_, t_) -> t_ = t) s
    x
    
// TODO implement this
(* 
    case 1: different tyvars for the same ty s
    case 2: different ty s for the same tyvars
*)
let compose_subst (s1 : subst) (s2 : subst) : subst =
    s1 @ s2 |> List.distinctBy (fun (_,y) -> y)

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

// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    failwith "not implemented"


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
