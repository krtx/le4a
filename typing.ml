open Syntax

exception Error of string

let err s = raise (Error s)
let todo () = err "Not Implemented!"
let polymorphism = true

(* Type Environment *)
type tyenv = tysc Environment.t

(* --- typing algorithm --- *)

(* 型スキームの中で自由な型変数の集合 *)
let freevar_tysc (TyScheme (lst, ty)) =
  let rec search = function
    | TyVar x when not (List.mem x lst) ->
      TyvarSet.singleton x
    | TyList x -> (search x)
    | TyFun (x, y) ->
      TyvarSet.union (search x) (search y)
    | _ -> TyvarSet.empty
  in search ty

(* 型環境の中で自由な型変数の集合 *)
let rec freevar_tyenv (tyenv : tyenv) =
  Environment.fold_right
    (fun ty set ->
      TyvarSet.union (freevar_tysc ty) set)
    tyenv TyvarSet.empty

let make_fresh_tyvar () =
  let obj =
    let counter = ref 0 in
    let body () =
      let v = !counter in
      counter := v + 1; v
    in body
  in obj

let fresh_tyvar = make_fresh_tyvar ()

let rec freevar_ty (ty : ty) : TyvarSet.t =
  match ty with
    | TyFun (t1, t2) -> TyvarSet.union (freevar_ty t1) (freevar_ty t2)
    | TyVar x -> TyvarSet.singleton x
    | TyList t -> freevar_ty t
    | _ -> TyvarSet.empty

let rec subst_type (substitutes : subst) (ty : ty) : ty =
  let rec subst_once ((id, ty) as s) = function
    | TyFun (t1, t2) -> TyFun (subst_once s t1, subst_once s t2)
    | TyVar x -> if x = id then ty else TyVar x
    | TyList t -> TyList (subst_once s t)
    | _ as it -> it
  in
  match substitutes with
    | [] -> ty
    | s :: ss -> subst_type ss (subst_once s ty)

let freevar_tyenv_with_subst (tyenv : tyenv) subst =
  TyvarSet.fold
    (fun id s ->
      TyvarSet.union
        (freevar_ty (subst_type subst (TyVar id))) s)
    (freevar_tyenv tyenv) TyvarSet.empty

(*
  型 ty 中の自由変数で、
  型代入 subst を施した型環境 tyenv には自由には出現しない
  型変数たち　をもつ型スキーム
*)
let closure ty (tyenv : tyenv) subst : tysc =
  let ids =
    TyvarSet.diff (freevar_ty ty)
      (freevar_tyenv_with_subst tyenv subst)
  in
  TyScheme (TyvarSet.elements ids, ty)

(* 型代入を型の等式集合に変換 *)
let eqs_of_subst (s : subst) : (ty * ty) list =
  List.map (fun (tvar, ty) -> (TyVar tvar, ty)) s

(* 型の等式集合に型代入を適用 *)
let subst_eqs (s : subst) (eqs : (ty * ty) list) : (ty * ty) list =
  List.map (fun (t1, t2) -> (subst_type s t1, subst_type s t2)) eqs

let rec unify (eqs : (ty * ty) list) : (tyvar * ty) list =
  match eqs with
  | [] -> []
  | (t1, t2) :: rest -> begin
    match t1, t2 with
      | (_ as x), (_ as y) when x = y  -> unify rest
      | ((TyVar t) as x), (_ as y)
      | (_ as y), ((TyVar t) as x) when x <> y ->
        if TyvarSet.mem t (freevar_ty y) then err ("Type Error")
        else
          let s = (t, y) in
          let helper (a, b) = (subst_type [s] a, subst_type [s] b)
          in s :: (unify (List.map helper rest))
      | TyFun (t11, t12), TyFun (t21, t22) ->
        unify ([(t11, t21); (t12, t22)] @ rest)
      | TyList t1, TyList t2 -> unify ([(t1, t2)] @ rest)
      | _, _ -> err ("Type Error")
  end

let primitives =
  let tbl = Hashtbl.create 100 in
  Hashtbl.add tbl "="
    (let t = fresh_tyvar () in
     TyScheme ([t], TyFun (TyVar t, TyFun (TyVar t, TyBool))));
  Hashtbl.add tbl "<"
    (TyScheme ([], TyFun (TyInt, TyFun (TyInt, TyBool))));
  Hashtbl.add tbl ">"
    (TyScheme ([], TyFun (TyInt, TyFun (TyInt, TyBool))));
  Hashtbl.add tbl "+"
    (TyScheme ([], TyFun (TyInt, TyFun (TyInt, TyInt))));
  Hashtbl.add tbl "-"
    (TyScheme ([], TyFun (TyInt, TyFun (TyInt, TyInt))));
  Hashtbl.add tbl "*"
    (TyScheme ([], TyFun (TyInt, TyFun (TyInt, TyInt))));
  Hashtbl.add tbl "/"
    (TyScheme ([], TyFun (TyInt, TyFun (TyInt, TyInt))));
  Hashtbl.add tbl "&&"
    (TyScheme ([], TyFun (TyBool, TyFun (TyBool, TyBool))));
  Hashtbl.add tbl "||"
    (TyScheme ([], TyFun (TyBool, TyFun (TyBool, TyBool))));
  tbl


(* --- type inferrence --- *)

(*  id1 id2 ... = exp1  *)
let rec ty_bind tyenv (ids, exp) : subst * ty =
  if List.length ids = 1 then ty_exp tyenv exp
  else ty_fun tyenv (List.tl ids) exp

(*  bind1 and bind2 and ...  *)
and ty_let (tyenv : tyenv) letand : subst * tyenv =
  let rec collect = function
    | [] -> ([], [])
    | (idlst, exp) :: rest ->
      let (s, ty) = ty_bind tyenv (idlst, exp) in
      let (substs, id_and_tys) = collect rest in
      (substs @ s, (List.hd idlst, ty) :: id_and_tys)
  in
  let (s, id_and_tys) = collect letand in
  let subst = unify (eqs_of_subst s) in
  (subst,
   List.fold_left
     (fun env (id, ty) ->
       Environment.extend id (closure ty tyenv subst) env)
     tyenv id_and_tys)

(*
  let rec a b c = exp1 and x y z = exp2 and ...
  => [(a : t1), (x : t2), ...]
*)
and letrec_typing (tyenv : tyenv) letand =
  let rec collect_params (tyenv : tyenv) = function
    | [] ->
      let retty = TyVar (fresh_tyvar ()) in
      (retty, tyenv, retty)
    | id :: rest ->
      let (vars, env, retty) = collect_params tyenv rest in
      let domty = TyVar (fresh_tyvar ()) in
      (TyFun (domty, vars), Environment.extend id (TyScheme ([], domty)) env, retty)
  and collect_binds (tyenv : tyenv) = function
    | [] -> []
    | (bind, exp) :: rest ->
      let (funty, env, retty) = collect_params tyenv (List.tl bind) in
      let envs = collect_binds tyenv rest in
      (env, exp, List.hd bind, funty, retty) :: envs
  in
  let envs = collect_binds tyenv letand in
  let rec typing = function
    | [] -> []
    | (env, exp, id, fty, retty) :: rest ->
      let env =
        List.fold_left
          (fun env (_, _, id, funty, _) ->
            Environment.extend id (TyScheme ([], funty)) env)
          env envs
      in
      let (s, ty) = ty_exp env exp in
      let subst = typing rest in
      (ty, retty) :: ((eqs_of_subst s) @ subst)
  in
  let subst = unify (typing envs) in
  let id_tys =
    List.map
      (fun (_, _, id, funty, _) -> (id, subst_type subst funty)) envs
  in (subst, id_tys)

and ty_letrec (tyenv : tyenv) letand : subst * tyenv =
  let (subst, envs) = letrec_typing tyenv letand in
  let newenv =
    List.fold_left
      (fun env (id, ty) ->
        Environment.extend id (closure ty tyenv subst) env)
      tyenv envs
  in (subst, newenv)

(*  fun id1 id2 ... -> exp  *)
and ty_fun (tyenv : tyenv) ids exp : (subst * ty) =
  let (param_tys, env) =
    List.fold_left
      (fun (tys, env) id ->
        let domty = TyVar (fresh_tyvar ()) in
        (domty :: tys, Environment.extend id (TyScheme ([], domty)) env))
      ([], tyenv) ids
  in
  let (s, retty) = ty_exp env exp in
  let body_type =
    List.fold_left (fun ty param -> TyFun (param, ty)) retty param_tys
  in (s, subst_type s body_type)

and ty_pattern (tyenv : tyenv) pat : (subst * ty * tyenv) =
  match pat with
    | PVar id ->
      let domty = TyVar (fresh_tyvar ()) in
      ([], domty, Environment.extend id (TyScheme ([], domty)) tyenv)
    | PILit _ -> ([], TyInt, tyenv)
    | PBLit _ -> ([], TyBool, tyenv)
    | PNil -> ([], TyList (TyVar (fresh_tyvar ())), tyenv)
    | PCons (p1, p2)
    | POr (p1, p2) ->
      let (s1, t1, tyenv) = ty_pattern tyenv p1 in
      let (s2, t2, tyenv) = ty_pattern tyenv p2 in
      let eqs =
        (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(TyList t1, t2)]
      in let s = unify eqs in (s, subst_type s t2, tyenv)
    | _ -> todo ()

and ty_exp (tyenv : tyenv) (exp : exp) : (subst * ty) =
  match exp with
    | Var x ->
      let subst_poly (TyScheme (vars, ty)) =
        let s = List.map (fun id -> (id, TyVar (fresh_tyvar ()))) vars
        in subst_type s ty
      in
      (try ([], subst_poly (Environment.lookup x tyenv))
       with Environment.Not_bound ->
         try ([], subst_poly (Hashtbl.find primitives x))
         with Not_found ->err ("Variable not bound: " ^ x))
    | ILit _ -> ([], TyInt)
    | BLit _ -> ([], TyBool)
    | NilExp -> ([], TyList (TyVar (fresh_tyvar ())))
    | ConsExp (e1, e2) ->
      let (s1, t1) = ty_exp tyenv e1 and (s2, t2) = ty_exp tyenv e2 in
      let eqs =
        (eqs_of_subst s1) @ (eqs_of_subst s2) @ [(TyList t1, t2)]
      in let s = unify eqs in (s, subst_type s t2)
    | IfExp (e1, e2, e3) ->
      let (s1, t1) = ty_exp tyenv e1
      and (s2, t2) = ty_exp tyenv e2
      and (s3, t3) = ty_exp tyenv e3 in
      let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ (eqs_of_subst s3) @ [(t1, TyBool); (t3, t2)] in
      let s3 = unify eqs in (s3, subst_type s3 t2)
    | LetExp (binds, e) ->
      let (s, env) = ty_let tyenv binds in
      let (sbody, tybody) = ty_exp env e in
      let s = unify (eqs_of_subst (s @ sbody)) in
      (s, subst_type s tybody)
    | LetRecExp (binds, e) ->
      let (s, env) = ty_letrec tyenv binds in
      let (sbody, tybody) = ty_exp env e in
      let s = unify (eqs_of_subst (s @ sbody)) in
      (s, subst_type s tybody)
    | FunExp (ids, exp) -> ty_fun tyenv ids exp
    | AppExp (func, args) ->
      let (func_subst, func_type) = ty_exp tyenv func in
      let args = List.map (fun arg -> ty_exp tyenv arg) args in
      let retty = TyVar (fresh_tyvar ()) in
      let (ss, ty) =
        List.fold_left
          (fun (s, ty) (ps, pty) -> (ps @ s, TyFun (pty, ty)))
          ([], retty) (List.rev args) in
      let s = unify ((func_type, ty) :: (eqs_of_subst (ss @ func_subst))) in
      (s, subst_type s retty)
    | MatchExp (exp, lst) ->
      let (s, ty) = ty_exp tyenv exp in
      let retty = TyVar (fresh_tyvar ()) in
      let rec check_pattern = function
        | [] -> ([], ty, retty)
        | (pat, guard, exp) :: rest ->
          let (s1, pty, env) = ty_pattern tyenv pat in
          let (s2, gty) = ty_exp env guard
          and (s3, ety) = ty_exp env exp in
          let (substs, patty, expty) = check_pattern rest
          in
          (substs
           @ (eqs_of_subst s1)
           @ (eqs_of_subst s2)
           @ (eqs_of_subst s3)
           @ [(pty, patty); (gty, TyBool); (ety, expty)],
           pty, ety)
      in
      let (eqs, _, _) = check_pattern lst in
      let s = unify eqs in (s, subst_type s retty)
    | _ -> todo ()

(*  let bindlst1 let bindlst2 ...  *)
let ty_declet tyenv letlst : (id list * tyenv * ty list) =
  let ty_declet tyenv letand =
    let rec collect = function
      | [] -> ([], [])
      | (idlst, exp) :: rest ->
        let (s, ty) = ty_bind tyenv (idlst, exp) in
        let (substs, id_and_tys) = collect rest in
        (substs @ s, (List.hd idlst, ty) :: id_and_tys)
    in
    let (subst, id_and_tys) = collect letand in
    let subst = unify (eqs_of_subst subst) in
    List.fold_left
      (fun (ids, env, tys) (id, ty) ->
        (id :: ids,
         Environment.extend id (closure ty tyenv subst) env,
         ty :: tys))
      ([], tyenv, []) id_and_tys
  in
  List.fold_left
    (fun (ids, env, tys) letand ->
      let (ids', env', tys') = ty_declet env letand
      in (ids @ ids', env', tys @ tys'))
    ([], tyenv, []) letlst

let ty_decletrec (tyenv : tyenv) letlst =
  let ty_decletrec tyenv letand =
    let (subst, envs) = letrec_typing tyenv letand in
    List.fold_left
      (fun (ids, env, tys) (id, ty) ->
        let tysc = closure ty tyenv subst in
        (ids @ [id], Environment.extend id tysc env, tys @ [ty]))
      ([], tyenv, []) envs
  in
  List.fold_left
    (fun (ids, env, tys) letand ->
      let (ids', env', tys') = ty_decletrec env letand
      in (ids @ ids', env', tys @ tys'))
    ([], tyenv, []) letlst

let ty_decl' tyenv = function
  | Exp e -> let (_, ty) = ty_exp tyenv e in (["-"], tyenv, [ty])
  | Decl lst -> ty_declet tyenv lst
  | RecDecl lst -> ty_decletrec tyenv lst

let ty_decl tyenv program =
  let (_, tyenv, tys) = ty_decl' tyenv program
  in (tyenv, tys)
