open Syntax
open Format

type exval = 
  | IntV of int
  | BoolV of bool
  | ProcV of id list * exp * dnval Environment.t ref
  | DProcV of id list * exp
  | PrimV of string
  | NilV
  | ConsV of exval * exval
and dnval = exval

type match_status = Not_matched | Matched of dnval Environment.t

exception Error of string

let err s = raise (Error s)

module StringSet = Set.Make(String)

let primitives =
  let tbl = Hashtbl.create 100 in
  Hashtbl.add tbl "=" (fun x y -> BoolV (x = y));
  Hashtbl.add tbl "<"
    (fun x y -> match x, y with | IntV x, IntV y -> BoolV (x < y)
      | _, _ -> err "Both arguments must be integer: <");
  Hashtbl.add tbl ">"
    (fun x y -> match x, y with | IntV x, IntV y -> BoolV (x > y)
        | _, _ -> err "Both arguments must be integer: >");
  Hashtbl.add tbl "+"
    (fun x y -> match x, y with | IntV x, IntV y -> IntV (x + y)
        | _, _ -> err "Both arguments must be integer: +");
  Hashtbl.add tbl "-"
    (fun x y -> match x, y with | IntV x, IntV y -> IntV (x - y)
      | _, _ -> err "Both arguments must be integer: -");
  Hashtbl.add tbl "*"
    (fun x y -> match x, y with | IntV x, IntV y -> IntV (x * y)
      | _, _ -> err "Both arguments must be integer: *");
  Hashtbl.add tbl "/"
    (fun x y -> match x, y with
      | IntV x, IntV y when y != 0 -> IntV (x / y)
      | IntV x, IntV y when y = 0 -> err "Division by Zero"
      | _, _ -> err "Both arguments must be integer: /");
  Hashtbl.add tbl "&&"
    (fun x y -> match x, y with | BoolV x, BoolV y -> BoolV (x && y)
      | _, _ -> err "Both arguments must be bool: &&");
  Hashtbl.add tbl "||"
    (fun x y -> match x, y with | BoolV x, BoolV y -> BoolV (x || y)
      | _, _ -> err "Both arguments must be bool: ||");
  tbl


(* --- pretty printing --- *)
  
let listp = function ConsV _ | NilV -> true | _ -> false
let rec nilend = function ConsV (car, cdr) -> nilend cdr | NilV -> true | _ -> false

let pp_exval ppf value =
  let rec pp_exval ppf = function
    | IntV i -> fprintf ppf "%d" i
    | BoolV b -> fprintf ppf "%b" b
    | ProcV (idlst, exp, env) -> fprintf ppf "<fun>"
    | DProcV (idlst, exp) -> fprintf ppf "<dfun>"
    | ConsV (car, cdr) -> (
      match cdr with
        | NilV -> (match car with
            | ConsV _ when nilend car -> fprintf ppf "[%a]" pp_exval car
            | _ -> fprintf ppf  "%a"  pp_exval car
        )
        | ConsV _ when nilend cdr -> (match car with
            | ConsV _ when nilend car -> fprintf ppf "[%a]; %a" pp_exval car pp_exval cdr
            | ConsV _ | _ -> fprintf ppf "%a; %a" pp_exval car pp_exval cdr
        )
        | _ -> (match car with
            | ConsV _ when nilend car -> fprintf ppf "[%a] :: %a" pp_exval car pp_exval cdr
            | ConsV _ -> fprintf ppf "(%a) :: %a" pp_exval car pp_exval cdr
            | _ -> fprintf ppf "%a :: %a" pp_exval car pp_exval cdr
        )
    )
    | NilV -> fprintf ppf "[]"
    | PrimV f -> fprintf ppf "%s" f
  in match value with 
    | ConsV (_, _) ->
      if nilend value then fprintf ppf "[%a]" pp_exval value
      else fprintf ppf "%a" pp_exval value
    | _ -> fprintf ppf "%a" pp_exval value

let string_of_exval value =
  pp_exval str_formatter value; flush_str_formatter ()
let print_exval value = pp_exval std_formatter value


(* --- evaluation --- *)

let rec apply_prim op arg1 arg2 =
  try (Hashtbl.find primitives op) arg1 arg2 with Not_found -> err ("not found: " ^ op)

let rec eval_let env lets =
  List.fold_left
    (fun (ids, preenv, vs) (idlst, exp) ->
      if (List.length idlst) = 1
      then let v = eval_exp env exp and x = List.hd idlst in
           (ids @ [x], Environment.extend x v preenv, vs @ [v])
      else let v = ProcV (List.tl idlst, exp, ref env) and fn = List.hd idlst in
           (ids @ [fn], Environment.extend fn v preenv, vs @ [v]))
    ([], env, []) lets

and eval_reclet env lets =
  let dummyenv = ref Environment.empty in
  let (ids, newenv, vs) = 
    List.fold_left
      (fun (ids, preenv, vs) (idlst, exp) ->
        if (List.length idlst) = 1
        then
          let v = match eval_exp env exp with
              (* let rec fact = fun x -> ... の場合 *)
              ProcV (ids, exp, _) -> ProcV (ids, exp, dummyenv)
            | _ as whole -> whole
          and x = List.hd idlst in
             (ids @ [x], Environment.extend x v preenv, vs @ [v])
        else let v = ProcV (List.tl idlst, exp, dummyenv) and fn = List.hd idlst in
             (ids @ [fn], Environment.extend fn v preenv, vs @ [v]))
      ([], env, []) lets in
  dummyenv := newenv; (ids, newenv, vs)

and apply (env : dnval Environment.t) params body args =
  let rec app (env : dnval Environment.t) params = function
    | [] ->
      if (List.length params) = 0 then eval_exp env body
      else ProcV (params, body, ref env)
    | arg :: args as whole ->
      if (List.length params) > 0
      then app (Environment.extend (List.hd params) arg env) (List.tl params) args
      else
        (match eval_exp env body with
          | ProcV (params, body, env') -> apply !env' params body whole
          | DProcV (params, body) -> apply env params body whole
          | PrimV f when List.length args = 2 -> apply_prim f (List.nth args 0) (List.nth args 1)
          | _ -> err ("Non-function value is applied"))
  in app env params args

and eval_exp (env : dnval Environment.t) (exp : Syntax.exp) : dnval =
  match exp with 
    | Var x -> (
      try Environment.lookup x env
      with Environment.Not_bound ->
        if Hashtbl.mem primitives x then PrimV x
        else err ("Variable not bound: " ^ x)
    )
    | ILit i -> IntV i
    | BLit b -> BoolV b
    | NilExp -> NilV
    | IfExp (test, thenc, elsec) ->
      (match eval_exp env test with
        | BoolV true -> eval_exp env thenc 
        | BoolV false -> eval_exp env elsec
        | _ -> err ("Test expression must be boolean: if"))
    | LetExp (lst, exp) -> let (_, newenv, _) = eval_let env lst in eval_exp newenv exp
    | LetRecExp (lst, exp) -> let (_, newenv, _) = eval_reclet env lst in eval_exp newenv exp
    | FunExp (idlst, exp) -> ProcV (idlst, exp, ref env)
    | DFunExp (idlst, exp) -> DProcV (idlst, exp)
    | ConsExp (e1, e2) -> ConsV (eval_exp env e1, eval_exp env e2)
    | AppExp (func, args) ->
      let funval = eval_exp env func in
      let args = List.map (fun arg -> eval_exp env arg) args in
      (match funval with
        | ProcV (params, body, env') -> apply !env' params body args
        | DProcV (params, body) -> apply env params body args
        | PrimV f when List.length args = 2 -> apply_prim f (List.nth args 0) (List.nth args 1)
        | _ -> err ("Non-function value is applied"))
    | MatchExp (exp, lst) ->
      List.iter (fun (pat, _, exp) -> ignore (pattern_check pat)) lst;
      let matched_value = eval_exp env exp in
      let rec run_match = function
        | [] -> err ("Not matched")
        | (pat, guard, exp) :: xs -> (
          match pattern_match env matched_value pat with
            | Matched newenv -> (
              match eval_exp newenv guard with
                | BoolV true -> eval_exp newenv exp
                | BoolV false -> run_match xs
                | _ -> err ("Test expression must be boolean: when")
            )
            | _ -> run_match xs
        )
      in run_match lst

and pattern_match (env : dnval Environment.t) (value : exval) pattern =
  match value, pattern with
    |    _, Wildcard -> Matched env
    | NilV, PNil     -> Matched env
    |    _, PVar x   -> Matched (Environment.extend x value env)
    |  IntV a, PILit b when a = b -> Matched env
    | BoolV a, PBLit b when a = b -> Matched env
    | ConsV (car, cdr), PCons (p1, p2) -> (
      match pattern_match env car p1 with
        | Not_matched -> Not_matched
        | Matched newenv -> pattern_match newenv cdr p2
    )
    | _, PAs (p, x) -> (
      match pattern_match env value p with
        | Not_matched -> Not_matched
        | Matched newenv -> Matched (Environment.extend x value newenv)
    )
    | _, POr (p1, p2) -> (
      match pattern_match env value p1 with
        | Not_matched -> pattern_match env value p2
        | Matched _ as whole -> whole
    )
    | _, _ -> Not_matched

(* variable と as すべてを見て同じ変数名があればエラー *)
and pattern_check = function
  | PVar x -> StringSet.singleton x
  | PCons (car, cdr) ->
    let cars = pattern_check car and cdrs = pattern_check cdr in (
      try
        err (Printf.sprintf "Variable %s is bound several times in this matching"
               (StringSet.choose (StringSet.inter cars cdrs)))
      with Not_found -> StringSet.union cars cdrs
    )
  | POr (p, q) -> 
    let ps = pattern_check p and qs = pattern_check q in 
    if StringSet.equal ps qs then ps
    else
      err (Printf.sprintf "Variable %s must occure in both sides of this | pattern"
             (StringSet.choose (StringSet.union (StringSet.diff ps qs) (StringSet.diff qs ps))))
  | _ -> StringSet.empty
  
(* eval one line *)
and eval_decl
    (env : dnval Environment.t) (exp : Syntax.program)
    : Syntax.id list * (exval Environment.t) * exval list =
  match exp with 
      Exp e -> let v = eval_exp env e in (["-"], env, [v])
    | Decl lst ->
      List.fold_left
        (fun (pids, penv, pvs) lst ->
          let (ids, nenv, vs) = eval_let penv lst in
          (pids @ ids, nenv, pvs @ vs))
        ([], env, []) lst
    | RecDecl lst ->
      List.fold_left
        (fun (pids, penv, pvs) lst ->
          let (ids, nenv, vs) = eval_reclet penv lst in
          (pids @ ids, nenv, pvs @ vs))
        ([], env, []) lst

(* eval lines *)
let eval (env : dnval Environment.t) (lst : Syntax.program list)
    : Syntax.id list * (exval Environment.t) * exval list =
  List.fold_left
    (fun (ids, preenv, vs) l ->
      let (id, newenv, v) = eval_decl preenv l in
      (id @ ids, newenv, v @ vs))
    ([], env, []) lst
