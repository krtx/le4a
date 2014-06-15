open Format

(* ML interpreter / type reconstruction *)
type id = string

and bind = id list * exp

and exp =
  | Var of id
  | ILit of int
  | BLit of bool
  | NilExp
  | ConsExp of exp * exp
  | IfExp of exp * exp * exp
  | LetExp of bind list * exp
  | LetRecExp of bind list * exp
  | FunExp of id list * exp
  | DFunExp of id list * exp
  | MatchExp of exp * (pattern * exp * exp) list
  | AppExp of exp * exp list

and pattern =
  | Wildcard
  | PVar of id
  | PILit of int
  | PBLit of bool
  | PNil
  | POr of pattern * pattern
  | PCons of pattern * pattern
  | PAs of pattern * id

and program =
  | Exp of exp
  | Decl of (bind list) list
  | RecDecl of (bind list) list

type tyvar = int

type ty =
  | TyInt
  | TyBool
  | TyVar of tyvar
  | TyFun of ty * ty
  | TyList of ty

type subst = (tyvar * ty) list

module TyvarSet =
  Set.Make(struct type t = tyvar let compare x y = x - y end)

let set_of_tyvars (tyvars : tyvar list) =
  List.fold_left
    (fun s tyvar -> TyvarSet.add tyvar s)
    TyvarSet.empty tyvars

type tysc = TyScheme of tyvar list * ty

let tysc_of_ty ty = TyScheme ([], ty)

(* --- printers --- *)

(* 型変数は 'a 'b ... 'z 'a1 'b1 ... 'z1 'a2 'b2 ... 'z2 ... *)
let varnum ppf num =
  let ch = Char.chr ((num mod 26) + (Char.code 'a'))
  and tl = num / 26 in
  if tl = 0 then (fun () -> fprintf ppf "'%c" ch)
  else (fun () -> fprintf ppf "'%c%d" ch tl)

let make_strtyvar () =
  let obj =
    let mapping = ref [] in
    let body ppf var =
      try (List.assoc var !mapping) ()
      with Not_found ->
        let strf = varnum ppf (List.length !mapping) in
        mapping := (var, strf) :: !mapping; strf ()
    in body
  in obj


let pp_ty ?maker ppf ty =
  let rec pp_ty mapping ppf = function
    | TyInt -> fprintf ppf "int"
    | TyBool -> fprintf ppf "bool"
    | TyVar x -> mapping ppf x
    | TyList x -> begin
      match x with
        | TyFun _ ->
          fprintf ppf "(%a) list" (pp_ty mapping) x
        | _ ->
          fprintf ppf "%a list" (pp_ty mapping) x
    end
    (* | TyList x -> fprintf ppf "%a list" (pp_ty mapping) x *)
    | TyFun (x, y) ->
      begin
        match x with
          | TyFun _ ->
            fprintf ppf "(%a) -> %a" (pp_ty mapping) x (pp_ty mapping) y
          | _ ->
            fprintf ppf "%a -> %a" (pp_ty mapping) x (pp_ty mapping) y
      end
  in
  match maker with
    | None -> pp_ty (make_strtyvar ()) ppf ty
    | Some maker -> pp_ty maker ppf ty

let string_of_type ty = pp_ty str_formatter ty; flush_str_formatter ()
let print_ty ty = pp_ty std_formatter ty


(* let pp_tyvar ppf value = pp_ty ppf (TyVar value) *)
let pp_tyvar ppf value = fprintf ppf "%d" value

let rec pp_list pp ppf = function
  | [] -> ()
  | [x] -> fprintf ppf "%a" pp x
  | x :: xs -> fprintf ppf "%a; %a" pp x (pp_list pp) xs

let pp_tyvarset ppf set =
  fprintf ppf "(%a)" (pp_list pp_tyvar) (TyvarSet.elements set)

let string_of_tyvarset set =
  pp_tyvarset str_formatter set; flush_str_formatter ()
let print_tyvarset set = pp_tyvarset std_formatter set

let pp_subst ppf lst =
  let pp_tuple ppf (a, b) =
    fprintf ppf "(%a, %a)" pp_tyvar a (fun ppf ty -> pp_ty ppf ty) b
  in fprintf ppf "[%a]" (pp_list pp_tuple) lst

let string_of_subst subst =
  pp_subst str_formatter subst; flush_str_formatter ()

let pp_eqs ppf (eqs : (ty * ty) list) =
  let pp_tuple ppf (a, b) =
    fprintf ppf "(%a, %a)"
      (fun ppf ty -> pp_ty ppf ty) a
      (fun ppf ty -> pp_ty ppf ty) b
  in fprintf ppf "[%a]" (pp_list pp_tuple) eqs

let string_of_eqs eqs =
  pp_eqs str_formatter eqs; flush_str_formatter ()

let pp_tysc ppf (TyScheme (vars, ty)) =
  let maker = make_strtyvar () in
  let tyvars = List.map (fun x -> TyVar x) vars in
  fprintf ppf "(%a)::%a"
    (pp_list (pp_ty ~maker:maker)) tyvars
    (fun ppf ty -> pp_ty ppf ty) ty

let string_of_tysc tysc =
  pp_tysc str_formatter tysc; flush_str_formatter ()
