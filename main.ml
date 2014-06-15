open Syntax
open Eval
open Typing

let initial_tyenv =
  Environment.extend "i" (TyScheme ([], TyInt))
    (Environment.extend "v" (TyScheme ([], TyInt))
       (Environment.extend "x" (TyScheme ([], TyInt))
          Environment.empty))

let initial_env = 
  Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5) 
       (Environment.extend "x" (IntV 10) Environment.empty))

let type_eval_print tyenv env decl =
  let (tyenv, ts) = ty_decl tyenv decl in
  let (ids, env, vs) = eval_decl env decl in
  let rec print_id ids ts vs =
    match ids, ts, vs with
      | id :: restid, ty :: restty, v :: restv ->
        Printf.printf "%s%s : %s = %s\n"
          (if id = "-" then "" else "val ")
          id (string_of_type ty) (string_of_exval v);
        print_id restid restty restv
      | _, _, _ -> ()
  in print_id ids ts vs; (tyenv, env)
        
let rec read_eval_print tyenv env =
  print_string "# ";
  flush stdout;
  try
    let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
    let (tyenv, env) = type_eval_print tyenv env decl in
    read_eval_print tyenv env
  with
      e -> Printf.printf "Error: %s\n" (Printexc.to_string e);
        read_eval_print tyenv env

let _ =
  if Array.length Sys.argv = 1
  then read_eval_print initial_tyenv initial_env
  else
    let fin = open_in Sys.argv.(1) in
    let decl = Parser.lines Lexer.main (Lexing.from_channel fin) in
    ignore (
      List.fold_left
        (fun (tyenv, env) program ->
          let (tyenv, env) = type_eval_print tyenv env program in
          (tyenv, env))
        (initial_tyenv, initial_env) decl
    );
    close_in fin
