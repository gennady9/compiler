(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
*)

#use "reader.ml";;

type constant =
    | Sexpr of sexpr
    | Void

type expr =
    | Const of constant
    | Var of string
    | If of expr * expr * expr
    | Seq of expr list
    | Set of expr * expr
    | Def of expr * expr
    | Or of expr list
    | LambdaSimple of string list * expr
    | LambdaOpt of string list * string * expr
    | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
    | Const Void, Const Void -> true
    | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
    | Var(v1), Var(v2) -> String.equal v1 v2
    | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                            (expr_eq el1 el2)
    | (Seq(l1), Seq(l2)
      | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
    | (Set(var1, val1), Set(var2, val2)
      | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
    | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
        (List.for_all2 String.equal vars1 vars2) &&
        (expr_eq body1 body2)
    | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
        (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
        (expr_eq body1 body2)
    | Applic(e1, args1), Applic(e2, args2) ->
        (expr_eq e1 e2) &&
        (List.for_all2 expr_eq args1 args2)
    | _ -> false;;
	

exception X_syntax_error;;




module type TAG_PARSER = sig
val tag_parse_expression : sexpr -> expr
val tag_parse_expressions : sexpr list -> expr list
  end;; (* signature TAG_PARSER *)

  

  
  module Tag_Parser : TAG_PARSER = struct

  

     

     

     
     let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
  "if"; "lambda"; "let"; "let*"; "letrec"; "or";
  "quasiquote"; "quote"; "set!"; "unquote";
  "unquote-splicing"];;  

  

  

  

  
  (* work on the tag parser starts here *)

open Reader;;


let check_list_for_word l x =
List.fold_left (fun acc y-> (((String.equal x y) || acc))) false l;;

let if_legal_symb x = check_list_for_word reserved_word_list x;;
let ch_legal_symb x = if(if_legal_symb x) then (raise X_syntax_error) else x;;

let rec extract_string_list_uniq_assist l l_uniq= 
    match l with
    | Nil -> []
    | Pair(Symbol(x),y) -> if(check_list_for_word l_uniq x) then (raise X_syntax_error) else ( (ch_legal_symb x)::(extract_string_list_uniq_assist y (x::l_uniq)) )
    | Symbol(x) -> if(check_list_for_word l_uniq x) then (raise X_syntax_error) else []
    | _ -> [];;

let extract_string_list_uniq l = extract_string_list_uniq_assist l [];; 

let rec last_symbol l =
  match l with
  | Symbol(x) -> x
  | Pair(x,y) -> last_symbol y
  | _ -> "";;

let rec is_lambda_simple args =
  match args with
  | Nil -> true
  | Symbol(x) -> false
  | Pair(Symbol(x),y) -> is_lambda_simple y
  | _ -> raise X_syntax_error;;

let rec list_of_sexprs l =
  match l with
  |  Nil -> []
  |  Pair(x,y) -> x::(list_of_sexprs y)
  |  _ -> raise X_syntax_error;;



exception X_and_case_not_found;;

let rec quasi_expansion x = match x with
  | Pair(Symbol("unquote"), Pair(y,Nil)) -> y
  | Pair(Symbol("unquote-splicing"), Pair(y,Nil)) -> (raise X_syntax_error)
  | Pair(Pair(Symbol("unquote-splicing"), Pair(s1,Nil)),s2) -> Pair(Symbol "append", Pair(s1, Pair(quasi_expansion s2, Nil)))
  | Pair(s1, Pair(Symbol("unquote-splicing"), s2)) -> Pair(Symbol "cons", Pair(quasi_expansion s1, s2))
  | Pair(s1,s2) -> Pair(Symbol "cons", Pair(quasi_expansion s1, Pair(quasi_expansion s2, Nil)))
  | Symbol(y) -> Pair(Symbol("quote"),Pair(Symbol(y),Nil))
  | Vector(y) -> Pair(Symbol("vector"),(List.fold_right (fun a b -> Pair(a,b)) (List.map quasi_expansion y) Nil) )
  | Nil -> Pair(Symbol("quote"),Pair(Nil,Nil))
  | _ -> x;;
  
  let rec and_expansion x = match x with
  | Nil -> Bool(true)
  | Pair(s1, Nil) -> s1
  | Pair(s1, s2) -> Pair(Symbol("if"), Pair(s1, Pair( (and_expansion s2), Pair( Bool(false), Nil ))))
  | _ -> raise X_and_case_not_found;;

let check_if_var x = match x with
  | Var(y) -> x
  | _ -> raise X_syntax_error;;
let rec wrap_with_lambda x = Pair(Symbol("lambda"),Pair(Nil,Pair(x,Nil)));;
let rec make_it_let name value = Pair(Symbol(name),Pair(value,Nil));;
let rec body_of_let test ditfunc difunc = Pair(Symbol("if"),Pair(Symbol(test),Pair(Pair(Pair(Symbol(ditfunc),Nil),Pair(Symbol(test),Nil)),Pair(Pair(Symbol(difunc),Nil),Nil))));;
let rec body_of_let2 test ditfunc = Pair(Symbol("if"),Pair(Symbol(test),Pair(Pair(Pair(Symbol(ditfunc),Nil),Pair(Symbol(test),Nil)),Nil)));;
    
    let rec cond_expansion x =
    match x with
    |  Pair(Pair(test,Pair(Symbol("=>"),Pair(dit,Nil))),Nil) -> Pair(Symbol("let"),Pair(Pair((make_it_let "value" test),Pair((make_it_let "f" (wrap_with_lambda dit)),Nil)),Pair((body_of_let2 "value" "f"),Nil)))
    |  Pair(Pair(test,Pair(Symbol("=>"),Pair(dit,Nil))),dif) -> Pair(Symbol("let"),Pair(Pair((make_it_let "value" test),Pair((make_it_let "f" (wrap_with_lambda dit)),Pair((make_it_let "rest" (wrap_with_lambda (Pair(Symbol("cond"),dif)))),Nil))),Pair((body_of_let "value" "f" "rest"),Nil)))
    |  Pair(Pair(Symbol("else"),dit),Nil) -> Pair(Symbol("begin"),dit)
    |  Pair(Pair(test,dit),Nil) -> Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),dit),Nil)))
    |  Pair(Pair(test,dit),dif) -> Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),dit),Pair(Pair(Symbol("cond"),dif),Nil))))
    |  _ -> x;; 

    let rec make_args_pairs x =
      match x with
    |  Nil -> Nil
    |  Pair(Pair(l,r),y) -> Pair(l,(make_args_pairs y))
    |  _ -> x;;

    let rec make_params_pairs x =
      match x with
    |  Nil -> Nil
    |  Pair(Pair(l,Pair(r,Nil)),y) -> Pair(r,(make_params_pairs y))
    |  _ -> x;;


    let rec let_expansion x =
      match x with
    |  Pair(vars,body) -> Pair(Pair(Symbol("lambda"),Pair((make_args_pairs vars), body)),(make_params_pairs vars))
    | _ -> x;;

    let rec letstar_expansion x =
      match x with
    |  Pair(Nil,y) -> Pair(Symbol("let"),x)
    |  Pair(Pair(Pair(l,r),Nil),y) -> Pair(Symbol("let"),x)
    |  Pair(Pair(first,rest),y) -> Pair(Symbol("let"),Pair(Pair(first,Nil),Pair(Pair(Symbol("let*"),Pair(rest,y)),Nil)))
    |  _ -> x;;

    let rec whatevers x =
      match x with
    |  Nil -> Nil
    |  Pair(Pair(name,exp),rest) -> Pair(Pair(name,Pair(Pair(Symbol("quote"),Pair(Symbol("whatever"),Nil)),Nil)),(whatevers rest))
    |  _ -> x;;

    let rec connect_to_body args body = 
      match args with
    |  Nil -> body
    |  Pair(Pair(name,exp),rest) -> Pair(Pair(Symbol("set!"),Pair(name,exp)),(connect_to_body rest body))
    |  _ -> Nil;;

    let rec letrec_expansion x =
      match x with
    |  Pair(args,body) -> Pair(Symbol("let"),Pair((whatevers args),(connect_to_body args body)))
    |  _ -> x;;

    let rec tag_parse x =
    match x with
    |  Number(x) -> Const(Sexpr(Number(x)))
    |  Bool(x) -> Const(Sexpr(Bool(x)))
    |  Char(x) -> Const(Sexpr(Char(x)))
    |  String(x) -> Const(Sexpr(String(x)))
    |  Pair(Symbol("quote") ,Pair(rest, Nil)) -> Const(Sexpr(rest))
    |  Pair(Symbol("if"),Pair(test,Pair(dit, Pair(dif,Nil)))) -> If((tag_parse test), (tag_parse dit),(tag_parse dif))
    |  Pair(Symbol("if"),Pair(test,Pair(dit, Nil))) -> If((tag_parse test),(tag_parse dit),Const(Void))
    |  Pair(Symbol("lambda"),Pair(Symbol(x),body)) -> LambdaOpt([],ch_legal_symb x,(body_of_lambda body))
    |  Pair(Symbol("lambda"),Pair(args,body)) -> if (is_lambda_simple args) then LambdaSimple((extract_string_list_uniq args), (body_of_lambda body)) else LambdaOpt((extract_string_list_uniq args),(last_symbol args),(body_of_lambda body))
    |  Pair(Symbol("or"),x) -> match_or x
    |  Pair(Symbol("define"), Pair(Symbol(x),Pair(y,Nil))) -> Def(Var(ch_legal_symb x), (tag_parse y))
    |  Pair(Symbol("define"), Pair(Pair(Symbol(var),arglst),body)) -> Def(Var(ch_legal_symb var), tag_parse (Pair(Symbol("lambda"), Pair(arglst, body))))
    |  Pair(Symbol("begin"),x) -> match_begin x
    |  Pair(Symbol("quasiquote"), Pair(y,Nil)) -> tag_parse (quasi_expansion y)
    |  Pair(Symbol("and"), y) -> tag_parse (and_expansion y)
    |  Pair(Symbol("cond"),y) -> tag_parse (cond_expansion y)
    |  Pair(Symbol("set!"), Pair(x,Pair(y,Nil))) -> Set((check_if_var (tag_parse x)),(tag_parse y))
    |  Pair(Symbol("let"),x) -> tag_parse (let_expansion x)
    |  Pair(Symbol("let*"),x) -> tag_parse (letstar_expansion x)
    |  Pair(Symbol("letrec"),x) -> tag_parse (letrec_expansion x)
    |  Pair(x,y) -> Applic((tag_parse x),(List.map tag_parse (list_of_sexprs y)))
    |  Symbol(x) ->  Var(ch_legal_symb x)
    |  _ -> raise X_syntax_error
    and match_begin x = match x with
    | Pair(x,Nil)-> tag_parse x
    | Pair(l,r)-> Seq((List.map tag_parse (list_of_sexprs x)))
    | Nil -> Const(Void)
    | _-> (raise X_syntax_error) 
    and match_or x = match x with
      | Nil -> Const(Sexpr(Bool(false)))
      | Pair(s2,Nil) -> tag_parse s2
      | Pair(s1,s2) -> Or((List.map tag_parse (list_of_sexprs x)))
      | _-> (raise X_syntax_error) 
    and body_of_lambda x = match x with
    | Pair(x,Nil) -> tag_parse x
    | Pair(l,r) -> Seq((List.map tag_parse (list_of_sexprs x)))
    | _ -> raise X_syntax_error;;




  

  

  
  let tag_parse_expression sexpr = tag_parse sexpr;;

  

  

  

  
  let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr);;

  

  

 
  

end;; (* struct Tag_Parser *)
