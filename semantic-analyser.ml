(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var =
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;


let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | Box'(_), Box'(_) -> true
  | BoxGet'(_), BoxGet'(_) -> true
  | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
  | _ -> false;;


exception X_syntax_error;;
exception X_no_match;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let add_to_end l x = (List.rev (x::(List.rev l) ));;

let rec is_param l num x = match l with
| [] -> raise X_no_match
| hd :: tl -> if(hd = x) then VarParam(x, num) else is_param tl (num + 1) x;;

let rec bound_to_level l level_num num x = match l with
| [] -> raise X_no_match
| hd :: tl -> if(hd = x) then VarBound(x,level_num, num) else bound_to_level tl level_num (num + 1) x;;

let rec is_bound l num x = match l with
| [] -> VarFree(x)
| hd :: tl -> try (bound_to_level hd num 0 x) with X_no_match -> (is_bound tl (num + 1) x)
| _ -> VarFree(x);;

(* check for var: assign the var according to his environment  *)
let rec check_for_var env_list x = match env_list with
| [] -> VarFree(x)
| hd :: tl -> try (is_param hd 0 x) with X_no_match -> (is_bound tl 0 x)
| _ -> VarFree(x);;


let rec find_vars env_list e = match e with
| Const(x) -> Const'(x)
| Var(x) -> Var'(check_for_var env_list x)
| If(x,y,z) -> If'((find_vars env_list x),(find_vars env_list y),(find_vars env_list z))
| Seq(l) -> Seq'(List.map (fun k -> find_vars env_list k ) l)
| Set(x, y) -> Set'((find_vars env_list x), (find_vars env_list y))
| Def(x, y) -> Def'((find_vars env_list x), (find_vars env_list y))
| Or(l) -> Or'(List.map (fun k -> find_vars env_list k ) l)
| LambdaSimple(param, body) -> LambdaSimple'(param, find_vars (param::env_list) body)
| LambdaOpt(param, lastparam, body) -> LambdaOpt'(param, lastparam,find_vars ((add_to_end param lastparam)::env_list) body)
| Applic(x, l) -> Applic'(find_vars env_list x, List.map (fun k -> find_vars env_list k ) l)

let annotate_lexical_addresses e = match e with
| Var(x) -> Var'(VarFree(x))
| _ -> find_vars [] e;;


(* TAIL ANNOTATION *)
let rec annotate_applic_tail is_lambda e= match e with
| Set'(x, y) -> Set'( x , (avoid_next_applic is_lambda y)  )
| LambdaSimple'(param, body) -> LambdaSimple'(param, annotate_applic_tail true body)
| LambdaOpt'(param, lastp, body) -> LambdaOpt'(param, lastp, annotate_applic_tail true body)
| Applic'(x, l) -> let_handle x l is_lambda
| If'(test,dit,dif) -> If'(annotate_applic_tail false test,annotate_applic_tail is_lambda dit ,annotate_applic_tail is_lambda dif)
| Seq'(l) -> Seq'(sequence_tail_last l is_lambda)
| Def'(x, y) -> Def'(x, (annotate_applic_tail is_lambda y))
| Or'(l) -> Or'(sequence_tail_last l is_lambda)
| _ -> e
and avoid_next_applic is_lambda e= match e with (* APPLIC & IF HANDLE *)
| Applic'(x, l) -> Applic'((annotate_applic_tail false x), (List.map (annotate_applic_tail false) l))
| If'(test,dit,dif) -> If'(annotate_applic_tail false test,annotate_applic_tail false dit,annotate_applic_tail false dif)
| _ -> annotate_applic_tail false e 
and let_handle x l is_lambda = match x with (*  LET HANDLE *)
| LambdaSimple'(param,body) -> 
  if(is_lambda) then(ApplicTP'(annotate_applic_tail is_lambda x , l)) else (Applic'(annotate_applic_tail is_lambda x , l))
| LambdaOpt'(param,lastp, body) ->
  if(is_lambda) then(ApplicTP'(annotate_applic_tail is_lambda x , l)) else (Applic'(annotate_applic_tail is_lambda x , l))
| _ -> if(is_lambda) then (ApplicTP'(x, (List.map (avoid_next_applic is_lambda) l))) else (Applic'(x, (List.map (avoid_next_applic is_lambda) l)))
and sequence_tail_last l is_lambda= match l with  (* SEQ HANDLE *)
| hd :: [] -> (annotate_applic_tail is_lambda hd ) :: []
| hd :: tl -> (avoid_next_applic is_lambda hd) :: (sequence_tail_last tl is_lambda)
| _ -> [];;

let annotate_tail_calls e = annotate_applic_tail false e;;


(* BOXING *)

(* Var'("Val",0,1) returns "Val" *)
let get_var_string e = match e with
| VarBound(x,x1,x2) -> x
| VarParam(x,x1) -> x
| _ -> "error at get_var_string func";;


(* RETURN LIST OF READ LAMBDAS POSITION*)
let rec list_of_read var count e = match e with
| Var'(x) -> if((get_var_string x) = var) then ([-1]) else ([])
| Set'(x,y) -> (list_of_read var (count+1) y)
| Const'(x) -> []
| Applic'(x,l) -> List.append (list_of_read var count x) (iter_rest var count l)
| ApplicTP'(x,l) -> List.append (list_of_read var count x) (iter_rest var count l)
| Seq'(l) -> (iter_rest var count l)
| Or'(l) -> (iter_rest var count l)
| Def'(x,y) -> List.append (list_of_read var count x) (list_of_read var count y) (* TODO: i unquoted it, is it okay? *)
| If'(test, dit, dif) -> List.append (List.append (list_of_read var (count+1) test) (list_of_read var (count+1) dit)) (list_of_read var (count+1) dif)
| LambdaSimple'(param, body) -> if(List.mem var param) then ([])
 else(if((list_of_read var (count+1) body) = []) then ([]) else ([count]))
| LambdaOpt'(param, lastp, body) -> if(List.mem var (List.append param [lastp])) then ([])
 else(if((list_of_read var (count+1) body) = []) then ([]) else ([count]))
| _ -> []
and iter_rest var count l = match l with
 | [] -> []
 | hd :: tl -> List.append (list_of_read var count hd) (iter_rest var (count + 1) tl);;


(* RETURN LIST OF WRITE LAMBDAS POSITION*)
let rec list_of_write var count e = match e with
| Set'(Var'(x),y) -> List.append (if((get_var_string x) = var) then ([-1]) else ([])) (list_of_write var (count+1) y)
| Var'(x) -> []
| Const'(x) -> []
| Applic'(x,l) -> List.append (list_of_write var count x) (iter_rest var count l)
| ApplicTP'(x,l) -> List.append (list_of_write var count x) (iter_rest var count l)
| Seq'(l) -> (iter_rest var count l)
| Or'(l) -> (iter_rest var count l)
| Def'(x,y) -> List.append (list_of_write var count x) (list_of_write var count y) (* TODO: i unquoted it, is it okay? *)
| If'(test, dit, dif) -> List.append (List.append (list_of_write var (count+1) test) (list_of_write var (count+1) dit)) (list_of_write var (count+1) dif)
| LambdaSimple'(param, body) -> if(List.mem var param) then ([])
 else(if((list_of_write var (count+1) body) = []) then ([]) else ([count]))
 | LambdaOpt'(param, lastp, body) -> if(List.mem var (List.append param [lastp])) then ([])
 else(if((list_of_write var (count+1) body) = []) then ([]) else ([count]))
| _ -> []
and iter_rest var count l = match l with
 | [] -> []
 | hd :: tl -> List.append (list_of_write var count hd) (iter_rest var (count + 1) tl);;

let rec is_read_and_write write_list read_list = match write_list with
 | [] -> "false"
 | hd :: tl -> if(List.fold_left (fun a b -> (a||(hd!=b))) false read_list) then "true" else (is_read_and_write tl read_list);;

  (* -- this func decides if the parameter var received needs to be boxed *)
let should_it_be_boxed x body = x::[(is_read_and_write (list_of_write x 0 body) (list_of_read x 0 body))];;

(* add_box_param --- lambda handle assist func
use: this function iterates lambda's parameters and check if each one needs to be boxed *)
let rec add_box_param param_list body = List.map (fun x -> (should_it_be_boxed x body)) param_list;;

let construct_set_param_var str count = Set'(Var'(VarParam(str,count)), Box'(VarParam(str,count)));;

let rec turn_param_var_to_set param_list count= match param_list with
| [] -> []
| hd :: tl -> if((List.nth hd 1) = "true") then ((construct_set_param_var (List.nth hd 0) count) :: (turn_param_var_to_set tl (count + 1))) else((turn_param_var_to_set tl (count + 1)));;

let add_vars_setters l = match l with
| [] -> []
| _ -> (turn_param_var_to_set l 0);;

let rec true_params l = match l with
| [] -> false
| hd :: tl -> if((List.nth hd 1) = "true") then (true) else (true_params tl);;

let rec rem_dup_assist l new_l = match l with
| [] -> new_l
| hd :: tl -> if((List.mem ((List.nth hd 0)::["false"]) new_l) || (List.mem ((List.nth hd 0)::["true"]) new_l)) then (rem_dup_assist tl new_l) else (rem_dup_assist tl (hd::new_l));;
let rem_dup l = rem_dup_assist l [];;

let rec wrap_with_box var_l e = match e with
| Set'(Var'(x), y) ->
    if(List.mem ((get_var_string x)::["true"]) var_l)
      then(BoxSet'(x, (wrap_with_box var_l y)))
      else(Set'(Var'(x), wrap_with_box var_l y))
| Var'(x) -> if (List.mem ((get_var_string x)::["true"]) var_l) then (BoxGet'(x)) else (e)
| LambdaSimple'(param, body) -> LambdaSimple'(param, (is_there_boxed_param param body var_l))
| LambdaOpt'(param, lastp, body) -> LambdaOpt'(param, lastp, (is_there_boxed_param (List.append param [lastp]) body var_l))
| Def'(x, y) -> Def'(x, (wrap_with_box var_l y))
| Applic'(x, l) -> Applic'((wrap_with_box var_l x), (List.map (wrap_with_box var_l) l))
| ApplicTP'(x, l) -> ApplicTP'((wrap_with_box var_l x), (List.map (wrap_with_box var_l) l))
| Seq'(l) -> Seq'((List.map (wrap_with_box var_l) l))
| If'(test, dit, dif) -> If'(wrap_with_box var_l test, wrap_with_box var_l dit, wrap_with_box var_l dif)
| Or'(l) -> Or'((List.map (wrap_with_box var_l) l))
| _ -> e
and is_there_boxed_param param_l body var_l =
  let boxed_param_l =  (add_box_param param_l body) in
  let continue_to_body = (wrap_with_box (rem_dup (List.append boxed_param_l var_l)) body) in
 if(true_params boxed_param_l) then(Seq'(List.append (add_vars_setters boxed_param_l) [continue_to_body]))
                          else(continue_to_body);;

let box_set e = wrap_with_box [] e;;
let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)

 (* TESTING FOR CONVINIENCE *)
 let read x = Reader.read_sexpr x;;
 let tag x = Tag_Parser.tag_parse_expression x;;
 let tag_read x = tag (read x);;
 let lexi_test x = Semantics.annotate_lexical_addresses (tag_read x);;
 let tail_test x = Semantics.annotate_tail_calls (lexi_test x);; 
 let tail_test_x x =  Semantics.annotate_tail_calls x;;
 let box_test x = Semantics.box_set (tail_test x);;

 let run_test x = Semantics.run_semantics x;;