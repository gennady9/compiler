#use "semantic-analyser.ml";;
 
let primitive_names = 
  ["boolean?"; "float?"; "integer?"; "pair?";
   "null?"; "char?"; "vector?"; "string?";
   "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "vector-length"; "vector-ref"; "vector-set!";
   "make-vector"; "symbol->string"; 
   "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "=";
   "apply"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"
  ];;
 
let rec rem_dup_assist l new_l = match l with
| [] -> new_l
| hd :: tl -> if(List.mem hd new_l) then (rem_dup_assist tl new_l) else (rem_dup_assist tl (new_l @ [hd]));;
let remove_dup l = rem_dup_assist l [];;

let sexpr_eq2 e1 e2 = match e1,e2 with
| Vector(l1), Vector(l2) -> if((List.length l1) == (List.length l2)) then (sexpr_eq e1 e2) else false
| _, _-> (sexpr_eq e1 e2);;

let rec get_const e = match e with
| Const'(y) -> y::[]
| BoxSet'(v, e) -> (get_const e)
| If'(test, dit, dif) -> (get_const test) @ (get_const dit) @ (get_const dif)
| Seq'(l) -> (List.fold_left (fun a b -> a @ b) [] (List.map get_const l))
| Set'(x,y) -> (get_const x) @ (get_const y)
| Def'(x,y) -> (get_const x) @ (get_const y)
| Or'(l) -> (List.fold_left (fun a b -> a @ b) [] (List.map get_const l))
| LambdaSimple'(param,body) -> (get_const body)
| LambdaOpt'(param,lastp,body) -> (get_const body)
| Applic'(x,l) -> (get_const x) @ (List.fold_left (fun a b -> a @ b) [] (List.map get_const l))
| ApplicTP'(x,l) -> (get_const x) @ (List.fold_left (fun a b -> a @ b) [] (List.map get_const l))
| _ -> [];;
 
 
exception X_sexpr_not_compound;;
(*
let unwrap_sexpr e = match e with
| Sexpr(x) -> x;;
let rec sexpr_mem x l = match l with
| [] -> false
| Sexpr(a)::tl -> (sexpr_eq a x) || sexpr_mem x tl;;
let rec rem_sexpr_dup_assist l new_l = match l with
| [] -> new_l
| hd :: tl -> if((List.mem hd new_l) || ((hd != Void) && (sexpr_mem (unwrap_sexpr hd) new_l))) then (rem_sexpr_dup_assist tl new_l) else (rem_sexpr_dup_assist tl (new_l @ [hd]));;
let remove_sexpr_dup l = rem_sexpr_dup_assist l [];;
 
if(sexpr_mem (unwrap_sexpr hd) new_l) then (rem_sexpr_dup_assist tl new_l) else (rem_sexpr_dup_assist tl (new_l @ [hd]))
*)
(*let unwrap_sexpr e = match e with
| Sexpr(x) -> x;;*)
let rec sexpr_mem x l = match l with
  |  [] -> false
  | Sexpr(a)::tl -> (sexpr_eq2 a x) || sexpr_mem x tl
  | hd::tl -> (compare hd (Sexpr x)) = 0 || sexpr_mem x tl;;
let rec rem_sexpr_dup_assist l new_l = match l with
| [] -> new_l
| Sexpr(hd) :: tl -> if(sexpr_mem hd new_l) then (rem_sexpr_dup_assist tl new_l) else (rem_sexpr_dup_assist tl (new_l @ [Sexpr(hd)]))
| hd :: tl -> if(List.mem hd new_l) then (rem_sexpr_dup_assist tl new_l) else (rem_sexpr_dup_assist tl (new_l @ [hd]));;
 
let remove_sexpr_dup l = rem_sexpr_dup_assist l [];;

(* turns string to char list *)
let rec str_to_ch_list_assist s i acc_l = 
  if(i = 0) then (s.[0]::acc_l)
            else str_to_ch_list_assist s (i-1) (s.[i]::acc_l);;
let str_to_ch_list s = str_to_ch_list_assist s ((String.length s)-1) [];;

let int_to_str x = Pervasives.string_of_int x;;
let change_str_format s = String.concat "," (List.map int_to_str (List.map Char.code (str_to_ch_list s)));; 

let rec find_offset calc_list e = match calc_list with
  | (Void,(o,_))::tl -> find_offset tl e
  | (Sexpr(v),(o,_))::tl -> if(sexpr_eq2 v e) then o else (find_offset tl e)
  | [] -> 203944673 (* lidor id magic number*)

 
and build_string calc_list e = match e with
  | Sexpr(Nil) -> "MAKE_NIL"
  | Sexpr(Bool(true)) -> "MAKE_BOOL(1)"
  | Sexpr(Bool(false)) -> "MAKE_BOOL(0)"
  | Sexpr(String(s)) -> (String.concat "" ["MAKE_LITERAL_STRING ";(change_str_format s)]) 
  | Sexpr(Number(Int(x))) -> (String.concat "" ["MAKE_LITERAL_INT(";(int_to_str x);")"])
  | Sexpr(Number(Float(x))) -> String.concat "" ["MAKE_LITERAL_FLOAT(";Pervasives.string_of_float x;")"]
 (* | Sexpr(Char(x)) -> String.concat "" ["MAKE_LITERAL_CHAR(\"";(String.make 1 x);"\")"] *)
  | Sexpr(Char(x)) -> String.concat "" ["MAKE_LITERAL_CHAR(";(int_to_str (Char.code x));")"] 
  | Sexpr(Pair(car,cdr)) -> String.concat "" ["MAKE_LITERAL_PAIR(const_tbl+";(int_to_str (find_offset calc_list car));", ";"const_tbl+";(int_to_str (find_offset calc_list cdr));")"]
  | Sexpr(Vector(l)) -> String.concat "" ["MAKE_LITERAL_VECTOR ";(String.concat "," (List.map (fun a -> "const_tbl+"^(int_to_str (find_offset calc_list a))) l))] 
 (* | Sexpr(Vector(l)) -> String.concat "" ["MAKE_LITERAL_VECTOR ";(String.concat "," (List.map (fun a -> (int_to_str (find_offset calc_list a))) l))] 
  | Sexpr(Vector(l)) -> String.concat "" ["MAKE_LITERAL_VECTOR ";(String.concat "," (l))] *)
  | Sexpr(Symbol(x)) -> String.concat "" ["MAKE_LITERAL_SYMBOL(const_tbl+";(int_to_str  (find_offset calc_list (String x)));")"]
  | _ -> "MAKE_VOID"
 
and get_offset calc_list = match calc_list with
  | [] -> 0
  | [(v,(o,_))] -> o+(sizeof v)
  | hd :: tl -> get_offset tl
 
and make_three_elements calc_list e = (e,((get_offset calc_list),(build_string calc_list e)))
 
and sizeof e = match e with
  | Sexpr(Nil) -> 1
  | Sexpr(Bool(x)) -> 2
  | Sexpr(Char(x)) -> 2
  | Sexpr(Number(x)) -> 9
  | Sexpr(Symbol(x)) -> 9
  | Sexpr(String(x)) -> 9 + (String.length x)
  | Sexpr(Vector(x)) -> 9 + 8 * (List.length x)
  | Sexpr(Pair(x,y)) -> 17
  | _ -> 1;;
 
let is_compound sexpr = match sexpr with
| Sexpr(Pair(x,y)) -> true
| Sexpr(Vector(l)) -> true
| Sexpr(Symbol(s)) -> true
| _ -> false;;
 

let rec const_list e = remove_sexpr_dup ([Void;Sexpr(Nil);Sexpr(Bool(true));Sexpr(Bool(false))] @ (remove_sexpr_dup (expand_list (remove_sexpr_dup (get_const e)))))
      and expand_pair_assist p = match p with
      | Nil -> [Sexpr(Nil)] (* TODO: should NIL be added? *)
      (*| Pair(Pair(x,z), y) -> ## *)
      | Pair(car,cdr) ->  (((const_list (Const' (Sexpr car))) @ (const_list (Const' (Sexpr cdr)))))
      | _ -> const_list (Const' (Sexpr p))
      and expand_pair p = List.rev ( expand_pair_assist p )
      and expand_list l = match l with
      | [] -> []
      | hd :: tl -> if(is_compound hd) then (((expand_compound hd) @ [hd]) @ (expand_list tl)) else (hd :: (expand_list tl))
      and expand_compound e = match e with
      | Sexpr(Pair(x,y)) -> expand_pair_assist (Pair(x,y))
      | Sexpr(Vector(l)) -> expand_vector_assist (l)
      | Sexpr(Symbol(s)) -> (build_const_t_sexpr (String(s))) @ [e]  (* Will learn to handle it later *)
      | _ -> raise X_sexpr_not_compound
      and build_const_t_sexpr s = (const_list (Const' (Sexpr(s))))
      and expand_vector_assist l = match l with
      | [] -> []
      | hd :: tl -> (List.fold_left (fun a b -> a @ b) [] (List.map build_const_t_sexpr l))
      and expand_vector v = List.rev ( expand_vector_assist v );;

 
     
 
let rec make_const_table asts = match asts with (* receives expr' list -> returns list *)
| [] -> []
| hd :: tl -> (get_const hd) @ make_const_table tl;;
 
let rec run_on_list acc l = match l with
  | [] -> acc
  | hd::tl -> (run_on_list (acc @ [(make_three_elements acc hd)]) tl);;
let testing s = run_on_list [] (const_list (Semantics.run_semantics (Tag_Parser.tag_parse_expression (Reader.read_sexpr s))));;

let unwrap_sexpr e = match e with
| Sexpr(x) -> x
| Void -> Number(Int(555));;

let first_const e_list= run_on_list [] (remove_sexpr_dup ([Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))] @ (remove_sexpr_dup (expand_list (remove_sexpr_dup (List.flatten (List.map get_const e_list)))))));;

(* FVAR TABLE impl start *)

let rec collect_fvar e = match e with
| Var'(VarFree(x)) -> [x]
| BoxSet'(v, e) -> (collect_fvar e)
| If'(test, dit, dif) -> (collect_fvar test) @ (collect_fvar dit) @ (collect_fvar dif)
| Seq'(l) -> (List.fold_left (fun a b -> a @ b) [] (List.map collect_fvar l))
| Set'(x,y) -> (collect_fvar x) @ (collect_fvar y)
| Def'(x,y) -> (collect_fvar x) @ (collect_fvar y)
| Or'(l) -> (List.fold_left (fun a b -> a @ b) [] (List.map collect_fvar l))
| LambdaSimple'(param,body) -> (collect_fvar body)
| LambdaOpt'(param,lastp,body) -> (collect_fvar body)
| Applic'(x,l) -> (collect_fvar x) @ (List.fold_left (fun a b -> a @ b) [] (List.map collect_fvar l))
| ApplicTP'(x,l) -> (collect_fvar x) @ (List.fold_left (fun a b -> a @ b) [] (List.map collect_fvar l))
| _ -> [];;


(* receives for example = [ ["car";"cdr"] ---> returns [("car",0);("cdr",1) etc *)
let rec str_to_fvar_list_assist l count = match l with
| [] -> []
| hd :: tl -> [(hd, count)] @ (str_to_fvar_list_assist tl (count+1));;
let str_to_fvar_list l = (str_to_fvar_list_assist l 0);;
let fvar_list e = str_to_fvar_list (remove_dup (collect_fvar e));;
let fvar_lists asts = str_to_fvar_list (remove_dup (primitive_names @ List.flatten (List.map collect_fvar asts)));;

let rec make_fvar_table asts = match asts with
| [] -> []
| hd :: tl -> (fvar_list hd) @ make_fvar_table tl;;


let get_const_address x consts = 
      let c_row = List.find (fun (const, (_, _)) -> (x == const) || ((const != Void) && (sexpr_eq2 (unwrap_sexpr const) (unwrap_sexpr x)))) consts in
      let offset = (fun (_, (offsett, __)) -> offsett) c_row in
      "const_tbl+"^(int_to_str offset);;

let get_freevar_index v fvars = 
            let c_row = List.find (fun (name, _) -> ((compare v name) == 0)) fvars in
            let id = (fun (_, id) -> id) c_row in
            id;;

let get_var_str e = match e with
| VarBound(x,_,_) -> x
| VarParam(x,_) -> x
| VarFree(x) -> x;;          

let lcount = (ref 0);;
let lamb_depth = (ref 0);;



module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = first_const asts;;


let rec gener consts fvars e = match e with
(*| Const'(x) -> Printf.sprintf ("mov rax, const_tbl+%d") (get_const_address x consts)  *)
| Const'(x) ->  ("mov rax,"^ (get_const_address x consts)  ^"\n") 
| Var'(VarParam(_, minor)) -> Printf.sprintf ("mov rax, qword [rbp + 8 * (4 + %d)]") (minor)
| Set'(Var'(VarParam(_, minor)), x) -> (String.concat "\n" ([(gener consts fvars x);(Printf.sprintf "mov qword [rbp + 8 * (4 + %d)],rax" minor);("mov rax, SOB_VOID_ADDRESS")]))
| Set'(Var'(VarBound(_, major, minor)), x) -> (String.concat "\n" ([(gener consts fvars x);"mov rbx, qword [rbp + 8 * 2]";(Printf.sprintf "mov rbx, qword [rbx + 8 * %d]" (major));(Printf.sprintf "mov qword [rbx + 8 * %d],rax" minor);("mov rax, SOB_VOID_ADDRESS")]))
| Set'(Var'(VarFree(v)), x) -> (String.concat "\n" (["; SET START";(gener consts fvars x);Printf.sprintf ("mov FVAR(%d), rax ; (set get func %s)") (get_freevar_index v fvars) (v);("mov rax, SOB_VOID_ADDRESS")]))
| Def'(Var'(VarFree(v)), x) -> (String.concat "\n" (["; DEFINE START";(gener consts fvars x);Printf.sprintf ("mov FVAR(%d), rax ; (def get func %s)") (get_freevar_index v fvars) (v);("mov rax, SOB_VOID_ADDRESS")]))
| Var'(VarBound(_, major, minor)) -> (String.concat "\n" (["mov rax, qword [rbp + 8 * 2]";(Printf.sprintf ("mov rax, qword [rax + 8 * %d]") (major));(Printf.sprintf ("mov rax, qword [rax + 8 * %d]") (minor))]))
| Var'(VarFree(v)) -> (Printf.sprintf ("mov rax, FVAR(%d)") (get_freevar_index v fvars))
| Seq'(l) -> (String.concat "\n" (List.map (gener consts fvars) l))
| Or'(l) -> (incr lcount);(handle_or consts fvars (!lcount) l)
| Applic'(proc,args_l) -> String.concat "\n" ["debug_applic"^(int_to_str (Random.int 1000000000))^": ;APPLIC START";"push 7 ; magic number";(List.fold_right (fun a b -> b^(gener consts fvars a)^"\npush rax\n") args_l "");("push "^(int_to_str (List.length args_l))) ;(gener consts fvars proc);"CLOSURE_ENV rsi,rax";"push rsi";"CLOSURE_CODE rsi, rax";"call rsi";"add rsp , 8*1 ; pop env";"pop rbx ; pop ret";"inc rbx";"shl rbx , 3";"add rsp , rbx ; pop params and magic\n"]
(*| Applic'(proc,args_l) -> String.concat "\n" ["debug_applic"^(int_to_str (Random.int 45))^": ;APPLIC START";"push 5874714";(List.fold_right (fun a b -> b^(gener consts fvars a)^"\npush rax\n") args_l "");("push "^(int_to_str (List.length args_l))) ;(gener consts fvars proc);"CLOSURE_ENV rsi,rax";"push rsi";"CLOSURE_CODE rsi, rax";"call rsi";"add rsp , 8*1 ; pop env";"pop rbx ; pop ret";"inc rbx";"shl rbx , 3";"add rsp , rbx ; pop params and magic\n"]*)
| ApplicTP'(proc,args_l) -> handle_applic_tp consts fvars e proc args_l
| If'(test,dit,dif) -> (incr lcount);let count = !lcount in let c = (int_to_str count) in String.concat "\n" [(gener consts fvars test);"cmp rax, SOB_FALSE_ADDRESS";"je Lelse"^c;(gener consts fvars dit);"jmp Lexit"^c;"Lelse"^c^":";(gener consts fvars dif);"Lexit"^c^":\n"]
| BoxGet'(x) -> ((gener consts fvars (Var'(x)))^"\n"^"mov rax, qword [rax]\n")
| BoxSet'(x,y) -> String.concat "\n" [(gener consts fvars y);"push rax";(gener consts fvars (Var'(x)));"pop qword [rax]";"mov rax, SOB_VOID_ADDRESS\n"]
| Box'(x) -> String.concat "\n" ["MALLOC rbx, 8";(gener consts fvars (Var'(x)));"mov qword [rbx], rax";"mov rax, rbx\n"]
| LambdaSimple'(param,body) -> (incr lcount);(incr lamb_depth);handle_lambda_simple consts fvars param body
| LambdaOpt'(param,lastp, body) -> (incr lcount);(incr lamb_depth);handle_lambda_opt consts fvars param body
| _ -> "; NOT_FOUND" (* TODO- change to not_generated yet for debugging *)
and handle_or consts fvars count l = match l with
| [x] -> (gener consts fvars x)^"\n"^"Lexit"^(int_to_str count)^":\n"
| [] -> "empty OR case in generate, probably shouldnt happen" (* todo: remove this before submitting, maybe change to "Lexit:" *)
| hd::tl -> ((gener consts fvars hd)^"\n"^"cmp rax, SOB_FALSE_ADDRESS"^"\n"^"jne Lexit"^(int_to_str count)^"\n"^(handle_or consts fvars count tl))
and handle_lambda_simple consts fvars param body =
  let count_str = (int_to_str !lcount) in
  let depth = !lamb_depth in
(String.concat "\n" [
          (*"%define PARAM_COUNT qword [rbp+3*WORD_BYTES]"*)
          "; LAMBDA SIMPLE START";
          "mov rsi,qword [rbp+3*WORD_BYTES]";
          ";mov rsi, qword [rsp]";
          "EXTENV rsi, "^(int_to_str (depth-1));
          "lambda_simple_after_env"^count_str^":";
          "MAKE_CLOSURE(rax, rbx, lambda_body_"^count_str^")";
          "jmp end_lambda_body_"^count_str;
          "lambda_body_"^count_str^":";
          "; lambda simple enter macro";
          (* LAMBDA BODY *)
          "push rbp";
          "mov rbp, rsp";
          "; param count, check if valid";
          "mov rax, "^(int_to_str (List.length param));
          ";cmp rax, PARAM_COUNT";
          ";jne lambda_error_"^count_str;
          "; GENERATE LAMBDA SIMPLE BODY";
          (gener consts fvars body);
          "leave";
          "ret";
          "lambda_error_"^count_str^":";
           (* error handling *)
          "mov rbx, 555";
          "end_lambda_body_"^count_str^":";
          ""
          ])
and handle_lambda_opt consts fvars param body =
let count = !lcount in
let depth = !lamb_depth in
let param_len = (int_to_str (List.length param)) in
(String.concat "\n" [
        (*"%define PARAM_COUNT qword [rbp+3*WORD_BYTES]"*)
        "; LAMBDA OPT START";
        "mov rsi,qword [rbp+3*WORD_BYTES]";
        "debug_lambda_opt_before_env"^(int_to_str count)^":";
        "EXTENV rsi, "^(int_to_str (depth-1));
        "debug_lambda_opt_after_env"^(int_to_str count)^":";
        "MAKE_CLOSURE(rax, rbx, lambda_body_"^(int_to_str count)^")";
        "jmp end_lambda_opt_body_"^(int_to_str count);
        "lambda_body_"^(int_to_str count)^":";
        "; lambda opt enter macro";
        (* LAMBDA OPT BODY *)
        "push rbp";
        "mov rbp, rsp";
        "mov rax, "^param_len;
        "cmp rax, PARAM_COUNT";
        "jg lambda_error_"^(int_to_str count);
        "; creating the optional args list";
        "mov rax,PARAM_COUNT";
        "mov r8,rax";
        "dec r8";
        "sub rax,"^param_len;
        "imul rax , WORD_BYTES";
       (* "MALLOC rbx, rax  ; allocate space for optional args list"; *)
        "mov rbx,const_tbl + 1 ; initial optional args list with sob_nil";
        "cmp rax, 0";
        "mov rax,PARAM_COUNT";
        "sub rax,"^param_len;
        "cmp rax, 0 ; if no opt args, skip";
        "je end_of_loop_"^(int_to_str count);
        "dec rax";
        "opt_loop_"^(int_to_str count)^":";
        "mov r13, PVAR(r8)";
        "mov r12,rbx";
        "MAKE_PAIR(rbx,r13,r12)";
        "dec r8";
        "dec rax";
        "cmp rax, 0";
        "jge opt_loop_"^(int_to_str count)^"";
        "end_of_loop_"^(int_to_str count)^":";
        "mov rax,PARAM_COUNT";
        "sub rax,"^param_len^" ; rax <- number of opt args";
        "mov r15, rax";
        "SHIFT_FRAME_UP r15";
        "mov qword [rbp + WORD_BYTES*(4+"^param_len^")],rbx";
        "mov rax, "^param_len;
        "cmp r15,0 ; if i have 0 optional args, then ovveride magic"; 
        "je not_adding"^(int_to_str count);
        "inc rax";
        "not_adding"^(int_to_str count)^":";
        "mov qword [rbp + 3*WORD_BYTES],rax";
        "; GENERATE LAMBDA OPT BODY";
        (gener consts fvars body);
        "leave";
        "ret";
        "lambda_error_"^(int_to_str count)^":";
         (* error handling *)
        "mov rbx, 555";
        "end_lambda_opt_body_"^(int_to_str count)^":";
        ""
        ])
 and handle_applic_tp consts fvars e proc args_l = "
 ;APPLIC_TP START
 push 7 ; magic number
 " ^(List.fold_right (fun a b -> b^(gener consts fvars a)^"\npush rax\n") args_l "") ^
 "push "^(int_to_str (List.length args_l)) ^ "
 "
 ^ (gener consts fvars proc) ^ 
 "
 CLOSURE_ENV rsi,rax
 push rsi
 mov rsi,qword [rbp + 8 ]
 push rsi
 mov rsi, "^(int_to_str (4+(List.length args_l)))^"
 mov r13, qword[rbp]
 SHIFT_FRAME_REG rsi
 mov rbp, r13
 CLOSURE_CODE rsi, rax
 jmp rsi
; applicTP end
 "
and handle_applic_list consts fvars l = match l with
| [] -> ""
| hd::tl -> (gener consts fvars hd)^"\npush rax\n"^ handle_applic_list consts fvars tl
and reserve_last_and_do_nothing_func x = x;;
 
 
 
  let make_fvars_tbl asts = fvar_lists asts;;
  let generate consts fvars e = (lamb_depth := 0);gener consts fvars e;;
 
end;;

 (* TESTING FOR CONVINIENCE *)
 let read x = Reader.read_sexpr x;;
 let tag x = Tag_Parser.tag_parse_expression x;;
 let sem x = Semantics.run_semantics x;;

 let tag_read x = tag (read x);;
 let box_read x = (sem (tag_read x));;

 let e_list_after_all s = (List.map (fun x -> (sem (tag x))) (Reader.read_sexprs s));; (* for list of expr *)
 let e_gen_str s = e_list_after_all s;;
 
 let lexi_test x = Semantics.annotate_lexical_addresses (tag_read x);;
 let tail_test x = Semantics.annotate_tail_calls (lexi_test x);; 
 let tail_test_x x =  Semantics.annotate_tail_calls x;;
 let box_test x = Semantics.box_set (tail_test x);;
 let gen_test s = let e = box_test s in
      Code_Gen.generate (Code_Gen.make_consts_tbl [e]) (Code_Gen.make_fvars_tbl [e]) e;; 
let gene_exp_test e = Code_Gen.generate (Code_Gen.make_consts_tbl [e]) (Code_Gen.make_fvars_tbl [e]) e;; 

let gen e = Code_Gen.generate (Code_Gen.make_consts_tbl [e]) (Code_Gen.make_fvars_tbl [e]) e;;
let gen_const_tbl s = let e_l = (e_list_after_all s) in Code_Gen.make_consts_tbl e_l;; 
let gen_fvar_tbl s =  let e_l = (e_list_after_all s) in Code_Gen.make_fvars_tbl e_l;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;


