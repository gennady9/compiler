#use "code-gen.ml";;

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
   "apply", "apply_t"; "car", "car_"; "cdr", "cdr_"; "cons", "cons_"; "set-car!", "set_car_"; "set-cdr!", "set_cdr_"
  ];;

let make_prologue consts_tbl fvars_tbl =
  let get_const_address const = (get_const_address const consts_tbl) in
  let get_fvar_address const = (Pervasives.string_of_int (get_freevar_index const fvars_tbl)) in
  let make_primitive_closure (prim, label) =
"    MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")
    mov FVAR(" ^ (get_fvar_address prim)  ^ "), rax" in
  let make_constant (c, (a, s)) = s in
"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

section .bss
malloc_pointer:
    resq 1

section .data
const_tbl:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS " ^ get_const_address Void ^ "
%define SOB_NIL_ADDRESS " ^ get_const_address (Sexpr Nil) ^ "
%define SOB_FALSE_ADDRESS " ^ get_const_address (Sexpr (Bool false)) ^ "
%define SOB_TRUE_ADDRESS " ^ get_const_address (Sexpr (Bool true)) ^ "

fvar_tbl:
" ^ (String.concat "\n" (List.map (fun _ -> "dq T_UNDEFINED") fvars_tbl)) ^ "

global main
section .text
main:
    push rbp
    mov rbp, rsp
    ;; set up the heap
    mov rdi, GB(4)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 0
    push qword SOB_NIL_ADDRESS
    push qword T_UNDEFINED
    push rsp
    mov rbp,rsp
    ;add rbp,16

    jmp code_fragment

code_fragment:
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
" ^ (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^ "
; CODE-GEN START
debug_label:
";; 

let epilogue = "



; epilogue --- our-implemented-funcs
 
car_:
push rbp
mov rbp, rsp
mov rsi, PVAR(0)
SKIP_TYPE_TAG rsi, rsi
mov r13, rsi
mov rax,r13
leave
ret
 
cdr_:
push rbp
mov rbp, rsp
mov rsi, PVAR(0)
mov rsi,qword [rsi + 9]
mov r13, rsi
mov rax,r13
leave
ret
 
cons_:
push rbp
mov rbp, rsp
mov rsi, PVAR(0)
mov rax,PVAR(1)
MAKE_PAIR(r13, rsi, rax)
mov rax, r13
leave
ret
 
set_car_:
push rbp
mov rbp, rsp
push rsi
push r13
mov rsi, PVAR(0)
mov r13,PVAR(1)
mov qword [rsi +1],r13
mov rax, SOB_VOID_ADDRESS
pop r13
pop rsi
leave
ret
 
set_cdr_:
push rbp
mov rbp, rsp
push rsi
push r13
mov rsi, PVAR(0)
mov r13,PVAR(1)
mov qword [rsi +9],r13
mov rax, SOB_VOID_ADDRESS
pop r13
pop rsi
leave
ret
 
apply_t:
;enter
push rbp
mov rbp, rsp
apply_start:
; mov r11, qword [rbp] ; backup old rbp for later use

mov rsi, PARAM_COUNT
dec rsi ; rsi <- param count minus function
mov r9,rsi ;r9 is param counter, not including the function itself
dec r9 ;num of parms minus proc and list
mov r8, qword [rbp+8*(4+rsi)] ; r8 <- optional args list ( as SOB_PAIR )
push 5871714 ;magic number
;; reverse optional args list
mov rax,const_tbl+1 ; rax <- SOB_NIL


; handeling empty optional args list
;CAR rcx,r8  ; rcx <- car
;CAR rcx, r8
mov r12b, byte[r8]
cmp r12b, T_NIL
je end_put_into_stack

make_new_pair:  ;; make new reversed pair
CAR rcx,r8  ; rcx <- car
MAKE_PAIR(rbx,rcx,rax)
mov rax, rbx
CDR r8,r8
mov r12b, byte[r8]
inc r9
cmp r12b, T_PAIR
je make_new_pair
mov r8,rbx ; r8 and rbx now has new pair list
put_into_stuck:
CAR rcx,r8
push rcx
CDR r8,r8
mov r12b, byte[r8]
cmp r12b, T_PAIR
je put_into_stuck

end_put_into_stack:
mov r8,rsi ; r8, rsi <- param count minus function
dec r8 ; r8 <- param minus function minus opt list

push_the_rest:
cmp r8, 0
jle end_of_func
push qword[rbp+8*(4+r8)] ; pushing 
dec r8
jmp push_the_rest
end_of_func:
push r9 ; insert num of params inserted to stack
mov rax, [rbp+4*8] ; insert rax first param [ function to apply ]
CLOSURE_ENV rsi,rax
push rsi  ; insert env of given proc [ probably doesnt have one? ]
DEBUG_APPL:
; APPLIC TP
mov rsi,qword [rbp + 8 ] ; old ret addr
push rsi

;mov r9,PARAM_COUNT

      ;dec r9 ; now r9 has param minus function
DEBUG_BEFORE:
add r9,5

        ;; return close
                ;; test
                mov r13, qword [rbp]
                push r13

        ;push rbp
        ;mov rbp,rsp
SHIFT_FRAME_REG r9

;add rsp, 5*8
;sub rbp, 8
;mov rbp,rsp
CLOSURE_CODE rsi, rax
pop rbp
;mov rbp, r13
DEBUG_AFTER:
jmp rsi

mov rax, 0
leave
ret
  
  ";;

exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in
  let code =   (file_to_string "stdlib.scm") ^ (file_to_string infile) in
  let asts = string_to_asts code in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl in
  let code_fragment = (String.concat "\n\n"
                        (List.map
                           (fun ast -> ((generate ast) ^ "\ncall write_sob_if_not_void\n")) asts)) ^ "
add rsp, 4*8
pop rbp ;; maybe not needed
ret
; CODE-GEN END\n" in
  let provided_primitives = file_to_string "prims.s" in
                   
  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^
                    provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;
