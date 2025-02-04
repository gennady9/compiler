%define T_UNDEFINED 0
%define T_VOID 1
%define T_NIL 2
%define T_INTEGER 3
%define T_FLOAT 4
%define T_BOOL 5
%define T_CHAR 6
%define T_STRING 7
%define T_SYMBOL 8
%define T_CLOSURE 9
%define T_PAIR 10
%define T_VECTOR 11
	
%define CHAR_NUL 0
%define CHAR_TAB 9
%define CHAR_NEWLINE 10
%define CHAR_PAGE 12
%define CHAR_RETURN 13
%define CHAR_SPACE 32
%define CHAR_DOUBLEQUOTE 34
%define CHAR_BACKSLASH 92
	
%define TYPE_SIZE 1
%define WORD_SIZE 8
%define WORD_BYTES 8
	
%define KB(n) n*1024
%define MB(n) 1024*KB(n)
%define GB(n) 1024*MB(n)


%macro SKIP_TYPE_TAG 2
	mov %1, qword [%2+TYPE_SIZE]	
%endmacro	

%define INT_VAL SKIP_TYPE_TAG

%macro CHAR_VAL 2
	movzx %1, byte [%2+TYPE_SIZE]
%endmacro

%define FLOAT_VAL SKIP_TYPE_TAG

%define STRING_LENGTH SKIP_TYPE_TAG

%define VECTOR_LENGTH SKIP_TYPE_TAG

%define SYMBOL_VAL SKIP_TYPE_TAG

%macro STRING_ELEMENTS 2
	lea %1, [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define VECTOR_ELEMENTS STRING_ELEMENTS

%define CAR SKIP_TYPE_TAG

%macro CDR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define CLOSURE_ENV CAR

%define CLOSURE_CODE CDR

%define PVAR(n) qword [rbp+(4+n)*WORD_SIZE]
%define FVAR(i) qword [fvar_tbl+i*WORD_BYTES]
	
%define SOB_UNDEFINED T_UNDEFINED
%define SOB_NIL T_NIL
%define SOB_VOID T_VOID
%define SOB_FALSE word T_BOOL
%define SOB_TRUE word (1 << TYPE_SIZE | T_BOOL)

; returns %2 allocated bytes in register %1
; Supports using with %1 = %2
%macro MALLOC 2
	add qword [malloc_pointer], %2
	push %2
	mov %1, qword [malloc_pointer]
	sub %1, [rsp]
	add rsp, 8
%endmacro
	
; Creates a short SOB with the
; value %2
; Returns the result in register %1
%macro MAKE_CHAR_VALUE 2
	MALLOC %1, 1+TYPE_SIZE
	mov byte [%1], T_CHAR
	mov byte [%1+TYPE_SIZE], %2
%endmacro

; Creates a long SOB with the
; value %2 and type %3.
; Returns the result in register %1
%macro MAKE_LONG_VALUE 3
	MALLOC %1, TYPE_SIZE+WORD_SIZE
	mov byte [%1], %3
	mov qword [%1+TYPE_SIZE], %2
%endmacro

%define MAKE_INT(r,val) MAKE_LONG_VALUE r, val, T_INTEGER
%define MAKE_FLOAT(r,val) MAKE_LONG_VALUE r, val, T_FLOAT
%define MAKE_CHAR(r,val) MAKE_CHAR_VALUE r, val

; Create a string of length %2
; from char %3.
; Stores result in register %1
%macro MAKE_STRING 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1,WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov byte [%1+rcx], %3
	jmp %%str_loop
%%str_loop_end:
	pop rcx
	sub %1, WORD_SIZE+TYPE_SIZE
%endmacro

; Create a vector of length %2
; from SOB at %3.
; Stores result in register %1
%macro MAKE_VECTOR 3
	lea %1, [%2*WORD_SIZE+WORD_SIZE+TYPE_SIZE] 
	MALLOC %1, %1
	mov byte [%1], T_VECTOR
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1, WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%vec_loop:
	jz %%vec_loop_end
	dec rcx
	mov qword [%1+rcx*WORD_SIZE], %3
	jmp %%vec_loop
%%vec_loop_end:
	sub %1, WORD_SIZE+TYPE_SIZE
	pop rcx
%endmacro

; Create a String of length %2
; from SOB at %3.
; Stores result in register %1
%macro MAKE_STRING_V 3
	lea %1, [%2*WORD_SIZE+WORD_SIZE+TYPE_SIZE] 
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1, WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov qword [%1+rcx*WORD_SIZE], %3
	jmp %%str_loop
%%str_loop_end:
	sub %1, WORD_SIZE+TYPE_SIZE
	pop rcx
%endmacro

;;; Creates a SOB with tag %2 
;;; from two pointers %3 and %4
;;; Stores result in register %1
%macro MAKE_TWO_WORDS 4 
        MALLOC %1, TYPE_SIZE+WORD_BYTES*2
        mov byte [%1], %2
        mov qword [%1+TYPE_SIZE], %3
        mov qword [%1+TYPE_SIZE+WORD_BYTES], %4
%endmacro

%macro MAKE_WORDS_LIT 3
	db %1
        dq %2
        dq %3
%endmacro

%define MAKE_PAIR(r, car, cdr) \
        MAKE_TWO_WORDS r, T_PAIR, car, cdr

%define MAKE_LITERAL_PAIR(car, cdr) \
        MAKE_WORDS_LIT T_PAIR, car, cdr

%define MAKE_CLOSURE(r, env, body) \
        MAKE_TWO_WORDS r, T_CLOSURE, env, body


; our add-ons to compiler.s
%define PARAM_COUNT qword [rbp+3*WORD_BYTES]

%macro MAKE_LITERAL 2 ; Make a literal of type %1
; followed by the definition %2
db %1
%2
%endmacro
%define MAKE_LITERAL_INT(val) MAKE_LITERAL T_INTEGER, dq val
%define MAKE_LITERAL_FLOAT(val) MAKE_LITERAL T_FLOAT, dq val
%define MAKE_LITERAL_CHAR(val) MAKE_LITERAL T_CHAR, db val
%define MAKE_LITERAL_SYMBOL(val) MAKE_LITERAL T_SYMBOL, dq val
%define MAKE_NIL db T_NIL
%define MAKE_VOID db T_VOID
%define MAKE_BOOL(val) MAKE_LITERAL T_BOOL, db val

; literal string macro, was changed to vector-style macro
%macro MAKE_LITERAL_STRING 0-*
db T_STRING
dq %0
%rep %0
db %1    ; TODO - should it be db or dq like vector
%rotate 1
%endrep
%endmacro

; MAKE_LITERAL_VECTOR
%macro MAKE_LITERAL_VECTOR 0-*
db T_VECTOR
dq %0
%rep %0
dq %1
%rotate 1
%endrep
%endmacro


%macro SHIFT_FRAME_UP 1
; 
; backuped registers
push rax ;
push rcx ;

mov rax, PARAM_COUNT
add rax, 4 ; adding the total num of other cells that below the parameters
sub rax, %1  ;removing num of opt params
mov r8,%1  ; r8 <- r15 (optional args count)
cmp r8,1
jle .end
dec r8

; loop initial
cmp rax, 0 ; rax has number of cells in frame, not including optional params
.shift_loop_start:
jz .shift_loop_end
dec rax

mov r13,r8 ; r8 has (opt args - 1)
add r13,rax
mov r9, qword [rbp+WORD_BYTES*rax]
mov qword [rbp+WORD_BYTES*r13], r9

cmp rax, 0
jmp .shift_loop_start
.shift_loop_end:
shl r8, 3 ; r8 has num of param, we multiply by BYTE SIZE for the total offset


; update stack pointer 'r8' times
add rbp,r8
add rsp,r8
.end:
;restore backuped registers
pop rcx
pop rax 
%endmacro
 
%macro EXTENV 2;num of params,depth
; EXTEND ENVIROMENT MACRO START
			; backup registers
			;push rdi
			;push rax
			;push r15


			mov r14, (1+%2) * WORD_BYTES  ; rbx <- env+1
			MALLOC r14, r14  ; number of extended envronments
			;mov r14,rbx ; backuping because rbx is loop counter

			mov rcx, %1 
			inc rcx ; rcx < num of params + 1
			shl rcx, 3 ; same as rsi * WORD_BYTES 
			MALLOC rcx, rcx  ; extend place for array of params

			; copying params to rib
			mov rax, 0 
			;%assign i 0
			.loop_ext_env:
			cmp rax, %1 ; number of params in stack
			je .loop_ext_env_end ; jump if 0 cycles
					mov r9,qword [rbp + WORD_BYTES*(4+rax)]
					mov qword [rcx + WORD_BYTES*rax],r9
				;%assign i i+1
				inc rax
				jmp .loop_ext_env

			
			.loop_ext_env_end:
			mov qword [r14],rcx ; insert new rib to ext env

			mov r9,qword [rbp + 16] ; r9 <- old env
			; checking if old env is SOB_NIL
			mov r10b, byte [r9]
			cmp r10b, SOB_NIL
			je .continue

			; copying old environments ribs to new extended env

				%assign i 0
					%rep %2
			mov r8,qword [r9+WORD_BYTES*i] ; get from old env
			mov qword [r14 + WORD_BYTES*(i+1)],r8 ; update rbx
				%assign i i+1
			;mov qword [rbp+16],rbx ;; override old env with extended?
					%endrep

			.continue:
			mov rbx, r14
			;pop r15
			;pop rax
			;pop rdi
			; EXTEND ENVIROMENT MACRO END, extended env stored in rbx
%endmacro

 
%macro SHIFT_FRAME 1 ; %1 = size of frame (constant)
push rax
mov rax, PARAM_COUNT
add rax, 5
mov rcx,rax
shl rcx, 3
    %assign i 1
    %rep %1
dec rax
mov r8,[rbp-WORD_BYTES*i]
mov [rbp+WORD_BYTES*rax], r8
        %assign i i+1
        %endrep
pop rax
; add rbp, rcx  ;;; TODO- check if needed
add rsp,rcx
%endmacro

%macro SHIFT_FRAME_REG 1 ; %1 = size of frame
push rax
mov rax, PARAM_COUNT
add rax, 5
mov rcx,rax
shl rcx, 3

push rbx

mov rbx,0

.loop_start:
cmp %1,0
jle .loop_end
		dec rax

		dec rbx

		mov r8,qword [rbp+WORD_BYTES*rbx]
		mov [rbp+WORD_BYTES*rax], r8

	dec %1
	jmp .loop_start
.loop_end:

pop rbx
pop rax

add rsp,rcx ; rcx has size of frame + params in bytes
;mov rbp,rsp
%endmacro

extern exit, printf, malloc
global write_sob, write_sob_if_not_void

	
write_sob_undefined:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .undefined
	call printf

	leave
	ret

section .data
.undefined:
	db "#<undefined>", 0

write_sob_integer:
	push rbp
	mov rbp, rsp

	INT_VAL rsi, rsi
	mov rdi, .int_format_string
	mov rax, 0
	call printf

	leave
	ret

section .data
.int_format_string:
	db "%ld", 0

write_sob_float:
	push rbp
	mov rbp, rsp

	FLOAT_VAL rsi, rsi
	movq xmm0, rsi
	mov rdi, .float_format_string
	mov rax, 1

	mov rsi, rsp
	and rsp, -16
	call printf
	mov rsp, rsi

	leave
	ret
	
section .data
.float_format_string:
	db "%f", 0		

write_sob_char:
	push rbp
	mov rbp, rsp

	CHAR_VAL rsi, rsi

	cmp rsi, CHAR_NUL
	je .Lnul

	cmp rsi, CHAR_TAB
	je .Ltab

	cmp rsi, CHAR_NEWLINE
	je .Lnewline

	cmp rsi, CHAR_PAGE
	je .Lpage

	cmp rsi, CHAR_RETURN
	je .Lreturn

	cmp rsi, CHAR_SPACE
	je .Lspace
	jg .Lregular

	mov rdi, .special
	jmp .done	

.Lnul:
	mov rdi, .nul
	jmp .done

.Ltab:
	mov rdi, .tab
	jmp .done

.Lnewline:
	mov rdi, .newline
	jmp .done

.Lpage:
	mov rdi, .page
	jmp .done

.Lreturn:
	mov rdi, .return
	jmp .done

.Lspace:
	mov rdi, .space
	jmp .done

.Lregular:
	mov rdi, .regular
	jmp .done

.done:
	mov rax, 0
	call printf

	leave
	ret

section .data
.space:
	db "#\space", 0
.newline:
	db "#\newline", 0
.return:
	db "#\return", 0
.tab:
	db "#\tab", 0
.page:
	db "#\page", 0
.nul:
	db "#\nul", 0
.special:
	db "#\x%02x", 0
.regular:
	db "#\%c", 0

write_sob_void:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .void
	call printf

	leave
	ret

section .data
.void:
	db "#<void>", 0
	
write_sob_bool:
	push rbp
	mov rbp, rsp

	cmp word [rsi], SOB_FALSE
	je .sobFalse
	
	mov rdi, .true
	jmp .continue

.sobFalse:
	mov rdi, .false

.continue:
	mov rax, 0
	call printf	

	leave
	ret

section .data			
.false:
	db "#f", 0
.true:
	db "#t", 0

write_sob_nil:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .nil
	call printf

	leave
	ret

section .data
.nil:
	db "()", 0

write_sob_string:
	push rbp
	mov rbp, rsp

	push rsi

	mov rax, 0
	mov rdi, .double_quote
	call printf
	
	pop rsi

	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rbx, CHAR_TAB
	je .ch_tab
	cmp rbx, CHAR_NEWLINE
	je .ch_newline
	cmp rbx, CHAR_PAGE
	je .ch_page
	cmp rbx, CHAR_RETURN
	je .ch_return
	cmp rbx, CHAR_DOUBLEQUOTE
	je .ch_doublequote
	cmp rbx, CHAR_BACKSLASH
	je .ch_backslash
	cmp rbx, CHAR_SPACE
	jl .ch_hex
	
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx
	jmp .printf
	
.ch_tab:
	mov rdi, .fs_tab
	mov rsi, rbx
	jmp .printf
	
.ch_page:
	mov rdi, .fs_page
	mov rsi, rbx
	jmp .printf
	
.ch_return:
	mov rdi, .fs_return
	mov rsi, rbx
	jmp .printf

.ch_newline:
	mov rdi, .fs_newline
	mov rsi, rbx
	jmp .printf

.ch_doublequote:
	mov rdi, .fs_doublequote
	mov rsi, rbx
	jmp .printf

.ch_backslash:
	mov rdi, .fs_backslash
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .double_quote
	call printf

	leave
	ret
section .data
.double_quote:
	db CHAR_DOUBLEQUOTE, 0
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	
.fs_tab:
	db "\t", 0
.fs_page:
	db "\f", 0
.fs_return:
	db "\r", 0
.fs_newline:
	db "\n", 0
.fs_doublequote:
	db CHAR_BACKSLASH, CHAR_DOUBLEQUOTE, 0
.fs_backslash:
	db CHAR_BACKSLASH, CHAR_BACKSLASH, 0

write_sob_pair:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .open_paren
	call printf

	mov rsi, [rsp]

	CAR rsi, rsi
	call write_sob

	mov rsi, [rsp]
	CDR rsi, rsi
	call write_sob_pair_on_cdr
	
	add rsp, 1*8
	
	mov rdi, .close_paren
	mov rax, 0
	call printf

	leave
	ret

section .data
.open_paren:
	db "(", 0
.close_paren:
	db ")", 0

write_sob_pair_on_cdr:
	push rbp
	mov rbp, rsp

	mov bl, byte [rsi]
	cmp bl, T_NIL
	je .done
	
	cmp bl, T_PAIR
	je .cdrIsPair
	
	push rsi
	
	mov rax, 0
	mov rdi, .dot
	call printf
	
	pop rsi

	call write_sob
	jmp .done

.cdrIsPair:
	CDR rbx, rsi
	push rbx
	CAR rsi, rsi
	push rsi
	
	mov rax, 0
	mov rdi, .space
	call printf
	
	pop rsi
	call write_sob

	pop rsi
	call write_sob_pair_on_cdr

	add rsp, 1*8

.done:
	leave
	ret

section .data
.space:
	db " ", 0
.dot:
	db " . ", 0

write_sob_vector:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .fs_open_vector
	call printf

	pop rsi

	VECTOR_LENGTH rcx, rsi
	cmp rcx, 0
	je .done
	VECTOR_ELEMENTS rax, rsi

	push rcx
	push rax
	mov rsi, qword [rax]
	call write_sob
	pop rax
	pop rcx
	dec rcx
	add rax, 8

.loop:
	cmp rcx, 0
	je .done

	push rcx
	push rax
	mov rax, 0
	mov rdi, .fs_space
	call printf
	
	pop rax
	push rax
	mov rsi, qword [rax]
	call write_sob
	pop rax
	pop rcx
	dec rcx
	add rax, 8
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .fs_close_vector
	call printf

	leave
	ret

section	.data
.fs_open_vector:
	db "#(", 0
.fs_close_vector:
	db ")", 0
.fs_space:
	db " ", 0

write_sob_symbol:
	push rbp
	mov rbp, rsp

	SYMBOL_VAL rsi, rsi
	
	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

	mov rdx, rcx

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rcx, rdx
	jne .ch_simple
	cmp rbx, '+'
	je .ch_hex
	cmp rbx, '-'
	je .ch_hex
	cmp rbx, 'A'
	jl .ch_hex

.ch_simple:
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	leave
	ret
	
section .data
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	

write_sob_closure:
	push rbp
	mov rbp, rsp

	CLOSURE_CODE rdx, rsi
	CLOSURE_ENV rsi, rsi

	mov rdi, .closure
	mov rax, 0
	call printf

	leave
	ret
section .data
.closure:
	db "#<closure [env:%p, code:%p]>", 0

section .text
write_sob:
	mov rbx, 0
	mov bl, byte [rsi]	
	jmp qword [.jmp_table + rbx * 8]

section .data
.jmp_table:
	dq write_sob_undefined, write_sob_void, write_sob_nil
	dq write_sob_integer, write_sob_float, write_sob_bool
	dq write_sob_char, write_sob_string, write_sob_symbol
	dq write_sob_closure, write_sob_pair, write_sob_vector

section .text
write_sob_if_not_void:
	mov rsi, rax
	mov bl, byte [rsi]
	cmp bl, SOB_VOID
	je .continue

	call write_sob
	
	mov rax, 0
	mov rdi, .newline
	call printf
	
.continue:
	ret
section .data
.newline:
	db CHAR_NEWLINE, 0
