
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
type number =
  | Int of int
  | Float of float;;
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;



  
  let pack_final nt s =
    let (e, s) = (nt s) in
      e;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

  open PC;;

  let nt_digit_0_to_9 =
    pack (const (fun ch -> '0' <= ch && ch <= '9'))
      (fun ch -> (int_of_char ch) - 48);;

  let nt_natural =
    let rec make_nt_natural () =
      pack (caten nt_digit_0_to_9
              (disj (delayed make_nt_natural)
                 nt_epsilon))
        (function (a, s) -> a :: s) in
      pack (make_nt_natural())
        (fun s ->
           (List.fold_left
              (fun a b -> 10 * a + b)
              0
              s));;

  let nt_digit_a_to_f =
    pack (const (fun ch -> 'a' <= ch && ch <= 'f'))
      (fun ch -> (int_of_char ch) - 87);;

  let nt_digit_A_to_F =
    pack (const (fun ch -> 'A' <= ch && ch <= 'F'))
      (fun ch -> (int_of_char ch) - 55);;

  let nt_hex =
    let rec make_nt_hex () =
      pack (caten (disj (disj nt_digit_0_to_9 nt_digit_a_to_f) nt_digit_A_to_F)
              (disj (delayed make_nt_hex)
                 nt_epsilon))
        (function (a, s) -> a :: s) in
      pack (pack (caten  (caten (caten (char '#') (char_ci 'x')) (pack (maybe (disj (char '+') (char '-'))) (fun l -> match l with
        | None -> 1
        | (Some('+')) -> 1
        | (Some('-')) -> -1
        | l -> 8))) (make_nt_hex())) (function (((a,b),c),d) -> List.map (fun (x) -> c*x) d))
        (fun s ->
           (List.fold_left
              (fun a b -> 16 * a + b)
              0
              s));;
  let nt_little_float =
    let rec make_nt_natural () =
      pack (caten nt_digit_0_to_9
              (disj (delayed make_nt_natural)
                 nt_epsilon))
        (function (a, s) -> a :: s) in
      pack (pack (make_nt_natural()) (fun (x) -> List.map float_of_int x))
        (fun (s) ->
           (List.fold_right
              (fun a b -> b /. 10.  +. a /. 10.)
              s
              0.));;
  let nt_hexdigit = disj (disj nt_digit_0_to_9 nt_digit_a_to_f) nt_digit_A_to_F;;
  let nt_hex_natural = pack (pack (plus nt_hexdigit) (fun (a) -> List.map float_of_int a)) (fun (s) ->
        (List.fold_right
          (fun a b -> b /. 16.  +. a /. 16.)
          s
          0.));;


  let nt_hex_for_float =
    let rec make_nt_hex () =
      pack (caten (disj (disj nt_digit_0_to_9 nt_digit_a_to_f) nt_digit_A_to_F)
              (disj (delayed make_nt_hex)
                  nt_epsilon))
        (function (a, s) -> a :: s) in
      pack (make_nt_hex())
        (fun s ->
            (List.fold_left
              (fun a b -> 16 * a + b)
              0
              s));;

  let nt_hexfloat =
    pack (caten (caten (caten  (caten (caten (char '#') (char_ci 'x')) (pack (maybe (disj (char '+') (char '-'))) (fun l -> match l with
                | None -> 1.
                | (Some('+')) -> 1.
                | (Some('-')) -> -1.
                | l -> 8.))) (pack nt_hex_for_float  (fun (a) ->  float_of_int a))) (char '.')) nt_hex_natural) (fun (((((a,b),c),d),e),f) -> c*.(d+.f));;


  let nt_float =
    let rec make_nt_natural () =
      pack (caten nt_digit_0_to_9
              (disj (delayed make_nt_natural)
                 nt_epsilon))
        (function (a, s) -> a :: s) in
      pack (pack (caten (caten (pack (maybe (disj (char '+') (char '-'))) (fun l -> match l with
            | None -> 1.
            | (Some('+')) -> 1.
            | (Some('-')) -> -1.
            | l -> 8.)) (caten (pack (make_nt_natural()) (fun (x) -> List.map float_of_int x)) (char '.'))) (nt_little_float)) (fun ((a,(b,c)),d) -> ((List.map (fun (x) -> a*.x) b),a*.d)))
        (fun (s,d) ->
           (List.fold_left
              (fun a b -> 10. *. a +. b)
              0.
              s)+.d);;



  let nt_plusminusinteger num =
    let m= disj (caten (char '-')   (pack nt_natural (fun s -> -1*s))) (caten  (pack (maybe (char '+')) (fun l -> match l with
        | None -> '+'
        | (Some('+')) -> '+'
        | l -> 'f' )) nt_natural) num in
      (fun ((e,s),c) -> (s,c)) m;;

  let nt_integer num =
    nt_plusminusinteger num;;

  let nt_scientific_int =  pack (caten (pack (caten (pack (maybe (disj (char '+') (char '-'))) (fun l -> match l with
              | None -> '0'
              | (Some('+')) -> '0'
              | (Some('-')) -> '-'
              | l -> '8')) (plus (range_ci '0' '9'))) (fun (a,b) -> List.append (a::[]) b)) (pack (caten (char_ci 'e') (pack (caten (pack (maybe (disj (char '+') (char '-'))) (fun l -> match l with
              | None -> '0'
              | (Some('+')) -> '0'
              | (Some('-')) -> '-'
              | l -> '8')) (plus (range_ci '0' '9'))) (fun (a,b) -> List.append (a::[]) b))) (fun (a,b) -> List.append (a::[]) b)))
                             (fun (a,b) -> float_of_string (list_to_string (List.append a b)));;

  let nt_scientific_float =  pack (caten (pack (caten (pack (caten (pack (maybe (disj (char '+') (char '-'))) (fun l -> match l with
                    | None -> '0'
                    | (Some('+')) -> '0'
                    | (Some('-')) -> '-'
                    | l -> '8')) (plus (range_ci '0' '9'))) (fun (a,b) -> List.append (a::[]) b)) (pack (caten (char '.') (plus (range_ci '0' '9'))) (fun (a,b) -> List.append (a::[]) b))) (fun (a,b) -> List.append a b)) (pack (caten (char_ci 'e') (pack (caten (pack (maybe (disj (char '+') (char '-'))) (fun l -> match l with
                                              | None -> '0'
                                              | (Some('+')) -> '0'
                                              | (Some('-')) -> '-'
                                              | l -> '8')) (plus (range_ci '0' '9'))) (fun (a,b) -> List.append (a::[]) b) )) (fun (a,b) -> List.append (a::[]) b)))
                               (fun (a,b) -> float_of_string (list_to_string (List.append a b)));;

  let nt_charprefix = (word "#\\");;
  let nt_visiblechar = const (fun ch -> (int_of_char ch)>32 && (int_of_char ch)<=127);;
  let nt_namedchar = disj_list [(pack (word_ci "newline") (fun (a) -> '\010'));(pack (word_ci "page") (fun (a) -> '\012'));(pack (word_ci "space") (fun (a) -> ' '));(pack (word_ci "nul") (fun (a) -> '\000'));(pack (word_ci "return") (fun (a) -> '\013'));(pack (word_ci "tab") (fun (a) -> '\009'))];;
  let nt_hexchar = pack (caten (char_ci 'x') (plus nt_hexdigit)) (fun (d,c) -> char_of_int
            (List.fold_left
              (fun a b -> 16 * a + b)
              0
              c));;



  let nt_stringlitteralchar = pack (diff nt_any (one_of "\\\"")) (fun (a) -> a::[]);;

  let nt_string_meta_f = pack (word "\\f") (fun _ -> '\012'::[]);;
  let nt_string_meta_bkslsh = pack (word "\\\\") (fun _ -> '\\'::[]);;
  let nt_string_meta_quote = pack (word "\\\"") (fun _ -> '\"'::[]);;
  let nt_string_meta_t = pack (word "\\t") (fun _ -> '\t'::[]);;
  let nt_string_meta_n = pack (word "\\n") (fun _ -> '\n'::[]);;
  let nt_string_meta_r = pack (word "\\r") (fun _ -> '\r'::[]);;

  let nt_stringmetachar = disj_list [nt_string_meta_f ; nt_string_meta_bkslsh ; nt_string_meta_quote ; nt_string_meta_t ; nt_string_meta_n ; nt_string_meta_r];;
  let nt_stringhexchar = pack (caten (caten (word_ci "\\x") (pack (plus nt_hexdigit)
        (fun (c) -> (char_of_int
                      (List.fold_left
                          (fun a b -> 16 * a + b)
                          0
                          c))))) (char ';')) (fun ((a,b),c) -> b::[]);;

  let nt_string_char = disj_list [nt_stringmetachar;nt_stringlitteralchar;nt_stringhexchar];;

  let nt_symbolhex = (range_ci 'a' 'f') 
  let nt_symbolchar = disj_list [(range '0' '9');(range_ci 'a' 'z'); (const (fun ch -> ch=='!' ||ch=='$' ||ch=='^' ||ch=='*' ||ch=='-' ||ch=='_' ||ch=='=' ||ch=='+' ||ch=='<' ||ch=='>' ||ch=='?' ||ch=='/' ||ch==':' ))];;
  let which_quote x = match x with
    | "\'" -> "quote"
    | "`" -> "quasiquote"
    | "," -> "unquote"
    | ",@" -> "unquote-splicing"
    | x -> "no"


  let nt_symbol = pack (plus nt_symbolchar) (fun (a) -> ( list_to_string (List.map lowercase_ascii a)));;
  let nt_string = pack (caten (caten (char '\"') (star nt_string_char)) (char '\"')) (fun ((a,b),c) -> list_to_string (List.flatten b));;
  let nt_number = disj (pack (disj_list [nt_scientific_int;nt_scientific_float;nt_float;nt_hexfloat]) (fun (a) -> Float(a))) (pack (disj nt_plusminusinteger nt_hex) (fun (a) -> Int(a)));;
  let nt_char = pack (caten nt_charprefix (disj_list [nt_hexchar;nt_namedchar;nt_visiblechar])) (fun (a,b) -> b);;

  (* line comment impl *)
  let nt_smcol = char ';';;
  let nt_nwln = char '\n';;
  let nt_end_inp = pack nt_end_of_input (fun _ -> ' ');;

  let nt_notend = const (fun ch -> ch != '\n');;
  let nt_skip = pack (star nt_notend) (fun l -> ' ');;
  let nt_line_comm = pack (caten_list [nt_smcol;nt_skip;(disj nt_nwln nt_end_inp)]) (fun a -> ' ');;

  (* Parsers without spaces from right & left   AND   sexp conversion *)
  let _whitespaces_ = star (disj nt_whitespace nt_line_comm);;
  let _whitespacesplus_ = plus (disj nt_whitespace nt_line_comm);;

  let get_middle_parser_res a b c = 
    let x = caten a b in
    let x = caten x c in
    let x = pack x (fun ((_,e),_) -> e) in
    x;;

  let remove_space target = get_middle_parser_res _whitespaces_ target _whitespaces_ ;;  (* combined parser as shown in lecture*)
 (*   let x = caten _whitespaces_ target in
    let x = caten x _whitespaces_ in
    let x = pack x (fun ((_,e),_) -> e) in
    x;;
*)

  let nts_symbol = pack (remove_space nt_symbol) (fun p -> Symbol p);;
  let nts_string = pack (remove_space nt_string) (fun p -> String p);;
  let nts_char = pack (remove_space nt_char) (fun p -> Char p);;
  let nts_number = pack (remove_space (not_followed_by nt_number nt_symbol) ) (fun p -> Number p);;

  let nt_bool =
    let istrue = pack (word_ci "#t") (fun _ -> Bool true) in
    let isfalse = pack (word_ci "#f") (fun _ -> Bool false) in
    disj istrue isfalse;;
  let nts_bool = (remove_space nt_bool);;

  let lp =  remove_space (char '(');;
  let rp =  remove_space (char ')');;
  let lbp = remove_space (char '[');;
  let rbp = remove_space (char ']');;
  let dot = remove_space (char '.');;
  
  let rec pack_for_right nt f s=
    let (e,s) =  (nt s) in
    (f s);;

  let nt_left = disj lp lbp;;
  let nt_right = disj rp rbp;;
  let nt_close_dots = remove_space (word "...");;

  (* sexprs disjoint impl *)
  let rec nts_sexpr s = (disj_list [nts_quote;nts_bool;nts_nil;nts_number;nts_symbol;nts_string;nts_char;nt_sexpr_removed_spaces;nts_compound;dotted_closing;nts_compound_td]) s
  and nts_sexprs s = (star nts_sexpr) s
  and nts_compound s = (disj_list [nts_vector;nts_list;nts_dot_list] ) s
  and nts_compound_td s = (disj_list [nts_vector_td;nts_list_td;nts_dot_list_td] ) s
  and nt_sexpr_removed_spaces s = (remove_space nt_sexpr_comment) s
  and ignore_close_dots s = (pack_for_right (remove_space nt_close_dots) (nts_sexpr) s)
  and nt_sexpr_comment s =
    match s with
    | ' '::('#'::(';'::tl)) | '#'::(';'::tl) -> (remove_space (comments_counter 1)) tl
    | _ -> raise X_no_match
  and comments_counter num str_list = 
    match str_list with
    | ' '::('#'::(';'::tl)) | '#'::(';'::tl) -> (remove_space (comments_counter (num + 1))) tl
    | _ -> sexpr_after_comment num str_list
  and sexpr_after_comment num str_list =
    if (num == 0 || str_list == []) then (nts_sexpr str_list) else (nts_sexpr_without_comment num str_list)
  and nts_sexpr_without_comment num str_list = (pack_for_right (diff nts_sexpr nt_sexpr_removed_spaces) (sexpr_after_comment (num-1)) str_list)

  and nt_sexpr_inc_dot s = (disj_list [(remove_space (diff nts_sexpr dotted_closing)) ; (remove_space nts_compound)]) s
  and dotted_closing s = pack (remove_space (caten nts_compound_td nt_close_dots)) (fun (a,b) -> a) s
  and nts_dot_list_td s =
    let nt_dotted_list = (caten (plus nt_sexpr_inc_dot) (caten dot nt_sexpr_inc_dot)) in
    let nt_dotted_list = get_middle_parser_res nt_left nt_dotted_list (maybe nt_right) in
    let nt_dotted_list = pack nt_dotted_list (fun (l,(c,r)) -> List.fold_right (fun a b -> Pair(a,b)) l r) in
      ((remove_space nt_dotted_list) s)
  and nts_list_td s =
    let x = get_middle_parser_res nt_left (star (diff nt_sexpr_inc_dot nt_close_dots)) (maybe nt_right) in
    let x = pack x (fun l -> List.fold_right (fun a b -> Pair(a,b)) l Nil) in
      ((remove_space x) s)
  and nts_vector_td s =
    let x = get_middle_parser_res lp (star nt_sexpr_inc_dot) (maybe rp) in
    let x = pack (caten (char '#') x) (fun (a, l) -> Vector l) in
    ((remove_space x) s)
  and nts_nil s = (pack (caten (caten lp _whitespaces_) rp) (fun _ -> Nil)) s
  and nts_dot_list s =
    let nt_dotted_list = (caten (plus nts_sexpr) (caten dot nts_sexpr)) in
    let nt_dotted_list = get_middle_parser_res nt_left nt_dotted_list (nt_right) in
    let nt_dotted_list = pack nt_dotted_list (fun (l,(c,r)) -> List.fold_right (fun a b -> Pair(a,b)) l r) in
      ((remove_space nt_dotted_list) s)
  and nts_list s =
    let x = get_middle_parser_res nt_left (star (diff nts_sexpr nt_close_dots)) (nt_right) in
    let x = pack x (fun l -> List.fold_right (fun a b -> Pair(a,b)) l Nil) in
      ((remove_space x) s)
  and nts_vector s =
    let x = get_middle_parser_res lp (star nts_sexpr) (rp) in
    let x = pack (caten (char '#') x) (fun (a, l) -> Vector l) in
    ((remove_space x) s)
  and nt_quote s = (pack (caten (disj_list [(word "\'");(word "`");(word ",@");(word ",")]) (nts_sexpr))
                              (fun (a,b) -> Pair(Symbol((which_quote (list_to_string a))), Pair(b,Nil)))) s
  and nts_quote s = ((remove_space nt_quote) s);;




(* three dots start 
  let is_substr_3_dots str =
    (String.equal str "...");;


  let rec find_next_3_dots str =
    if(String.contains str '.')
    then (
      let dot_ndx = (String.index str '.') in
      let rest_of_str = (String.length str) - (dot_ndx + 1) in
      if(is_substr_3_dots (String.sub str dot_ndx 3) )
      then (
        dot_ndx
      ) else (
        let next = (find_next_3_dots (String.sub str (dot_ndx+1) rest_of_str)) in
        if(next > 0)
        then (dot_ndx + next + 1)
        else -1
      )
    )
    else -1;;

  let rec change_dots_helper l brack_list=
    if((List.length l) == 0)
    then(brack_list) # Vomit all brackets 
    else(
      let ch = (List.hd l) in
      if(Char.equal ch '(') then (change_dots_helper (List.tl l) (')'::brack_list))
      else if(Char.equal ch '[') then (change_dots_helper (List.tl l) (']'::brack_list))
      else if((Char.equal ch ')') || (Char.equal ch ']')) then (
          if(Char.equal (List.hd brack_list) ch)
          then(change_dots_helper (List.tl l) (List.tl brack_list))
          else(raise X_no_match)
          )
      else (change_dots_helper (List.tl l) brack_list)
    );;
    
  let change_dots str = str ^ (list_to_string (change_dots_helper (string_to_list str) []));; 

  let rec pre_read str =
    let not_found = -1 in
    let next_index = (find_next_3_dots str) in
    let rest_of_str = (String.length str) - (next_index + 3) in
    if(next_index != not_found)
    then ( 
      let before_dots = (change_dots (String.sub str 0 (next_index))) in
      let after_dots = (String.sub str (next_index + 3) rest_of_str) in
      pre_read (before_dots ^ after_dots)
    )
    else (str);;
 three dots end *)




let read_sexpr string = pack_final nts_sexpr (string_to_list string);;

let read_sexprs string = if(String.length string <1) then ([]) else (pack_final nts_sexprs (string_to_list string));;

end;; (* struct Reader *)


