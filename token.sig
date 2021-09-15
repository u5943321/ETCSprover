signature token = 
sig
datatype token = Key of string | Id of string;

(*
val is_char : char * char * char -> bool
val is_letter_or_digit : char -> bool
val token_of : string -> token
val scan_ident : char list * char list -> token * char list
val scan : token list * char list -> int -> token list
val scannext : token list * (token * char list) -> int -> token list
val enclose : string -> string
val tokentoString: token -> string
val lex : string -> token list
*)


val is_char : int * int * int -> bool
val is_letter_or_digit : int -> bool
val token_of : string -> token
val scan_ident : string list * string -> token * string
val scan : token list * string -> int -> token list
val scannext : token list * (token * string) -> int -> token list
val enclose : string -> string
val tokentoString: token -> string
val lex : string -> token list


end
