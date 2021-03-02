structure token :> token =
struct 
datatype token = Key of string | Id of string;

fun is_char(l,c,u) = ord l <= ord c andalso ord c <= ord u;

fun is_letter_or_digit c =
    is_char(#"A",c,#"Z") orelse is_char(#"a",c,#"z") orelse is_char(#"0",c,#"9");

fun token_of a = if mem a ["ALL","EXISTS","ar","ob"] then (Key a) else (Id a); 

fun scan_ident (front, c::cs) =
    if is_letter_or_digit c
    then scan_ident (c::front, cs)
    else (token_of (implode(rev front)), c::cs)
  | scan_ident (front, []) = (token_of (implode(rev front)), []);

fun scan (front_toks, []) = rev front_toks (*end of char list*)
  (*long infix operators*)
  | scan (front_toks, (#"=")::(#"=")::(#">")::cs) = scan (Key"==>" ::front_toks, cs)
  | scan (front_toks, (#"<")::(#"=")::(#">")::cs) = scan (Key"<=>" ::front_toks, cs)
  | scan (front_toks, (#"-")::(#">")::cs) = scan (Key"->" ::front_toks, cs) 
  | scan (front_toks, (#":")::cs) = scan (Key":" ::front_toks, cs)
  (*blanks, tabs, newlines*)
  | scan (front_toks, (#" ")::cs) = scan (front_toks, cs)
  | scan (front_toks, (#"\t")::cs) = scan (front_toks, cs)
  | scan (front_toks, (#"\n")::cs) = scan (front_toks, cs)
  | scan (front_toks, c::cs) =
    if is_letter_or_digit c then scannext(front_toks, scan_ident([c], cs))
    else scan (Key(str c)::front_toks, cs)
and scannext (front_toks, (tok, cs)) = scan (tok::front_toks, cs);

fun enclose a = "(" ^ a ^ ")";

fun tokentoString tok = 
    case tok of 
        Key s => "Key" ^ enclose s
      | Id s => "Id" ^ enclose s

fun lex s = scan ([],explode s)

end

