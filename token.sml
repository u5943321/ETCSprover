structure token :> token =
struct 
datatype token = Key of string | Id of string;

fun is_char(l,c,u) = ord l <= ord c andalso ord c <= ord u;

fun is_letter_or_digit c =
    is_char(#"A",c,#"Z") orelse is_char(#"a",c,#"z") orelse is_char(#"0",c,#"9") orelse c = #"'";

fun token_of a = if mem a ["ALL","EXISTS","ar","ob","o"] then (Key a) else (Id a); 

fun scan_ident (front, c::cs) =
    if is_letter_or_digit c
    then scan_ident (c::front, cs)
    else (token_of (implode(rev front)), c::cs)
  | scan_ident (front, []) = (token_of (implode(rev front)), []);

(*change scan to have cd (comment depth)
if see (*  then increase comment depth, and do not change front_toks, instead, drop everything.

when see *), reduce comment depth 

when cd = 0, proceed as usual tokenizing

*)
(*
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
*)

exception TER of string

fun scan (front_toks, []) cd = 
    if cd = 0 then rev front_toks (*end of char list*)
    else raise TER "end of comment not found"
  (*long infix operators*)
  | scan (front_toks, (#"(")::(#"*")::cs) cd = scan (front_toks,cs) (cd+1)
  | scan (front_toks, (#"*")::(#")")::cs) cd = 
    if cd > 0 then scan (front_toks,cs) (cd-1) else raise TER "beginning of comment not found" 
  | scan (front_toks,c::cs) cd =
    if cd = 0 then
        case (c::cs) of 
            (#"=")::(#"=")::(#">")::cs => scan (Key"==>" ::front_toks, cs) 0
          | (#"<")::(#"=")::(#">")::cs => scan (Key"<=>" ::front_toks, cs) 0
          | (#"-")::(#">")::cs => scan (Key"->" ::front_toks, cs) 0
          | (#":")::cs => scan (Key":" ::front_toks, cs) 0
          | (#" ")::cs => scan (front_toks, cs) 0
          | (#"\t")::cs => scan (front_toks, cs) 0 
          | (#"\n")::cs => scan (front_toks, cs) 0 
          | c:: cs => if is_letter_or_digit c then scannext(front_toks, scan_ident([c], cs)) 0
                     else scan (Key(str c)::front_toks, cs) 0
    else if cd < 0 then raise TER "unexpected comment depth" else scan (front_toks, cs) cd
and scannext (front_toks, (tok, cs)) n = scan (tok::front_toks, cs) n;


fun enclose a = "(" ^ a ^ ")";

fun tokentoString tok = 
    case tok of 
        Key s => "Key" ^ enclose s
      | Id s => "Id" ^ enclose s

fun lex s = scan ([],explode s) 0

(*change scan to handle comments scan for the 
(* and find *), then remove them all 

record how many comments


[QUOTE " (*#(*loc*) 481 4*)P(f)"]*)



end

