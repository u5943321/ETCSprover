structure token :> token =
struct 
datatype token = Key of string | Id of string;


(*new stuff *)
exception TER of string

fun is_char(l,i,u) = l <= i andalso i <= u;

fun is_symbol c = 
let val cl = List.map ord [#"=",#"<",#">",#"-",#":",#"*",#"(",#")"]
in  mem c cl
end



fun is_letter_or_digit c =
    is_char(ord #"A",c,ord #"Z") orelse is_char(ord #"a",c,ord #"z") orelse is_char(ord #"0",c,ord #"9") orelse
    is_char(913,c,937) orelse is_char(945,c,969) orelse c = ord #"'" orelse c = ord #"_";


fun token_of a = if mem a ["ar","ob","o","!","?","==>","<=>",":","->","(*","*)","=="] then (Key a) else (Id a); 

fun char_of a = case a of Key a0 => a0 | Id a0 => a0

fun getN s n = 
    if n <= 0 then ([], s)
    else case UTF8.getChar s of
             NONE => ([], s)
           | SOME ((cs,_), s') =>
             let val (css, s'') = getN s' (Int.-(n ,1))
             in
                 (cs::css, s'')
             end

(*

(* abcde*) P(a) <=> Q(c)

PQ(A) 

"==="




*)(*string list * string -> token * string*)

fun scan_symbol s = 
    let 
        val (l1,s1) = getN s 1
        val (l2,s2) = getN s 2
        val (l3,s3) = getN s 3
        val syml = 
            ["=","<",">","-",":","*","(",")"]
    in 
        if l3 = ["=","=",">"] then (Key "==>",s3) else
        if l3 = ["<","=",">"] then (Key "<=>",s3) else
        if l2 = ["(","*"] then (Key "(*",s2) else
        if l2 = ["*",")"] then (Key "*)",s2) else
        if l2 = ["-",">"] then (Key "->",s2) else
        if l2 = ["=","="] then (Key "==",s2) else
        if mem (List.hd l1) syml then (Key $ List.hd l1,s1) else
        (Id "",s)
    end


(* lex "P (* a*) + Q";
val it = [Id "P", Key "+", Id "Q"]: token list

 lex "P (* a*) * Q";
val it = [Id "P", Key "*", Id "Q"]: token list

old scan symbol can do
*)
(*
fun scan_symbol (front, s) =
    case UTF8.getChar s of 
        NONE => 
        (token_of (String.concat $ rev front),s)
      | SOME ((s0,i),rest) => 
        if is_symbol i then 
            scan_symbol (s0 :: front,rest)
        else 
            (token_of (String.concat $ rev front),s)
*)


fun scan_ident (front, s) =
    case UTF8.getChar s of 
        NONE => 
        (token_of (String.concat $ rev front),s)
      | SOME ((s0,i),rest) => 
        if is_letter_or_digit i then 
            scan_ident (s0 :: front,rest)
        else 
            (token_of (String.concat $ rev front),s)



fun scan (front_toks, "") cd = 
    if cd = 0 then rev front_toks (*end of char list*)
    else raise TER "end of comment not found"
  (*long infix operators*)
  | scan (front_toks,s) 0 = 
    let val (tok,rest) = scan_symbol s
    in 
        case tok of 
            Key "==>" => 
            scan(Key"==>" :: front_toks,rest) 0 
          | Key "<=>" =>
            scan(Key"<=>" :: front_toks,rest) 0 
          | Key "->" =>
            scan(Key"->" :: front_toks,rest) 0 
          | Key "==" =>
            scan(Key"==" :: front_toks,rest) 0 
          | Key ":" =>
            scan(Key":" :: front_toks,rest) 0
          | Key "(*" => 
            scan(front_toks,rest) 1
          | _ =>
            case UTF8.getChar s of 
                NONE => raise TER "unexpected eng of string"
              | SOME ((s0,i),rest) => 
                if is_letter_or_digit i then 
                    scannext(front_toks,
                             scan_ident([s0],rest)) 0
                else
                    if mem s0 [" ","\n","\t"] then
                        scan (front_toks,rest) 0 
                    else
                    scan (Key s0 :: front_toks,rest) 0
    end
  | scan (front_toks,s) cd = 
    if cd < 0 then raise TER "unexpected comment depth"
    else 
        let val (tok,rest) = scan_symbol s
        in if tok = Key "(*" then 
               scan (front_toks, rest) (cd + 1) else
           if tok = Key "*)" then
               if cd > 0 then 
                   scan (front_toks, rest) (Int.-(cd,1)) else
               raise TER "beginning of comment not found" 
           else 
               case UTF8.getChar s of
                   SOME(_,rest) => scan (front_toks, rest) cd
                 | _ => raise TER "end of comment not found'"
        end
and scannext (front_toks, (tok, cs)) n = scan (tok::front_toks, cs) n;

fun enclose a = "(" ^ a ^ ")";

fun tokentoString tok = 
    case tok of 
        Key s => "Key" ^ enclose s
      | Id s => "Id" ^ enclose s

fun lex s = scan ([],s) 0

(*


fun token_of a = if mem a ["ar","ob","o","!","?"] then (Key a) else (Id a); 


fun is_char(l,c,u) = ord l <= ord c andalso ord c <= ord u;

fun is_letter_or_digit c =
    is_char(#"A",c,#"Z") orelse is_char(#"a",c,#"z") orelse is_char(#"0",c,#"9") orelse c = #"'";




fun scan_ident (front, c::cs) =
    if is_letter_or_digit c
    then scan_ident (c::front, cs)
    else (token_of (implode(rev front)), c::cs)
  | scan_ident (front, []) = (token_of (implode(rev front)), []);



(*
exception TER of string


fun lex s = scan ([],s) 0

fun scan (front_toks, "") cd = 
    if cd = 0 then rev front_toks (*end of char list*)
    else raise TER "end of comment not found"
  (*long infix operators*)
  | scan(front_toks, str) cd = 
    if cd = 0 then
        case getChar str of 
            SOME ((str0,i0),rest0) =>
            (case getChar str0 of 
                 SOME ((str1,i1),rest1) => 
                 case )
        let val ((str0,i0),rest0) = getChar str
            val ((str1,i1),rest1) = getChar str0
            val ((str2,i2),rest2) = getChar str1
        in 
            if str0 = "=" andalso
               str1 = "=" andalso str2 = ">"
            then scan (Key "==>" :: front_toks,rest2) 0 (*else
            if str0 = "<" andalso 
               str1 = "=" andalso str2 = ">"
            then scan (Key "<=>" :: front_toks,rest2) 0 else
            if str0 = "-" andalso str1 = ">"
            then scan (Key "->" :: front_toks,rest1) 0 else
            if str0 = ":"
            then scan (Key ":" :: front_toks,rest0) 0 else
            if str0 = " " orelse 
               str0 = "\t" orelse str0 = "\n"
            then scan (front_toks,rest0) 0 else
            if is_letter_or_digit i0 then
            scannext(front_toks, scan_ident([str0],rest0)) 0
         *)   else scan (Key(str0) :: front_toks,rest0)
        end
    else raise TER "unexpected comment depth"


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

fun string_of_char (# a) = a
*)


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


*)

end

