structure pp = 
struct 
open form term smpp

infix >>


fun paren pp = block HOLPP.INCONSISTENT 1 
                     (add_string "(" >> pp >> 
                                 add_string ")")

fun ppterm ss t = 
    case t of 
        Var(n,s) => 
        if ss then paren 
                       (add_string n >> add_string " :" >>
                       add_break (1,2) >> ppsort s)
        else add_string n
      | Fun(f,s,args) => 
        add_string f >> paren (pr_list (ppterm ss) (add_string "," >> add_break (1,0)) args)
and ppsort s =
    case s of
        ob => add_string "ob"
      | ar(d,c) => 
        block HOLPP.INCONSISTENT 2 
              (ppterm false d >> add_string " ->" >>
                      add_break(1,0) >> ppterm false c)

val show_types = ref false
                     
fun PPT printdepth _ t = let val s = ppterm (!show_types) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPT

end
