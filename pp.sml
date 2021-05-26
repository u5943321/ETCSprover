structure pp = 
struct 
open form term smpp

infix >>

(*also want this pp for HOLset... *)
 
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
      | Fun(f,s,[t1,t2]) => ppterm ss t1 >>  add_break(1,0) >> add_string f >> add_break(1,0) >> ppterm ss t2
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




 
 (*
fun pp_cont dpth s =
    let
        open HOLPP
         fun ppi ((n:string,s:sort)) = PPT dpth () (Var(n,s))
    in
        if dpth <= 0 then add_string "HOLset{...}"
        else
            block CONSISTENT 0 [
                add_string "HOLset{",
                block INCONSISTENT 7
                      (pr_list ppi [add_string ",",add_break (1,0)] (listItems s)),
                add_string "}"
            ]
    end

fun PPsss printdepth _ sss = let val s = pp_cont 70 sss 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end
*)


val print = HOLPP.pp_to_string 75 (fn f => PPF 70 () f)  (*70-75 for the int*)


          
fun ppform (ss:bool) (f:form) = 
    case f of 
        Pred(p,[t1,t2]) => ppterm ss t1 >> add_break(1,0) >> add_string p >> add_break(1,0) >> ppterm ss t2
      | Pred(p,args) => 
        add_string p >> paren (pr_list (ppterm ss) (add_string "," >> add_break (1,0)) args)
      | Conn(co,[f1,f2]) => 
        block HOLPP.INCONSISTENT 2
              (ppform ss f1 >> add_break(1,0) >> add_string co >> add_break(1,0) >> ppform ss f2)
      | Conn("~",[f]) => add_string "~" >> ppform ss f
      | Quant(q,n,s,b) =>
        block HOLPP.INCONSISTENT 2
              (add_string q >> add_break (1,0) >> ppterm ss (Var(n,s)) >> add_string "." >> add_break (1,0) >> ppform ss (subst_bound (Var(n,s)) b))
      | _ => raise ERR "ill-formed formula"


(*
HOLset.foldl

HOLset.ppHOLset
*)



fun PPF printdepth _ t = let val s = ppform (!show_types) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPF

fun ppthm (thm(G,A,C)) =
    let
        val Gvl = List.map Var (HOLset.listItems G)
    in
        pr_list (ppterm true) (add_string "," >> add_break (1,0)) Gvl >>
                block HOLPP.INCONSISTENT 2 
                (pr_list (ppform false) (add_string "," >> add_break (1,0)) A >>
                ppform false C)
    end 

fun PPTH printdepth _ th = let val s = ppthm th
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPTH


end
