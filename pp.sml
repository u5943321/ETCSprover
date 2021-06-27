structure pp = 
struct 
open term form smpp symbols

infix >>

fun is_infix sym = 
    if mem sym ["*","+","^","=","o"] then true else false

(*also want this pp for HOLset... *)
 
fun paren pp = block HOLPP.INCONSISTENT 1 
                     (add_string "(" >> pp >> 
                                 add_string ")")

datatype gravity = LR of int option * int option (*prec of left and right neighbours*)

(*
Fun("*",[A, Fun("+",[B,C])])

*)

fun int_option_leq (n,n0) = 
    case n0 of NONE => false
             | SOME m => n <= m

fun int_option_less (n,n0) = 
    case n0 of NONE => false
             | SOME m => n < m

fun ppterm ss g t = 
    case t of 
        Var(n,s) => 
        if ss then paren 
                       (add_string n >> add_string " :" >>
                                   add_break (1,2) >> ppsort g s)
        else add_string n
      | Fun(f,s,[t1,t2]) => 
        if is_infix f then 
            case g of 
                LR(lg,rg) => 
                let 
                    val g1 = LR (lg, SOME (fxty f))
                    val g2 = LR (SOME (fxty f),rg)
                in 
                    if int_option_less (fxty f, lg) orelse int_option_leq (fxty f, rg) then 
                        add_string "(" >> 
                                   ppterm ss (LR (NONE, SOME (fxty f))) t1 >>  add_break(1,0) >> add_string f >> add_break(1,0) >>
                                   ppterm ss (LR (SOME (fxty f), NONE)) t2 >> add_string ")"
                    else 
                        ppterm ss g1 t1 >>  add_break(1,0) >> add_string f >> add_break(1,0) >>
                               ppterm ss g2 t2
                end
        else 
            add_string f >> paren (pr_list (ppterm ss g) (add_string "," >> add_break (1,0)) [t1,t2])
      | Fun(f,s,args) => 
        if args = [] then add_string f else
        add_string f >> paren (pr_list (ppterm ss g) (add_string "," >> add_break (1,0)) args)
      | Bound i => add_string "B" >> paren (add_string (int_to_string i))
and ppsort g s =
    case s of
        ob => add_string "ob"
      | ar(d,c) => 
        block HOLPP.INCONSISTENT 2 
              (ppterm false g d >> add_string " ->" >>
                      add_break(1,0) >> ppterm false g c)

val show_types = ref false
                     
fun PPterm printdepth _ t = let val s = ppterm (!show_types) (LR (NONE,NONE)) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPterm

          
fun ppform (ss:bool) (f:form) = 
    case f of 
        Pred(p,[t1,t2]) => 
        if is_infix p then 
            block HOLPP.INCONSISTENT 2 (ppterm ss (LR (NONE,NONE)) t1) >> add_break(1,0) >>
                  add_string p >> add_break(1,0) >>
                  block HOLPP.INCONSISTENT 2 (ppterm ss (LR (NONE,NONE)) t2)
        else
            add_string p >> paren (pr_list (ppterm ss (LR (NONE,NONE))) (add_string "," >> add_break (1,0)) [t1,t2])
      | Pred(p,args) => 
        add_string p >> paren (pr_list (ppterm ss (LR (NONE,NONE))) (add_string "," >> add_break (1,0)) args)
      | Conn(co,[f1,f2]) => 
        block HOLPP.INCONSISTENT 2
              (ppform ss f1 >> add_break(1,0) >> add_string co >> add_break(1,0) >> ppform ss f2)
      | Conn("~",[f]) => add_string "~" >> ppform ss f
      | Quant(q,n,s,b) =>
        block HOLPP.INCONSISTENT 2
              (add_string q >> add_break (1,0) >> 
                          (if s = ob then ppterm false (LR (NONE,NONE)) (Var(n,s)) else ppterm true (LR (NONE,NONE)) (Var(n,s))) >> add_string "." >> add_break (1,0) >> ppform ss (subst_bound (Var(n^"?",s)) b))
      | fVar fv => add_break (1,0)  >> add_string fv >> add_break (1,0) 
      | _ => raise ERR ("ill-formed formula",[],[],[f])




fun PPform printdepth _ t = let val s = ppform (!show_types) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPform

fun ppthm (thm(G,A,C)) =
    let
        val Gvl = List.map Var (HOLset.listItems G)
    in
        pr_list (ppterm true (LR (NONE,NONE))) (add_string "," >> add_break (1,0)) Gvl >> add_newline >>
                block HOLPP.INCONSISTENT 2 
                (pr_list (ppform false) (add_string "," >> add_newline) A) >>
                add_newline >>
                add_string "|-" >>
                add_newline >>
                block HOLPP.INCONSISTENT 2 
                (ppform false C)
    end 

fun PPthm printdepth _ th = let val s = ppthm th
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val printf = HOLPP.pp_to_string 75 (fn f => PPform 70 () f)  (*70-75 for the int*) 

val printth = HOLPP.pp_to_string 75 (fn th => PPthm 70 () th)  (*70-75 for the int*) 

val _ = PolyML.addPrettyPrinter PPthm

(*TODO: Dont print thm and goal as same*)

end
