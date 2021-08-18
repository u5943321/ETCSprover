structure pp = 
struct 
open (* term form logic*) smpp

infix >>

fun is_infix sym = 
    if mem sym ["*","+","^","=","o"] then true else false

 
fun paren pp = block HOLPP.INCONSISTENT 1 
                     (add_string "(" >> pp >> 
                                 add_string ")")

datatype gravity = LR of int option * int option (*prec of left and right neighbours*)


fun int_option_leq (n,n0) = 
    case n0 of NONE => false
             | SOME m => n <= m

fun int_option_less (n,n0) = 
    case n0 of NONE => false
             | SOME m => n < m



fun ppterm ss g t = 
    case view_term t of 
        vVar(n,s) => 
        if ss then paren 
                       (add_string n >> add_string " :" >>
                                   add_break (1,2) >> ppsort g s)
        else add_string n
      | vFun(f,s,[t1,t2]) => 
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
            if f = "pa" then 
                add_string "<" >> ppterm ss g t1 >> add_string " , " >> ppterm ss g t2 >> add_string ">"
            else
            add_string f >> paren (pr_list (ppterm ss g) (add_string "," >> add_break (1,0)) [t1,t2])
      | vFun(f,s,args) => 
        if length args = 0 then add_string f else
        add_string f >> paren (pr_list (ppterm ss g) (add_string "," >> add_break (1,0)) args)
      | vB i => add_string "B" >> paren (add_string (int_to_string i))
and ppsort g s =
    case view_sort s of
        vo => add_string "ob"
      | va(d,c) => 
        block HOLPP.INCONSISTENT 2 
              (ppterm false g d >> add_string " ->" >>
                      add_break(1,0) >> ppterm false g c)


fun PPsort printdepth _ st = let val s = ppsort (LR (NONE,NONE)) st
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPsort

val show_types = ref false
                     
fun PPterm printdepth _ t = let val s = ppterm (!show_types) (LR (NONE,NONE)) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPterm


fun pr_tlist g tl = 
    case tl of
        h :: h' :: t => if eq_sort(sort_of h,mk_ob_sort) then ppterm false g h >> add_break (1,0) >> pr_tlist g (h' :: t)
                  else ppterm true g h >> add_break (2,0) >> pr_tlist g (h' :: t)
      | [t] => if eq_sort(sort_of t,mk_ob_sort) then
                       ppterm false g t else ppterm true g t
      | [] => add_string ""

fun strip_forall' f = 
    case view_form f of 
        vQ("!",n,s,b) => 
        let val (b1,l) = strip_forall' (substf ((n,s),mk_var (n^"#") s) b) in
            (b1,(n,s) :: l) end
      | _ => (f,[])

fun strip_exists' f = 
    case view_form f of 
        vQ("?",n,s,b) => 
        let val (b1,l) = strip_exists (substf ((n,s),mk_var (n^"#") s) b) in
            (b1,(n,s) :: l) end
      | _ => (f,[])

fun strip_quants' f = 
    case view_form f of 
        vQ(q,_,_,_) => if q = "!" then strip_forall' f 
                          else if q = "?" then strip_exists' f 
                          else raise ERR ("strip_exists.not a quantified formula",[],[],[f])
      | _ => raise ERR ("strip_exists.not a quantified formula",[],[],[f])



fun ppform (ss:bool) g (f:form) = 
    case view_form f of 
        vPred(p,[t1,t2]) => 
        if is_infix p then 
            block HOLPP.INCONSISTENT 2 (ppterm ss (LR (NONE,NONE)) t1) >> add_break(1,0) >>
                  add_string p >> add_break(1,0) >>
                  block HOLPP.INCONSISTENT 2 (ppterm ss (LR (NONE,NONE)) t2)
        else
            add_string p >> paren (pr_list (ppterm ss (LR (NONE,NONE))) (add_string "," >> add_break (1,0)) [t1,t2])
      | vPred(p,args) => 
        if length args = 0 then add_string p else
        add_string p >> paren (pr_list (ppterm ss (LR (NONE,NONE))) (add_string "," >> add_break (1,0)) args)
      | vConn(co,[f1,f2]) => 
            (case g of 
                LR(lg,rg) => 
                let 
                    val g1 = LR (lg, SOME (fxty co))
                    val g2 = LR (SOME (fxty co),rg)
                in 
                    if int_option_less (fxty co, lg) orelse int_option_leq (fxty co, rg) then 
                        add_string "(" >> 
                                   ppform ss (LR (NONE, SOME (fxty co))) f1 >> add_break(1,0) >> add_string co >> add_break(1,0) >>
                                   ppform ss (LR (SOME (fxty co), NONE)) f2 >> add_string ")"
                    else 
                        ppform ss g1 f1 >>  add_break(1,0) >> add_string co >> add_break(1,0) >>
                               ppform ss g2 f2
                end)
      | vConn("~",[f]) => add_string "~" >> ppform ss g f
      | vQ(q,n,s,b) =>
        let val (b0,vs) = strip_quants' f
        in
        case g of
            LR(_,NONE) => 
            block HOLPP.INCONSISTENT 2
                  (add_string q >> pr_tlist (LR (NONE,NONE)) (List.map (uncurry mk_var) vs)
                             (* pr_list (ppterm true (LR (NONE,NONE)))
                              (add_string " " >> add_break (1,0))
                              (List.map (uncurry mk_var) vs) *) >> 
                              add_string ". " >> ppform ss (LR (NONE,NONE)) b0)
          | _ => paren 
                     (block HOLPP.INCONSISTENT 2
                            (add_string q >> 
                                        pr_tlist (LR (NONE,NONE)) (List.map (uncurry mk_var) vs)
                         (* pr_list (ppterm true (LR (NONE,NONE))) (add_string " " >> add_break (1,0)) (List.map (uncurry mk_var) vs) *) >> add_string ". " >> ppform ss (LR (NONE,NONE)) b0))
         end
      | vfVar fv => add_break (1,0)  >> add_string fv >> add_break (1,0) 
      | _ => raise ERR ("ill-formed formula",[],[],[f])


fun PPform printdepth _ t = let val s = ppform (!show_types) (LR (NONE,NONE)) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPform

fun ppthm th  =
    let
        val (G,A,C) = dest_thm th
        val Gvl = List.map (uncurry mk_var) (HOLset.listItems G)
    in
        pr_list (ppterm true (LR (NONE,NONE))) (add_string "," >> add_break (1,0)) Gvl >> add_newline >>
                block HOLPP.INCONSISTENT 2 
                (pr_list (ppform false (LR (NONE,NONE))) (add_string "," >> add_newline) A) >>
                add_newline >>
                add_string "|-" >>
                add_newline >>
                block HOLPP.INCONSISTENT 2 
                (ppform false (LR (NONE,NONE)) C)
    end 

fun PPthm printdepth _ th = let val s = ppthm th
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val printf = HOLPP.pp_to_string 75 (fn f => PPform 70 () f)  (*70-75 for the int*) 

val printth = HOLPP.pp_to_string 75 (fn th => PPthm 70 () th)  (*70-75 for the int*) 

val _ = PolyML.addPrettyPrinter PPthm

end
