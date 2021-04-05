structure tactic :> tactic = 
struct
open term form thm

type goal = form list * form
type validation = thm list -> thm
type tactic = goal -> goal list * validation


fun conj_tac ((fl,f):goal):goal list * validation = 
    case f of 
        (Conn("&",[f1,f2])) =>
        ([(fl,f1), (fl,f2)],fn [thm1,thm2] => conjI thm1 thm2
                           | _ => raise ERR "incorrect length of list")
      | _ => raise ERR "not a conjunction"

fun disj1_tac (fl,f) = 
    case f of
        Conn("|",[f1,f2]) => 
         ([(fl,f1)], 
          fn [thm1] => disjI1 thm1 f2
          | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not a disjunction"



fun disj2_tac (fl,f) = 
    case f of
        Conn("|",[f1,f2]) => 
         ([(fl,f2)], fn [thm2] => disjI2 f1 thm2
                   | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not a disjunction"

 
fun cases_on c (fl,f) =
    ([(c::fl,f),((mk_neg c)::fl,f)], 
     fn [th1,th2] => disjE c (mk_neg c) (concl th1) (tautI c) th1 th2
     | _ => raise ERR "incorrect length of list") 

fun contra_tac (fl,f) = 
    case f of
        Conn("~",[A]) => 
        ([(A::fl,FALSE)], fn [th] => negI th f
                         | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not a negation"


fun imp_tac (fl,f) = 
    case f of 
        Conn("==>",[f1,f2]) => 
        ([(f1::fl,f2)],
         fn [th] => disch f1 th
         | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not an implication"


fun dimp_tac (fl,f) = 
    case f of
        Conn("<=>",[f1,f2]) => 
        ([(fl,Conn("==>",[f1,f2])),(fl,Conn("==>",[f2,f1]))],
         fn [thm1,thm2] => dimpI thm1 thm2
         | _ => raise ERR "incorrect number of list item")
      | _ => raise ERR "not an iff"


fun conj_tac ((fl,f):goal):goal list * validation = 
    case f of 
        (Conn("&",[f1,f2])) =>
        ([(fl,f1), (fl,f2)],fn [thm1,thm2] => conjI thm1 thm2
                           | _ => raise ERR "incorrect length of list")
      | _ => raise ERR "not a conjunction"


fun wexists_tac t (fl,f) = 
    case f of 
        Quant("EXISTS",n,s,b) =>
        if sort_of t = s then 
            ([(fl,subst_bound t b)], fn [th] => existsI th (n,s) t f
                                   | _ => raise ERR "incorrect length of list")
        else raise ERR "inconsist sorts"
      | _ => raise ERR "not an EXISTS"

fun gen_all_tac (fl,f) = 
    case f of
        Quant("ALL",n,s,b) =>
        let val f' = subst_bound (Var(n,s)) b in
        ([(fl,f')], fn [th] => allI (n,s) th
                   | _ => raise ERR "incorrect length of list")
        end
        | _ => raise ERR "goal is not universally quantified"


fun h1_of l = 
    case l of 
        [] => []
      | (a,b) :: t => a :: h1_of t

fun then_tac ((tac1:tactic),(tac2:tactic)) (fl,f) = 
    let val (gl,func) = tac1 (fl,f)
        val branches = List.map tac2 gl
        val gl1 = flatten (h1_of branches)
        fun func1 l = 
            (if List.length l = List.length gl1 then 
                 func (mapshape (List.map List.length (h1_of branches))
                           (List.map (fn (a,b) => b) branches) l)
             else raise ERR "incorrect number of list items")
    in (gl1,func1) 
    end



infix >> then_tac 

val op >> = then_tac

fun then1_tac ((tac1:tactic),(tac2:tactic)) (fl,f) = 
    let val (gl,func) = tac1 (fl,f)
        val (gl1,func1) = tac2 (hd gl)
        val gl' = gl1 @ (tl gl)
        fun func' l = 
            (if length l = length gl' then
                 case (func1 (List.take (l,length gl1))) of thm(G,C) =>
                 func (thm(G,C) :: (List.drop (l,length gl1)))
             else raise ERR "incorrect number of list items")
    in (gl',func')
    end

infix >- then1_tac 

val op >- = then1_tac

fun Orelse0 (tac1:goal -> goal list * validation) 
            (tac2:goal -> goal list * validation) (g as (fl,f)) = 
           tac1 g handle ERR _ => tac2 g

fun Orelse (t1,t2) = Orelse0 t1 t2
infix Orelse;


val stp_tac = conj_tac Orelse contra_tac Orelse imp_tac Orelse gen_all_tac

fun all_tac (fl,l) =  ([(fl,l)],(fn [th] => th
                     | _ => raise ERR "incorrect number of list items"))

fun try tac:tactic = tac Orelse all_tac

fun repeat tac g = ((tac >> (repeat tac)) Orelse all_tac) g


end
