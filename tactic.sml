structure tactic :> tactic = 
struct
open term form thm conv

type goal = form list * form
type validation = thm list -> thm
type tactic = goal -> goal list * validation

fun assume_tac th (fl,f) = 
    ([(concl th:: fl,f)], fn [a] => prove_hyp th)



fun drule0 th (fl:form list,f) = 
    let 
        val c = concl th
        val (b,vs) = strip_all c
        val (ant,con) = dest_imp b
        fun mfn _ asm = 
            let 
                val menv = match_form ant asm mempty
                val ith = inst_thm menv th
            in
                SOME (mp ith (assume asm))
            end
            handle ERR _ => NONE
    in
        case (first_opt mfn fl) of 
            NONE => raise ERR "no match"
          | SOME th => assume_tac th (fl,f)
    end

fun efn (n,s) (f,th) = 
    let 
        val ef = mk_exists n s f
    in
        (ef,existsE (n,s) (assume ef) th)
    end

fun genl nsl th = 
    case nsl of 
        [] => th
      | h :: t => allI h (genl t th)

fun match_mp_tac th (A,g) = 
    let
        val (imp,gvs) = strip_all (concl th)
        val (ant,conseq) = dest_imp imp
        val (con,cvs) = strip_all (conseq)
        val th1 = specl (undisch (specl th (List.map Var gvs))) (List.map Var cvs) 
        val (vs,evs) = partition (fn v => HOLset.member(fvf con,v)) gvs
        val th2 = uncurry disch (itlist efn evs (ant, th1))
        val (gl,vs) = strip_all g
        val env = match_form con gl mempty
        val ith = inst_thm env th2
        val gth = genl vs (undisch ith)
                          (*should be genl! need fix this*)
        val ant = fst (dest_imp (concl ith))
    in
        ([(A, ant)], fn thl => mp (disch ant gth) (hd thl))
    end




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
                 case (func1 (List.take (l,length gl1))) of thm(G,A,C) =>
                 func (thm(G,A,C) :: (List.drop (l,length gl1)))
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

fun fconv_tac fc (fl,f) = 
    ([(fl, (snd o dest_dimp) (concl (fc f)))],
     (fn [th] => dimp_mp_r2l (fc f) th
     | _ => raise ERR "incorrect number of list items"))
 
(*
fun rw_tac thl = 
    let val thms = flatten (List.map imp_canon thl)
        val conv = first_conv (mapfilter rewr_conv thms)
        val fconv = first_fconv (mapfilter rewr_fconv thms)
    in fconv_tac (basic_fconv conv fconv) 
    end
*)

fun rw_tac thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv thl)
        val fconv = first_fconv (mapfilter rewr_fconv thl)
    in fconv_tac (basic_fconv conv fconv) 
    end
(*

val simp_trace = ref false
*)



fun by_tac na (fl,f) = 
    ([(fl,na),(na::fl,f)],
     fn [th1,th2] => prove_hyp th1 th2
     | _ => raise ERR "incorrect length of list")

fun mp_tac thb (asl,w) = 
    ([(asl, mk_imp (concl thb) w)], fn [th] => mp th thb)


             
end
