structure tactic :> tactic = 
struct
open term form thm drule abbrev


fun empty th [] = th
  | empty th _ = raise ERR "empty" 

fun sing f [x] = f x
  | sing f _ = raise ERR "sing" 

fun pairths f [x, y] = f x y
  | pairths f _ = raise ERR "pairths" 

val accept_tac = 
 fn th => fn (ct,asl,w) =>
    if eq_form(concl th,w)  then ([], empty th) else raise ERR "ACCEPT_TAC"

val T_INTRO_TAC:tactic = 
 fn (ct,asl,w) => 
    if w = TRUE then ([],fn [] => trueI asl)
    else raise ERR "the goal is not T"


fun gen_tac (ct,asl,w) = 
    case w of
        Quant("ALL",n,s,b) =>
        let val w' = subst_bound (Var(n,s)) b 
            val ct' = HOLset.union(ct,fvt (Var(n,s))) 
        in
            ([(ct',asl,w')], fn [th] => allI (n,s) th
                   | _ => raise ERR "incorrect length of list")
        end
        | _ => raise ERR "goal is not universally quantified"



(*

A1 |- t1 A2 |- t2
 ------------------------ PROVE_HYP
 A1 u (A2 - {t1}) |- t2

*)

val assume_tac:thm_tactic = 
    fn th => fn (G:(string * sort) set,fl:form list,f:form) =>
    ([(G,concl th:: fl,f)], fn [a:thm] => prove_hyp th a)



fun drule th (G,fl:form list,f) = 
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
          | SOME th => assume_tac th (G,fl,f)
    end

(*
fun efn (n,s) (G,f,th) = 
    let 
        val ef = mk_exists n s f
    in
        (G,ef,existsE (n,s) (assume ef) th)
    end

fun genl nsl th = 
    case nsl of 
        [] => th
      | h :: t => allI h (genl t th)
*)
(*
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

*)
(*********)

fun conj_tac ((G,fl,f):goal):goal list * validation = 
    case f of 
        (Conn("&",[f1,f2])) =>
        ([(G,fl,f1), (G,fl,f2)],fn [thm1,thm2] => conjI thm1 thm2
                              | _ => raise ERR "incorrect length of list")
      | _ => raise ERR "not a conjunction"

fun disj1_tac (g:goal as (G,fl,f)) = 
    case f of
        Conn("|",[f1,f2]) => 
        ([(G,fl,f1)], 
         fn [thm1] => disjI1 thm1 f2
         | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not a disjunction"



fun disj2_tac (G,fl,f) = 
    case f of
        Conn("|",[f1,f2]) => 
        ([(G,fl,f2)], fn [thm2] => disjI2 f1 thm2
                  | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not a disjunction"

                   
fun cases_on c (G,fl,f) =
    let 
        val G' = HOLset.union(G,fvf c)
    in
        ([(G',c::fl,f),(G',(mk_neg c)::fl,f)], 
         fn [th1,th2] => disjE c (mk_neg c) (concl th1) (tautI c) th1 th2
         | _ => raise ERR "incorrect length of list") 
    end

fun contra_tac (g:goal as (G,fl,f)) = 
    case f of
        Conn("~",[A]) => 
        ([(G,A::fl,FALSE):goal], fn [th] => negI th f
                          | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not a negation"


fun imp_tac (G,fl,f) = 
    case f of 
        Conn("==>",[f1,f2]) => 
        ([(G,f1::fl,f2)],
         fn [th] => disch f1 th
         | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not an implication"


fun dimp_tac (G,fl,f) = 
    case f of
        Conn("<=>",[f1,f2]) => 
        ([(G,fl,Conn("==>",[f1,f2])),(G,fl,Conn("==>",[f2,f1]))],
         fn [thm1,thm2] => dimpI thm1 thm2
         | _ => raise ERR "incorrect number of list item")
      | _ => raise ERR "not an iff"


fun conj_tac ((G,fl,f):goal):goal list * validation = 
    case f of 
        (Conn("&",[f1,f2])) =>
        ([(G,fl,f1), (G,fl,f2)],fn [thm1,thm2] => conjI thm1 thm2
                              | _ => raise ERR "incorrect length of list")
      | _ => raise ERR "not a conjunction"


(*maybe need to be more carful about the context*)

fun wexists_tac t (G,fl,f) = 
    case f of 
        Quant("EXISTS",n,s,b) =>
        if sort_of t = s then 
            ([(G,fl,subst_bound t b)], fn [th] => existsI th (n,s) t f
                                   | _ => raise ERR "incorrect length of list")
        else raise ERR "inconsist sorts"
      | _ => raise ERR "not an EXISTS"

fun spec_all_tac (G,fl,f) = 
    case f of
        Quant("ALL",n,s,b) =>
        let val f' = subst_bound (Var(n,s)) b 
            val G' = HOLset.union(G,fvt (Var(n,s))) 
        in
            ([(G',fl,f')], fn [th] => allI (n,s) th
                   | _ => raise ERR "incorrect length of list")
        end
        | _ => raise ERR "goal is not universally quantified"


fun h1_of l = 
    case l of 
        [] => []
      | (a,b) :: t => a :: h1_of t

fun then_tac ((tac1:tactic),(tac2:tactic)) (G,fl,f) = 
    let val (gl,func) = tac1 (G,fl,f)
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

fun then1_tac ((tac1:tactic),(tac2:tactic)) (G,fl,f) = 
    let val (gl,func) = tac1 (G,fl,f)
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



fun Orelse (tac1:tactic, tac2:tactic) = 
    fn (g as (G,fl,f)) =>
       tac1 g handle ERR _ => tac2 g

infix Orelse;


val stp_tac = conj_tac Orelse contra_tac Orelse imp_tac Orelse gen_tac

fun all_tac (G,fl,l) =  ([(G,fl,l):goal],(fn [th] => th
                     | _ => raise ERR "incorrect number of list items"))

fun try tac:tactic = tac Orelse all_tac

fun repeat tac g = ((tac >> (repeat tac)) Orelse all_tac) g

fun fconv_tac fc (G,fl,f) = 
    let val G' = HOLset.union(G,cont (fc f))
    in
    ([(G',fl, (snd o dest_dimp) (concl (fc f)))],
     (fn [th] => dimp_mp_r2l (fc f) th
     | _ => raise ERR "incorrect number of list items"))
    end

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
fun by_tac f0 (G,fl,f) = 
    let 
        val G' = HOLset.union(G,fvf f0) 
    in
    ([(G',fl,f0),(G',f0::fl,f)],
     fn [th1,th2] => prove_hyp th1 th2)
    end
(*
A ?- t
============== MP_TAC (A’ |- s) 
A ?- s ==> t
*)

fun mp_tac th0 (G,asl,w) = 
    let val G' = HOLset.union(G,cont th0) in
    ([(G',asl, mk_imp (concl th0) w)], fn [th] => mp th th0) end

fun assum_list aslfun (g as (_,asl, _)) = aslfun (List.map assume asl) g
end
