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

val hyp = ant

fun drule th (G,fl:form list,f) = 
    let 
        val c = concl th
        val (b,vs) = strip_all c
        val (ant,con) = dest_imp b
        fun mfn _ asm = 
            let 
                val menv = match_form (fvfl (hyp th)) ant asm mempty
                val ith = inst_thm menv (spec_all th)
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
require specially that the name of free variable substituted is precisely the bounded variable name.

?B:ob. P(B) |-  ?B. P(B)           P(B) |- C
-------------------------------------------- efn (B,ob) (P(B), P(B) |- C)
?B.P(B) |- C    

*)


fun efn (n,s) (f,th) = 
    let 
        val ef = mk_exists n s f
    in
        (ef,existsE (n,s) (assume ef) th)
    end


fun match_mp_tac th (ct:cont,asl:form list,w) = 
    let
        val (imp,gvs) = strip_all (concl th)
        val (ant,conseq) = dest_imp imp
        val (con,cvs) = strip_all (conseq)
        val th1 = specl (undisch (specl th (List.map Var gvs))) (List.map Var cvs) 
        val (vs,evs) = partition (fn v => HOLset.member(fvf con,v)) gvs
        val th2 = uncurry disch (itlist efn evs (ant, th1))
        val (gl,vs) = strip_all w
        val env = match_form (cont th) con gl mempty
        val ith = inst_thm env th2
        val gth = genl vs (undisch ith)
        val ant = fst (dest_imp (concl ith))
    in
        ([(ct,asl,ant)], fn thl => mp (disch ant gth) (hd thl))
    end

(*
 ALL (A : ob). ALL (x : 1() -> A). P(x) ==> Q(A)   -- test passed

ALL (A : ob). ALL (B : ob). ALL (f : A -> B). P(A, B, f) ==> Q(f) test passed


ALL (A : ob).
       ALL (B : ob). ALL (f : A -> B). ALL (C : ob). P(A, B, C, f) ==> Q(f):
   thm
> # val it =
   ([(HOLset{("C", ob), ("D", ob), ("g", ar (Var ("C", ob), Var ("D", ob)))},
      [], EXISTS (C : ob). P(C, D, C, g))], fn):
   (cont * form list * form) list * (thm list -> thm) -- name issue,  but:

 
   |-
   ALL (A : ob).
       ALL (B : ob). ALL (f : A -> B). ALL (K : ob). P(A, B, K, f) ==> Q(f):
   thm
> # val it =
   ([(HOLset{("C", ob), ("D", ob), ("g", ar (Var ("C", ob), Var ("D", ob)))},
      [], EXISTS (K : ob). P(C, D, K, g))], fn):
   (cont * form list * form) list * (thm list -> thm) -- test passed

|-
   ALL (A : ob).
       ALL (B : ob).
         ALL (f : A -> B).
           ALL (K : ob). P(A, B, K, f) ==> ALL (g : X -> Y). Q(g) -- test passed


|-
   ALL (A : ob).
       ALL (B : ob).
         ALL (f : A -> B).
           ALL (K : ob). P(A, B, K, f) ==> ALL (g : A -> B). Q(g) -- test passed


|-
   ALL (A : ob). ALL (B : ob). A P B ==> ALL (f : A -> B). Q(f) -- test passed

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
        ([(G,A::fl,FALSE):goal], fn [th] => negI th A
                          | _ => raise ERR "incorrect number of list items")
      | _ => raise ERR "not a negation"

(*
fun F_INTRO_TAC cf (g:goal as (G,fl,f)) = 
    case f of 
        FALSE => if fmem cf fl andalso fmem (mk_neg cf) fl then
                     ([],)
*)

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
            ([(G,fl,subst_bound t b)], 
             fn [th] => existsI th (n,s) t (subst_bound (Var(n,s)) b)
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


val op >-- = then1_tac


fun op Orelse (tac1:tactic, tac2:tactic) = 
    fn (g as (G,fl,f)) =>
       tac1 g handle ERR _ => tac2 g




val stp_tac = conj_tac Orelse contra_tac Orelse imp_tac Orelse gen_tac

fun all_tac (G,fl,l) =  ([(G,fl,l):goal],(fn [th] => th
                     | _ => raise ERR "incorrect number of list items"))

fun try tac:tactic = tac Orelse all_tac

fun repeat tac g = ((tac >> (repeat tac)) Orelse all_tac) g


fun fconv_tac fc (G,fl,f) = 
    let 
        val th = fc f
        val G' = HOLset.union(G,cont th)
        val (_,rhs) = dest_dimp (concl th)
    in
        if eq_form (rhs,TRUE) 
        then ([],empty (dimp_mp_l2r (trueI []) (iff_swap th)))
        else
            ([(G',fl,rhs)],
             (fn [th] => dimp_mp_r2l (fc f) th
             | _ => raise ERR "incorrect number of list items"))
    end


(*TODO: see Tactical.sml CONV_TAC,    if aconv rhs T then ([], empty (EQ_MP (SYM th) boolTheory.TRUTH)), if fc f is eq_form to T, then this extra line*)

fun gen_rw_tac fc thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv thl)
        val fconv = first_fconv (mapfilter rewr_fconv thl)
    in fconv_tac (fc conv fconv) 
    end


fun rw_tac thl = gen_rw_tac basic_fconv thl

fun once_rw_tac thl = gen_rw_tac basic_once_fconv thl

fun once_rw_ftac thl = gen_rw_tac once_depth_fconv thl

fun once_rw_ttac thl = gen_rw_tac once_depth_fconv thl

(*
fun rw_tac thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv thl)
        val fconv = first_fconv (mapfilter rewr_fconv thl)
    in fconv_tac (basic_fconv conv fconv) 
    end

*)

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

fun arw_tac thl = assum_list (fn l => rw_tac (l @ thl))

fun pop_assum_list (asltac:thm list -> tactic):tactic = 
    fn (G,asl, w) => asltac (map assume asl) (G,[], w)

fun stp_rw thl g = 
    repeat (stp_tac >> rw_tac thl) g

(*only difference between pop_assum_list and assum_list is the former removes the assumptions?*)

fun every tacl = List.foldr (op then_tac) all_tac tacl

fun map_every tacf lst = every (map tacf lst) 

fun rule_assum_tac rule: tactic =
    pop_assum_list
        (fn asl => map_every assume_tac (rev_itlist (cons o rule) asl []))

(*TODO: let rw_tac strip as much as it can: i.e. if it rw RHS into something which can be stripped, also strip that*)


(*
If tac applied to the goal (asl,g) produces a justification that does not create a theorem A |- g, with A a subset of asl, then VALID tac (asl,g) fails (raises an exception)
*)

(*
val validity_tag = "ValidityCheck"
   fun masquerade goal = Thm.mk_oracle_thm validity_tag goal
   datatype validity_failure = Concl of term | Hyp of term
   fun bad_prf th (asl, w) =
       if concl th !~ w then SOME (Concl (concl th))
       else
         case List.find (fn h => List.all (not o aconv h) asl) (hyp th) of
             NONE => NONE
           | SOME h => SOME (Hyp h)
*)


fun masquerade goal = thm goal

datatype validity_failure = Concl of form | Ant of form| Cont of (string * sort)

fun bad_prf th (ct,asl,w) =
    if not (eq_form(concl th,w)) then SOME (Concl (concl th))
    else
        let val clth = HOLset.listItems (cont th)
            val clct = HOLset.listItems ct
        in 
            case
                List.find 
                    (fn ns0 => List.all (fn ns => not (ns = ns0)) clct) clth
             of
                SOME ns => SOME (Cont ns)
              | NONE => 
                (case List.find (fn h => List.all (not o ((curry eq_form) h)) asl)
                               (ant th) of
                    NONE => NONE
                  | SOME h => SOME (Ant h))
        end

fun error f t e =
       let
         val pfx = "Invalid " ^ t ^ ": theorem has "
         val (desc, t) =
             case e of
                 Ant h => ("bad hypothesis", string_of_form h)
               | Concl c => ("wrong conclusion", string_of_form c)
               | Cont ns => ("extra variable involved",string_of_term (Var ns))
       in
         raise ERR (f^pfx ^ desc ^ " " ^ t)
       end


fun valid (tac: tactic) : tactic =
      fn g: goal =>
         let
            val (result as (glist, prf)) = tac g
         in
           case bad_prf (prf (map masquerade glist)) g of
               NONE => result
             | SOME e => error "VALID" "tactic" e
         end

end
    
