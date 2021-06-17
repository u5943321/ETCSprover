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

(*
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


*)

fun gen_tac (ct,asl,w) = 
    case w of
        Quant("ALL",n,s,b) =>
        let val t0 = pvariantt ct (Var(n,s))
            val w' = subst_bound t0 b 
            val ct' = HOLset.union(ct,fvt t0) 
        in
            ([(ct',asl,w')], fn [th] => allI (dest_var t0) th
                   | _ => raise ERR "incorrect length of list")
        end
        | _ => raise ERR "goal is not universally quantified"


(*

A1 |- t1 A2 |- t2
 ------------------------ PROVE_HYP
 A1 u (A2 - {t1}) |- t2

*)

(*
val assume_tac:thm_tactic = 
    fn th => fn (G:(string * sort) set,fl:form list,f:form) =>
    ([(G,concl th:: fl,f)], fn [a:thm] => prove_hyp th a)
edited because of bug of missing variables in context
*)


val assume_tac:thm_tactic = 
    fn th => fn (G:(string * sort) set,fl:form list,f:form) =>
    ([(HOLset.union(G,cont th),concl th:: fl,f)], fn [a:thm] => prove_hyp th a)

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

fun hyp (thm(_,A,_))= A


fun match_mp_tac th (ct:cont,asl:form list,w) = 
    let
        val (imp,gvs) = strip_all (concl th)
        val (ant,conseq) = dest_imp imp
        val (con,cvs) = strip_all (conseq)
        val th1 = specl (undisch (specl th (List.map Var gvs))) (List.map Var cvs) 
        val (vs,evs) = partition (fn v => HOLset.member(fvf con,v)) gvs
        val th2 = uncurry disch (itlist efn evs (ant, th1)) 
        val (gl,vs) = strip_all w
        val env = match_form (fvfl (hyp th)) con gl mempty
        val ith = inst_thm env th2
        val gth = genl vs (undisch ith)
        val ant = fst (dest_imp (concl ith))
    in
        ([(ct,asl,ant)], fn thl => mp (disch ant gth) (hd thl))
    end


(*

A ==> !x. C x
---
!x. A ==> C
---

both directions 


A /\ B ==>C 

<=>

A ==> B ==> C

prove as a thm and rw with this

*)


(*TODO:


 ALL x. P(a) ==> Q(x) <=> P(a) ==> ALL x. Q(x): thm

add ()

 (ALL x. P(a) ==> Q(x)) <=> P(a) ==> ALL x. Q(x): thm
*)


(*TODO: change functions allE, specl, thm should be the last argument*)


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


fun ccontra_tac (g:goal as (G,fl,f)) = 
    case f of
        Conn("~",[A]) => 
        ([(G,A::fl,FALSE):goal], fn [th] => negI th A
                          | _ => raise ERR "incorrect number of list items")
      | _ => 
        ([(G,(mk_neg f)::fl,FALSE):goal], fn [th] => dimp_mp_l2r (negI th (mk_neg f)) (double_neg f)
                          | _ => raise ERR "incorrect number of list items")



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

fun conj_pair th =
    (conjE1 th,conjE2 th)
    handle ERR _ => 
           raise ERR ("not a conjunction" ^ (string_of_form (concl th)) ^ ": From conj_pair")

fun fconv_canon th = 
    let val th = spec_all th
        val f = concl th
    in 
        if is_dimp f then [th] else
        if is_conj f then (op@ o (fconv_canon ## fconv_canon) o conj_pair) th else
        if is_neg f then [eqF_intro th]  
        else [eqT_intro th]
    end 

fun conv_canon th = 
    let val th = spec_all th
        val f = concl th
    in 
       (* if aconv f TRUE then [] else seems happens in HOL but not here*)
        if is_dimp f then [th] else
        if is_conj f then (op@ o (fconv_canon ## fconv_canon) o conj_pair) th else
        if is_neg f then [eqF_intro th]  else
        if not (is_eqn f) then [eqT_intro th]
        else [th]
    end 

(*

FCONV-CANON
alters the consequent
of certain implications into logical
equivalences: P(X)
+ P(X)*TRUTH(
ip(x)
--, P(X) -FALSITY(
C-D
+ unchanged
else fail.
)

Larry's FCONV_CANON seems turns  a = b into a=b <=> T for fconv, but not conv AQ
*)

fun gen_rw_tac fc thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv thl)
        val fconv = first_fconv (mapfilter rewr_fconv thl)
    in fconv_tac (fc conv fconv) 
    end

(*TODO: Fix eqT_intro, eqF_intro!*)



(* old rw_tac
fun rw_tac thl = gen_rw_tac basic_fconv thl
fun arw_tac thl = assum_list (fn l => rw_tac (l @ thl))
*)

fun once_rw_tac thl = gen_rw_tac basic_once_fconv thl

fun once_rw_ftac thl = gen_rw_tac once_depth_fconv thl

fun once_rw_ttac thl = gen_rw_tac once_depth_fconv thl

(*
fun rw_tac thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv (flatten (mapfilter conv_canon thl)))
        val fconv = first_fconv (mapfilter rewr_fconv (flatten (mapfilter fconv_canon thl)))
    in fconv_tac (basic_fconv conv fconv) 
    end
*)

fun rw_tac thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv (flatten (mapfilter conv_canon thl)))
        val fconv = first_fconv (mapfilter rewr_fconv (flatten (mapfilter conv_canon thl)))
    in fconv_tac (basic_fconv conv fconv) 
    end



(*

TODO: Add to drule, to rw under quantifiers
P <=> Q 


<=>

!x.P <=> !x. Q

x allowed in P and Q, but not allowed to appear in assumption

P <=> Q 

<=>

?x.P <=> ?x. Q

*)

(*conv_canon/ fconv_canon should never raise exception, check this*)

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
exists na such that complicated term = na.

use existsE to eliminate the na


strip_assume_tac instead of existsE to deal with elimanation

*)
(*
readf “P(f)”

*)

(*
g: A-> B
----------
ALL g:A' -> B. P(g)

TODO: check gen_tac do this. 


f(x') = g(y')

f(a) = g(b)
 same as abbrev

*)

(*
A ?- t
============== MP_TAC (A’ |- s) 
A ?- s ==> t
*)

fun suffices_tac f0 (G,fl,f) = 
    let
        val G' = HOLset.union(G,fvf f0)
    in 
        ([(G',fl,mk_imp f0 f),(G',fl,f0)],
         fn [th1,th2] => mp th1 th2)
    end

fun mp_tac th0 (G,asl,w) = 
    let val G' = HOLset.union(G,cont th0) in
    ([(G',asl, mk_imp (concl th0) w)], fn [th] => mp th th0) end

fun assum_list aslfun (g as (_,asl, _)) = aslfun (List.map assume asl) g

fun arw_tac thl = assum_list (fn l => rw_tac (l @ thl))

fun once_arw_tac thl = assum_list (fn l => once_rw_tac (l @ thl))

fun pop_assum_list (asltac:thm list -> tactic):tactic = 
    fn (G,asl, w) => asltac (map assume asl) (G,[], w)

fun pop_assum thfun (ct,a :: asl, w) = thfun (assume a) (ct,asl, w)
  | pop_assum   _   (_,[], _) = raise ERR "POP_ASSUM:no assum"

fun stp_rw thl g = 
    repeat (stp_tac >> rw_tac thl) g

(*only difference between pop_assum_list and assum_list is the former removes the assumptions?*)

fun every tacl = List.foldr (op then_tac) all_tac tacl

fun map_every tacf lst = every (map tacf lst) 

fun rule_assum_tac rule: tactic =
    pop_assum_list
        (fn asl => map_every assume_tac (rev_itlist (cons o rule) asl []))

(*TODO: let rw_tac strip as much as it can: i.e. if it rw RHS into something which can be stripped, also strip that*)

fun choose_tac cn a0:tactic = 
    fn (ct,asl,w) => 
       let val _ = fmem a0 asl orelse
                   raise ERR "formula to be substitute not in assumption list"
           val _ = not (mem cn (List.map fst (HOLset.listItems ct))) 
                   orelse raise ERR "name to be choose is already used"
           val ((n,s),b) = dest_exists a0
           val newasm = subst_bound (Var(cn,s)) b
       in ([(HOLset.add(ct,(cn,s)),newasm ::(ril a0 asl),w)],
           fn [th] => existsE (cn,s) (assume a0) th)
       end

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


fun (ttcl1: thm_tactical) THEN_TCL (ttcl2: thm_tactical) =
   fn ttac => ttcl1 (ttcl2 ttac)

fun (ttcl1: thm_tactical) ORELSE_TCL (ttcl2: thm_tactical) =
   fn ttac => fn th => ttcl1 ttac th handle ERR _ => ttcl2 ttac th

fun REPEAT_TCL ttcl ttac th =
   ((ttcl THEN_TCL (REPEAT_TCL ttcl)) ORELSE_TCL I) ttac th

val ALL_THEN: thm_tactical = I
val NO_THEN: thm_tactical = fn ttac => fn th => raise ERR "NO_THEN"
val FIRST_TCL = List.foldr (op ORELSE_TCL) NO_THEN


val CONTR_TAC: thm_tactic =
   fn cth => fn (ct,asl, w) =>
      let
         val th = CONTR w cth
      in
         ([], empty th)
      end
      handle ERR _ => raise ERR "CONTR_TAC"

(*
  A,"~t" |- F                                                             *
 *   --------------                                                          *
 *       A |- t    

fun CCONTR f th = 
    let val f0 = dest_neg f 
        val _ = fmem f (ant th) orelse raise "CCONTR: formula not in assumption" 
*)


fun first tacl = 
    case tacl of
        [] => all_tac
      | h :: t => h Orelse (first t)


fun conjuncts_then2 ttac1 ttac2 =
   fn cth =>
      let
         val (th1,th2) = conj_pair cth
      in
         then_tac (ttac1 th1, ttac2 th2)
      end
      handle ERR _ => raise ERR "conjuncts_then2"

val conjuncts_then:thm_tactical = fn ttac => conjuncts_then2 ttac ttac





(*opposite_tac to be come back and check TODO:*)

(* --------------------------------------------------------------------------*
 * OPPOSITE_TAC: proves the goal using the theorem p and an assumption ~p.   *
 * --------------------------------------------------------------------------*)

(*
val contr_tac: thm_tactic =
   fn cth => fn (asl, w) =>
      let
         val th = CONTR w cth
      in
         ([], empty th)
      end
      handle HOL_ERR _ => raise ERR "CONTR_TAC" ""
*)

fun resolve th th' = mp (mp (F_imp (concl th)) th') th
fun target_rule tm =
      if is_neg tm then (dest_neg tm, Lib.C resolve) else (mk_neg tm, resolve)

fun OPPOSITE_TAC th:tactic = fn (ct,asl, w) =>
    let
        val (opp, rule) = target_rule (concl th)
    in
        case List.find ((C (curry eq_form)) opp) asl of
            NONE => raise ERR "OPPOSITE_TAC"
          | SOME asm => CONTR_TAC (rule th (assume asm)) (ct,asl, w)
    end

(*discard_tac*)

(* --------------------------------------------------------------------------*
 * DISCARD_TAC: checks that a theorem is useless, then ignores it.           *
 * Revised: 90.06.15 TFM.  TODO: do not quite understand why it is necessary                                                  *
 * --------------------------------------------------------------------------*)

fun DISCARD_TAC th (ct,asl, w) =
   if Lib.exists ((curry eq_form) (concl th)) (TRUE :: asl)
      then all_tac (ct,asl, w)
   else raise ERR "DISCARD_TAC"

(*disj_cases_then*)

fun foo th m = mp (disch (concl th) (assume m)) th

(*
 A |- t1 \/ t2   ,   A1,t1 |- t   ,   A2,t2 |- t
 *   -----------------------------------------------
 *               A u A1 u A2 |- t
 *
 * fun DISJ_CASES th1 th2 th3 =
 *   let val (t1,t2) = dest_disj(concl th1)
 *       and t = concl th2
 *       val th4 = SPEC t2 (SPEC t1 (SPEC t OR_ELIM_THM))
 *   in
 *   MP (MP (MP th4 th1) (DISCH t1 th2)) (DISCH t2 th3)
 *   end
 *   handle _ => ERR{function = "DISJ_CASES",message = ""};

*)

fun disj_cases th1 th2 th3 = 
    let val (A,B) = dest_disj(concl th1)
        val _ = (concl th2 = concl th3) orelse raise ERR "two concls no match"
    in disjE A B (concl th2) th1 th2 th3
    end


fun disj_cases_then2 (ttac1:thm_tactic) (ttac2:thm_tactic):thm_tactic =
   fn disth =>
   let
      val (disj1, disj2) = dest_disj (concl disth)
   in
      fn g  =>
         let
            val (gl1, prf1) = ttac1 (foo disth disj1) g
(*               ttac1 (itlist add_assum (thm.hyp disth) (assume disj1)) g *)
            and (gl2, prf2) = ttac2 (foo disth disj2) g
(*              ttac2 (itlist add_assum (thm.hyp disth) (assume disj2)) g *)
         in
            (gl1 @ gl2,
             fn thl =>
               let
                  val (thl1, thl2) = split_after (length gl1) thl
               in
                  disj_cases disth (prf1 thl1) (prf2 thl2)
               end)
         end
   end
   handle ERR _ => raise ERR "DISJ_CASES_THEN2"
 
val disj_cases_then: thm_tactical = fn ttac => disj_cases_then2 ttac ttac


(*choose_then*)

fun foo th m = mp (disch (concl th) (assume m)) th

fun x_choose_then n0 (ttac: thm_tactic) : thm_tactic =
   fn xth =>
      let
         val ((n,s),b) = dest_exists (concl xth)
      in
         fn (ct,asl,w) =>
            let
               val th = add_cont (foo xth (subst_bound (Var (n0,s)) b)) 
                                 (HOLset.add(essps,(n0,s)))
               val (gl,prf) = ttac th (ct,asl,w)
            in
               (gl, (existsE (n0,s) xth) o prf)
            end
      end
      handle ERR _ => raise ERR "X_CHOOSE_THEN"

val choose_then: thm_tactical =
   fn ttac => fn xth =>
      let
         val (cot,hyp,conc) = dest_thm xth
         val ((n,s),_) = dest_exists conc
      in
         fn (ct,asl,w) =>
         let
             val vd = HOLset.union(cot,ct)
             val y = pvariantt vd (Var(n,s))|> dest_var|> fst
         in
            x_choose_then y ttac xth (ct,asl,w)
         end
      end
      handle ERR _ => raise ERR "CHOOSE_THEN"

val choose_tac' = choose_then assume_tac

fun x_choose_tac x = x_choose_then x assume_tac

val check_assume_tac: thm_tactic =
   fn gth =>
      first [CONTR_TAC gth, accept_tac gth, OPPOSITE_TAC gth,
             DISCARD_TAC gth,assume_tac gth]

val strip_thm_then = FIRST_TCL [conjuncts_then, disj_cases_then, choose_then]

val STRIP_ASSUME_TAC = REPEAT_TCL strip_thm_then check_assume_tac

val STRIP_ASM_CONJ_TAC = conjuncts_then assume_tac

fun find (ttac:thm_tactic) goal [] = raise ERR "find"
    | find ttac goal (a :: L) =
      ttac (assume a) goal handle ERR _ => find ttac goal L
 
fun first_assum ttac = fn (ct,asl, w) => find ttac (ct,asl,w) asl

fun last_assum ttac = fn (ct,asl, w) => find ttac (ct,asl,w) (rev asl)

fun undisch_then f (ttac:thm_tactic): tactic = fn (ct,asl, w) =>
      let val (_, A) = Lib.pluck ((curry eq_form) f) asl in ttac (assume f) (ct,A, w) end

local
    fun f ttac th = undisch_then (concl th) ttac
in
val first_x_assum = first_assum o f
val last_x_assum = last_assum o f
end

(*what is the "name" in Tactical.find for?change above to first_opt?*)

(*
conjuncts_THEN f (A |- l /\ r) = f (A |- l) THEN f (A |- r) so
*)

(*
Suppose we have a goal of the following form:
{a /\ b, c, (d /\ e) /\ f} ?- t
Then we can split the conjunctions in the assumption list apart by applying the tactic: POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC)
which results in the new goal: {a, b, c, d, e, f} ?- t
Uses
page 722

STRIP_ASSUME_TAC page 978
*)

(*
fun CONJUNCTS_THEN ttac th =
      let val (c1, c2) = (CONJUNCT1 th, CONJUNCT2 th)
      in ttac c1 THEN ttac c2
      end

in Thm_cont


*)


end
    
