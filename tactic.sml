structure tactic :> tactic = 
struct
open term form logic drule abbrev

fun wrap_err s exn = 
    case exn of ERR (s0,sl,tl,fl) => ERR (s^s0,sl,tl,fl)
               | _ => raise simple_fail s

fun empty th [] = th
  | empty th _ = raise simple_fail "empty" 

fun sing f [x] = f x
  | sing f _ = raise simple_fail "sing" 

fun pairths f [x, y] = f x y
  | pairths f _ = raise simple_fail "pairths" 

val accept_tac = 
 fn th => fn (ct,asl,w) =>
    if eq_form(concl th,w)  then ([], empty th) 
    else raise ERR ("accept_tac.concl of th not equal to the goal",[],[],[concl th,w])

val T_INTRO_TAC:tactic = 
 fn (ct,asl,w) => 
    if w = TRUE then ([], empty (trueI asl))
    else raise ERR ("T_intro_tac.the goal is not T",[],[],[w])

fun gen_tac (ct,asl,w) = 
    case w of
        Quant("!",n,s,b) =>
        let val t0 = pvariantt ct (Var(n,s))
            val w' = subst_bound t0 b 
            val ct' = HOLset.union(ct,fvt t0) 
        in
            ([(ct',asl,w')], sing (allI (dest_var t0)))
        end
        | _ => raise ERR ("gen_tac.goal is not universally quantified",[],[],[w])


fun spec_tac0 (n,s): tactic = 
    fn (ct,asl,w) =>
    let val ct' = HOLset.delete(ct,(n,s))
        val w' = mk_all n s w
    in
        ([(ct',asl,w')], sing (allE (Var(n,s))))
    end

fun spec_tac n: tactic = 
    fn (ct,asl,w) =>
    let val (n,s) = case List.find (fn (n0,s0) => n0 = n) (HOLset.listItems ct) of
                        SOME ns => ns
                       | _ => raise simple_fail ("spec_tac.no variable with name: " ^ n)
    in spec_tac0 (n,s) (ct,asl,w)
    end


(*

A1 |- t1 A2 |- t2
 ------------------------ PROVE_HYP
 A1 u (A2 - {t1}) |- t2

*)



val assume_tac:thm_tactic = 
    fn th => fn (G:(string * sort) set,fl:form list,f:form) =>
    ([(HOLset.union(G,cont th),concl th:: fl,f)], sing (prove_hyp th))

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
            handle _ => NONE 
    in
        case (first_opt mfn fl) of 
            NONE => raise simple_fail "drule.no match"
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
        val th1 = (C specl) (undisch ((C specl) th (List.map Var gvs))) (List.map Var cvs) 
        val (vs,evs) = partition (fn v => HOLset.member(fvf con,v)) gvs
        val th2 = uncurry disch (itlist efn evs (ant, th1)) 
        val (gl,vs) = strip_all w
        val env = match_form (fvfl (hyp th)) con gl mempty
        val ith = inst_thm env th2
        val gth = genl vs (undisch ith)
        val ant = fst (dest_imp (concl ith))
    in
        ([(ct,asl,ant)], sing (mp (disch ant gth)))
    end

(*
fun match_mp_canon th = 
    th |> undisch_all |> conj_all_assum *)
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


fun conj_tac ((G,fl,f):goal):goal list * validation = 
    case f of 
        (Conn("&",[f1,f2])) =>
        ([(G,fl,f1), (G,fl,f2)], pairths conjI)
      | _ => raise ERR ("conj_tac.not a conjunction",[],[],[f])

fun disj1_tac (g:goal as (G,fl,f)) = 
    case f of
        Conn("|",[f1,f2]) => 
        ([(G,fl,f1)], sing (disjI1 f2))
      | _ => raise ERR ("disj1_tac.not a disjunction",[],[],[f])

fun disj2_tac (G,fl,f) = 
    case f of
        Conn("|",[f1,f2]) => 
        ([(G,fl,f2)], sing (disjI2 f1))
      | _ => raise ERR ("disj2_tac.not a disjunction",[],[],[f])

                   
fun cases_on c (G,fl,f) =
    let 
        val G' = HOLset.union(G,fvf c)
    in
        ([(G',c::fl,f),(G',(mk_neg c)::fl,f)], pairths (disjE (tautI c))) 
    end

fun contra_tac (g:goal as (G,fl,f)) = 
    case f of
        Conn("~",[A]) => 
        ([(G,A::fl,FALSE):goal], sing (negI A))
      | _ => raise ERR ("contra_tac.goal is not a negation",[],[],[f])


fun ccontra_tac (g:goal as (G,fl,f)) = 
    case f of
        Conn("~",[A]) => 
        ([(G,A::fl,FALSE):goal], sing (negI A))
      | _ => 
        ([(G,(mk_neg f)::fl,FALSE):goal], fn [th] => dimp_mp_l2r (negI (mk_neg f) th) (double_neg f)
                          | _ => raise simple_fail "ccontra_tac.incorrect number of list items")



fun imp_tac (G,fl,f) = 
    case f of 
        Conn("==>",[f1,f2]) => 
        ([(G,f1::fl,f2)], sing (disch f1))
      | _ => raise ERR ("imp_tac.goal is not an implication",[],[],[f])
 
 
fun dimp_tac (G,fl,f) = 
    case f of
        Conn("<=>",[f1,f2]) => 
        ([(G,fl,Conn("==>",[f1,f2])),(G,fl,Conn("==>",[f2,f1]))],
         pairths dimpI)
      | _ => raise ERR ("dimp_tac.goal is not an double imp",[],[],[f])


fun conj_tac ((G,fl,f):goal):goal list * validation = 
    case f of 
        (Conn("&",[f1,f2])) =>
        ([(G,fl,f1), (G,fl,f2)], pairths conjI)
      | _ => raise ERR ("conj_tac.goal is not conjunction",[],[],[f])

fun exists_tac t (G,fl,f) = 
    case f of 
        Quant("?",n,s,b) =>
        if sort_of t = s then 
            ([(G,fl,subst_bound t b)], 
             sing (existsI (n,s) t (subst_bound (Var(n,s)) b)))
        else raise ERR ("exists_tac.inconsist sorts",[sort_of t,s],[t,Var(n,s)],[])
      | _ => raise ERR ("exists_tac.goal is not an existential",[],[],[f])

fun spec_all_tac (G,fl,f) = 
    case f of
        Quant("!",n,s,b) =>
        let val f' = subst_bound (Var(n,s)) b 
            val G' = HOLset.union(G,fvt (Var(n,s))) 
        in
            ([(G',fl,f')], sing (allI (n,s)))
        end
        | _ => raise ERR ("spec_all_tac.goal is not universally quantified",[],[],[f])

 
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
             else raise ERR ("then_tac.length list not consistent,start with respectively: ",[],[],[concl (hd l),#3 (hd gl1)]))
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
             else raise simple_fail "then1_tac.incorrect number of list items")
    in (gl',func')
    end
 

val op >-- = then1_tac


fun op Orelse (tac1:tactic, tac2:tactic) = 
    fn (g as (G,fl,f)) =>
       tac1 g handle _ => tac2 g




val stp_tac = conj_tac Orelse contra_tac Orelse imp_tac Orelse gen_tac

fun all_tac (G,fl,l) =  ([(G,fl,l):goal],sing I)

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
              sing (dimp_mp_r2l (fc f)))
    end


fun conj_pair th =
    (conjE1 th,conjE2 th)
    handle ERR _ => 
      raise ERR ("conj_pair.not a conjunction",[],[],[concl th])
 
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
        if is_dimp f then [th] else
        if is_conj f then (op@ o (fconv_canon ## fconv_canon) o conj_pair) th else
        if is_neg f then [eqF_intro th]  else
        if not (is_eqn f) then [eqT_intro th]
        else [th]
    end 


fun gen_rw_tac fc thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv thl)
        val fconv = first_fconv (mapfilter rewr_fconv thl)
    in fconv_tac (fc conv fconv) 
    end


fun once_rw_tac thl = gen_rw_tac basic_once_fconv  (flatten (mapfilter conv_canon thl))

fun once_rw_ftac thl = gen_rw_tac once_depth_fconv thl

fun once_rw_ttac thl = gen_rw_tac once_depth_fconv thl

(*
fun rw'_conv th t = part_tmatch
okay to let rw_conv loop, but do check here, and discard the thm after inst raise ERR if do not like it.

*)

fun rw_tac thl = 
    let 
        val conv = first_conv (mapfilter rewr_conv (flatten (mapfilter conv_canon thl)))
        val fconv = first_fconv (mapfilter rewr_fconv (flatten (mapfilter conv_canon thl)))
    in fconv_tac (basic_fconv conv fconv) 
    end




(*conv_canon/ fconv_canon should never raise exception, check this*)


fun by_tac f0 (G,fl,f) = 
    let 
        val G' = HOLset.union(G,fvf f0) 
    in
    ([(G',fl,f0),(G',f0::fl,f)], pairths prove_hyp)
    end


fun suffices_tac f0 (G,fl,f) = 
    let
        val G' = HOLset.union(G,fvf f0)
    in 
        ([(G',fl,mk_imp f0 f),(G',fl,f0)], pairths mp)
    end

fun mp_tac th0 (G,asl,w) = 
    let val G' = HOLset.union(G,cont th0) in
    ([(G',asl, mk_imp (concl th0) w)], fn [th] => mp th th0) end

fun assum_list aslfun (g as (_,asl, _)) = aslfun (List.map assume asl) g

fun arw_tac thl = assum_list (fn l => rw_tac (l @ thl))

fun once_arw_tac thl = assum_list (fn l => once_rw_tac (l @ thl))

fun pop_assum_list (asltac:thm list -> tactic):tactic = 
    fn (G,asl, w) => asltac (List.map assume asl) (G,[], w) 

fun excl_ths P thlt: thm list -> tactic = 
    fn thl => 
       let val (_,ths) = partition P thl
       in thlt ths
       end


fun pop_assum thfun (ct,a :: asl, w) = thfun (assume a) (ct,asl, w)
  | pop_assum   _   (_,[], _) = raise simple_fail"pop_assum.no assum"

fun rev_pop_assum thfun (ct,a :: asl, w) = thfun (assume (hd (rev (a :: asl)))) (ct,(rev (tl (rev (a :: asl)))), w)
  | rev_pop_assum   _   (_,[], _) = raise simple_fail"rev_pop_assum.no assum"

fun stp_rw thl g = 
    repeat (stp_tac >> rw_tac thl) g

(*only difference between pop_assum_list and assum_list is the former removes the assumptions?*)

fun every tacl = List.foldr (op then_tac) all_tac tacl

fun map_every tacf lst = every (List.map tacf lst) 

fun rule_assum_tac rule: tactic =
    pop_assum_list
        (fn asl => map_every assume_tac (rev_itlist (cons o rule) asl []))

(*TODO: let rw_tac strip as much as it can: i.e. if it rw RHS into something which can be stripped, also strip that*)

fun choose_tac cn a0:tactic = 
    fn (ct,asl,w) => 
       let val _ = fmem a0 asl orelse
                   raise ERR ("choose_tac.formula to be substitute not in assumption list",[],[],[a0])
           val _ = not (mem cn (List.map fst (HOLset.listItems ct))) 
                   orelse raise simple_fail "name to be choose is already used"
           val ((n,s),b) = dest_exists a0
           val newasm = subst_bound (Var(cn,s)) b
       in ([(HOLset.add(ct,(cn,s)),newasm ::(ril a0 asl),w)],
           sing (existsE (cn,s) (assume a0)))
       end

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
               | Cont ns => ("extra variable involved",(string_of_term (Var ns))^ ":" ^ (string_of_sort (snd ns)))
       in
         raise simple_fail(f^pfx ^ desc ^ " " ^ t)
       end

(*check the validaty error message: TODO, add term/form information*)

fun valid (tac: tactic) : tactic =
      fn g: goal =>
         let
            val (result as (glist, prf)) = tac g
         in
           case bad_prf (prf (List.map masquerade glist)) g of
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
val NO_THEN: thm_tactical = fn ttac => fn th => raise simple_fail "NO_THEN"
val FIRST_TCL = List.foldr (op ORELSE_TCL) NO_THEN



val CONTR_TAC: thm_tactic =
   fn cth => fn (ct,asl, w) =>
      let
         val th = CONTR w cth
      in
         ([], empty th)
      end
      handle e => raise (wrap_err "contr_tac." e)



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

val conjuncts_then:thm_tactical = fn ttac => conjuncts_then2 ttac ttac

(* --------------------------------------------------------------------------*
 * OPPOSITE_TAC: proves the goal using the theorem p and an assumption ~p.   *
 * --------------------------------------------------------------------------*)

(*F_imp f = ~f ⇒ f ⇒ F
 
th = A |- C 

th' =  A' |- ~C

~C ⇒ C ⇒ F 
A,A' |- F
*)

fun resolve th th' = mp (mp (F_imp (concl th)) th') th
                     handle e => raise (wrap_err "resolve." e)

fun target_rule tm =
      if is_neg tm then (dest_neg tm, Lib.C resolve) else (mk_neg tm, resolve)

fun OPPOSITE_TAC th:tactic = fn (ct,asl, w) =>
    let
        val (opp, rule) = target_rule (concl th)
    in
        case List.find ((C (curry eq_form)) opp) asl of
            NONE => raise simple_fail "OPPOSITE_TAC"
          | SOME asm => CONTR_TAC (rule th (assume asm)) (ct,asl, w)
    end

(*discard_tac*)

(* --------------------------------------------------------------------------*
 * DISCARD_TAC: checks that a theorem is useless, then ignores it.           *
 *  TODO: do not quite understand why it is necessary                                                  *
 * --------------------------------------------------------------------------*)

fun DISCARD_TAC th (ct,asl, w) =
   if Lib.exists ((curry eq_form) (concl th)) (TRUE :: asl) andalso HOLset.isSubset(cont th,ct)
      then all_tac (ct,asl, w)
   else raise simple_fail "DISCARD_TAC"


fun foo th m = mp (disch (concl th) (assume m)) th 
               handle e => raise wrap_err "foo." e

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
(*
fun disj_cases th1 th2 th3 = 
    let val (A,B) = dest_disj(concl th1)
        val _ = eq_form(concl th2, concl th3) orelse raise simple_fail"two concls no match"
    in disjE A B (concl th2) th1 th2 th3
    end
*)

val disj_cases = disjE


fun disj_cases_then2 (ttac1:thm_tactic) (ttac2:thm_tactic):thm_tactic =
   fn disth =>
   let
      val (disj1, disj2) = dest_disj (concl disth)
   in
      fn g  =>
         let
            val (gl1, prf1) = ttac1 (foo disth disj1) g
            and (gl2, prf2) = ttac2 (foo disth disj2) g
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
   handle e => raise wrap_err "DISJ_CASES_THEN2." e
 
val disj_cases_then: thm_tactical = fn ttac => disj_cases_then2 ttac ttac


(*choose_then*)

fun foo th m = mp (disch (concl th) (assume m)) th 
               handle e => raise wrap_err "foo." e

fun x_choose_then n0 (ttac: thm_tactic) : thm_tactic =
   fn xth =>
      let
         val ((n,s),b) = dest_exists (concl xth)
      in
         fn (ct,asl,w) =>
            let
               val th = add_cont (HOLset.add(essps,(n0,s)))
                                 (foo xth (subst_bound (Var (n0,s)) b))              
               val (gl,prf) = ttac th (ct,asl,w)
            in
               (gl, (existsE (n0,s) xth) o prf)
            end
      end
      handle e => raise wrap_err "X_CHOOSE_THEN." e

fun x_choosel_then nl (ttac: thm_tactic):thm_tactic =
    case nl of
        [] => ttac 
      | h :: t => x_choose_then h (x_choosel_then t ttac)



fun specl_then tl (ttac: thm_tactic): thm_tactic = 
    fn th => ttac (specl tl th)

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
      handle e => raise wrap_err "CHOOSE_THEN." e

val choose_tac' = choose_then assume_tac

fun x_choose_tac x = x_choose_then x assume_tac

fun x_choosel_tac xs = x_choosel_then xs assume_tac 

val check_assume_tac: thm_tactic =
   fn gth =>
      first [CONTR_TAC gth, accept_tac gth, OPPOSITE_TAC gth,
             DISCARD_TAC gth,assume_tac gth]
      handle e => raise wrap_err "check_assume_tac." e

val strip_thm_then = FIRST_TCL [conjuncts_then, disj_cases_then, choose_then]

val STRIP_ASSUME_TAC = REPEAT_TCL strip_thm_then check_assume_tac
                       handle e => raise wrap_err "strip_assume_tac." e

val STRIP_ASM_CONJ_TAC = conjuncts_then assume_tac

fun find (ttac:thm_tactic) goal [] = raise simple_fail "find"
    | find ttac goal (a :: L) =
      ttac (assume a) goal handle _ => find ttac goal L
 
fun first_assum ttac = fn (ct,asl, w) => find ttac (ct,asl,w) asl

fun pick_assum f ttac = fn (ct,asl, w) => ttac (assume f) (ct,asl, w)

fun last_assum ttac = fn (ct,asl, w) => find ttac (ct,asl,w) (rev asl)

fun undisch_then f (ttac:thm_tactic): tactic = fn (ct,asl, w) =>
      let val (_, A) = Lib.pluck ((curry eq_form) f) asl in ttac (assume f) (ct,A, w) end

local
    fun f ttac th = undisch_then (concl th) ttac
in
val first_x_assum = first_assum o f
val last_x_assum = last_assum o f
fun pick_x_assum f0 = (pick_assum f0) o f
end



fun rewr_rule thl =
    let 
        val c = first_conv (mapfilter rewr_conv (flatten (mapfilter conv_canon thl)))
        val fc = first_fconv (mapfilter rewr_fconv (flatten (mapfilter conv_canon thl)))
    in
        conv_rule (basic_fconv c fc)
    end

fun abbrev_tac eq0:tactic = 
    fn (ct,asl,w) => 
       let 
           val (lhs,rhs) = dest_eq eq0
           val (n,s) = dest_var rhs
           val _ = HOLset.isSubset(fvt lhs,ct) orelse
                   raise simple_fail "the term to be abbrev has unknown variable" 
           val _ = not (mem n (List.map fst (HOLset.listItems ct)))
                   orelse raise simple_fail "name of the abbrev is already used"
           val eth =  existsI (n,s) lhs (Pred("=",[lhs,Var(n,s)])) (refl lhs) 
       in
           ([(HOLset.add(ct,(n,s)),eq0::asl,w)],fn [th] => existsE (n,s) eth th)
       end


(*
x = 3, take every  x into 3.

... & !x. ...

If go into a binder with intersects of the fv of the LHS of the eqn, then stop.

use sub_fconv to go through subforms/subterms

*)
(*subst_all_tac which does not do matching, but check for exactly the occurrence of some term. *)

fun remove_asm_tac f: tactic = 
    fn (ct,asl,w) =>
       if fmem f asl then 
           ([(ct,ril f asl,w)], sing (add_assum f))
       else raise ERR ("assumption to be removed is not in the assumption list",[],[],[f])

 

val once_rwl_tac = map_every (fn th => once_rw_tac[th])
val once_arwl_tac = map_every (fn th => once_arw_tac[th])

(*---------------------------------------------------------------------------*
 *       A,t1 |- t2                A,t |- F                                  *
 *     --------------              --------                                  *
 *     A |- t1 ==> t2               A |- ~t                                  *
 *---------------------------------------------------------------------------*)

fun neg_disch t th =
   if eq_form(concl th,FALSE) then negI t th 
   else disch t th



fun disch_then (ttac: thm_tactic): tactic = 
 fn ((ct,asl,w):goal) =>
   let
      val (ant, conseq) = dest_imp w
      val (gl, prf) = ttac (assume ant) (ct,asl,conseq)
   in
      (gl, (if is_neg w then neg_disch ant else disch ant) o prf):(goal list * validation)
   end
 

fun strip_goal_then ttac : tactic = first [gen_tac, conj_tac, disch_then ttac] 

val strip_tac:tactic = fn g => strip_goal_then STRIP_ASSUME_TAC g

fun disch_tac g = disch_then assume_tac g 


end
    
