fun q_ttac ttac str: tactic =
    fn (ct,asl,w) => ttac (pwct ct str) (ct,asl,w)

fun q_tltac tltac strl: tactic =
    fn (ct,asl,w) => tltac (List.map (pwct ct) strl) (ct,asl,w)

(*
fun q_ftac ftac str: tactic =
    fn (ct,asl,w) => ftac (pwcf ct str) (ct,asl,w)
*)

fun q2str [QUOTE s] = s

fun pwcfq ct fq = pwcf ct (q2str fq)

fun q_ftac ftac q: tactic =
    fn (ct,asl,w) => ftac (pwcfq ct q) (ct,asl,w)

val qabbrev_tac  = q_ftac abbrev_tac

fun q_tltcl (tltcl:term list -> thm_tactic -> thm_tactic) strl thtac th :tactic = 
    fn (ct,asl,w) => tltcl (List.map (pwct ct) strl) thtac th (ct,asl,w)

fun sing f [x] = f x
  | sing f _ = raise simple_fail "sing" 
(*
fun exists_tac' t (G,fl,f) = 
    case view_form f of 
        vQ("?",n,s,b) =>
        if eq_sort(sort_of t,s) then 
            let val nv = pvariantt (fvf b) (var(n,s))
            in
            ([(G,fl,subst_bound t b)], 
             sing (existsI (dest_var nv) t (subst_bound nv b)))
            end
        else raise ERR ("exists_tac.inconsist sorts",[sort_of t,s],[t,var(n,s)],[])
      | _ => raise ERR ("exists_tac.goal is not an existential",[],[],[f])
*)

fun exists_tac' t (G,fl,f) = 
    case view_form f of 
        vQ("?",n,s,b) =>
        if eq_sort(sort_of t,s) then 
            let val nv = (var(n,s))
            in
            ([(G,fl,substf ((n,s),t) b)], 
             sing (existsI (dest_var nv) t (substf ((n,s),nv) b)))
            end
        else raise ERR ("exists_tac.inconsist sorts",[sort_of t,s],[t,var(n,s)],[])
      | _ => raise ERR ("exists_tac.goal is not an existential",[],[],[f])


val qexists_tac = q_ttac exists_tac'

fun existsl_tac l = map_every (exists_tac') l

val qexistsl_tac = q_tltac existsl_tac

val qspecl_then = q_tltcl specl_then

val qsuff_tac = q_ftac suffices_tac


val qby_tac = q_ftac by_tac


(*what to do pick_assum... val it = fn: form -> thm_tactic -> tactic?
what is the technique of qpat_x_assum? possible to make it more flexible and allow functions as input?

can just do...
*)

fun qpick_assum fstr (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_assum (pwcfq ct fstr) thtac (ct,asl,w) 

fun qpick_x_assum fstr (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_x_assum (pwcfq ct fstr) thtac (ct,asl,w) 

fun uex_def f = 
    let val ((n,s),_) = dest_exists f
        val b0 = fst (strip_exists f)
        val ct0 = fvf b0
        val v1 = pvariantt ct0 (mk_var n s)
        val (n1,s1) = dest_var v1
        val v2 = pvariantt (HOLset.add(ct0,(n1,s1))) (mk_var n s)
        val (n2,s2) = dest_var v2
        val b1 = substf ((n,s),v1) b0
        val b2 = substf ((n,s),v2) b0
        val b = mk_imp (mk_conj b1 b2) (mk_eq v1 v2)
        val conj2_rhs = mk_forall n1 s1 (mk_forall n2 s2 b)
        val rhs = mk_conj (mk_exists n s b0) conj2_rhs
        val thf = mk_dimp f rhs
    in mk_thm(fvf thf) [] thf
    end

(*function symbol from unique existence under some precondition, if no precondition then the condition is just T*)

(*a problem is that if already have a:A->B as input, then do not need A and B as input as well, for instance, the def of pr.

any comment with the style? 
*)

fun filter_cont ct = 
    let val ctl = HOLset.listItems ct
        val sctl = List.map snd ctl
        val obl = List.map fvs sctl
        val rptob = (*List.foldr (fn (e,s) => HOLset.add(s,e)) essps sctl*)
            mk_sss obl
    in HOLset.difference(ct,rptob)
    end

(*val order_vars l1 user should be able to control the order of inputs*)

fun ex2fsym fsym strl th = 
    let val th' = spec_all th
        val (ct,asl) = (cont th',ant th')
        val (hyp,conc) = dest_imp (concl th')
        val inputvars0 = filter_cont (cont th') 
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) essps 
                                   (List.map (dest_var o (pwct ct)) strl)
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val inputvl = List.map (pwct ct) strl
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,List.map dest_var inputvl)
        val fterm = mk_fun fsym inputvl
        val b' = substf ((n,s),fterm) b
    in mk_thm ct asl (mk_imp hyp b')
    end

(*

val char_exists' = char_exists |> strip_all_and_imp |> conj_all_assum
                               |> disch_all'' |> gen_all

val by1 = (rapf "(f:X->Z) o pX o e = (g:Y->Z) o pY o (e:E->XY)")

val by2 = (rapf "!c:A->XY. (pX:XY->X) o c = u:A->X & (pY:XY->Y) o c = v:A->Y <=> c = pa(pX,pY,u,v)") 

val by3 = (rapf "((f:X->Z) o pX) o pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y) = (g o pY) o pa(pX, pY, u, v)")

val by4 = (rapf "pX o e o eqind(e:E->XY, (f:X->Z) o pX, (g:Y->Z) o pY, pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y)) = u & pY o e o eqind(e:E->XY, (f:X->Z) o pX, (g:Y->Z) o pY, pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y)) = v")

val sf1 = (rapf "e o a1 = (e:E->XY) o (a2:A->E)") 

val sf2 = (rapf "(e:E->XY) o a1 = pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y) & e o a2 = pa(pX, pY, u, v)")

val slowtest = proved_th $
e0
(rw_tac[ispb_def_alt] >> repeat strip_tac  >> 
 (specl_then (List.map rastt ["X","Y"])
             (x_choosel_then ["XY","pX","pY"] assume_tac)) pr_ex >>
 (specl_then (List.map rastt ["XY","Z","(f:X->Z)o (pX:XY->X)","(g:Y->Z)o (pY:XY->Y)"])
             (x_choosel_then ["E","e"] assume_tac)) eq_ex >>
 exists_tac (rastt "E") >>  exists_tac (rastt "(pX:XY->X) o (e:E->XY)") >>
 exists_tac (rastt "(pY:XY->Y) o (e:E->XY)") >>
 by_tac by1
 >-- (drule eq_equality >> arw_tac[GSYM o_assoc]) >>
 arw_tac[] >> repeat strip_tac >> rw_tac[o_assoc] >> 
 by_tac by2
 >-- (drule pa_def >> strip_tac >> arw_tac[] >> dimp_tac >> rw_tac[]) >>
 drule eqind_def' >> 
 by_tac by3
 >-- (rw_tac[o_assoc] >> drule p12_of_pa >> arw_tac[]) >>
 first_x_assum (specl_then (List.map rastt ["A","pa(pX:XY->X, pY:XY->Y, u:A->X, v)"]) assume_tac) >> first_x_assum drule >> 
 exists_tac long_induced_map >> 
 by_tac by4
 >-- (pop_assum (assume_tac o (fn th => th |> allE long_induced_map |> (C dimp_mp_r2l) (refl long_induced_map))) >> arw_tac[]) >> repeat strip_tac (* 3 *)
 >-- arw_tac[]
 >-- arw_tac[] >>
 suffices_tac sf1
 >-- (suffices_tac (rapf "ismono(e:E->XY)") 
      >-- (strip_tac >> drule ismono_property >> 
           strip_tac >> first_x_assum drule >> arw_tac[]) >>
      drule eqa_is_mono >> arw_tac[]) >>
 suffices_tac sf2
 >-- (strip_tac >> arw_tac[]) >>
 strip_tac (* 2 *)
 >> (first_x_assum (match_mp_tac o iffLR) >> arw_tac[])
 )
(rapg "!X Z f:X->Z Y g:Y->Z.?P p:P->X q. ispb(f,g,p,q)")

(*AQ list

1.AQ match_mp_tac iso_trans does the wrong thing
2. gen_all should look at the context instead of just the variables in the concl? maybe should collect the variables which does not appear in any assumption. and gen them as early as possible.
3.can only think of 
 !B f:A->B g. f o i = g o i ==> f = g if g is not quantified, there will be a free variable g whose sort is bounded variables
4.qdy qsuff does not response

5.to1unique to rw then Exception- ERR ("extra variable involved", [1 -> 1], [f], []) raised
>  because the only way to use eqn is to match lhs and rw it into RHS, it does not match an equation a = b to an eqn c = d.

after parsing, add a function which collects the set of free variables, and complain if there is something whose domain is bounded, is there any better way?

Worry that if do this in the procedure of making formula then it will be slow.

*)

 to_zero_zero |> strip_all_and_imp |> disch_all |> allI ("f",mk_ar_sort (mk_ob "A") (mk_ob "B")) |> gen_all

(*uex2fsym "none" ax5; test pass*)
        
*)



