fun q_ttac ttac str: tactic =
    fn (ct,asl,w) => ttac (pwct ct str) (ct,asl,w)

fun q_ftac ftac str: tactic =
    fn (ct,asl,w) => ftac (pwcf ct str) (ct,asl,w)

fun q_tltcl (tltcl:term list -> thm_tactic -> thm_tactic) strl thtac th :tactic = 
    fn (ct,asl,w) => tltcl (List.map (pwct ct) strl) thtac th (ct,asl,w)

val qexists_tac = q_ttac exists_tac

val qspecl_then = q_tltcl specl_then

val qsuff_tac = q_ftac suffices_tac


val qby_tac = q_ftac by_tac


(*what to do pick_assum... val it = fn: form -> thm_tactic -> tactic?
what is the technique of qpat_x_assum? possible to make it more flexible and allow functions as input?

can just do...
*)

fun qpick_assum fstr (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_assum (pwcf ct fstr) thtac (ct,asl,w) 

fun qpick_x_assum fstr (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_x_assum (pwcf ct fstr) thtac (ct,asl,w) 

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

