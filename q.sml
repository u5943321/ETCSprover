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


val qexists_tac = q_ttac exists_tac

val qexistsl_tac = q_tltac existsl_tac

val qspecl_then = q_tltcl specl_then

val qsuff_tac = q_ftac suffices_tac


val qby_tac = q_ftac by_tac


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



