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

fun uex2fsym fsym th = 
    let val th' = spec_all th
        val (ct,asl) = (cont th',ant th')
        val (hyp,conc) = dest_imp (concl th')
       (* val _ = HOLset.isSubset(fvf conc,fvf hyp)
                orelse raise ERR ("uex2fsym.conclusion has extra free variable",[],[],[hyp,conc]) *)
        val inputvars = HOLset.listItems $ filter_cont (cont th') (*need filter it*)
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,inputvars)
        val fterm = mk_fun fsym (List.map var inputvars)
        val b' = subst_bound fterm b
    in mk_thm ct asl (mk_imp hyp b')
    end

(*uex2fsym "none" ax5; test pass*)
        
