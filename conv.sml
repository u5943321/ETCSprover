structure conv :> conv = 
struct
open term form logic drule abbrev
(*type conv = term -> thm
type fconv = form -> thm
*)
exception unchanged of string * term list * form list



(*think about inst_thm when names clash!!!!!!!!!!!*)



fun part_tmatch partfn th t = 
    let 
        val env = match_term (fvfl (ant th)) (partfn th) t mempty
    in 
        inst_thm env th
    end

(*parttern matcher without loop*)

(*

fun part_tmatch_norf partfn th t = 
    let 
        val env = match_term (fvfl (ant th)) (partfn th) t mempty
        val th' = inst_thm env th
        val (l,r) = dest_eq (concl th')
    in 
        if l = r then raise unchanged ("part_tmatch_norf",[t],[concl th])
        else th'
    end

fun occurs_tt t1 t2 = 
    case (t1,t2) of 
        (Var (n1,s1),Var (n2,s2)) => 
        if n1 = n2 andalso s1 = s2 then 
            true 
        else if occurs_ts t1 s2 then true 
        else false
      | (Var(n,s1),Fun(f,s2,l)) => 
        occurs_ts t1 s2 orelse List.exists (occurs_tt t1) l
      | _ => false
and occurs_ts t s = 
    case s of 
        ob => false
      | ar(d,c) => occurs_tt t d orelse occurs_tt t c


(*P(a) (P(a) | P(b)) & Q(c)*)


fun occurs_f f1 f2 = 
    case (f1,f2) of
        (Pred _,Pred _) => eq_form(f1,f2)
      | (Quant _ ,Quant _) => eq_form(f1,f2)
      | (fVar _, fVar _) => eq_form(f1,f2)
      | (_,Conn(co,fl)) => List.exists (occurs_f f1) fl
      | (_,Quant(_,_,_,b)) => occurs_f f1 b
      | (_,_) => false


fun cause_loop_teq th = 
    let val (l,r) = dest_eq(concl th)
    in if occurs_tt l r then true else false
    end


fun cause_loop_dimp th = 
    let val (l,r) = dest_dimp(concl th)
    in if occurs_f l r then true else false
    end

fun part_tmatch_nolp partfn th t = 
    let 
        val env = match_term (fvfl (ant th)) (partfn th) t mempty
        val th' = inst_thm env th
    in 
        if cause_loop_teq th' then raise ERR ("part_tmatch_nolp.the result of term matching causes loop",[],[],[concl th'])
        else th'
    end
*)

val rewr_conv = part_tmatch (fst o dest_eq o concl)

(*
val rewr_conv' = part_tmatch_nolp (fst o dest_eq o concl)
*)


(*operations on conv*)

fun all_conv t = refl t

infix thenc

fun thenc (c1,c2) t = 
    let 
        val th1 = c1 t 
    in 
        trans th1 (c2 (snd (dest_eq (concl th1))))
    end

infix orelsec

fun orelsec (c1,c2) t = 
    c1 t handle _ => c2 t

fun try_conv c = c orelsec all_conv

fun repeatc c t =
    ((c thenc (repeatc c)) orelsec all_conv) t

fun no_conv f = raise simple_fail "no_conv" 

fun first_conv cl = 
    case cl of [] => no_conv
             | h :: t => h orelsec (first_conv t)

(*conv on subterms*)


(*

"f" ["g" [a,b],c]

*)
fun arg_conv c t = 
    case (view_term t) of 
        vFun (f,s,l) => EQ_fsym f (List.map c l)
      | _ => raise ERR ("arg_conv.not a function term",[],[t],[])


fun depth_conv c t = 
    ((try_conv (arg_conv (depth_conv c))) thenc (repeatc c)) t

fun redepth_conv c t =
    (try_conv (arg_conv (redepth_conv c)) thenc
              ((c thenc (redepth_conv c)) orelsec all_conv))
        t

fun changed_conv (c:term -> thm) t = 
    if eq_thm (c t) (refl t) then raise unchanged ("changed_conv",[t],[])
    else c t


fun top_depth_conv conv tm =
   (repeatc conv thenc
    try_conv (changed_conv (arg_conv (top_depth_conv conv)) thenc
              try_conv (conv thenc top_depth_conv conv))) tm


(*
fun top_depth_conv c t =
    (repeatc c thenc
             (sub_conv (top_depth_conv c)) thenc
             ((c thenc (top_depth_conv c)) 
                  orelsec all_conv))
             t
*)
 

(*fconvs*)

val simp_trace = ref false
(*
fun part_fmatch partfn th f = 
    let 
        val fvd = match_form (fvfl (ant th)) (partfn th) f mempty
        val th' = inst_thm fvd th
        val (l,r) = dest_dimp (concl th')
       (* val _ = if !simp_trace then Lib.say (printth th') else ()*)
    in 
        if l = r then raise unchanged ("part_fmatch.the result of form matching is a refl",[],[concl th'])
        else th' 
    end
*)


fun part_fmatch partfn th f = 
    let 
        val fvd = match_form (fvfl (ant th)) (partfn th) f mempty
    in 
        inst_thm fvd th
    end

(*        
fun part_fmatch_nolp partfn th f = 
    let 
        val fvd = match_form (fvfl (ant th)) (partfn th) f mempty
        val th' = inst_thm fvd th
       (* val _ = if !simp_trace then Lib.say (printth th') else ()*)
    in 
        if cause_loop_dimp th' then raise ERR ("part_fmatch_nolp.the result of form matching causes loop",[],[],[concl th'])
        else th' 
    end
*)
 
val rewr_fconv = part_fmatch (fst o dest_dimp o concl)

(*
val rewr_fconv_nolp = part_fmatch_nolp (fst o dest_dimp o concl)
*)

(*TODO: let rewr_fconv check the imput thm is an iff, so it raises err before the conv is applied*)
(*operation on fconvs*)

infix thenfc

fun thenfc (fc1:fconv,fc2:fconv) f = 
    let 
        val th1 = fc1 f 
    in 
        iff_trans th1 (fc2 (snd (dest_dimp (concl th1))))
    end


fun all_fconv f = frefl f

infix orelsefc;

fun orelsefc (fc1,fc2) f = fc1 f handle _ => fc2 f

fun no_fconv f = raise simple_fail "no_fconv"

fun first_fconv fcl = 
    case fcl of [] => no_fconv
             | h :: t => h orelsefc (first_fconv t)

fun try_fconv fc = fc orelsefc all_fconv

fun changed_fconv (fc:form -> thm) f = 
    if eq_thm (fc f) (frefl f) then raise unchanged ("changed_fconv",[],[f])
    else fc f

fun repeatfc fc f = 
    ((fc thenfc (repeatfc fc)) orelsefc all_fconv) f

fun pred_fconv c f = 
    case view_form f of 
        vPred (P,tl) => EQ_psym P (List.map c tl)
      | _ => raise ERR ("pred_fconv.not a predicate",[],[],[f])

(*conv on subformulas*)

fun disj_fconv fc f = 
    case view_form f of 
        vConn("|",[p,q]) => disj_iff (fc p) (fc q)
      | _ => raise ERR ("disj_fconv.not a disjunction",[],[],[f])


(*call fc on p, if throw unchanged exp, then call fc on q, 
if fc q throws unchanged as well, throw unchanged on the conj_fconv 

then do not need to call eq_form 


*)

fun conj_fconv fc f = 
    case view_form f of 
        vConn("&",[p,q]) => conj_iff (fc p) (fc q)
      | _ => raise ERR ("conj_fconv.not a conjunction",[],[],[f])

(*if needed, add try_conv on fc*)


(*

TODO: call dest_conj / dest_imp

*)

fun imp_fconv fc f = 
    case view_form f of
        vConn("==>",[p,q]) => imp_iff (fc p) (fc q)       
      | _ => raise ERR ("imp_fconv.not an implication",[],[],[f])


fun dimp_fconv fc f = 
    case view_form f of
        vConn("<=>",[p,q]) => dimp_iff (fc p) (fc q)
      | _ => raise ERR ("dimp_fconv.not an iff",[],[],[f])

fun forall_fconv fc f = 
    case view_form f of
        (vQ("!",n,s,b)) => 
        forall_iff (n,s) $ fc (subst_bound (mk_var n s) b)
      | _ => raise ERR ("forall_fconv.not an all",[],[],[f])
 
fun exists_fconv fc f = 
    case view_form f of
        (vQ("?",n,s,b)) => 
        exists_iff (n,s) $ fc (subst_bound (mk_var n s) b)
      | _ => raise ERR ("exists_fconv.not an all",[],[],[f])

val reflTob = equivT (refl (mk_var  "a" mk_ob_sort))

val reflTar = equivT (refl (mk_var "a" 
                            (mk_ar_sort
                                 (mk_ob "A") (mk_ob "B"))))

val refl_fconv = 
    first_fconv [rewr_fconv reflTob,rewr_fconv reflTar]
     
fun sub_fconv c fc = 
    try_fconv (first_fconv [conj_fconv fc,
                 disj_fconv fc,
                 imp_fconv fc,
                 dimp_fconv fc,
                 forall_fconv fc,
                 exists_fconv fc,
                 pred_fconv c])




fun depth_fconv c fc f =
    (sub_fconv c (depth_fconv c fc) thenfc
               (repeatfc fc))
        f

fun redepth_fconv c fc f =
    (sub_fconv c (redepth_fconv c fc) thenfc
              ((fc thenfc (redepth_fconv c fc)) orelsefc all_fconv))
        f

val taut_conj_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_conj_1,T_conj_2,F_conj_1,F_conj_2])

val taut_disj_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_disj_1,T_disj_2,F_disj_1,F_disj_2])

val f2f = disch (mk_fvar "f0") (assume (mk_fvar "f0"))
val f2f_T  = eqT_intro f2f

val taut_imp_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_imp_1,T_imp_2,F_imp_1,F_imp_2,f2f_T])

val taut_dimp_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_dimp_1,T_dimp_2,F_dimp_1,F_dimp_2])



val taut_forall_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [forall_true_ar,forall_true_ob,
                   forall_false_ar,forall_false_ob])



val taut_exists_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [(*exists_true_ar,*)exists_true_ob,
                   exists_false_ar,exists_false_ob])

val ec = rewr_fconv exists_true_ar 

val basic_taut_fconv = 
    first_fconv [taut_conj_fconv,
                 taut_disj_fconv,
                 taut_imp_fconv,
                 taut_dimp_fconv,
                 taut_forall_fconv,
                 taut_exists_fconv]

val nFT_fconv = first_fconv [rewr_fconv nF2T,rewr_fconv nT2F]

val taut_fconv = basic_taut_fconv orelsec refl_fconv orelsec nFT_fconv

(*
fun top_depth_fconv c fc f =
    (repeatfc fc thenfc
             (sub_fconv c (top_depth_fconv c fc)) thenfc
             ((fc thenfc (top_depth_fconv c fc)) 
                  orelsefc all_fconv))
        f
*)

fun top_depth_fconv c fc f =
   (repeatfc fc thenfc
    try_fconv (changed_fconv (sub_fconv c (top_depth_fconv c fc)) thenfc
              try_fconv (fc thenfc top_depth_fconv c fc))) f

                                                           

fun once_depth_conv conv tm =
   try_conv (conv orelsec (arg_conv (once_depth_conv conv))) tm

fun once_depth_fconv c fc f =
   try_fconv (fc orelsefc (sub_fconv c (once_depth_fconv c fc))) f

fun basic_once_fconv c fc = 
    once_depth_fconv (once_depth_conv c) 
                     (fc orelsefc basic_taut_fconv orelsefc refl_fconv)


fun basic_fconv c fc =
    top_depth_fconv (top_depth_conv c) 
                    (fc orelsefc basic_taut_fconv orelsefc refl_fconv)

fun conv_rule c th = dimp_mp_l2r th (c (concl th)) 




fun right_imp_forall_fconv f  = 
    let
        val (ant,conc) = dest_imp f
        val (ns,b) = dest_forall conc
        val asm1 = assume f 
        val ath = assume ant 
        val mpth = mp asm1 ath
        val sth = specl [(uncurry mk_var) ns] mpth
        val gth = sth |> disch ant |> allI ns 
        val asm2 = assume (concl gth)
        val sasm2 = (C allE) asm2 ((uncurry mk_var) ns) 
        val mpsasm = mp sasm2 ath
        val gmpasm = allI ns mpsasm
        val dth' = disch ant gmpasm
    in dimpI (disch f gth)  (disch (concl gth) dth')
    end


fun sym_fconv f = 
    case view_form f of 
    vPred("=",[t1,t2]) => dimpI (assume f|> sym |> disch_all) (assume (mk_pred "=" [t2,t1]) |> sym |> disch_all)
  | vConn("<=>", [f1,f2]) => dimpI (assume f|> iff_swap |> disch_all) (assume (mk_dimp f2 f1)|> iff_swap |> disch_all)
  | _ => raise simple_fail "not an iff or equality"


val GSYM = conv_rule (once_depth_fconv no_conv sym_fconv)

fun double_neg_fconv f = rewr_fconv double_neg_elim f

val neg_neg_elim = conv_rule (once_depth_fconv no_conv double_neg_fconv)

end
