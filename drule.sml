structure drule :> drule = 
struct
open term form logic
 
exception ERR of string * sort list * term list * form list

fun simple_fail s = form.simple_fail ("drule."^s)


fun imp_trans th1 th2 = 
    let val (ant,cl) = dest_imp (concl th1)
    in disch ant (mp th2 (mp th1 (assume ant)))
    end

fun add_assum f th = mp (disch f th) (assume f)

fun undisch th = mp th (assume (#1(dest_imp (concl th))))

fun undisch_all th = 
    case (concl th) of 
        (Conn("==>",[f1,f2])) => undisch_all (undisch th) 
      | _ => th

(**********************************************************************

A1 |- t1, A2 |- t2 
------------------------ prove_hyp
A1 u (A2 - {t1}) |- t2

**********************************************************************)

fun prove_hyp th1 th2 = mp (disch (concl th1) th2) th1



fun equivT (thm(G,A,C)) = dimpI (disch C (trueI (C :: A))) 
                              (disch TRUE (add_assum TRUE (thm(G,A,C))))

fun frefl f = dimpI (disch f (assume f)) (disch f (assume f))

fun dimpl2r th = conjE1 (dimpE th)

fun dimpr2l th = conjE2 (dimpE th)

fun imp_iff (thm(G1,A1,C1)) (thm(G2,A2,C2)) =  
    let val (a1,a2) = dest_dimp C1
        val (b1,b2) = dest_dimp C2
        val a12a2 = dimpl2r (thm(G1,A1,C1))
        val a22a1 = dimpr2l (thm(G1,A1,C1))
        val b12b2 = dimpl2r (thm(G2,A2,C2))
        val b22b1 = dimpr2l (thm(G2,A2,C2))
        val imp1 = Conn("==>",[a1,b1])
        val imp2 = Conn("==>",[a2,b2])
        val imp12imp2 = disch imp1 (imp_trans a22a1 (imp_trans (assume imp1) b12b2))
        val imp22imp1 = disch imp2 (imp_trans a12a2 (imp_trans (assume imp2) b22b1))
    in 
        dimpI imp12imp2 imp22imp1
    end


fun cj_imp1 pq = disch pq (conjE1 (assume pq))

fun cj_imp2 pq = disch pq (conjE2 (assume pq))


(*given |- A1 <=> A2 , |- B1 <=> B2, return |- A1 /\ B1 <=> A2 /\ B2, similar for other _iff thms*)

fun conj_iff (thm(G1,A1,C1)) (thm(G2,A2,C2)) = 
    let val (a1,a2) = dest_dimp C1
        val (b1,b2) = dest_dimp C2
        val a12a2 = dimpl2r (thm(G1,A1,C1))
        val a22a1 = dimpr2l (thm(G1,A1,C1))
        val b12b2 = dimpl2r (thm(G2,A2,C2))
        val b22b1 = dimpr2l (thm(G2,A2,C2))
        val cj1 = Conn("&",[a1,b1])
        val cj2 = Conn("&",[a2,b2])
    in dimpI
            (disch cj1
                   (conjI 
                        (mp a12a2 (conjE1 (assume cj1)))
                        (mp b12b2 (conjE2 (assume cj1))))
            )
            (disch cj2
                   (conjI
                        (mp a22a1 (conjE1 (assume cj2)))
                        (mp b22b1 (conjE2 (assume cj2))))
            )
    end


fun disj_iff (thm(G1,A1,C1)) (thm(G2,A2,C2)) = 
    let val (a1,a2) = dest_dimp C1
        val (b1,b2) = dest_dimp C2
        val a1ona2 = undisch (dimpl2r (thm(G1,A1,C1)))
        val a2ona1 = undisch (dimpr2l (thm(G1,A1,C1)))
        val b1onb2 = undisch (dimpl2r (thm(G2,A2,C2)))
        val b2onb1 = undisch (dimpr2l (thm(G2,A2,C2)))
        val dj1 = Conn("|",[a1,b1])
        val dj2 = Conn("|",[a2,b2])
        val a1ondj2 = disjI1 b2 a1ona2
        val b1ondj2 = disjI2 a2 b1onb2
        val dj12dj2 = disch dj1 
                            (disjE (assume dj1) a1ondj2 b1ondj2)
        val a2ondj1 = disjI1 b1 a2ona1
        val b2ondj1 = disjI2 a1 b2onb1
        val dj22dj1 = disch dj2
                            (disjE (assume dj2) a2ondj1 b2ondj1) 
    in 
        dimpI dj12dj2 dj22dj1
    end

fun neg_iff (thm(G,A,C)) = 
    let val (a1,a2) = dest_dimp C
        val a1ona2 = undisch (dimpl2r (thm(G,A,C)))
        val a2ona1 = undisch (dimpr2l (thm(G,A,C)))
        val neg1 = Conn("~",[a1])
        val neg2 = Conn("~",[a2])
        val neg1a22F = negE (assume neg1) a2ona1
        val neg2a12F = negE (assume neg2) a1ona2
        val neg12neg2 = disch neg1 (negI a2 neg1a22F)
        val neg22neg1 = disch neg2 (negI a1 neg2a12F)
    in 
        dimpI neg12neg2 neg22neg1
    end


fun simple_exists (v as (n,s)) th = existsI v (Var v) (concl th) th


(*will be used in chained implication tactic*)

(*A /\ B ==> C <=> A ==> B ==> C*)

fun conj_imp_equiv A B C = 
    let val ab = Conn("&",[A,B])
        val ab2c = Conn("==>",[ab,C])
        val a2b2c = Conn("==>",[A,Conn("==>",[B,C])])
        val conjabonc = mp (assume ab2c) (conjI (assume A) (assume B))
        val conj2imp = disch ab2c (disch A (disch B conjabonc))
        val abona = conjE1 (assume ab)
        val abonb = conjE2 (assume ab)
        val imp2conj = disch a2b2c (disch ab (mp (mp (assume a2b2c) abona) abonb))
    in dimpI conj2imp imp2conj
    end

(*A , A <=> B gives B. A <=> B , B gives A*)

fun dimp_mp_l2r A B =  mp (dimpl2r B) A
                          
fun dimp_mp_r2l B A =  mp (dimpr2l B) A

(*A /\ ¬A ==> B*)

fun contra2any A B = 
    let val na = Conn("~",[A])
        val a_na = negE (assume A) (assume na)
        val F2b = disch FALSE (falseE [FALSE] B)
        val anaonb = mp F2b a_na
        val a2na2b = disch A (disch na anaonb)
    in dimp_mp_r2l (conj_imp_equiv A na B) a2na2b
    end

(*A \/ B <=> ¬A ==> B*)

fun disj_imp_equiv A B = 
    let val na = Conn("~",[A])
        val imp = Conn("==>",[na,B])
        val ana2b = contra2any A B
        val anaonb = undisch (undisch (dimp_mp_l2r ana2b (conj_imp_equiv A na B)))
        (*not sure if correct way to do it*)
        val aorbnaonb = disjE (assume (Conn("|",[A,B]))) anaonb (assume B)
        val disj2imp = disch (Conn("|",[A,B])) (disch na aorbnaonb)
        val t = tautI A 
        val aonaorb = disjI1 B (assume A)
        val impnaonaorb = disjI2 A (mp (assume imp) (assume na))
        val imp2disj = disch imp (disjE t aonaorb impnaonaorb)
    in
        dimpI disj2imp imp2disj
    end

fun disj_swap A B = 
    let val dj = Conn("|",[A,B])
        val aonbora = disjI2 B (assume A)
        val bonbora = disjI1 A (assume B)
    in disch dj (disjE (assume dj) aonbora bonbora)
    end

fun disj_comm A B = dimpI (disj_swap A B) (disj_swap B A)

fun double_neg f = 
    let val nf = Conn("~",[f])
        val nnf = Conn("~",[nf])
        val fnfonF = negE (assume f) (assume nf)
        val f2nnf = disch f (negI nf fnfonF)
        val nforf = dimp_mp_l2r (tautI f) (disj_comm f nf)
        val nnf2f = dimp_mp_l2r nforf (disj_imp_equiv nf f)
    in
        dimpI nnf2f f2nnf
    end

val conj_T = equivT (conjI (trueI []) (trueI []))

(* T /\ f <=> f; f /\ T <=> f; F /\ f <=> F ; f /\ F <=> f*)

fun T_conj1 f = dimpI (disch (Conn("&",[TRUE,f])) (conjE2 (assume (Conn("&",[TRUE,f])))))
                      (disch f (conjI (trueI []) (assume f)))

fun T_conj2 f = dimpI (disch (Conn("&",[f,TRUE])) (conjE1 (assume (Conn("&",[f,TRUE])))))
                      (disch f (conjI (assume f) (trueI [])))

fun F_conj1 f = dimpI (disch (Conn("&",[FALSE,f])) (conjE1 (assume (Conn("&",[FALSE,f])))))
                      (disch FALSE (falseE [FALSE] (Conn("&",[FALSE,f]))))

fun F_conj2 f = dimpI (disch (Conn("&",[f,FALSE])) (conjE2 (assume (Conn("&",[f,FALSE])))))
                      (disch FALSE (falseE [FALSE] (Conn("&",[f,FALSE]))))

fun T_imp1 f =
    let val Timpf2f = disch (Conn("==>",[TRUE,f])) (mp (assume (Conn("==>",[TRUE,f]))) (trueI []))
        val f2Timpf = disch f (disch TRUE (add_assum TRUE (assume f)))
    in
        dimpI Timpf2f f2Timpf
    end

fun T_imp2 f = 
    let val f2T2T = disch (Conn("==>",[f,TRUE])) (trueI [Conn("==>",[f,TRUE])])
        val T2f2T = disch TRUE (disch f (trueI [f,TRUE]))
    in dimpI f2T2T T2f2T
    end

fun F_imp1 f = 
    let val F2f2T = disch (Conn("==>",[FALSE,f])) (trueI [Conn("==>",[FALSE,f])])
        val T2F2f = disch TRUE (disch FALSE (falseE [FALSE] f))
    in dimpI F2f2T T2F2f
    end

fun F_imp2 f = 
    let val nf2f2F = disch (mk_neg f) (disch f (negE (assume f) (assume (mk_neg f)))) 
        val f2F2nf = disch (Conn("==>",[f,FALSE])) ((C negI) (mp (assume (Conn("==>",[f,FALSE]))) (assume f)) f)
    in dimpI f2F2nf nf2f2F
    end

fun T_disj1 f = 
    let val Torf = Conn("|",[TRUE,f])
        val Torf2T = disch Torf (trueI [Torf]) 
        val T2Torf = disch TRUE (disjI1 f (assume TRUE))
    in dimpI Torf2T T2Torf
    end

fun T_disj2 f = 
    let val forT = Conn("|",[f,TRUE])
        val forT2T = disch forT (trueI [forT]) 
        val T2forT = disch TRUE (disjI2 f (assume TRUE))
    in dimpI forT2T T2forT
    end

fun F_disj1 f = 
    let val Forf = Conn("|",[FALSE,f])
        val Forf2f = disch Forf (disjE (assume Forf) (falseE [FALSE] f) (assume f))
        val f2Forf = disch f (disjI2 FALSE (assume f))
    in dimpI Forf2f f2Forf
    end


fun F_disj2 f = 
    let val forF = Conn("|",[f,FALSE])
        val forF2f = disch forF (disjE (assume forF) (assume f) (falseE [FALSE] f))
        val f2forF = disch f (disjI1 FALSE (assume f))
    in dimpI forF2f f2forF
    end

fun tautT f = 
    let val t = concl (tautI f)
        val t2T = disch t (trueI [t])
        val T2t = disch TRUE (add_assum TRUE (tautI f))
    in dimpI t2T T2t
    end

fun contraF f = 
    let val fnf = mk_conj f (mk_neg f)
        val fnf2F = disch fnf (negE (conjE1 (assume fnf)) (conjE2 (assume fnf)))
        val F2fnf = disch FALSE (falseE [FALSE] fnf)
    in dimpI fnf2F F2fnf
    end


fun T_dimp1 f = 
    let val Teqf = Conn("<=>",[TRUE,f])
        val Teqf2f = disch Teqf (dimp_mp_l2r (trueI []) (assume Teqf))
        val f2Teqf = disch f (dimpI (disch TRUE (add_assum TRUE (assume f)))
                                    (add_assum f (disch f (trueI [f]))))
    in dimpI Teqf2f f2Teqf
    end

fun T_dimp2 f = 
    let val feqT = Conn("<=>",[f,TRUE])
        val feqT2f = disch feqT (dimp_mp_r2l (assume feqT) (trueI []))
        val f2feqT = disch f (dimpI (add_assum f (disch f (trueI [f])))
                                    (disch TRUE (add_assum TRUE (assume f))))
    in dimpI feqT2f f2feqT
    end

fun F_dimp1 f = 
    let val Feqf = Conn("<=>",[FALSE,f])
        val Feqf2nf = disch Feqf (negI f (dimp_mp_r2l (assume Feqf) (assume f)))
        val nf2Feqf = disch (mk_neg f) (dimpI (disch FALSE (add_assum (mk_neg f) (falseE [FALSE] f)))
                                     (disch f (negE (assume f) (assume (mk_neg f)))))
    in dimpI Feqf2nf nf2Feqf
    end

fun F_dimp2 f = 
    let val feqF = Conn("<=>",[f,FALSE])
        val feqF2nf = disch feqF (negI f (dimp_mp_l2r (assume f) (assume feqF)))
        val nf2feqF = disch (mk_neg f) (dimpI (disch f (negE (assume f) (assume (mk_neg f))))
                                              (disch FALSE (add_assum (mk_neg f) (falseE [FALSE] f))))
    in dimpI feqF2nf nf2feqF
    end

(*the 2 below can be better!!*)

fun forall_true (n,s) = 
    let val aT = mk_all n s TRUE
        val G = HOLset.union(HOLset.add(essps,(n,s)),fvs s)
        val aT2T = disch aT (trueI [aT])
        val T2aT = disch TRUE (allI (n,s) (add_cont G (assume TRUE)))
    in dimpI aT2T T2aT
    end


fun forall_false (n,s) = 
    let val aF = mk_all n s FALSE
        val G = HOLset.union(HOLset.add(essps,(n,s)),fvs s)
        val aF2F = disch aF ((C allE) (add_cont G (assume aF)) (Var(n,s)))
        val F2aF = disch FALSE (falseE [FALSE] aF)
    in dimpI aF2F F2aF
    end

fun exists_true (n,s) = 
    let 
        val TwG = add_cont (HOLset.union(HOLset.add(essps,(n,s)),fvs s)) (trueI [])                          
        val T2eT =
            disch TRUE 
                  (add_assum TRUE 
                             (existsI (n,s) (Var(n,s)) TRUE TwG))
        val eT2T = disch (mk_exists n s TRUE) TwG
    in dimpI eT2T T2eT
    end

(*?a:A->B.F <=> F *)

fun exists_false (n,s) = 
    let val F2eF = disch FALSE (falseE [FALSE] (Quant("?",n,s,FALSE)))
        val eF2F = disch (Quant("?",n,s,FALSE))
                         (existsE (n,s) (assume (Quant("?",n,s,FALSE))) (assume FALSE))
    in
        dimpI eF2F F2eF
    end


fun iff_trans (thm(G1,A1,C1)) (thm(G2,A2,C2)) =
    case (C1,C2) of 
        (Conn("<=>",[f1,f2]), Conn("<=>",[f3,f4])) => 
        if eq_form (f2,f3) then 
            let val f1f2 = conjE1 (dimpE (thm(G1,A1,C1)))
                val f2f1 = conjE2 (dimpE (thm(G1,A1,C1)))
                val f2f4 = conjE1 (dimpE (thm(G2,A2,C2)))
                val f4f2 = conjE2 (dimpE (thm(G2,A2,C2)))
                val f1f4 = imp_trans f1f2 f2f4
                val f4f1 = imp_trans f4f2 f2f1
            in dimpI f1f4 f4f1
            end
        else raise ERR ("iff_trans.two iffs do not match",[],[],[C1,C2])
      | _ => raise ERR ("iff_trans.not a pair of iffs",[],[],[C1,C2])

fun iff_swap (thm(G,A,C)) = 
    let val Q2P = conjE2 (dimpE (thm(G,A,C)))
        val P2Q = conjE1 (dimpE (thm(G,A,C)))
    in dimpI Q2P P2Q
    end

(*P <=> P', Q <=> Q', gives (P <=> Q) <=> (P' <=> Q')*)

fun dimp_iff (th1 as thm(G1,A1,C1)) (th2 as thm(G2,A2,C2)) = 
     case (C1,C2) of 
        (Conn("<=>",[P1,P2]), Conn("<=>",[Q1,Q2])) => 
        let val P1iffQ1 = Conn("<=>",[P1,Q1])
            val P2iffQ2 = Conn("<=>",[P2,Q2])
            val P1iffQ12P2iffQ2 = disch P1iffQ1 (iff_trans (iff_swap th1) (iff_trans (assume P1iffQ1) th2))
            val P2iffQ22P1iffQ1 = disch P2iffQ2 (iff_trans (iff_trans th1 (assume P2iffQ2)) (iff_swap th2))
        in dimpI P1iffQ12P2iffQ2 P2iffQ22P1iffQ1
        end
      | _ => raise ERR ("dimp_iff.not a pair of iff: ",[],[],[C1,C2])


fun all_iff (n,s) (th as thm(G,A,C0)) = 
    case C0 of 
        Conn("<=>",[P,Q]) => 
        let val allP = Quant("!", n, s, abstract (n,s) P)
            val allQ = Quant("!", n, s, abstract (n,s) Q)
            val allP2allQ = disch allP (allI (n,s) (dimp_mp_l2r ((C allE) (assume allP) (Var(n,s))) th))
            val allQ2allP = disch allQ (allI (n,s) (dimp_mp_r2l th ((C allE) (assume allQ) (Var(n,s)))))
        in
            dimpI allP2allQ allQ2allP
        end
      | _ => raise ERR ("all_iff.conclusion of theorem is not an iff:",[],[],[C0])



fun exists_iff (n,s) (th as thm(G,A,C)) = 
    let
        val (P,Q) = dest_dimp C
        val P2Q = undisch (conjE1 (dimpE th))
        val Q2P = undisch (conjE2 (dimpE th))
        val eP = Quant("?", n, s, abstract (n,s) P)        
        val eQ = Quant("?", n, s, abstract (n,s) Q)
        val P2eQ = existsI (n,s) (Var(n,s)) Q P2Q
        val Q2eP = existsI (n,s) (Var(n,s)) P Q2P
        val eP2eQ = existsE (n,s) (assume eP) P2eQ |> disch eP
        val eQ2eP = existsE (n,s) (assume eQ) Q2eP |> disch eQ
    in dimpI eP2eQ eQ2eP
    end

(*F_IMP: ~f ==> f ==> F*)

fun F_imp f = assume f|> (C negE) (assume (mk_neg f)) |> disch f |> disch (mk_neg f)

(*theorems with fVars to be matched, to deal with propositional taut*)

val T_conj_1 = T_conj1 (fVar "f0")
val T_conj_2 = T_conj2 (fVar "f0")
val F_conj_1 = F_conj1 (fVar "f0")
val F_conj_2 = F_conj2 (fVar "f0")

val T_disj_1 = T_disj1 (fVar "f0")
val T_disj_2 = T_disj2 (fVar "f0")
val F_disj_1 = F_disj1 (fVar "f0")
val F_disj_2 = F_disj2 (fVar "f0")

val T_imp_1 = T_imp1 (fVar "f0")
val T_imp_2 = T_imp2 (fVar "f0")
val F_imp_1 = F_imp1 (fVar "f0")
val F_imp_2 = F_imp2 (fVar "f0")

val T_dimp_1 = T_dimp1 (fVar "f0")
val T_dimp_2 = T_dimp2 (fVar "f0")
val F_dimp_1 = F_dimp1 (fVar "f0")
val F_dimp_2 = F_dimp2 (fVar "f0")

val all_true_ob = forall_true ("A",ob)
val all_true_ar = forall_true ("a",ar(mk_ob "A",mk_ob "B"))

val all_false_ob = 
    let 
        val f0 = assume (mk_all "A" ob FALSE)
        val L2R = disch (mk_all "A" ob FALSE) ((C allE) f0 (Fun("N",ob,[])))
        val R2L = disch FALSE (falseE [FALSE] (mk_all "A" ob FALSE))
    in
        dimpI L2R R2L
    end

val all_false_ar = forall_false ("a",ar(mk_ob "A",mk_ob "B"))



val exists_true_ob = 
    let
        val L2R = disch (mk_exists "A" ob TRUE) (trueI [mk_exists "A" ob TRUE])
        val R2L = disch TRUE (existsI ("A",ob) (Fun("N",ob,[])) TRUE (trueI []))
    in
        dimpI L2R R2L
    end

val exists_true_ar = exists_true ("a",ar(mk_ob "A",mk_ob "B"))

 
val exists_false_ob = exists_false ("A",ob)
val exists_false_ar = exists_false ("a",ar(mk_ob "A",mk_ob "B"))


(*A \/ B ==> C  <=> A ==> C /\ B ==> C*)

fun disj_imp_distr1 A B C = 
    let val AorB = mk_disj A B
        val AorB2C = mk_imp AorB C
        val AonC = mp (assume AorB2C) (disjI1 B (assume A))
    in disch AorB2C (disch A AonC)
    end


fun disj_imp_distr2 A B C = 
    let val AorB = mk_disj A B
        val AorB2C = mk_imp AorB C
        val BonC = mp (assume AorB2C) (disjI2 A (assume B))
    in disch AorB2C (disch B BonC)
    end

fun imp_disj_distr A B C = 
    let val A2C = mk_imp A C
        val B2C = mk_imp B C
        val A2CandB2C = mk_conj A2C B2C
        val AorB = mk_disj A B
        val AonC = mp (conjE1 (assume A2CandB2C)) (assume A)
        val BonC = mp (conjE2 (assume A2CandB2C)) (assume B)
    in disch A2CandB2C (disch AorB (disjE (assume AorB) AonC BonC))
    end


fun disj_imp_distr A B C = 
    dimpI (disch (mk_imp (mk_disj A B) C)
               (conjI (undisch (disj_imp_distr1 A B C)) (undisch (disj_imp_distr2 A B C)))) (imp_disj_distr A B C)
  
fun disj_imp_distr_th (th as thm(G,A,C)) = 
    case C of
        (Conn("==>",[Conn("|",[P,Q]),R])) => dimp_mp_l2r th (disj_imp_distr P Q R)
      | f => raise ERR ("disj_imp_distr_th.not a implication from a disjunction: ",[],[],[f])

(*function that deal with dimp_mp_l2r for thm?*)


(*exists imp need to be tested func sym*)

(*(?x A) ==> B ==> A[y/x] ==> B*)

fun exists_imp x s y A B = 
    let val eA = mk_exists x s A
        val eA2B = mk_imp eA B
        val Ayx = substf ((x,s),y) A
        val AyxoneA = existsI (x,s) y A (assume Ayx) 
        val AyxonB = mp (assume eA2B) AyxoneA
    in  disch eA2B (disch Ayx AyxonB)
    end

(*(?x A(x)) ==> B <=> !y. A(y) ==> B

assume A is A(x)*)
(*
fun exists_all_imp x sx y sy A B = 
    let val eA = mk_exists x sx A
        val eA2B = mk_imp eA B
        val Ayx = substf ((x,sx),Var(y,sy)) A
        val AyxoneA = existsI (assume Ayx) (x,sx) (Var(y,sy)) A
        val AyxonB = mp (assume eA2B) AyxoneA
        val l2r = disch eA2B (allI (y,sy) (disch Ayx AyxonB))
        val Ayx2B = (mk_imp Ayx B)
        val eAonA = existsE (assume eA) (x,sx)
        val ayAyx2BeAonB =
            mp (allE 
                    (assume (mk_all y sy (mk_imp Ayx B)))
                    (Var(x,sx))) eAonA
        val r2l = disch (mk_all y sy (mk_imp Ayx B)) (disch eA ayAyx2BeAonB)
    in dimpI l2r r2l
    end

!!!!!!!!!!!!!!!!!!!!!
*)
(*need rename for existential case...

say we have (?b. P(b)) ==> A(b)*)

(*
fun imp_canon (th as thm(G,C)) = 
    case C of
        Conn("&",[A,B]) => (imp_canon (conjE1 th)) @ (imp_canon (conjE2 th))
      | Conn("==>",[Conn("|",[P,Q]),R]) => 
        (imp_canon (conjE1 (disj_imp_distr_th th)))  @ (imp_canon (conjE2 (conjE2 (disj_imp_distr_th th))))
      | Conn("==>",[Conn("&",[P,Q]),R]) => 
        imp_canon (dimp_mp_l2r th (conj_imp_equiv P Q R))
      | Quant("!",n,s,b) => 
        imp_canon (allE th (Var(n,s)))
      | Conn("==>",[Quant("?",n,s,b),B]) => 
        let 
            val n = if HOLset.member (fvf B,(n,s)) then n ^ " ' " else n 
        in
        imp_canon (dimp_mp_l2r th (exists_all_imp n s n s (subst_bound (Var(n,s)) b) B))
        end
      | Conn("==>",[_,_]) => imp_canon (undisch th) 
      | _ => [th]
*)

val nT_equiv_F = 
    let val nT2F = disch (mk_neg TRUE) (negE (trueI []) (assume (mk_neg TRUE)))
        val F2nT = disch FALSE (falseE [FALSE] (mk_neg TRUE))
    in dimpI nT2F F2nT
    end

(*need nF_equiv_T ?*)



fun eqT_intro_form f = 
    let val f2feqT = disch f (dimpI (disch f (trueI [f,f]))
                                    (disch TRUE (add_assum TRUE (assume f))))
        val feqT2f = disch (mk_dimp f TRUE) (dimp_mp_r2l (assume (mk_dimp f TRUE)) (trueI []))
    in
        dimpI f2feqT feqT2f
    end
                           
fun eqT_intro th = dimp_mp_l2r th (eqT_intro_form (concl th)) 

fun eqF_intro_form f = 
    let 
        val nF2feqF = disch (mk_neg f)
                            (dimpI (disch f (negE (assume f) (assume (mk_neg f))))
                                   (disch FALSE
                                                 (add_assum (mk_neg f) (falseE [FALSE] f))))
        val Feqf2nF = disch (mk_dimp f FALSE) 
                            (negI f (dimp_mp_l2r (assume f) (assume (mk_dimp f FALSE))))
    in 
        dimpI nF2feqF Feqf2nF
    end

fun eqF_intro th = 
    case (concl th) of
        Conn("~",[f]) => dimp_mp_l2r th (eqF_intro_form f)
      | _ => raise ERR ("eqF_intro.conclusion is not an negation: ",[],[],[concl th]) 
    



(**********************************************************************

specl: if bounded variable name clash with existing variable, then add a " ' "

**********************************************************************)


fun specl l th = 
    case l of [] => th 
            | h :: t => if is_all (concl th) then 
                            let val f1 = allE h th  
                            in 
                                specl t f1
                            end
                        else raise ERR ("specl.thm is not universally quantified",[],[],[concl th])


fun spec_all th = 
    let 
        val fv = cont th(* ((concl th) ::ant th)
        (*maybe use cont instead of fvfl?*)*)
        val v2bs = snd (strip_all (concl th))
        val v2bs' = List.map (pvariantt fv) (List.map Var v2bs)
    in 
        specl v2bs' th
    end



(**********************************************************************

gen_all:to quantify over a term, we just need to make sure that all of 
the variables which appears in it has already be quantified.

**********************************************************************)

open SymGraph

fun depends_t (n,s) t = 
    case t of 
        Var(n1,s1) => (n,s) = (n1,s1) orelse depends_s (n,s) s1
      | Fun(f,s1,l) => depends_s (n,s) s1 
                       orelse List.exists (depends_t (n,s)) l 
      | _ => false
and depends_s (n,s) sort = 
    case sort of
        ar(d,c) => depends_t (n,s) d orelse depends_t (n,s) c
      | _ => false

fun edges_from_fvs1 (n:string,s:sort) l = 
    case l of [] => []
            | h :: t => 
              if depends_t (n,s) (Var h) then 
                  ((n,s),h) :: edges_from_fvs1 (n,s) t
              else edges_from_fvs1 (n,s) t

fun edges_from_fvs0 nss = 
    let val l = HOLset.listItems nss
    in List.foldr 
           (fn (ns,l0) => (edges_from_fvs1 ns l) @ l0) [] l 
    end

fun edges_from_fvs nss = List.filter (op<>) (edges_from_fvs0 nss)



fun order_of_fvs f = 
    let val nss = fvf f
        val g0 = HOLset.foldr (fn ((n,s),g) => new_node (n,s) g) empty nss
        val g = List.foldr (fn (((n1,_),(n2,_)),g) => 
                               add_edge (n1,n2) g) g0 (edges_from_fvs nss)
    in topological_order g
    end

fun order_of nss = 
    let 
        val g0 = HOLset.foldr (fn ((n,s),g) => new_node (n,s) g) empty nss
        val g = List.foldr (fn (((n1,_),(n2,_)),g) => 
                               add_edge (n1,n2) g) g0 (edges_from_fvs nss)
    in topological_order g
    end

fun abstl l th = 
    case l of 
        [] => th
      | (n,s) :: t => allI (n,s) (abstl t th)

fun find_var l n = 
    case l of 
        [] => simple_fail"variable name not found"
      | h :: t => 
        if fst h = n then h 
        else find_var t n

fun genl vsl th = 
    let
        val ovs = order_of ((foldr (uncurry (C (curry HOLset.add)))) essps vsl)
        val vl = List.map (find_var vsl) ovs
    in 
        abstl vl th
    end


fun gen_all th = 
    let 
        val vs = HOLset.difference
                     (fvf (concl th), fvfl (ant th))
        val vsl = HOLset.listItems vs
        val ovs = order_of vs
        val vl = List.map (find_var vsl) ovs
    in 
        abstl vl th
    end



fun dischl l th = 
    case l of 
        [] => th
      | h :: t => dischl t (disch h th)

fun disch_all th = dischl (ant th) th


(*f1,f2 |- C maps to f1 /\ f2 |- C*)

fun conj_assum f1 f2 (th as thm(G,A,C)) = 
    let 
        val _ = fmem f1 A orelse raise ERR ("conj_assum.first formula not in assumption: ",[],[],[f1])
        val _ = fmem f2 A orelse raise ERR ("conj_assum.second formula not in assumption: ",[],[],[f2])
        val th1 = disch f1 (disch f2 th)
    in mp (mp th1 (conjE1 (assume (mk_conj f1 f2))))
          (conjE2 (assume (mk_conj f1 f2)))
    end

fun conj_all_assum (th as thm(G,A,C)) = 
    case A of 
        [] => th
       |[h] => th
       |h1 :: h2 :: t => conj_all_assum (conj_assum h1 h2 (thm(G,A,C)))

(*~f |-> f ==> F*)

fun notf_f2F f = 
    let val d1 = negE (assume f) (assume (mk_neg f))|> disch f |> disch (mk_neg f)
        val d2 = (assume (mk_imp f FALSE)) |> undisch |> negI f|> disch (mk_imp f FALSE)
    in
        dimpI d1 d2
    end

fun strip_neg th = 
    case (concl th) of 
        (Conn("~",[f])) => dimp_mp_l2r th (notf_f2F f)
      | _ => th


(*F2f f = |-F ⇒ f *)
fun F2f f = disch FALSE (falseE [FALSE] f)

(*for a th with concl FALSE, A |- F. 
CONTR f th = A |- f
*)
fun CONTR f th =
    if concl th  = FALSE then
        mp (F2f f) th else 
    raise ERR ("contr.input theorem not a FALSE",[],[],[concl th])


fun double_neg_th th = 
    dimp_mp_r2l (double_neg (concl th)) th

fun elim_double_neg th = 
    dimp_mp_l2r th (double_neg(dest_neg (dest_neg (concl th)))) 

fun exists_all (n,s) = 
    let val d1 = (C negI)
                 (existsE (n,s) (assume (Quant("?",n,s,fVar "f0")))
                 (negE (assume (fVar "f0")) 
                   ((C allE) (assume (Quant("!",n,s,mk_neg (fVar "f0"))))
                         (Var(n,s)))))
                 (Quant("!",n,s,mk_neg (fVar "f0"))) |>
                 disch (Quant("?",n,s,fVar "f0"))
        val d2 = elim_double_neg
                     ((C negI)
                          (negE
                               (allI (n,s)
                                     ((C negI)
                                          (negE
                                               (existsI (n,s) (Var(n,s)) (fVar "f0") ((C add_cont) (assume (fVar "f0")) (HOLset.add(essps,(n,s))))
                                                        )
                                               (assume (mk_neg (Quant("?",n,s,fVar "f0")))))
                                          (fVar "f0")))
                               (assume (mk_neg (Quant("!",n,s,mk_neg (fVar "f0")))))
)
                          (mk_neg (Quant("?",n,s,fVar "f0"))))|>
                     disch (mk_neg (Quant("!",n,s,mk_neg (fVar "f0"))))
    in dimpI d1 d2
    end


fun split_assum f th = 
    if fmem f (ant th) then
        case f of (Conn("&",[f1,f2])) => 
                  th |> disch f |> (C mp) (conjI (assume f1) (assume f2))
                | _ =>  raise ERR ("split_assum.not a conjunction: ",[],[],[f])
    else raise ERR ("split_assum.formula not in assumption list",[],[],[f])

(*todo:dual for exists_all: !a.P(a) <=> ~?a.~P(a)*)
(*todo: a rule for eleminating ~~ taking an ~~ formula*)


(*~F <=> T and also ~T <=> F*)

val nF2T = 
    let val l2r = trueI [mk_neg FALSE] |> disch_all
        val r2l = assume FALSE |> add_assum TRUE |> negI FALSE |> disch_all
    in dimpI l2r r2l
    end

val nT2F = 
    let val l2r = assume (mk_neg TRUE) |> negE (trueI []) |> disch_all
        val r2l = falseE [FALSE] (mk_neg TRUE) |> disch_all
    in dimpI l2r r2l
    end

val double_neg_elim = double_neg (fVar "f0")



fun all_exists (n,s) = 
    let val th0 = exists_all (n,s) |> neg_iff |> inst_thm (mk_inst [] [("f0",mk_neg (fVar "f0"))]) 
        val rhs1 = double_neg (fVar "f0") |> all_iff (n,s)
        val rhs2 = double_neg (mk_all n s (mk_neg (mk_neg (fVar "f0"))))
        val rhs = iff_trans rhs2 rhs1
        val th0' = iff_trans th0 rhs
    in iff_swap th0'
    end


fun aimp_rule th =
    let
      val (l, r) = dest_imp (concl th)
      val (c1, c2) = dest_conj l
      val cth = conjI (assume c1) (assume c2)
    in
      disch c1 (disch c2 (mp th cth))
    end

fun (s1 - s2) = HOLset.difference(s1,s2)

fun is_forall f = 
    case f of 
        Quant(q,_,_,_) => if q = "!" then true else false
      | _ => false

fun dest_imp_only f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("dest_imp_only.not a implication",[],[],[f])

fun norm th =
    if is_forall (concl th) then norm (spec_all th)
    else
      case Lib.total dest_imp_only (concl th) of
          NONE => th
        | SOME (l,r) =>
          if is_conj l then norm (aimp_rule th)
          else norm (undisch th)

fun overlaps fvset (tfvs,_) =
      not (HOLset.isEmpty (HOLset.intersection(fvset, tfvs)))

fun union ((fvset1, tlist1), (fvset2, tlist2)) =
      (HOLset.union(fvset1, fvset2), tlist1 @ tlist2)

fun recurse gfvs acc tlist =
      case tlist of
          [] => acc
        | t::ts =>
          let
            val tfvs = (fvf t) - gfvs
          in
            case List.partition (overlaps tfvs) acc of
                ([], _) => recurse gfvs ((tfvs,[t])::acc) ts
              | (ovlaps, rest) =>
                recurse gfvs (List.foldl union (tfvs, [t]) ovlaps :: rest) ts
          end

fun group_hyps gfvs tlist = recurse gfvs [] tlist

fun foldthis ((n,s),(t,th)) =
      let val ext = mk_exists n s t
      in
        (ext, existsE (n,s) (assume ext) th)
      end

fun choosel vs t th = List.foldr foldthis (t,th) vs


val conjuncts =
   let
      fun aux acc th =
         aux (aux acc (conjE2 th)) (conjE1 th)
         handle _ => th :: acc
   in
      aux []
   end

(*to get consistent order, foldl, or rev and take hd and tl, then foldr
current gives 
 ["P(a)","P(b)","P(c)"] |-> P(c) & (P(b) & P(a))
*)
fun list_mk_conj fl = List.foldl (uncurry mk_conj) (List.hd fl) (List.tl fl)



fun conjl ts th = let
  val c = list_mk_conj ts
  val cths = conjuncts (assume c)
in
  (List.foldl (fn (c,th) => prove_hyp c th) th cths, c)
end

fun recurse acc groups th =
      case groups of
          [] => (acc, th)
        | (fvset, ts) :: rest =>
          let
            val (th1,c) = conjl ts th
            val (ext, th2) = choosel (HOLset.listItems fvset) c th1
          in
            recurse (ext::acc) rest th2
          end



fun recurse acc groups th =
      case groups of
          [] => (acc, th)
        | (fvset, ts) :: rest =>
          let
            val (th1,c) = conjl ts th
            val (ext, th2) = choosel (HOLset.listItems fvset) c th1
          in
            recurse (ext::acc) rest th2
          end

fun reconstitute groups th = recurse [] groups th

fun form_list_diff l1 l2 = 
    case l1 of 
        [] => []
      | h :: t => if fmem h l2 then list_diff t l2 else h :: list_diff t l2


fun irule_canon th =
  let
    val th1 = norm (gen_all th)
    val origl = ant th
    val gfvs = fvfl (concl th1 :: origl) 
    val newhyps = form_list_diff (ant th1)  origl
    val grouped = group_hyps gfvs newhyps
    val (cs, th2) = reconstitute grouped th1
  in
    case cs of
        [] => gen_all th2
      | _ =>
        let
          val (th3,c) = conjl cs th2
        in
          disch c th3 |> gen_all
        end
  end



fun eq_imp_rule th = (dimpl2r th,dimpr2l th)

datatype AI = imp of form | fa of {orig:string * sort, new:string * sort}

fun dest_forall f = 
    case f of
        Quant("!",n,s,b) => ((n,s),b)
      | _ => raise ERR ("dest_forall.not a forall",[],[],[f])

fun spec t = specl [t]

fun AIdestAll th =
    case total dest_forall (concl th) of
        NONE => NONE
      | SOME ((n,s),b) =>
        let
          val hfvs = fvfl (ant th)
        in
          if HOLset.member(hfvs, (n,s)) then
            let val new = dest_var (pvariantt hfvs (Var(n,s)))
            in
              SOME (fa{orig=(n,s),new=new}, spec (Var new) th)
            end
          else
            SOME (fa{orig=(n,s),new=(n,s)}, spec (Var(n,s)) th)
        end

(*!y.P(y)<=> !x.P(x)*)

fun all_rename x f = 
    case f of
        Quant("!",n,s,b) =>
        let val l2r =  assume f |> allE (Var(x,s)) |> allI (x,s) |> disch_all
            val r2l =  assume (Quant("!",x,s,b)) |> allE (Var(y,s)) |> allI (y,s) |> disch_all
        in dimpI l2r r2l
        end
      | _ => raise ERR ("all_rename.not a forall",[],[],[f])

(*
fun exists_rename x f = 
    case f of
        Quant("?",n,s,b) =>
        let val l2r =  assume f |> existsE (Var(y,s)) |> allI (x,s) |> disch_all
            val r2l =  assume (Quant("!",x,s,b)) |> allE (Var(y,s)) |> allI (y,s) |> disch_all
        in dimpI l2r r2l
        end
      | _ => raise ERR ("all_rename.not a forall",[],[],[f])



fun gen_rename_fconv x 
*)

fun restore hs (acs, th) =
    case acs of
        [] => rev_itlist add_assum hs th
      | imp t :: rest => restore hs (rest, disch t th)
      | fa{orig,new} :: rest =>
        if orig = new then
          restore hs (rest, allI orig th)
        else
          restore hs (rest, th |> allI new |> conv_rule (all_rename (fst orig)))


fun underALLs f th =
    let
      fun getbase A th =
          case AIdestAll th of
              NONE => (A, f th)
            | SOME (act, th') => getbase (act::A) th'
    in
      restore [] (getbase [] th)
    end


fun underAIs f th =
    let
      fun getbase A th =
          case AIdestAll th of
              NONE => (case total dest_imp_only (concl th) of
                           NONE => (A, f th)
                         | SOME (l,r) => getbase (imp l :: A) (undisch th))
            | SOME (act,th') => getbase (act::A) th'
    in
      restore (ant th) (getbase [] th)
    end


end
