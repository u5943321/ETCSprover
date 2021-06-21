structure drule :> drule = 
struct
open term form thm


fun undisch th = mp th (assume (#1(dest_imp (concl th))))

fun add_assum f th = mp (disch f th) (assume f)

fun simple_exists (v as (n,s)) th = existsI th v (Var v) (concl th)

fun imp_trans th1 th2 = 
    let val (ant,cl) = dest_imp (concl th1)
    in disch ant (mp th2 (mp th1 (assume ant)))
    end

fun prove_hyp th1 th2 = mp (disch (concl th1) th2) th1

fun equivT (thm(G,A,C)) = dimpI (disch C (trueI (C :: A))) 
                              (disch TRUE (add_assum TRUE (thm(G,A,C))))

fun frefl f = dimpI (disch f (assume f)) (disch f (assume f))

fun dimpl2r th = conjE1 (dimpE th)

fun dimpr2l th = conjE2 (dimpE th)

fun cj_imp1 pq = disch pq (conjE1 (assume pq))

fun cj_imp2 pq = disch pq (conjE2 (assume pq))

(*given |- A1 <=> A2 , |- B1 <=> B2, return |- A1 /\ B1 <=> A2 /\ B2*)

(*conj_swap conj_comm*)

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
        val a1ondj2 = disjI1 a1ona2 b2
        val b1ondj2 = disjI2 a2 b1onb2
        val dj12dj2 = disch dj1 
                            (disjE a1 b1 dj2 
                                   (assume dj1) a1ondj2 b1ondj2)
        val a2ondj1 = disjI1 a2ona1 b1
        val b2ondj1 = disjI2 a1 b2onb1
        val dj22dj1 = disch dj2
                            (disjE a2 b2 dj1
                                   (assume dj2) a2ondj1 b2ondj1) 
    in 
        dimpI dj12dj2 dj22dj1
    end

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

fun neg_iff (thm(G,A,C)) = 
    let val (a1,a2) = dest_dimp C
        val a1ona2 = undisch (dimpl2r (thm(G,A,C)))
        val a2ona1 = undisch (dimpr2l (thm(G,A,C)))
        val neg1 = Conn("~",[a1])
        val neg2 = Conn("~",[a2])
        val neg1a22F = negE (assume neg1) a2ona1
        val neg2a12F = negE (assume neg2) a1ona2
        val neg12neg2 = disch neg1 (negI neg1a22F a2)
        val neg22neg1 = disch neg2 (negI neg2a12F a1)
    in 
        dimpI neg12neg2 neg22neg1
    end

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
        val aorbnaonb = disjE A B B (assume (Conn("|",[A,B]))) anaonb (assume B)
        val disj2imp = disch (Conn("|",[A,B])) (disch na aorbnaonb)
        val t = tautI A 
        val aonaorb = disjI1 (assume A) B
        val impnaonaorb = disjI2 A (mp (assume imp) (assume na))
        val imp2disj = disch imp (disjE A na (Conn("|",[A,B])) t aonaorb impnaonaorb)
    in
        dimpI disj2imp imp2disj
    end

fun disj_swap A B = 
    let val dj = Conn("|",[A,B])
        val aonbora = disjI2 B (assume A)
        val bonbora = disjI1 (assume B) A
    in disch dj (disjE A B (Conn("|",[B,A])) (assume dj) aonbora bonbora)
    end

fun disj_comm A B = dimpI (disj_swap A B) (disj_swap B A)

fun double_neg f = 
    let val nf = Conn("~",[f])
        val nnf = Conn("~",[nf])
        val fnfonF = negE (assume f) (assume nf)
        val f2nnf = disch f (negI fnfonF nf)
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
        val f2F2nf = disch (Conn("==>",[f,FALSE])) (negI (mp (assume (Conn("==>",[f,FALSE]))) (assume f)) f)
    in dimpI f2F2nf nf2f2F
    end

fun T_disj1 f = 
    let val Torf = Conn("|",[TRUE,f])
        val Torf2T = disch Torf (trueI [Torf]) 
        val T2Torf = disch TRUE (disjI1 (assume TRUE) f)
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
        val Forf2f = disch Forf (disjE FALSE f f (assume Forf) (falseE [FALSE] f) (assume f))
        val f2Forf = disch f (disjI2 FALSE (assume f))
    in dimpI Forf2f f2Forf
    end


fun F_disj2 f = 
    let val forF = Conn("|",[f,FALSE])
        val forF2f = disch forF (disjE f FALSE f (assume forF) (assume f) (falseE [FALSE] f))
        val f2forF = disch f (disjI1 (assume f) FALSE)
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
        val Feqf2nf = disch Feqf (negI (dimp_mp_r2l (assume Feqf) (assume f)) f)
        val nf2Feqf = disch (mk_neg f) (dimpI (disch FALSE (add_assum (mk_neg f) (falseE [FALSE] f)))
                                     (disch f (negE (assume f) (assume (mk_neg f)))))
    in dimpI Feqf2nf nf2Feqf
    end

fun F_dimp2 f = 
    let val feqF = Conn("<=>",[f,FALSE])
        val feqF2nf = disch feqF (negI (dimp_mp_l2r (assume f) (assume feqF)) f)
        val nf2feqF = disch (mk_neg f) (dimpI (disch f (negE (assume f) (assume (mk_neg f))))
                                              (disch FALSE (add_assum (mk_neg f) (falseE [FALSE] f))))
    in dimpI feqF2nf nf2feqF
    end

(*the 2 below can be better!!*)

fun forall_true (n,s) = 
    let val aT = mk_all n s TRUE
        val G = HOLset.union(HOLset.add(essps,(n,s)),fvs s)
        val aT2T = disch aT (trueI [aT])
        val T2aT = disch TRUE (allI (n,s) (add_cont (assume TRUE) G))
    in dimpI aT2T T2aT
    end


fun forall_false (n,s) = 
    let val aF = mk_all n s FALSE
        val G = HOLset.union(HOLset.add(essps,(n,s)),fvs s)
        val aF2F = disch aF (allE (add_cont (assume aF) G) (Var(n,s)))
        val F2aF = disch FALSE (falseE [FALSE] aF)
    in dimpI aF2F F2aF
    end

fun exists_true (n,s) = 
    let 
        val TwG = add_cont (trueI [])   
                           (HOLset.union(HOLset.add(essps,(n,s)),fvs s))
        val T2eT =
            disch TRUE 
                  (add_assum TRUE 
                             (existsI TwG (n,s) (Var(n,s)) TRUE))
        val eT2T = disch (mk_exists n s TRUE) TwG
    in dimpI eT2T T2eT
    end

(*more general version use term instead of variable?*)


fun exists_false (n,s) = 
    thm(essps,[],mk_dimp (mk_exists n s FALSE) FALSE)


(* TODO: cj_asm: A1,A2 |- B <=> A1/\ A2 |- B *)


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
        else raise ERR ("two iffs do not match" ^ (string_of_form C1) ^ " , " ^ (string_of_form C2))
      | _ => raise ERR "not a pair of iffs"

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
      | _ => raise ERR ("not a pair of iff" ^ string_of_form C1 ^ " , " ^ string_of_form C2)



fun all_iff (th as thm(G,A,C)) (n,s) = 
    case C of 
        Conn("<=>",[P,Q]) => 
        let val allP = Quant("ALL", n, s, P)
            val allQ = Quant("ALL", n, s, Q)
            val allP2allQ = disch allP (allI (n,s) (dimp_mp_l2r (allE (assume allP) (Var(n,s))) th))
            val allQ2allP = disch allQ (allI (n,s) (dimp_mp_r2l th (allE (assume allQ) (Var(n,s)))))
        in
            dimpI allP2allQ allQ2allP
        end
      | _ => raise ERR ("conclusion of theorem is not an iff" ^ " " ^ string_of_form C)


fun all_iff (th as thm(G,A,C)) (n,s) = 
    case C of 
        Conn("<=>",[P,Q]) => 
        let val allP = Quant("ALL", n, s, abstract (n,s) P)
            val allQ = Quant("ALL", n, s, abstract (n,s) Q)
            val allP2allQ = disch allP (allI (n,s) (dimp_mp_l2r (allE (assume allP) (Var(n,s))) th))
            val allQ2allP = disch allQ (allI (n,s) (dimp_mp_r2l th (allE (assume allQ) (Var(n,s)))))
        in
            dimpI allP2allQ allQ2allP
        end
      | _ => raise ERR ("conclusion of theorem is not an iff" ^ " " ^ string_of_form C)



fun exists_iff (th as thm(G,A,C)) (n,s) = 
    let
        val (P,Q) = dest_dimp C
        val P2Q = undisch (conjE1 (dimpE th))
        val Q2P = undisch (conjE2 (dimpE th))
        val eP = Quant("EXISTS", n, s, abstract (n,s) P)        
        val eQ = Quant("EXISTS", n, s, abstract (n,s) Q)
        val P2eQ = existsI P2Q (n,s) (Var(n,s)) Q
        val Q2eP = existsI Q2P (n,s) (Var(n,s)) P
        val eP2eQ = existsE (n,s) (assume eP) P2eQ |> disch eP
        val eQ2eP = existsE (n,s) (assume eQ) Q2eP |> disch eQ
    in dimpI eP2eQ eQ2eP
    end

(*F_IMP: ~f ==> f ==> F*)
fun F_imp f = assume f|> negE (assume (mk_neg f)) |> disch f |> disch (mk_neg f)

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
        val L2R = disch (mk_all "A" ob FALSE) (allE f0 (Fun("N",ob,[])))
        val R2L = disch FALSE (falseE [FALSE] (mk_all "A" ob FALSE))
    in
        dimpI L2R R2L
    end

val all_false_ar = forall_false ("a",ar(mk_ob "A",mk_ob "B"))



val exists_true_ob = 
    let
        val L2R = disch (mk_exists "A" ob TRUE) (trueI [mk_exists "A" ob TRUE])
        val R2L = disch TRUE (existsI (trueI []) ("A",ob) (Fun("N",ob,[])) TRUE)
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
        val AonC = mp (assume AorB2C) (disjI1 (assume A) B)
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
    in disch A2CandB2C (disch AorB (disjE A B C (assume AorB) AonC BonC))
    end


fun disj_imp_distr A B C = 
    dimpI (disch (mk_imp (mk_disj A B) C)
               (conjI (undisch (disj_imp_distr1 A B C)) (undisch (disj_imp_distr2 A B C)))) (imp_disj_distr A B C)
  
fun disj_imp_distr_th (th as thm(G,A,C)) = 
    case C of
        (Conn("==>",[Conn("|",[P,Q]),R])) => dimp_mp_l2r th (disj_imp_distr P Q R)
      | f => raise ERR ("Error disj_imp_distr_th" ^ " : " ^ (string_of_form f))

(*function that deal with dimp_mp_l2r for thm?*)


(*exists imp need to be tested func sym*)

(*(?x A) ==> B ==> A[y/x] ==> B*)

fun exists_imp x s y A B = 
    let val eA = mk_exists x s A
        val eA2B = mk_imp eA B
        val Ayx = substf ((x,s),y) A
        val AyxoneA = existsI (assume Ayx) (x,s) y A
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
      | Quant("ALL",n,s,b) => 
        imp_canon (allE th (Var(n,s)))
      | Conn("==>",[Quant("EXISTS",n,s,b),B]) => 
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
                            (negI (dimp_mp_l2r (assume f) (assume (mk_dimp f FALSE))) f)
    in 
        dimpI nF2feqF Feqf2nF
    end

fun eqF_intro th = 
    case (concl th) of
        Conn("~",[f]) => dimp_mp_l2r th (eqF_intro_form f)
      | _ => raise 
                 ERR ("eqF_intro: conclusion " ^ (string_of_form (concl th)) ^ " is not a negation") 
    



(*spec_all*)
(*
fun specl th l = 
    if is_all (concl th) then 
        case l of [] => th
                | h :: t => 
                  let val f1 = allE th h  (*handle ERR _ => th*)
                  in 
                      specl f1 t
                  end
    else th 

*)

fun specl th l = 
    case l of [] => th 
            | h :: t => if is_all (concl th) then 
                            let val f1 = allE th h  (*handle ERR _ => th*)
                            in 
                                specl f1 t
                            end
                        else raise ERR "thm is not universally quantified"


(*issue caused by pvariant also rename the sorts*)


fun spec_all th = 
    let 
        val fv = fvfl ((concl th) ::ant th)
        (*maybe use cont instead of fvfl?*)
        val v2bs = snd (strip_all (concl th))
        val v2bs' = List.map (pvariantt fv) (List.map Var v2bs)
    in 
        specl th v2bs'
    end



(*

fun conj_pair th =
    (conjE1 th,conjE2 th)
    handle ERR _ => 
           raise ERR ("not a conjunction" ^ (string_of_form (concl th)) ^ ": From conj_pair")

fun fconv_canon th = 
    let val th = spec_all th
        val f = concl th
    in 
       (* if aconv f TRUE then [] else seems happens in HOL but not here*)
        if is_dimp f then [th] else
        if is_conj f then (op@ o (fconv_canon ## fconv_canon) o conj_pair) th else
        if is_neg f then [eqF_intro th] 
        else [eqT_intro th]
    end 


*)


(*to quantify over a term, we just need to make sure that all of the variables which appears in it has already be quantified.*)

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

fun abstl th l = 
    case l of 
        [] => th
      | (n,s) :: t => allI (n,s) (abstl th t)

fun find_var l n = 
    case l of 
        [] => raise ERR "variable name not found"
      | h :: t => 
        if fst h = n then h 
        else find_var t n

fun genl vsl th = 
    let
        val ovs = order_of ((foldr (uncurry (C (curry HOLset.add)))) essps vsl)
        val vl = List.map (find_var vsl) ovs
    in 
        abstl th vl
    end


fun gen_all th = 
    let 
        val vs = HOLset.difference
                     (fvf (concl th), fvfl (ant th))
        val vsl = HOLset.listItems vs
        val ovs = order_of vs
        val vl = List.map (find_var vsl) ovs
    in 
        abstl th vl
    end



fun dischl l th = 
    case l of 
        [] => th
      | h :: t => dischl t (disch h th)

fun disch_all th = dischl (ant th) th

(*new GSYM*)






(*
readf "f <=> g";
val it = f <=> g: form
> val f = it;
val f = f <=> g: form
> # Exception- ERR "f <=> g is not a double implication" raised

check what does it read...
*)

(*fun GSYM th =  sym (spec_all th) *)

(*f1,f2 |- C maps to f1 /\ f2 |- C*)

fun conj_assum f1 f2 (th as thm(G,A,C)) = 
    let 
        val _ = fmem f1 A orelse raise ERR "first formula not in assumption"
        val _ = fmem f2 A orelse raise ERR "second formula not in assumption"
        val th1 = disch f1 (disch f2 th)
    in mp (mp th1 (conjE1 (assume (mk_conj f1 f2))))
          (conjE2 (assume (mk_conj f1 f2)))
    end

(*
fun conj_asl fl th = 
case fl

*)
fun F2f f = disch FALSE (falseE [FALSE] f)

fun CONTR f th =
   mp (F2f f) th handle ERR _ => raise ERR "CONTR"


fun double_neg_th th = 
    dimp_mp_r2l (double_neg (concl th)) th
end
