structure drule :> drule = 
struct
open term form thm


fun simple_exists (v as (n,s)) th = existsI th v (Var v) (concl th)

fun imp_trans th1 th2 = 
    let val (ant,cl) = dest_imp (concl th1)
    in disch ant (mp th2 (mp th1 (assume ant)))
    end

fun prove_hyp th1 th2 = mp (disch (concl th1) th2) th1

fun equivT (thm(G,C)) = dimpI (disch C (trueI (C :: G))) 
                              (disch TRUE (add_assum TRUE (thm(G,C))))

fun frefl f = dimpI (disch f (assume f)) (disch f (assume f))

fun dimpl2r th = conjE1 (dimpE th)

fun dimpr2l th = conjE2 (dimpE th)

fun cj_imp1 pq = disch pq (conjE1 (assume pq))

fun cj_imp2 pq = disch pq (conjE2 (assume pq))

(*given |- A1 <=> A2 , |- B1 <=> B2, return |- A1 /\ B1 <=> A2 /\ B2*)

(*conj_swap conj_comm*)

fun conj_iff (thm(G1,C1)) (thm(G2,C2)) = 
    let val (A1,A2) = dest_dimp C1
        val (B1,B2) = dest_dimp C2
        val A12A2 = dimpl2r (thm(G1,C1))
        val A22A1 = dimpr2l (thm(G1,C1))
        val B12B2 = dimpl2r (thm(G2,C2))
        val B22B1 = dimpr2l (thm(G2,C2))
        val cj1 = Conn("&",[A1,B1])
        val cj2 = Conn("&",[A2,B2])
    in dimpI
            (disch cj1
                   (conjI 
                        (mp A12A2 (conjE1 (assume cj1)))
                        (mp B12B2 (conjE2 (assume cj1))))
            )
            (disch cj2
                   (conjI
                        (mp A22A1 (conjE1 (assume cj2)))
                        (mp B22B1 (conjE2 (assume cj2))))
            )
    end

fun disj_iff (thm(G1,C1)) (thm(G2,C2)) = 
    let val (A1,A2) = dest_dimp C1
        val (B1,B2) = dest_dimp C2
        val A1onA2 = undisch (dimpl2r (thm(G1,C1)))
        val A2onA1 = undisch (dimpr2l (thm(G1,C1)))
        val B1onB2 = undisch (dimpl2r (thm(G2,C2)))
        val B2onB1 = undisch (dimpr2l (thm(G2,C2)))
        val dj1 = Conn("|",[A1,B1])
        val dj2 = Conn("|",[A2,B2])
        val A1ondj2 = disjI1 A1onA2 B2
        val B1ondj2 = disjI2 A2 B1onB2
        val dj12dj2 = disch dj1 
                            (disjE A1 B1 dj2 
                                   (assume dj1) A1ondj2 B1ondj2)
        val A2ondj1 = disjI1 A2onA1 B1
        val B2ondj1 = disjI2 A1 B2onB1
        val dj22dj1 = disch dj2
                            (disjE A2 B2 dj1
                                   (assume dj2) A2ondj1 B2ondj1) 
    in 
        dimpI dj12dj2 dj22dj1
    end

fun imp_iff (thm(G1,C1)) (thm(G2,C2)) =  
    let val (A1,A2) = dest_dimp C1
        val (B1,B2) = dest_dimp C2
        val A12A2 = dimpl2r (thm(G1,C1))
        val A22A1 = dimpr2l (thm(G1,C1))
        val B12B2 = dimpl2r (thm(G2,C2))
        val B22B1 = dimpr2l (thm(G2,C2))
        val imp1 = Conn("==>",[A1,B1])
        val imp2 = Conn("==>",[A2,B2])
        val imp12imp2 = disch imp1 (imp_trans A22A1 (imp_trans (assume imp1) B12B2))
        val imp22imp1 = disch imp2 (imp_trans A12A2 (imp_trans (assume imp2) B22B1))
    in 
        dimpI imp12imp2 imp22imp1
    end

fun neg_iff (thm(G,C)) = 
    let val (A1,A2) = dest_dimp C
        val A1onA2 = undisch (dimpl2r (thm(G,C)))
        val A2onA1 = undisch (dimpr2l (thm(G,C)))
        val neg1 = Conn("~",[A1])
        val neg2 = Conn("~",[A2])
        val neg1A22F = negE (assume neg1) A2onA1
        val neg2A12F = negE (assume neg2) A1onA2
        val neg12neg2 = disch neg1 (negI neg1A22F A2)
        val neg22neg1 = disch neg2 (negI neg2A12F A1)
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
        val F2b = disch FALSE (falseE B)
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

fun T_conj1 f = dimpI (disch (Conn("&",[TRUE,f])) (conjE2 (assume (Conn("&",[TRUE,f])))))
                      (disch f (conjI (trueI []) (assume f)))

fun T_conj2 f = dimpI (disch (Conn("&",[f,TRUE])) (conjE1 (assume (Conn("&",[f,TRUE])))))
                      (disch f (conjI (assume f) (trueI [])))

fun F_conj1 f = dimpI (disch (Conn("&",[FALSE,f])) (conjE1 (assume (Conn("&",[FALSE,f])))))
                      (disch FALSE (falseE (Conn("&",[FALSE,f]))))

fun F_conj2 f = dimpI (disch (Conn("&",[f,FALSE])) (conjE2 (assume (Conn("&",[f,FALSE])))))
                      (disch FALSE (falseE (Conn("&",[f,FALSE]))))

fun all_true (n,s) = dimpI (disch (Quant("ALL",n,s,TRUE)) (trueI []))
                           (disch TRUE (allI (n,s) (trueI [])))

(*
val all_true_ar = all_true ("a",ar(Var("A",ob),Var("B",ob)))
val all_true_ob = all_true ("A",ob)
*)

fun all_false (n,s) = dimpI (disch (Quant("ALL",n,s,FALSE)) 
                                   (allE (assume (Quant("ALL",n,s,FALSE))) (Var (n,s))))
                            (disch FALSE (allI (n,s) (assume FALSE)))

(*
val all_false_ar = all_false ("a",ar(Var("A",ob),Var("B",ob)))
val all_false_ob = all_false ("A",ob)
*)

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
        val T2F2f = disch TRUE (disch FALSE (falseE f))
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
        val Forf2f = disch Forf (disjE FALSE f f (assume Forf) (falseE f) (assume f))
        val f2Forf = disch f (disjI2 FALSE (assume f))
    in dimpI Forf2f f2Forf
    end


fun F_disj2 f = 
    let val forF = Conn("|",[f,FALSE])
        val forF2f = disch forF (disjE f FALSE f (assume forF) (assume f) (falseE f))
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
        val F2fnf = disch FALSE (falseE fnf)
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
        val nf2Feqf = disch (mk_neg f) (dimpI (disch FALSE (add_assum (mk_neg f) (falseE f)))
                                     (disch f (negE (assume f) (assume (mk_neg f)))))
    in dimpI Feqf2nf nf2Feqf
    end

fun F_dimp2 f = 
    let val feqF = Conn("<=>",[f,FALSE])
        val feqF2nf = disch feqF (negI (dimp_mp_l2r (assume f) (assume feqF)) f)
        val nf2feqF = disch (mk_neg f) (dimpI (disch f (negE (assume f) (assume (mk_neg f))))
                                              (disch FALSE (add_assum (mk_neg f) (falseE f))))
    in dimpI feqF2nf nf2feqF
    end

fun forall_true (n,s) = 
    let val aT = mk_all n s TRUE
        val aT2T = disch aT (trueI [aT])
        val T2aT = disch TRUE (allI (n,s) (assume TRUE))
    in dimpI aT2T T2aT
    end


fun forall_false (n,s) = 
    let val aF = mk_all n s FALSE
        val aF2F = disch aF (allE (assume aF) (Var(n,s)))
        val F2aF = disch FALSE (falseE aF)
    in dimpI aF2F F2aF
    end


(*the Var(n,s) can be any term*)

fun exists_true (n,s) = 
    let val eT = mk_exists n s TRUE
        val eT2T = disch eT (trueI [eT])
        val T2eT = disch TRUE (existsI (assume TRUE) (n,s) (Var(n,s)) TRUE)
    in dimpI eT2T T2eT
    end


fun exists_false (n,s) = 
    let val eF = mk_exists n s FALSE
        val eF2F = disch eF (existsE (assume eF) (n,s))
        val F2eF = disch FALSE (falseE eF)
    in dimpI eF2F F2eF
    end

(*
fun conj_comm c1 c2 = 

*)

(*compare*)

fun iff_trans (thm(G1,C1)) (thm(G2,C2)) =
    case (C1,C2) of 
        (Conn("<=>",[f1,f2]), Conn("<=>",[f3,f4])) => 
        if eq_form (f2,f3) then 
            let val f1f2 = conjE1 (dimpE (thm(G1,C1)))
                val f2f1 = conjE2 (dimpE (thm(G1,C1)))
                val f2f4 = conjE1 (dimpE (thm(G2,C2)))
                val f4f2 = conjE2 (dimpE (thm(G2,C2)))
                val f1f4 = imp_trans f1f2 f2f4
                val f4f1 = imp_trans f4f2 f2f1
            in dimpI f1f4 f4f1
            end
        else raise ERR ("two iffs do not match" ^ (string_of_form C1) ^ " , " ^ (string_of_form C2))
      | _ => raise ERR "not a pair of iffs"

fun iff_swap (thm(G,C)) = 
    let val Q2P = conjE2 (dimpE (thm(G,C)))
        val P2Q = conjE1 (dimpE (thm(G,C)))
    in dimpI Q2P P2Q
    end

(*P <=> P', Q <=> Q', gives (P <=> Q) <=> (P' <=> Q')*)

fun dimp_iff (th1 as thm(G1,C1)) (th2 as thm(G2,C2)) = 
     case (C1,C2) of 
        (Conn("<=>",[P1,P2]), Conn("<=>",[Q1,Q2])) => 
        let val P1iffQ1 = Conn("<=>",[P1,Q1])
            val P2iffQ2 = Conn("<=>",[P2,Q2])
            val P1iffQ12P2iffQ2 = disch P1iffQ1 (iff_trans (iff_swap th1) (iff_trans (assume P1iffQ1) th2))
            val P2iffQ22P1iffQ1 = disch P2iffQ2 (iff_trans (iff_trans th1 (assume P2iffQ2)) (iff_swap th2))
        in dimpI P1iffQ12P2iffQ2 P2iffQ22P1iffQ1
        end
      | _ => raise ERR ("not a pair of iff" ^ string_of_form C1 ^ " , " ^ string_of_form C2)


fun all_iff (th as thm(G,C)) (n,s) = 
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

(*
fun exists_iff (th as thm(G,C)) (n,s) = 
    case C of 
        Conn("<=>",[P,Q]) => 
        let val eP = Quant("EXISTS", n, s, P)
            val eQ = Quant("EXISTS", n, s, Q)
            val eP2eQ = disch eP (simple_exists (n,s) (dimp_mp_l2r (existsE (assume eP) (n,s)) th))
            val eQ2eP = disch eQ (existsI (dimp_mp_r2l th (existsE (assume eQ) (n,s))) (n,s))
        in
            dimpI eP2eQ eQ2eP
        end
      | _ => raise ERR ("conclusion of theorem is not an iff"  ^ " " ^ string_of_form C)
*)

fun exists_iff (th as thm(G,C)) (n,s) = 
    case C of 
        Conn("<=>",[P,Q]) => 
        let val eP = Quant("EXISTS", n, s, P)
            val eQ = Quant("EXISTS", n, s, Q)
            val eP2eQ = disch eP (simple_exists (n,s) (dimp_mp_l2r (existsE (assume eP) (n,s)) th))
            val eQ2eP = disch eQ (simple_exists (n,s) (dimp_mp_r2l th (existsE (assume eQ) (n,s))))
        in
            dimpI eP2eQ eQ2eP
        end
      | _ => raise ERR ("conclusion of theorem is not an iff"  ^ " " ^ string_of_form C)



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

val all_false_ob = forall_false ("A",ob)
val all_false_ar = forall_false ("a",ar(mk_ob "A",mk_ob "B"))


val exists_true_ob = exists_true ("A",ob)
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
  
fun disj_imp_distr_th (th as thm(G,C)) = 
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

(*need rename for existential case...

say we have (?b. P(b)) ==> A(b)*)

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

val nT_equiv_F = 
    let val nT2F = disch (mk_neg TRUE) (negE (trueI []) (assume (mk_neg TRUE)))
        val F2nT = disch FALSE (falseE (mk_neg TRUE))
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
                                                 (add_assum (mk_neg f) (falseE f))))
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

fun specl th l = 
    if is_all (concl th) then 
        (case l of [] => th
                 | h :: t => 
                   let val f1 = allE th h handle ERR _ => th
                   in 
                       specl f1 t
                   end)
    else th (*raise ERR "conclusion not universally quantified"*)



fun spec_all th = 
    let val fv = fvfl (ant th)
        val v2bs = snd (strip_all (concl th))
        val v2bs' = List.map (pvariantt fv) (List.map Var v2bs)
    in 
        specl th (rev v2bs')
    end

fun abstl th l = 
    case l of 
        [] => th
      | (n,s) :: t => allI (n,s) (abstl th t)


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


end
