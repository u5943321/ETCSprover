structure thm :> thm = 
struct
open token pterm_dtype form pterm term

datatype thm = thm of form list * form 


(*destructor functions*)

fun ant (thm(G,C)) = G

fun concl (thm(G,C)) = C

fun ril i l = 
    case l of [] => []
            | h :: t => 
              if h = i then t else h :: (ril i t)

val assum_U = op_union (fn f1 => fn f2 => eq_form (f1,f2))

(*primitive inference rules*)

fun inst1 (thm(G,C)) (fm,f0) = thm(List.map (inst_fVar (fm,f0)) G,inst_fVar (fm,f0) C)

fun inst (thm(G,C)) (env:menv) = thm(List.map (inst_fVare env) G,inst_fVare env C)

fun assume f = thm ([f],f)

fun conjI (thm (G1,C1)) (thm (G2,C2)) = thm ((op_union (fn f1 => fn f2 => eq_form (f1,f2)) G1 G2),Conn ("&",[C1,C2]))

fun conjE1 (thm(G,C)) = 
    case C of 
        Conn("&",[C1,C2]) => thm (G,C1)
               | _ => raise ERR ("not a conjunction" ^ " " ^ string_of_form C)

fun conjE2 (thm(G,C)) = 
    case C of 
        Conn("&",[C1,C2]) => thm (G,C2)
               | _ => raise ERR ("not a conjunction" ^ " " ^ string_of_form C)


fun disjI1 (thm (G,C)) f = thm (G,Conn ("|",[C,f]))

fun disjI2 f (thm (G,C)) = thm (G,Conn ("|",[f,C]))

fun disjE A B C (thm (G1,AorB)) (thm (G2,C1)) (thm (G3,C2)) = 
    if AorB = (Conn("|",[A,B])) andalso C1 = C andalso C2 = C 
       andalso mem A G2 andalso mem B G3 then 
        (thm (assum_U (ril A G2) (assum_U (ril B G3) G1),C))
    else raise ERR ("not sufficient for elimination"
              ^ " " ^ (string_of_form AorB) ^ " , " ^ string_of_form C1 ^
              " " ^ (string_of_form C2))

fun EQ_fsym f s thml = 
    let fun is_eq (thm(G,C),(ll,rl,assuml)) = 
            case C of Pred("=",[t1,t2]) => 
                      (t1::ll,t2::rl,op_union (fn f1 => fn f2 => eq_form (f1,f2)) G assuml)
                    | _ => raise ERR ("not an equality" 
                           ^ " " ^ (string_of_form C))
        val (ll,rl,assuml) = List.foldr is_eq ([],[],[]) thml 
    in 
        thm(assuml,Pred("=",[Fun(f,s,ll),Fun(f,s,rl)]))
    end

fun EQ_psym p thml = 
    let fun is_eq (thm(G,C),(ll,rl,assuml)) = 
            case C of Pred("=",[t1,t2]) => 
                      (t1::ll,t2::rl,op_union (fn f1 => fn f2 => eq_form (f1,f2)) G assuml)
                    | _ => raise ERR ("not an equality" ^ " " ^ string_of_form C)
        val (ll,rl,assuml) = List.foldr is_eq ([],[],[]) thml 
    in 
        thm(assuml,Conn("<=>",[Pred(p,ll),Pred(p,rl)]))
    end

fun tautI f = thm([],Conn("|",[f,mk_neg f]))

fun negI (thm (G,C)) f = 
    if C = FALSE andalso mem f G then 
        (thm (ril f G, (Conn("~",[f]))))
    else raise ERR ("conclusion is not a FALSE" ^ " " ^ string_of_form C)

fun negE (thm (G1,A1)) (thm (G2,A2)) = 
    if A2 = (Conn("~",[A1])) orelse A1 = (Conn("~",[A2]))
    then (thm (assum_U G1 G2,FALSE))
    else raise ERR ("not a contradiction" 
         ^ " " ^ (string_of_form A1)  ^ " , " ^ string_of_form A2)

(*should I have the orelse in above?*)

fun falseE f = thm([FALSE],f)

fun trueI G = thm (G,TRUE)

fun dimpI (thm (G1,I1)) (thm (G2,I2)) = 
    case (I1,I2) of 
        (Conn("==>",[f1,f2]),Conn("==>",[f3,f4])) =>
        if f1 = f4 andalso f2 = f3 
        then (thm (assum_U G1 G2,Conn("<=>",[f1,f2])))
        else raise ERR ("implications are not inverse of each other"
              ^ " " ^ (string_of_form I1) ^ " , " ^ string_of_form I2)
      | _ => raise ERR ("not a pair of implications"
              ^ " " ^ (string_of_form I1) ^ " , " ^ string_of_form I2)

fun dimpE (thm(G,A)) = 
    case A of
        Conn("<=>",[f1,f2]) => 
        thm(G,Conn("&", 
             [Conn("==>",[f1,f2]),Conn("==>",[f2,f1])]))
      | _ => raise ERR ("not an iff" ^ " " ^ string_of_form A)

fun allI (n,s) (thm(G,C)) = 
    if HOLset.member (fvfl G,(n,s))
    then raise ERR ("term occurs free on assumption" ^
         " " ^ string_of_term (Var(n,s)))
    else thm(G,Quant("ALL",n,s,abstract (n,s) C))

fun allE (thm(G,C)) t = 
    case C of
        (Quant("ALL",n,s,b)) => 
        if sort_of t = s then thm(G,subst_bound t b)
        else raise ERR ("sort inconsistant"
             ^ (string_of_sort (sort_of t)) ^ " " ^ string_of_sort s)
      | _ => raise ERR ("not an ALL" ^ string_of_form C)

fun existsI (thm(G,C)) (n,s) t f = 
    if C = substf ((n,s),t) f then 
        thm(G,Quant("EXISTS",n,s,abstract (n,s) f))
    else raise ERR ("formula has the wrong form" ^ string_of_form C)

fun simple_exists (v as (n,s)) th = existsI th v (Var v) (concl th) 

fun existsE (thm(G,C)) (n,s) = 
    case C of 
        Quant("EXISTS",n1,s1,b) => 
        if HOLset.member(fvfl G,(n,s)) then raise ERR "term occurs free in assumption"
        else if s = s1 
        then thm(G,subst_bound (Var (n,s)) b)
        else raise ERR ("inconsist sorts" ^ (string_of_sort s) ^ " " ^ string_of_sort s1)
      | _ => raise ERR ("not an EXISTS"  ^ string_of_form C) 

(*refl, sym, trans of equalities*)

fun refl t = thm ([],(Pred("=",[t,t]))) 

fun sym th = 
    if is_eqn (concl th)
    then let val (l,r) = dest_eq (concl th)
         in thm(ant th,Pred("=",[r,l]))
         end
    else raise ERR ("not an equality" ^ string_of_form (concl th))

fun trans th1 th2 = 
    if is_eqn (concl th1) andalso is_eqn (concl th2)
    then let val (t1,t2) = dest_eq (strip_all (concl th1))
             val (t3,t4) = dest_eq (strip_all (concl th2))
         in 
             (if t2 = t3 then 
                  thm(assum_U (ant th1) (ant th2),Pred("=",[t1,t4]))
              else raise ERR ("equalities do not  match" ^ 
                   (string_of_form (concl th1)) ^ " " ^ string_of_form (concl th2)))
         end
    else raise ERR ("not an equality" ^ 
         (string_of_form (concl th1)) ^ " " ^ string_of_form (concl th2))

(*derived rules*)

fun disch f1 (thm(G,f2)) = thm (ril f1 G,Conn ("==>",[f1,f2]))

fun mp (thm (G1,f1)) (thm (G2,f2)) = 
    case f1 of 
        Conn ("==>",[A,B]) =>
        if eq_form(f2,A) then (thm (assum_U G1 G2,B)) 
        else raise ERR ("no match" ^ (string_of_form f1) ^ " " ^ string_of_form f2)
      | _ => raise ERR ("no match" ^ (string_of_form f1) ^ " " ^ string_of_form f2)

fun undisch th = mp th (assume (#1(dest_imp (concl th))))

fun add_assum f th = mp (disch f th) (assume f)

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
    let val (A1,A2) = dest_iff C1
        val (B1,B2) = dest_iff C2
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
    let val (A1,A2) = dest_iff C1
        val (B1,B2) = dest_iff C2
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
    let val (A1,A2) = dest_iff C1
        val (B1,B2) = dest_iff C2
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
    let val (A1,A2) = dest_iff C
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
    let val fnf = Conn("&",[f,mk_neg f])
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

(*ETCS axioms*)

val idL = thm([], #1 (read_f "ALL f. id (A) o f = f"))

val idR = thm([], #1 (read_f "ALL f. f o id(A) = f"))

val o_assoc = thm([], #1 (read_f "(f o g) o h = f o g o h"))

val ax1_1 = thm([],#1 (read_f "ALL X. ALL tx. tx = to1(X)"))

val ax1_2 = thm([],#1 (read_f "ALL X. ALL ix. ix = from0(X)"))

val ax1_3 = thm([],#1 (read_f "ALL fg. p1(A,B) o fg = f &  p2(A,B) o fg = g <=> fg = pa(f,g)"))


val ax1_4 = thm([],#1 (read_f "ALL fg. fg o i1(A,B) = f & fg o i2(A,B) = g <=> fg = copa(f,g)"))

val ax1_5 = thm([],#1 (read_f "g o eqa(f,g) = f o eqa(f,g) & (f o h = g o h ==> (eqa(f,g) o x0 = h <=> x0 = eqinduce(f,g,h)))"))


val ax1_6 = thm([],#1 (read_f "coeqa(f,g) o f = coeqa(f,g) o g & (h o f = h o g ==> (x0 o coeqa(f,g) = h <=> x0 = coeqinduce(f,g,h)))"))


val ax2 = thm([],#1 (read_f "ev(A,B) o pa(p1(A,X), h o p2(A,X)) = f <=> h = tp(f)"))

val ax3 = thm([],#1 (read_f "x o z = x0 & x o s = t o x <=> x = Nind(x0,t)"))

val ax4 = thm([], #1 (read_f "~(f = g) ==> EXISTS a: 1 -> A. ~(f o a = g o a)")) 

val ax5 = thm([],#1 (read_f "ALL f: A -> B. ALL a: 1 -> A. EXISTS g : B -> A. f o g o f = f"))


end
