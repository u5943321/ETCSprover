structure thm :> thm = 
struct
open token pterm_dtype form pterm term

datatype thm = thm of form list * form 



fun ant (thm(G,C)) = G

fun concl (thm(G,C)) = C

fun ril i l = 
    case l of [] => []
            | h :: t => 
              if h = i then t else h :: (ril i t)

val assum_U = op_union (fn f1 => fn f2 => eq_form (f1,f2))

fun assume f = thm ([f],f)

fun conjI (thm (G1,C1)) (thm (G2,C2)) = thm ((op_union (fn f1 => fn f2 => eq_form (f1,f2)) G1 G2),Conn ("&",[C1,C2]))


fun disjI1 (thm (G,C)) f = thm (G,Conn ("|",[C,f]))

fun disjI2 f (thm (G,C)) = thm (G,Conn ("|",[f,C]))


fun refl t = thm ([],(Pred("=",[t,t]))) 


fun EQ_fsym f s thml = 
    let fun is_eq (thm(G,C),(ll,rl,assuml)) = 
            case C of Pred("=",[t1,t2]) => (t1::ll,t2::rl,op_union (fn f1 => fn f2 => eq_form (f1,f2)) G assuml)
                    | _ => raise ERR "not an equality" 
        val (ll,rl,assuml) = List.foldr is_eq ([],[],[]) thml 
    in 
        thm(assuml,Pred("=",[Fun(f,s,ll),Fun(f,s,rl)]))
    end


fun EQ_psym p thml = 
    let fun is_eq (thm(G,C),(ll,rl,assuml)) = 
            case C of Pred("=",[t1,t2]) => (t1::ll,t2::rl,op_union (fn f1 => fn f2 => eq_form (f1,f2)) G assuml)
                    | _ => raise ERR "not an equality" 
        val (ll,rl,assuml) = List.foldr is_eq ([],[],[]) thml 
    in 
        thm(assuml,Conn("<=>",[Pred(p,ll),Pred(p,rl)]))
    end

 

fun conjE1 (thm (G1,Conn("&",[C1,C2]))) = thm (G1,C1)
  | conjE1 _ = raise ERR "not a conjunction"

fun conjE2 (thm (G1,Conn("&",[C1,C2]))) = thm (G1,C2)
  | conjE2 _ = raise ERR "not a conjunction"

fun disjE A B C (thm (G1,AorB)) (thm (G2,C1)) (thm (G3,C2)) = 
    if AorB = (Conn("|",[A,B])) andalso C1 = C andalso C2 = C 
       andalso mem A G2 andalso mem B G3 then 
        (thm (assum_U (ril A G2) (assum_U (ril B G3) G1),C))
    else raise ERR "not sufficient for elimination"



(*fun imp_conj *)


fun tautI f = thm([],Conn("|",[f,mk_neg f]))

fun negI (thm (G,C)) f = 
    if C = FALSE andalso mem f G then 
        (thm (ril f G, (Conn("~",[f]))))
    else raise ERR "conclusion is not a FALSE"


(*should I have the orelse?*)

fun negE (thm (G1,A1)) (thm (G2,A2)) = 
    if A2 = (Conn("~",[A1])) orelse A1 = (Conn("~",[A2]))
    then (thm (assum_U G1 G2,FALSE))
    else raise ERR "not a contradiction"


(*
fun conj_subst1 (thm(G1,pq)) (thm(G2,pp')) = 
    let val p2p' = dimpl2r (thm(G,pp'))
    in trans (cj_imp1 pq) p2p'

fun conj_subst (thm(G1,pq)) (thm(G2,pp')) (thm(G3,qq' = 
    let val p2p' = 
    dimpI 
        (disch pq (conjI (imp_trans ) 
                         ()))
*)
(* have a \/ b iff ~a ==> b as a derived rule? not in manual.*)

fun falseE f = thm([FALSE],f)

fun trueI G = thm (G,TRUE)
(*
fun dimpI (thm (G1,A1)) (thm (G2,A2)) = 
    if mem A1 G2 andalso mem A2 G1 then 
        (thm(assum_U G1 G2, Conn("<=>",[A1,A2])))
    else raise ERR "not sufficient for an iff"

*)
fun dimpI (thm (G1,I1)) (thm (G2,I2)) = 
    case (I1,I2) of 
        (Conn("==>",[f1,f2]),Conn("==>",[f3,f4])) =>
        if f1 = f4 andalso f2 = f3 
        then (thm (assum_U G1 G2,Conn("<=>",[f1,f2])))
        else raise ERR "implications are not inverse of each other"
      | _ => raise ERR "not a pair of implications"

(*modify above?*)

fun dimpE (thm(G,A)) = 
    case A of
        Conn("<=>",[f1,f2]) => 
        thm(G,Conn("&", 
             [Conn("==>",[f1,f2]),Conn("==>",[f2,f1])]))
      | _ => raise ERR "not an iff"

fun dimpE1 (thm (G,A)) B = 
    if mem (Conn("<=>",[A,B])) G then (thm (G,B))
    else raise ERR "not an iff (1)" 


fun dimpE2 (thm (G,A)) B = 
    if mem (Conn("<=>",[B,A])) G then (thm (G,B))
    else raise ERR "not an iff (2)" 


fun allI (n,s) (thm(G,C)) = 
    if HOLset.member (fvfl G,(n,s)) then raise ERR "term occurs free on assumption"
    else thm(G,Quant("ALL",n,s,abstract (n,s) C))


fun allE (thm(G,C)) t = 
    case C of
        (Quant("ALL",n,s,b)) => 
        if sort_of t = s then thm(G,subst_bound t b)
        else raise ERR "sort inconsistant"
      | _ => raise ERR "not an ALL"


fun existsE (thm(G,C)) (n,s) = 
    case C of 
        Quant("EXISTS",n1,s1,b) => 
        if HOLset.member(fvfl G,(n,s)) then raise ERR "term occurs free in assumption"
        else if s = s1 
        then thm(G,subst_bound (Var (n,s)) b)
        else raise ERR "inconsist sorts"
      | _ => raise ERR "not an EXISTS"

fun existsI (thm(G,C)) (n,s) t f = 
    if C = substf ((n,s),t) f then 
        thm(G,Quant("EXISTS",n,s,abstract (n,s) f))
    else raise ERR "formula has the wrong form"

fun simple_exists (v as (n,s)) th = existsI th v (Var v) (concl th) 




(*do we need is_eq, is_forall etc or case (_,_) of (Pred =, ...)*)
fun trans th1 th2 = 
    if is_eqn (concl th1) andalso is_eqn (concl th2)
    then let val (t1,t2) = dest_eq (strip_all (concl th1))
             val (t3,t4) = dest_eq (strip_all (concl th2))
         in 
             (if t2 = t3 then 
                  thm(assum_U (ant th1) (ant th2),Pred("=",[t1,t4]))
              else raise ERR "equalities do not  match")
         end
    else raise ERR "not an equality"


fun sym th = 
    if is_eqn (concl th)
    then let val (l,r) = dest_eq (concl th)
         in thm(ant th,Pred("=",[r,l]))
         end
    else raise ERR "not an equality"


(*derived rules*)

fun disch f1 (thm(G,f2)) = thm (ril f1 G,Conn ("==>",[f1,f2]))

fun mp (thm (G1,f1)) (thm (G2,f2)) = 
    case f1 of 
        Conn ("==>",[A,B]) => if f2 = A then (thm (assum_U G1 G2,B)) else raise ERR "no match" 
      | _ => raise ERR "no match" 




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


fun negI (thm (G,C)) f = 
    if C = FALSE andalso mem f G then 
        (thm (ril f G, (Conn("~",[f]))))
    else raise ERR "conclusion is not a FALSE"


(*should I have the orelse?*)

fun negE (thm (G1,A1)) (thm (G2,A2)) = 
    if A2 = (Conn("~",[A1])) orelse A1 = (Conn("~",[A2]))
    then (thm (assum_U G1 G2,FALSE))
    else raise ERR "not a contradiction"

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

val all_true_ar = all_true ("a",ar(Var("A",ob),Var("B",ob)))
val all_true_ob = all_true ("A",ob)

fun all_false (n,s) = dimpI (disch (Quant("ALL",n,s,FALSE)) 
                                   (allE (assume (Quant("ALL",n,s,FALSE))) (Var (n,s))))
                            (disch FALSE (allI (n,s) (assume FALSE)))

val all_false_ar = all_false ("a",ar(Var("A",ob),Var("B",ob)))
val all_false_ob = all_false ("A",ob)




fun iff_trans (thm(G1,C1)) (thm(G2,C2)) =
    case (C1,C2) of 
        (Conn("<=>",[f1,f2]), Conn("<=>",[f3,f4])) => 
        if f2 = f3 then 
            let val f1f2 = conjE1 (dimpE (thm(G1,C1)))
                val f2f1 = conjE2 (dimpE (thm(G1,C1)))
                val f2f4 = conjE1 (dimpE (thm(G2,C2)))
                val f4f2 = conjE2 (dimpE (thm(G2,C2)))
                val f1f4 = imp_trans f1f2 f2f4
                val f4f1 = imp_trans f4f2 f2f1
            in dimpI f1f4 f4f1
            end
        else raise ERR "two iffs do not match"
      | _ => raise ERR "not a pair of iffs"


(*
fun thl_from_th th = 
    let val th1 = spec_all th
    in case (concl th1) of 
           Conn("&",[f1,f2]) => 
           (thl_from_th thm(ant th1,f1)) @
           (thl_from_th thm(ant th1,f2))
         | Conn("~",[f]) => [iffF_intro th1]
         | _ => [th1]
    end
*)

(*
(*for rewr_conv*)

fun is_eq (thm(G,C)) = 
    case C of
        Pred("=",[A,B]) => true
     | Quant("ALL",n,s,b) => is_eq (thm(G,b))
     | _ => false




fun inst_sort t1 t2 (thm(G,C)) = 
    if (sort_of t1,sort_of t2) = (ob,ob) then
        case C of
            Quant("ALL",n,ar(d,c),b) =>
            thm(G,Quant("ALL",n,ar(t1,t2),
                        subst_bound (Var(n,ar(t1,t2))) b))
          | _ => raise ERR "nothing to be inst"
    else raise ERR "can only inst objects"


fun inst env th =
    case th of (thm(G,C)) =>
               thm(List.map (inst_form env) G, inst_form env C)


(*this one will definitely be too simple *)
fun rewr_conv_t th t = 
    let val (lhs,rhs) = dest_eq (strip_all (concl th))
        val env = match_term0 lhs t (Binarymap.mkDict String.compare)
    in thm(ant th, Pred("=",[t,inst_term env rhs]))
    end

fun rewr_conv_tl thl t = 
    case thl of
        [] => refl t
      | h :: thl0 =>
        rewr_conv_t h (#2 (dest_eq (concl (rewr_conv_tl thl0 t))))
        handle _ => rewr_conv_tl thl0 t 



fun find_match_subst th f = 
    let val (lhs,rhs) = dest_eq (strip_all (concl th))
    in case f of 
           Pred(P,tl) => Pred(P,List.map 
                                    (fn tm =>
                                        inst_term (match_term0 lhs tm
                                        (Binarymap.mkDict String.compare)) rhs
                                        handle _ => tm) tl)
         | Conn(co,fl) => Conn(co,List.map (find_match_subst th) fl)
         | Quant(q,n,s,b) => Quant(q,n,s,find_match_subst th b)
    end


fun find_match_substl thl f = 
    case thl of [] => f 
              | h :: t => 
                let val f1 = find_match_subst h f
                in find_match_substl t f1
                end
                handle _ => find_match_substl t f


fun rewr_conv_f th f = 
    let val (lhs,rhs) = dest_iff (strip_all (concl th))
        val env = match_form lhs f (Binarymap.mkDict String.compare)
    in thm(ant th,Conn("<=>",[f,inst_form env rhs]))
    end



fun iffF_intro th = 
    case (concl th) of 
        Conn("~",[f]) => thm(ant th,Conn("<=>",[f,FALSE]))
      | _ => raise ERR "not a negation"

fun flip f = 
    case f of Pred("=",[t1,t2]) => Pred("=",[t2,t1])
            | _ => raise ERR "not an equality"

fun gsym th = thm(ant th, flip (concl th))

fun is_all f =
    case f of 
        Quant("ALL",_,_,_) => true
      | _ => false

fun specl l f = 
    case l of 
        [] => f
      | h :: t => 
        (case f of 
             Quant("ALL",n,s,b) => 
             subst_bound h (specl t b)
           | _ => f)

fun strip_ALL f = 
    let fun strip_all0 f = 
            case f of 
                Quant("ALL",n,s,b) => 
                let val (b1,l) = strip_all0 (subst_bound (Var(n,s)) b) in
                    (b1,(n,s) :: l) end
              | _ => (f,[])
    in strip_all0 f
    end


fun pvariant vl v = 
    if mem v vl then 
        case v of 
            Var(n,ob) => Var(n ^ "'",ob)
         | Var(n,ar(t1,t2)) => Var(n ^ "'", ar(pvariant vl t1,pvariant vl t2))
         | _ => v
    else v 

fun varyAcc v (V,l) = 
    let val v' = pvariant V v in (v':: V,v'::l)
    end

*)
(*

fun spec_all th = 
    if is_all (concl th) then 
        let val fv = fvfl (ant th) 
            val c = concl th
            val fv1 = fvf c 
            val vars = List.map Var (snd (strip_ALL c))
        in thm(ant th,specl (snd (itlist varyAcc vars (List.map Var (fv @ fv1),[]))) c)
        end
    else th

*)
(*spec all ,specl, spec cannot find def of spec*)

(*need a function split a theorem into a theorem list*)


(*
fun thl_from_th th = 
    let val th1 = spec_all (concl th)
        val c = concl th1
    in case c of 
           Conn("&",[f1,f2]) => 
           (thl_from_th thm(ant th1,f1)) @
           (thl_from_th thm(ant th1,f2))
         | Conn("~",[f]) => [iffF_intro th1]
         | _ => [th1]
    end
*)


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
