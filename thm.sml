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
       andalso mem A G1 andalso mem B G2 then 
        (thm (assum_U (ril A G1) (assum_U (ril B G2) G3),C))
    else raise ERR "not sufficient for elimination"


(*fun imp_conj *)

fun mk_neg f = Conn("~",[f])

fun tautI f = thm([],Conn("|",[f,mk_neg f]))

fun cases_on c (fl,f) =
    ([(c::fl,f),((mk_neg c)::fl,f)], 
     fn [th1,th2] => disjE c (mk_neg c) (concl th1) (tautI c) th1 th2
     | _ => raise ERR "incorrect length of list") 



fun negI (thm (G,C)) f = 
    if C = FALSE andalso mem f G then 
        (thm (ril f G, (Conn("~",[f]))))
    else raise ERR "conclusion is not a FALSE"

fun negE (thm (G1,A1)) (thm (G2,A2)) = 
    if A2 = (Conn("~",[A1])) orelse A1 = (Conn("~",[A2]))
    then (thm (assum_U G1 G2,FALSE))
    else raise ERR "not a contradiction"

fun disch f1 (thm(G,f2)) = thm (ril f1 G,Conn ("==>",[f1,f2]))

fun mp (thm (G1,f1)) (thm (G2,f2)) = 
    case f1 of 
        Conn ("==>",[A,B]) => if f2 = A then (thm (assum_U G1 G2,B)) else raise ERR "no match" 
      | _ => raise ERR "no match" 




(*
fun strip_all_from_thm (thm(G,C)) = 
    let val fvs = fvfl G
        val  



fun irule th (fl,f) = 
*)

(*derived rules*)

fun undisch th = mp th (assume (#1(dest_imp (concl th))))

fun add_assum f th = mp (disch f th) (assume f)

fun imp_trans th1 th2 = 
    let val (ant,cl) = dest_imp (concl th1)
    in disch ant (mp th2 (mp th1 (assume ant)))
    end

fun prove_hyp th1 th2 = mp (disch (concl th1) th2) th1

(* have a \/ b iff ~a ==> b as a derived rule? not in manual.*)

fun falseE f = thm([FALSE],f)

fun truthI G = thm (G,TRUE)

fun dimpI (thm (G1,A1)) (thm (G2,A2)) = 
    if mem A1 G2 andalso mem A2 G1 then 
        (thm(assum_U G1 G2, Conn("<=>",[A1,A2])))
    else raise ERR "not sufficient for an iff"

(*modify above?*)

fun dimpE1 (thm (G,A)) B = 
    if mem (Conn("<=>",[A,B])) G then (thm (G,B))
    else raise ERR "not an iff (1)" 


fun dimpE2 (thm (G,A)) B = 
    if mem (Conn("<=>",[B,A])) G then (thm (G,B))
    else raise ERR "not an iff (2)" 


fun allI (n,s) (thm(G,C)) = 
    if mem (n,s) (fvfl G) then raise ERR "term occurs free on assumption"
    else thm(G,Quant("ALL",n,s,abstract (n,s) C))


fun allE (thm(G,C)) t = 
    case C of
        (Quant("ALL",n,s,b)) => 
        if sort_of t = s then thm(G,subst_bound t b)
        else raise ERR "sort inconsistant"
      | _ => raise ERR "not an ALL"


fun specl th l = 
    if is_all (concl th) then 
        (case l of [] => th
                 | h :: t => allE (specl th t) h)
    else raise ERR "conclusion not universally quantified"



fun spec_all th = 
    let val fv = fvfl (ant th)
        val v2bs = snd (strip_ALL (concl th))
        val v2bs' = List.map (pvariantt fv) (List.map Var v2bs)
    in 
        specl th (rev v2bs')
    end

(*find the sort of a variable with name n in a name-sort list*)

fun find_sort n nsl = 
    case nsl of [] => raise ERR "not found"
              | (n0,s) :: t => if n = n0 then s else find_sort n t


fun abstl th l = 
    case l of 
        [] => th
      | n :: t => 
        (let val fv = fvf (concl th)
             val s = find_sort n fv
         in
             allI (n,s) (abstl th t)
         end)


fun existsE (thm(G,C)) (n,s) = 
    case C of 
        Quant("EXISTS",n1,s1,b) => 
        if mem (n,s) (fvfl G) then raise ERR "term occurs free in assumption"
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

fun dict2l dict = Binarymap.foldl (fn (k:string,v:term,A) => (k,v) :: A) [] dict



fun part_tmatch partfn A t = 
    let val env = dict2l (match_term0 (partfn A) t (Binarymap.mkDict String.compare))
        val A' = abstl A (List.map (fn (a,b) => a) env)
    in specl A' (List.map (fn (a,b) => b) env)
    end

val rewr_conv = part_tmatch (snd o dest_eq o concl o spec_all)


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

val ax1_3 = thm([],#1 (read_f "ALL fg. fg o p1(A,B) = f & fg o p2(A,B) = g <=> fg = pa(f,g)"))


val ax1_4 = thm([],#1 (read_f "ALL fg. i1(A,B) o fg = f & i2(A,B) o fg = g <=> fg = copa(f,g)"))

val ax1_5 = thm([],#1 (read_f "eqa(f,g) o g = eqa(f,g) o f & (h o f = h o g ==> (x0 o eqa(f,g) = h <=> x0 = eqinduce(f,g,h)))"))


val ax1_6 = thm([],#1 (read_f "f o coeqa(f,g)= g o coeqa(f,g) & (f o h = g o h ==> (coeqa(f,g) o x0 = h <=> x0 = coeqinduce(f,g,h)))"))


val ax2 = thm([],#1 (read_f "pa(p1(A,X), p2(A,X) o h) o ev(A,B) = f <=> h = tp(f)"))

val ax3 = thm([],#1 (read_f "z o x = x0 & s o x = x o t <=> x = Nind(x0,t)"))

val ax4 = thm([], #1 (read_f "~(f = g) ==> EXISTS a: 1 -> A. ~(a o f = a o g)")) 

val ax5 = thm([],#1 (read_f "ALL f: A -> B. ALL a: 1 -> A. EXISTS g : B -> A. f o g o f = f"))


end
