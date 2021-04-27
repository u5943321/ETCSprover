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


(*change to eq_form in some proper way?*)
fun existsI (thm(G,C)) (n,s) t f = 
    if C = substf ((n,s),t) f then 
        thm(G,Quant("EXISTS",n,s,abstract (n,s) f))
    else raise ERR ("formula has the wrong form" ^ string_of_form C)



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
    then let val (t1,t2) = dest_eq ((fst o strip_all) (concl th1))
             val (t3,t4) = dest_eq ((fst o strip_all) (concl th2))
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





fun all_distinct l = 
    case l of [] => true
            | h :: ts => if List.exists (fn t => t = h) ts then false
                         else true



fun ukn_psym p = lookup_pred psyms0 p = NONE


fun no_ukn_psym f = HOLset.isEmpty (HOLset.filter ukn_psym (psymsf f))

fun ctn_ukn_psym f = (no_ukn_psym f = false)


fun ukn_fsym p = lookup_fun fsyms0 p = NONE


fun no_ukn_fsym f = HOLset.isEmpty (HOLset.filter ukn_fsym (fsymsf f))

fun ctn_ukn_fsym f = (no_ukn_fsym f = false)


fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise ERR "formula has unexpected free variables"
        val (body,bvs) = strip_all f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_pred l 
        val _ = List.all is_var args orelse raise ERR "input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise ERR "unexpected free variable on RHS"
        val _ = (lookup_pred psyms0 P = NONE) orelse raise ERR ("redefining predicate: " ^ P)
        val _ = all_distinct args orelse raise ERR "input arguments are not all distinct"
        val _ = no_ukn_psym r orelse raise ERR "RHS contains unknown predicate"
        val _ = no_ukn_fsym r orelse raise ERR "RHS contains unknown function"
        (*check P is a fresh name if not then fail*)
        (*check RHS variables are subset of LHS ones*)
        (*check arguments are all distinct*)
        (*store P in psymd*)
        val psymd0 = new_pred P (List.map dest_var args)
    in thm([],f)
    end
(*check that R does not contain any unknown predicate symbols/fun syms*)


fun define_fun f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise ERR "formula has unexpected free variables"
        val (body,bvs) = strip_all f 
        val (l,r) = dest_eq body 
        val (nf,sf,args) = dest_fun l 
        val _ = List.all is_var args orelse raise ERR "input arguments is not a variable list"
        val _ = HOLset.isSubset (fvt r,fvt l) 
                orelse raise ERR "unexpected free variable on RHS"
        val _ = (lookup_fun fsyms0 nf = NONE) orelse raise ERR ("redefining predicate: " ^ nf)
        val _ = all_distinct args orelse raise ERR "input arguments are not all distinct"
        val fsymd0 = new_fun nf (sf,(List.map dest_var args))
    in thm([],f)
    end



(*definition database*)

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


 
val ismono_def = define_pred (readf "ALL A. ALL B. ALL  f: A -> B. ismono(f) <=> ALL X.ALL g:X -> A. ALL h. f o g = f o h ==> h = g")

(*val isiso_def = define_pred (readf "") *)


end
