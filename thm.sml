structure thm :> thm = 
struct
open token pterm_dtype form pterm term

datatype thm = thm of ((string * sort) set * form list * form) 

fun ant (thm(_,A,_)) = A

fun concl (thm(_,_,C)) = C 

fun cont (thm(G,_,_)) = G

fun unionList sl = 
    case sl of 
        [] => essps


fun inst_thm env th = 
    let
        val G0 = HOLset.listItems (cont th)
        val G = List.foldr 
                    HOLset.union
                    essps
                    (List.map (fvt o (inst_term env) o Var) G0)
(*
HOLset.addList(essps,List.map (fvt o (inst_term env) o Var) G0)*)
        val A = List.map (inst_form env) (ant th)
        val C = inst_form env (concl th)
    in
        thm(G,A,C)
    end

fun ril i l = 
    case l of [] => []
            | h :: t => 
              if h = i then t else h :: (ril i t)

fun asm_U (A1:form list) (A2:form list) = 
    op_union (fn f1 => fn f2 => eq_form (f1,f2)) A1 A2

fun asml_U (asml:(form list) list) = 
    case asml of 
        [] => []
      | h :: t => h @ asml_U t

fun contl_U contl = 
    case contl of 
        [] => HOLset.empty (pair_compare String.compare sort_compare)
      | h :: t => HOLset.union(h,contl_U t)

(*primitive inference rules*)

(*
fun inst (thm(G,A,C)) (env:menv) = 
    thm(fvf (inst_fVare env C),List.map (inst_fVare env) A,inst_fVare env C)
*)

fun assume f = thm (fvf f,[f],f)

fun conjI (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    thm (contl_U [G1,G2],asml_U [A1,A2],Conn ("&",[C1,C2]))
   
fun conjE1 (thm(G,A,C)) = 
    let 
        val (C1,_) = dest_conj C
    in 
        thm (G,A,C1)
    end

fun conjE2 (thm(G,A,C)) = 
    let 
        val (_,C2) = dest_conj C
    in 
        thm (G,A,C2)
    end

fun disjI1 (thm (G,A,C)) f = thm (G,A,Conn ("|",[C,f]))

fun disjI2 f (thm (G,A,C)) = thm (G,A,Conn ("|",[f,C]))

fun disjE A B C (thm (G1,A1,AorB)) (thm (G2,A2,C1)) (thm (G3,A3,C2)) = 
    let 
        val _ = (AorB = Conn("|",[A,B])) orelse 
                raise ERR "theorem #1 unexpected"
        val _ = (C1 = C) orelse 
                raise ERR "theorem #2 unexpected"
        val _ = (C2 = C) orelse 
                raise ERR "theorem #3 unexpected"
        val _ = mem A A2 orelse
                raise ERR "first disjunct not in theorem #2"
        val _ = mem B A3 orelse
                raise ERR "first disjunct not in theorem #3"
    in
        thm (contl_U [G1,G2,G3], asml_U [ril A A2, ril B A3, A1],C)
    end

fun is_eq th = 
    case (concl th) of
        Pred("=",[t1,t2]) => true
      | _ => false

fun thml_eq_pairs (th:thm,(ll,rl,asml)) = 
    if is_eq th then  
        let 
            val (l,r) = dest_eq (concl th)
            val asm = ant th
        in 
            (l::ll,r::rl,asml_U [asm,asml])
        end
    else 
        raise ERR "input theorem is not an equality" 

fun EQ_fsym f s thml = 
    let 
        val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
    in 
        thm (contl_U (List.map cont thml),asml,
             Pred("=",[Fun(f,s,ll),Fun(f,s,rl)]))
    end

fun EQ_psym p thml = 
    let 
        val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
    in 
        thm (contl_U (List.map cont thml),asml,
             Conn("<=>",[Pred(p,ll),Pred(p,rl)]))
    end

fun tautI f = thm(fvf f,[],Conn("|",[f,mk_neg f]))

fun negI (thm (G,A,C)) f = 
    let 
        val _ = (C = FALSE) orelse 
                raise ERR "conclusion is not FALSE"
        val _ = mem f A orelse
                raise ERR "formula to be negated not in assumption"
    in
        thm (G,ril f A, (Conn("~",[f])))
    end

fun negE (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let 
        val _ = (C2 = Conn("~",[C1])) orelse 
                raise ERR "not a pair of contradiction"
    in
        thm (contl_U [G1,G2],asml_U [A1,A2],FALSE)
    end

fun falseE fl f = 
    let val _ = mem FALSE fl orelse 
                raise ERR "FALSE is not in the list"
    in
        thm(fvfl fl,[FALSE],f)
    end

fun trueI A = thm (fvfl A,A,TRUE)

fun dimpI (thm (G1,A1,I1)) (thm (G2,A2,I2)) =
    let 
        val (f1,f2) = dest_imp I1
        val (f3,f4) = dest_imp I2
        val _ = (f1 = f4 andalso f2 = f3) orelse
                raise ERR "no match"
    in
        thm (contl_U[G1,G2],asml_U[A1,A2],Conn("<=>",[f1,f2]))
    end

fun dimpE (thm(G,A,C)) = 
    let
        val (f1,f2) = dest_dimp C
    in
        thm(G,A,Conn("&", 
             [Conn("==>",[f1,f2]),Conn("==>",[f2,f1])]))
    end

(*A ⊆ Γ by induction, so I think no need to check a notin A*)

fun allI (a,s) (thm(G,A,C)) = 
    let (*val _ = HOLset.member(G,(a,s)) orelse 
                raise ERR "variable to be abstract is not currently in the context" *)
        val G0 = HOLset.delete(G,(a,s)) 
                 handle _ => G
        val _ = HOLset.isSubset(fvs s,G0) orelse 
                raise ERR "sort of the variable to be abstract has extra variable(s)"
        val _ = HOLset.isSubset(fvfl A,G0) orelse
                raise ERR "variable to be abstract occurs in assumption"
    in thm(G0,A,mk_all a s C)
    end

fun dest_all f = 
    case f of 
        Quant("ALL",n,s,b) => ((n,s),b)
      | _ => raise ERR "not a universal"

(*--------------------------------------------
allE:

A,Γ |- !x:s. ϕ(s)
-----------------  sort of t is s
A,Γ ∪ (Var(t)) |- ϕ(t)

----------------------------------------------*)

fun allE (thm(G,A,C)) t = 
    let 
        val ((_,s),b) = dest_all C
        val _ = (sort_of t = s) orelse 
                raise ERR ("sort inconsistant"
                           ^ (string_of_sort (sort_of t)) ^ " " ^ 
                           string_of_sort s)
    in
        thm(contl_U [G,fvt t],A,subst_bound t b)
    end

(*by induction, already  have Var(s), Var(t) is subset of G*)

fun existsI (thm(G,A,C)) (a,s) t f = 
    let 
        val _ = (sort_of t = s) orelse 
                raise ERR "term and variable to be abstract of different sorts"
        val _ = (C = substf ((a,s),t) f) orelse
                raise ERR ("formula has the wrong form" ^ string_of_form C)
    in
        thm(G,A,Quant("EXISTS",a,s,abstract (a,s) f))
    end

fun dest_exists f = 
    case f of 
        Quant("EXISTS",n,s,b) => ((n,s),b)
      | _ => raise ERR "not an existential"

(*--------------------------------------------------
existsE:

X, Γ1 |- ?x. ϕ(x)        Y, ϕ(a),Γ2 ∪ {a:s0} |- B
----------------------------------------- a not in Y and not in B
X,Y, Γ1 ∪ Γ2 |- B

---------------------------------------------------*)

fun existsE (a,s0) (thm(G1,A1,C1)) (thm(G2,A2,C2)) =
    let 
        val ((n,s),b) = dest_exists C1
        val _ = mem (subst_bound (Var(a,s0)) b) A2
        val _ = (s = s0) orelse 
                raise ERR "the given variable has unexpected sort"
        val _ = (HOLset.member
                     (HOLset.union(fvfl A2,fvf C2),(a,s0)) = false) orelse
                raise ERR "the given variable occurs unexpectedly"
    in
        thm(contl_U[G1,HOLset.delete(G2,(a,s0))],asml_U[A1,A2],C2)
    end

fun refl t = thm (fvt t,[],(Pred("=",[t,t]))) 

fun sym th = 
    if is_eqn (concl th) then 
        let 
            val (l,r) = dest_eq (concl th)
        in thm(cont th,ant th,Pred("=",[r,l]))
        end
    else raise ERR ("not an equality" ^ string_of_form (concl th))

fun trans th1 th2 = 
    let 
        val _ = is_eqn (concl th1) orelse 
                raise ERR "first theorem not an equality"
        val _ = is_eqn (concl th2) orelse
                raise ERR "second thoerem not an equality"
        val (t1,t2) = dest_eq ((fst o strip_all) (concl th1))
        val (t3,t4) = dest_eq ((fst o strip_all) (concl th2))
        val _ = (t2 = t3) orelse
                raise ERR ("equalities do not match" ^ 
                           (string_of_form (concl th1)) ^ " " ^ 
                           string_of_form (concl th2))
    in 
        thm(contl_U[cont th1,cont th2],
            asml_U[ant th1,ant th2],Pred("=",[t1,t4]))
    end


(*---------------------------------------------------------------------------*
 * DISCH                                                                     *
 *                                                                           *
 *    A ,f1 ,Γ |- f2                                                         *
 *  -----------------                                                        *
 *   A,Γ |- f1 ==> f2                                                 *
 *---------------------------------------------------------------------------*)

fun disch f1 (thm(G,A,f2)) =
    let 
        val _ = HOLset.isSubset(fvf f1,G) orelse
                raise ERR "formula to be disch has extra variable(s)"
    in
        thm (G,ril f1 A,Conn ("==>",[f1,f2]))
    end


fun mp (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let
        val (A,B) = dest_imp C1
        val _ = eq_form(C2,A) orelse 
                raise ERR 
                      ("no match" ^ (string_of_form C1) ^ " " ^ 
                       string_of_form C2)
    in
        thm (contl_U [G1,G2],asml_U[A1,A2],B) 
    end


(*---------------------------------------------------------------------------*
 * ADD_CONT                                                                  *
 *                                                                           *
 *    A ,Γ |- B                                                       *
 *  -----------------                                                        *
 *   A ,Γ ∪ Γ'|- B                                             *
 *---------------------------------------------------------------------------*)

fun add_cont th nss = thm(HOLset.union(cont th,nss),ant th,concl th)




fun all_distinct l = 
    case l of [] => true
            | h :: ts => if List.exists (fn t => t = h) ts then false
                         else true

fun ukn_psym p = Binarymap.peek (!fpdict,p) = NONE

fun no_ukn_psym f = HOLset.isEmpty (HOLset.filter ukn_psym (psymsf f))

fun ctn_ukn_psym f = (no_ukn_psym f = false)

fun ukn_fsym f = Binarymap.peek (!fpdict,f) = NONE

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
    in thm(essps,[],f)
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
    in thm(essps,[],f)
    end

(*definition database*)

(*ETCS axioms*)

fun read_thm thstr = 
    let
        val f = readf thstr
        val _ = HOLset.equal(fvf f,essps) orelse
                raise ERR "formula has free variables"
    in
        thm(essps,[],f)
    end

val idL = read_thm "ALL B. ALL A. ALL f:B -> A. id (A) o f = f"

val idR = read_thm "ALL A. ALL B. ALL f: A -> B. f o id(A) = f"

val o_assoc = read_thm "ALL A. ALL B. ALL C. ALL D. ALL f: A -> B. ALL g:B -> C. ALL h: C -> D.(h o g) o f = h o g o f"

val ax1_1 = read_thm "ALL X. ALL tx: X -> 1. tx = to1(X)"

val ax1_2 = read_thm "ALL X. ALL ix: 0 -> X. ix = from0(X)"

val ax1_3 = read_thm "ALL A. ALL B. ALL X. ALL fg: X -> A * B. ALL f: X -> A. ALL g: X -> B. p1(A,B) o fg = f & p2(A,B) o fg = g <=> fg = pa(f,g)"

(*
read_f 
"ALL A. ALL B. ALL X. ALL fg: X -> A * B. p1(A,B) o fg = f & p2(A,B) o fg = g <=> fg = pa(f,g)"


readf 
"ALL A.ALL fg: X -> A * B. p1(A,B) o fg = f"

read_f 
"ALL A.ALL fg: X -> A * B. p1(A,B) o fg = f"

just fixed

*)

val ax1_4 = read_thm "ALL A. ALL B. ALL X. ALL fg: A + B -> X. ALL f: A -> X. ALL g. fg o i1(A,B) = f & fg o i2(A,B) = g <=> fg = copa(f,g)"

val ax1_5 = read_thm "ALL A. ALL B. ALL f:A -> B. ALL g:A -> B. ALL X. ALL x0: X -> eqo(f,g).ALL h: X -> A. g o eqa(f,g) = f o eqa(f,g) & (f o h = g o h ==> (eqa(f,g) o x0 = h <=> x0 = eqinduce(f,g,h)))"

val ax1_6 = read_thm "ALL A. ALL B. ALL f: A -> B. ALL g: A -> B. ALL X. ALL x0:coeqo(f,g) -> X. ALL h: B -> X. coeqa(f,g) o f = coeqa(f,g) o g & (h o f = h o g ==> (x0 o coeqa(f,g) = h <=> x0 = coeqinduce(f,g,h)))"

val ax2 = read_thm "ALL A. ALL B. ALL X. ALL f: A * X -> B.ALL h: X -> exp(A,B). ev(A,B) o pa(p1(A,X), h o p2(A,X)) = f <=> h = tp(f)"

val ax3 = read_thm "ALL X. ALL x0: 1 -> X. ALL x: N -> X. ALL t: X -> X. x o z = x0 & x o s = t o x <=> x = Nind(x0,t)"

val ax4 = read_thm "ALL A. ALL B.ALL f: A -> B. ALL g:A ->B.~(f = g) ==> EXISTS a: 1 -> A. ~(f o a = g o a)"

val ax5 = read_thm "ALL A. ALL a: 1 -> A. ALL B. ALL f: A -> B. EXISTS g : B -> A. f o g o f = f"

val psyms0 = insert_psym "ismono";
 
val ismono_def = define_pred (readf "ALL A. ALL B. ALL  f: A -> B. ismono(f) <=> ALL X.ALL g:X -> A. ALL h. f o g = f o h ==> h = g")

val psyms0 = insert_psym "areiso";

val areiso_def = define_pred (readf "ALL A. ALL B. areiso(A,B) <=> EXISTS f: A -> B. EXISTS g: B -> A. f o g = id(B) & g o f = id(A)") 

val ax6 = read_thm "ALL X. ~ areiso(X,0) ==> EXISTS x: 1 -> X. T"

val psyms0 = insert_psym "issubset";

val issubset_def = define_pred (readf "ALL X. ALL A. ALL a: X -> A. issubset(a,A) <=> ismono(a)")

val psyms0 = insert_psym "ismem"

val ismem_def = define_pred (readf "ALL A. ALL A0. ALL a:A0 -> A. ALL x:1 -> A. ismem(x,a,A) <=> issubset(a,A) & EXISTS x0:1 -> A0. a o x0 = x")

val ax7 = read_thm "ALL A. ALL B. ALL f: 1 -> A + B. ismem(f,i1(A,B),A + B) | ismem(f,i2(A,B),A + B)"

val ax8 = read_thm "EXISTS X. EXISTS x1: 1 -> X. EXISTS x2: 1 -> X. ~ x1 = x2"

end
