structure thm :> thm = 
struct
open token pterm_dtype term form pterm symbols

datatype thm = thm of ((string * sort) set * form list * form) 

fun dest_thm (thm(G,A,C)) = (G,A,C)

fun ant (thm(_,A,_)) = A

fun concl (thm(_,_,C)) = C 

fun cont (thm(G,_,_)) = G

fun eq_forml (l1:form list) (l2:form list) = 
    case (l1,l2) of 
        ([],[]) => true
      | (h1 :: t1, h2 :: t2) => eq_form(h1,h2) andalso eq_forml t1 t2
      | _ => raise ERR "incorrect length of list"

fun fmem f fl = List.exists (curry eq_form f) fl

fun eq_thm th1 th2 = 
    HOLset.equal(cont th1,cont th2) andalso
    eq_forml (ant th1) (ant th2) andalso
    eq_form (concl th1, concl th2)

(*
INST_THM: 
A, Γ |- C
------------- INST_THM env
A', Γ' |- C'

A',C' is obtained by pluging in variables recorded in env
Γ' is obtained by collecting all variables in substituted Γ.

name clash with bound variable is treated by specl:

If we have f = ALL a. Bound 0 o a: A ->B = b

then specl on f will give a' o a: A -> B = b

*)

fun mk_sss l = List.foldr HOLset.union essps l

(*make (string * sort) set*)
(*specl/genl instead of inst_thm*)

(*need to worry about the env makes sense*)
fun inst_thm env th = 
    if is_wfmenv env then
        let
            val G0 = HOLset.listItems (cont th)
            val G = mk_sss (List.map (fvt o (inst_term env) o Var) G0)
            val A = List.map (inst_form env) (ant th)
            val C = inst_form env (concl th)
        in
            thm(G,A,C)
        end
    else raise ERR "bad environment"

fun ril i l = 
    case l of [] => []
            | h :: t => 
              if eq_form(h,i) then t else h :: (ril i t)


fun asml_U (asml:(form list) list) = 
    case asml of 
        [] => []
      | h :: t => op_union (curry eq_form) h (asml_U t)

fun contl_U contl = 
    case contl of 
        [] => HOLset.empty (pair_compare String.compare sort_compare)
      | h :: t => HOLset.union(h,contl_U t)

(*primitive inference rules*)

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
        val _ = fmem A A2 orelse
                raise ERR "first disjunct not in theorem #2"
        val _ = fmem B A3 orelse
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

(*avoid EQ_psym/fsym using by hand*)

fun EQ_fsym f s thml = 
    let 
        val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
    in 
        thm (contl_U (List.map cont thml),asml,
             Pred("=",[Fun(f,s,ll),Fun(f,s,rl)]))
    end



fun EQ_fsym f thml = 
    case lookup_fun fsyms0 f of 
        NONE => raise ERR ("function:" ^ f ^ " is not found")
      | SOME(s,l) => 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val menv0 = match_tl essps (List.map Var l) sl mempty 
            val s' = inst_sort menv0 s
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in
            thm (contl_U (List.map cont thml),asml,
                 Pred("=",[Fun(f,s',ll),Fun(f,s',rl)]))
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
        val _ = fmem f A orelse
                raise ERR "formula to be negated not in assumption"
    in
        thm (G,ril f A, (Conn("~",[f])))
    end

fun negE (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let 
        val _ = eq_form(C2,Conn("~",[C1])) orelse 
                raise ERR "not a pair of contradiction"
    in
        thm (contl_U [G1,G2],asml_U [A1,A2],FALSE)
    end

fun falseE fl f = 
    let val _ = fmem FALSE fl orelse 
                raise ERR "FALSE is not in the list"
    in
        thm(fvfl (f::fl),fl,f)
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
    let 
        val G0 = HOLset.delete(G,(a,s)) 
                 handle _ => G
        val _ = HOLset.isSubset(fvs s,G0) orelse 
                raise ERR "sort of the variable to be abstract has extra variable(s)"
        val _ = not (HOLset.member(fvfl A,(a,s))) orelse
                raise ERR "variable to be abstract occurs in assumption" 
    (*    val _ = HOLset.isSubset(fvfl A,G0) orelse
                raise ERR "variable to be abstract occurs in assumption" *)
    in thm(G0,A,mk_all a s C)
    end



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

(*by induction, already  have Var(s), Var(t) is subset of G? No, say:

EXISTS a:ob. TRUE

A,Γ |- f[t/Var(a,s)]
---------------- sort_of t = s, Var(t) ⊆ Γ
A,Γ |- EXISTS a: s. f
*)

(*----------------------------------------------------------------------
Γ,A |- f[t/(a,s)]
-------------------
Γ,A |- ?a:s. f


----------------------------------------------------------------------*)

fun existsI (thm(G,A,C)) (a,s) t f = 
    let 
        val _ = HOLset.isSubset(fvt t,G)
        val _ = (sort_of t = s) orelse 
                raise ERR "term and variable to be abstract of different sorts"
        val _ = eq_form (C, substf ((a,s),t) f) orelse
                raise ERR ("formula has the wrong form" ^ string_of_form C)
    in
        thm(G,A,Quant("EXISTS",a,s,abstract (a,s) f))
    end


(*--------------------------------------------------
existsE:

X, Γ1 |- ?x. ϕ(x)        Y, ϕ(a),Γ2 ∪ {a:s0} |- B
----------------------------------------- a not in Y and not in B
X,Y, Γ1 ∪ Γ2 |- B

---------------------------------------------------*)

fun delete'(s,e) = HOLset.delete(s,e) handle _ => s 



 
fun existsE (a,s0) (thm(G1,A1,C1)) (thm(G2,A2,C2)) =
    let 
        val ((n,s),b) = dest_exists C1
        val _ = fmem (subst_bound (Var(a,s0)) b) A2
        val _ = (s = s0) orelse 
                raise ERR "the given variable has unexpected sort"
        val _ = (HOLset.member
                     (HOLset.union
                          (fvfl (ril (subst_bound (Var(a,s0)) b) A2),
                           fvf C2),(a,s0)) = false) orelse
                raise ERR "the given variable occurs unexpectedly"
    in
        thm(contl_U[G1,delete'(G2,(a,s0))],
            asml_U[A1,(ril (subst_bound (Var(a,s0)) b) A2)],C2)
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
 *  -----------------                                               *
 *   A,Γ |- f1 ==> f2  

do not require f1 in assumption, if not, add its variables into the context. *
 *---------------------------------------------------------------------------*)
(*
fun disch f1 (thm(G,A,f2)) =
    let 
        val _ = HOLset.isSubset(fvf f1,G) orelse
                raise ERR "formula to be disch has extra variable(s)"
    in
        thm (HOLset.union(G,fvf f1),ril f1 A,Conn ("==>",[f1,f2]))
    end

*)

fun disch f1 (thm(G,A,f2)) =
        thm (HOLset.union(G,fvf f1),ril f1 A,Conn ("==>",[f1,f2]))
 



(*-------------------------------------
MP: 

A1, Γ1 |- A ==> B           A2, Γ2|- A
-------------------------------------
A1 ∪ A2, Γ1 ∪ Γ2 |- B
---------------------------------------*)


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
        val psyms0 = new_pred P (List.map dest_var args)
    in thm(essps,[],f)
    end
(*check that R does not contain any unknown predicate symbols/fun syms*)

(*define fun spec

a rule that turns

!a b c. ?!R. P(a,b,c,R).

into 

ALL a b c. P(a,b,c,f(a,b,c))

and defines f


!a b c. Q(a) ==> ?!R. P(a,b,c,R).

allow this, and put Q(a) in the output thm as well.
*)

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
        val fsyms0 = new_fun nf (sf,(List.map dest_var args))
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

val o_assoc' = read_thm "ALL A. ALL B. ALL f: A -> B. ALL C. ALL g:B -> C. ALL D.ALL h: C -> D.(h o g) o f = h o g o f"

val ax1_1 = read_thm "ALL X. ALL tx: X -> 1. tx = to1(X)"

val ax_tml = ax1_1

val ax1_2 = read_thm "ALL X. ALL ix: 0 -> X. ix = from0(X)"

val ax_inl = ax1_2

val ax1_3 = read_thm "ALL A. ALL B. ALL X. ALL fg: X -> A * B. ALL f: X -> A. ALL g: X -> B.(p1(A,B) o fg = f & p2(A,B) o fg = g) <=> fg = pa(f,g)"

val ax_pr = ax1_3

val ax1_4 = read_thm "ALL A. ALL B. ALL X. ALL fg: A + B -> X. ALL f: A -> X. ALL g. (fg o i1(A,B) = f & fg o i2(A,B) = g) <=> fg = copa(f,g)"

val ax_copr = ax1_4

val ax1_5 = read_thm "ALL A. ALL B. ALL f:A -> B. ALL g:A -> B. ALL X. ALL x0: X -> eqo(f,g).ALL h: X -> A. g o eqa(f,g) = f o eqa(f,g) & (f o h = g o h ==> (eqa(f,g) o x0 = h <=> x0 = eqinduce(f,g,h)))"

val ax_eq = ax1_5

val ax1_5' = read_thm "ALL A. ALL B. ALL f:A -> B. ALL g:A -> B. g o eqa(f,g) = f o eqa(f,g) & ALL X.ALL h: X -> A. (f o h = g o h ==> (ALL x0: X -> eqo(f,g).eqa(f,g) o x0 = h <=> x0 = eqinduce(f,g,h)))"

(*actually stronger than ax1_5*)

val ax_eq' = ax1_5'

val ax1_6 = read_thm "ALL A. ALL B. ALL f: A -> B. ALL g: A -> B. ALL X. ALL x0:coeqo(f,g) -> X. ALL h: B -> X. coeqa(f,g) o f = coeqa(f,g) o g & (h o f = h o g ==> (x0 o coeqa(f,g) = h <=> x0 = coeqinduce(f,g,h)))"

val ax_coeq = ax1_6


val ax1_6' = read_thm "ALL A. ALL B. ALL f: A -> B. ALL g: A -> B. coeqa(f,g) o f = coeqa(f,g) o g & ALL X. ALL h: B -> X. (h o f = h o g ==> (ALL x0:coeqo(f,g) -> X. x0 o coeqa(f,g) = h <=> x0 = coeqinduce(f,g,h)))"

val ax_coeq' = ax1_6'


val ax2 = read_thm "ALL A. ALL B. ALL X. ALL f: A * X -> B.ALL h: X -> exp(A,B). ev(A,B) o pa(p1(A,X), h o p2(A,X)) = f <=> h = tp(f)"

val ax_exp = ax2

val ax3 = read_thm "ALL X. ALL x0: 1 -> X. ALL x: N -> X. ALL t: X -> X. (x o z = x0 & x o s = t o x) <=> x = Nind(x0,t)"

val ax_N = ax3

val ax4 = read_thm "ALL A. ALL B.ALL f: A -> B. ALL g:A ->B.~(f = g) ==> EXISTS a: 1 -> A. ~(f o a = g o a)"

val ax_wp = ax4

val ax5 = read_thm "ALL A. ALL a: 1 -> A. ALL B. ALL f: A -> B. EXISTS g : B -> A. f o g o f = f"

val ax_c = ax5

val psyms0 = insert_psym "ismono";
 
val ismono_def = define_pred (readf "ALL A. ALL B. ALL  f: A -> B. ismono(f) <=> ALL X.ALL g:X -> A. ALL h. f o g = f o h ==> h = g")

(*TODO: debug the define_pred*)

val psyms0 = insert_psym "areiso";

val areiso_def = define_pred (readf "ALL A. ALL B. areiso(A,B) <=> EXISTS f: A -> B. EXISTS g: B -> A. f o g = id(B) & g o f = id(A)") 

val ax6 = read_thm "ALL X. ~ areiso(X,0) ==> EXISTS x: 1 -> X. T"

val ax_elt = ax6

val psyms0 = insert_psym "issubset";

val issubset_def = define_pred (readf "ALL X. ALL A. ALL a: X -> A. issubset(a,A) <=> ismono(a)")

val psyms0 = insert_psym "ismem"

val ismem_def = define_pred (readf "ALL A. ALL A0. ALL a:A0 -> A. ALL x:1 -> A. ismem(x,a,A) <=> issubset(a,A) & EXISTS x0:1 -> A0. a o x0 = x")

val ax7 = read_thm "ALL A. ALL B. ALL f: 1 -> A + B. ismem(f,i1(A,B),A + B) | ismem(f,i2(A,B),A + B)"

val ax_mcp = ax6

val ax8 = read_thm "EXISTS X. EXISTS x1: 1 -> X. EXISTS x2: 1 -> X. ~ x1 = x2"

val ax_delt = ax6

end
