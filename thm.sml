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
      | _ => raise simple_fail "incorrect length of list"

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
    else raise simple_fail "bad environment"

(*fun subst_thm *)

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

fun disjI1 f (thm (G,A,C)) = thm (G,A,Conn ("|",[C,f]))

fun disjI2 f (thm (G,A,C)) = thm (G,A,Conn ("|",[f,C]))

(*TODO: replace disjE with the simpler version*)

fun disjE A B C (thm (G1,A1,AorB)) (thm (G2,A2,C1)) (thm (G3,A3,C2)) = 
    let 
        val _ = eq_form(AorB, mk_disj A B) orelse 
                raise ERR ("disjE.theorem #1 is not the desired disjunction: ",
                           [],[],[mk_disj A B,AorB])
        val _ = eq_form(C1,C) orelse 
                raise ERR ("disjE.theorem #2 unexpected: ",
                           [],[],[C1,C])
        val _ = eq_form(C2,C) orelse 
                raise ERR ("disjE.theorem #3 unexpected: ",
                           [],[],[C2,C])
        val _ = fmem A A2 orelse
                raise ERR ("disjE.first disjunct not in the formula list: ",
                           [],[],[A])
        val _ = fmem B A3 orelse
                raise ERR ("disjE.second disjunct not in the formula list: ",
                           [],[],[B])
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
        raise ERR ("thml_eq_pairs.input thm is not an equality: ",
                   [],[],[concl th])

(*avoid EQ_psym/fsym using by hand*)


fun EQ_fsym f thml = 
    case lookup_fun fsyms0 f of 
        NONE => raise simple_fail ("function: " ^ f ^ " is not found")
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

fun negI f (thm (G,A,C)) = 
    let 
        val _ = (C = FALSE) orelse 
                raise ERR ("negI.concl of thm is not FALSE",
                          [],[],[C])
        val _ = fmem f A orelse
                raise ERR ("negI.formula to be negated not in the asl",
                           [],[],[f])
    in
        thm (G,ril f A, (Conn("~",[f])))
    end

fun negE (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let 
        val _ = eq_form(C2,Conn("~",[C1])) orelse 
                raise ERR ("negE.not a pair of contradiction",
                           [],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U [A1,A2],FALSE)
    end

fun falseE fl f = 
    let val _ = fmem FALSE fl orelse 
                raise simple_fail "falseE.FALSE is not in the asl"
    in
        thm(fvfl (f::fl),fl,f)
    end

        
fun trueI A = thm (fvfl A,A,TRUE)

fun dimpI (thm (G1,A1,I1)) (thm (G2,A2,I2)) =
    let 
        val (f1,f2) = dest_imp I1
        val (f3,f4) = dest_imp I2
        val _ = eq_form(f1,f4) andalso eq_form(f2,f3) orelse
                raise ERR ("dimpI.no match",
                           [],[],[I1,I2])
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
                raise simple_fail "sort of the variable to be abstract has extra variable(s)"
        val _ = not (HOLset.member(fvfl A,(a,s))) orelse
                raise simple_fail "variable to be abstract occurs in assumption" 
    in thm(G0,A,mk_all a s C)
    end



(*--------------------------------------------
allE:

A,Γ |- !x:s. ϕ(s)
-----------------  sort of t is s
A,Γ ∪ (Var(t)) |- ϕ(t)

----------------------------------------------*)

fun allE t (thm(G,A,C)) = 
    let 
        val ((n,s),b) = dest_all C
        val _ = (sort_of t = s) orelse 
                raise ERR ("allE.sorts inconsistent",
                           [s,sort_of t],[Var(n,s),t],[])
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
                raise simple_fail"term and variable to be abstract of different sorts"
        val _ = eq_form (C, substf ((a,s),t) f) orelse
                raise ERR ("existsI.formula has the wrong form, should be something else: ",
                           [],[],[C,substf ((a,s),t) f])
    in
        thm(G,A,Quant("?",a,s,abstract (a,s) f))
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
                raise ERR ("the given variable has unexpected sort, should have another sort",[s,s0],[],[])
        val _ = (HOLset.member
                     (HOLset.union
                          (fvfl (ril (subst_bound (Var(a,s0)) b) A2),
                           fvf C2),(a,s0)) = false) orelse
                raise simple_fail "the given variable occurs unexpectedly"
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
    else raise ERR ("sym.not an equality: ",[],[],[concl th])

fun trans th1 th2 = 
    let 
        val _ = is_eqn (concl th1) orelse 
                raise ERR ("trans.first thm not an equality: ",[],[],[concl th1])
        val _ = is_eqn (concl th2) orelse
                raise ERR ("trans.second thm not an equality: ",[],[],[concl th2])
        val (t1,t2) = dest_eq ((fst o strip_all) (concl th1))
        val (t3,t4) = dest_eq ((fst o strip_all) (concl th2))
        val _ = (t2 = t3) orelse
                raise ERR ("trans.equalities do not match",[],[],[concl th1,concl th2])
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
                raise simple_fail"formula to be disch has extra variable(s)"
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
                raise ERR ("mp.no match",[],[],[C1,C2])
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

fun add_cont nss th = thm(HOLset.union(cont th,nss),ant th,concl th)

(*
       
fun EQ_psym p thml = 
    let 
        val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
    in 
        thm (contl_U (List.map cont thml),asml,
             Conn("<=>",[Pred(p,ll),Pred(p,rl)]))
    end


fun subst_ct_t t nt tm = 
    case tm of
        Var(n,s) => if tm = t then nt else Var(n,)

fun subst_sort eq (d,c)

fun rsm s e e' = HOLset.add(HOLset.delete(s,e),e')

fun eq_ar_ct v eqth th = 
    if HOLset.member(cont th,v) then 
        let val (n,s) = dest_var v 
            val (d,c) = dest_ar s
            val (t,t') = (dest_eq o concl) eqth 
        in if d = t then rsm (cont th) v (n,ar(t,d))
*)
(*
fun subst thml tmp t = 
    let 
        val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
    in 
*)


fun substfnt ot nt t = 
    case t of
        Var(n,s) => if t = ot then nt else Var(n,substfns ot nt s)
       |Fun(f,s,l) => if t = ot then nt else 
                      let val ns = substfns ot nt s
                          val nl = List.map (substfnt ot nt) l
                      in Fun(f,ns,nl)
                      end
       |Bound i => t
and substfns ot nt s = 
    case s of 
        ob => s
       |ar(d,c) => ar(substfnt ot nt d,substfnt ot nt c)


fun mk_cont nsl =
    List.foldr (fn (new,set) => HOLset.add(set,new)) essps nsl

fun substfnf ot nt (redex as (n,s)) f0 f =
    if eq_form(f,substf ((n,s),ot) f0) then 
        substf ((n,s),nt) f0 
    else raise ERR ("substfnf.formula to be subst is of the wrong form: ",
                    [],[Var(n,s)],[f0,f])

fun subst_cont eqth th = 
    let val ctl = HOLset.listItems (HOLset.union(cont th,cont eqth))
        val (obs,ars) = partition (fn (n,s) => s = ob) ctl
        val (names,arss) = unzip ars
        val (ot,nt) = dest_eq (concl eqth)
        val arss' = List.map (substfns ot nt) arss
        val nars = zip names arss'
        val ct' = mk_cont (obs @ nars)
    in thm(ct',asml_U [ant eqth,ant th],concl th)
    end


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
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_all f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_pred l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = (lookup_pred (!psyms) P = NONE) orelse raise simple_fail("redefining predicate: " ^ P)
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val _ = no_ukn_psym r orelse raise simple_fail"RHS contains unknown predicate"
        val _ = no_ukn_fsym r orelse raise simple_fail"RHS contains unknown function"
        (*check P is a fresh name if not then fail*)
        (*check RHS variables are subset of LHS ones*)
        (*check arguments are all distinct*)
        (*store P in psymd*)
        val _ = new_pred P (List.map dest_var args)
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
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_all f 
        val (l,r) = dest_eq body 
        val (nf,sf,args) = dest_fun l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvt r,fvt l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = (lookup_fun fsyms0 nf = NONE) orelse raise simple_fail("redefining predicate: " ^ nf)
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val fsyms0 = new_fun nf (sf,(List.map dest_var args))
    in thm(essps,[],f)
    end

(*definition database*)

(*ETCS axioms*)

fun read_thm thstr = 
    let
        val f = readf thstr
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm essps [] f
    end


val idL = read_axiom "!B. !(A) (f:B -> A). id (A) o f = f"

val idR = read_thm rapf "!A.!(B) (f: A -> B). f o id(A) = f"

val o_assoc = read_thm "!A.!B.!C.!D.!f: A -> B.!g:B -> C.!h: C -> D.(h o g) o f = h o g o f"

val o_assoc' = read_thm "!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f"


val psyms0 = insert_psym "istml";

val istml_def = define_pred (readf "!one.istml(one) <=> !X.!t1x:X->one.t1x =to1(one,X)")

val ax1_1 = read_thm "?one.istml(one)"

val ax_tml = ax1_1

val psyms0 = insert_psym "isinl";

val isinl_def = define_pred (readf "!zero.isinl(zero) <=> !X.!f0x:zero ->X.f0x =from0(zero,X)")

val zero_ex = read_thm "?zero.isinl(zero)"

val ax1_2 = zero_ex

(**********************************************************************
Ax1-3, existence of product
**********************************************************************)

val psyms0 = insert_psym "ispr";
val fsyms0 = insert_fsym "pa";
val pr_def = define_pred (readf "!A.!B.!AB.!p1:AB->A.!p2:AB->B.ispr(p1,p2)<=>!X.!f:X->A.!g:X->B.!fg:X->AB.p1 o fg = f & p2 o fg = g <=> fg = pa(p1,p2,f,g)")
(*
val pr_def = define_pred (readf "!A.!B.?AB.ispr (p1(AB,A),p2(AB,B)).
*)

!p1:AB->A.!p2:AB->B.ispr(p1,p2)<=>!X.!f:X->A.!g:X->B.!fg:X->AB.p1 o fg = f & p2 o fg = g <=> fg = pa(p1,p2,f,g)")

val pr_ex = read_thm "!A.!B.?AB.?p1:AB->A.?p2:AB->A.ispr(p1,p2)"
val ax1_3 = pr_ex

(**********************************************************************
Ax1-4, existence of coproduct
**********************************************************************)

val psyms0 = insert_psym "iscopr";
val fsyms0 = insert_fsym "copa";
val pr_def = define_pred (readf "!A.!B.!AB.!i1:A->AB.!i2:B->AB.iscopr(i1,i2)<=>!X.!f:A->X.!g:B->X.!fg:AB->X.fg o i1 = f & fg o i2 = g <=> fg = copa(i1,i2,f,g)")
val copr_ex = read_thm "!A.!B.?AB.?i1:A->AB.?i2:B->AB.iscopr(i1,i2)"
val ax1_4 = copr_ex

(**********************************************************************
Ax1-5, existence of equalizer
**********************************************************************)

val psyms0 = insert_psym "iseq";
val fsyms0 = insert_fsym "eqind";

val eq_def = define_pred (readf "!A.!B.!f:A->B.!g:A->B.!E.!e:E->A.iseq(e,f,g)<=> f o e = g o e & !X.!x:X->A.f o x = g o x ==> (!x0:X->E.e o x0 = x <=> x0 = eqind(e,f,g,x))")
val eq_ex = read_thm "!A.!B.!f:A->B.!g:A->B.?E.?e:E->A.iseq(e,f,g)"
val ax1_5 = eq_ex

(**********************************************************************
Ax1-6, existence of coequalizer
**********************************************************************)

val psyms0 = insert_psym "iscoeq";
val fsyms0 = insert_fsym "coeqind";
val coeq_def = define_pred (readf "!A.!B.!f:A->B.!g:A->B.!cE.!ce:B->cE.iscoeq(ce,f,g)<=> ce o f = ce o g & !X.!x:B->X. x o f = x o g ==> (!x0:cE->X.x0 o ce = x <=> x0 = coeqind(ce,f,g,x))")
val coeq_ex = read_thm "!A.!B.!f:A->B.!g:A->B.?cE.?ce:B->cE.iscoeq(ce,f,g)"
val ax1_6 = coeq_ex

(**********************************************************************
Ax2, existence of exponential
**********************************************************************)

val psyms0 = insert_psym "isexp";
val fsyms0 = insert_fsym "tp";
val fsyms0 = insert_fsym "ev";
val exp_def =
    define_pred 
        (readf 
             "!A.!B.!A2B.!efs.!p1:efs ->A.!p2:efs ->A2B.!ev:efs->B.isexp(p1,p2,ev)<=> ispr(p1,p2) & !AX.!p1':AX->A.!p2':AX->X.!f:AX->B.!h:X->A2B.(ev o (p1',h o p2') = f <=> h = tp(p1,p2,ev,f))")
val coeq_ex = read_thm "!A.!B.!f:A->B.!g:A->B.?cE.?ce:B->cE.iscoeq(ce,f,g)";

val ax1_6 = coeq_ex

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
