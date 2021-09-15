(*
fun all_distinct l = 
    case l of [] => true
            | h :: ts => if List.exists (fn t => eq_term(t,h)) ts then false
                         else true

fun no_ukn_psym f = HOLset.isEmpty (HOLset.filter (not o is_pred) (psymsf f))

fun no_ukn_fsym f = HOLset.isEmpty (HOLset.filter (not o is_fun) (fsymsf f))

fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_pred l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = case lookup_pred (psyms0) P of NONE => () | _ => raise simple_fail("redefining predicate: " ^ P)
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val _ = no_ukn_psym r orelse raise simple_fail"RHS contains unknown predicate"
        val _ = no_ukn_fsym r orelse raise simple_fail"RHS contains unknown function"
        (*check P is a fresh name if not then fail*)
        (*check RHS variables are subset of LHS ones*)
        (*check arguments are all distinct*)
        (*store P in psymd*)
        val _ = new_pred P (List.map dest_var args)
    in mk_thm essps [] f
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
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_eq body 
        val (nf,sf,args) = dest_fun l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvt r,fvt l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = case lookup_fun fsyms0 nf of NONE => () | _ => raise simple_fail("redefining predicate: " ^ nf)
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val fsyms0 = new_fun nf (sf,(List.map dest_var args))
    in mk_thm essps [] f
    end
*)

(*definition database*)

(*ETCS axioms*)

fun check_wffv fvs = 
    case fvs of 
        [] => true
      | h :: t => if ill_formed_fv h then
                      raise ERR ("ill-formed free variable",[snd h],[var h],[])
                  else check_wffv t

fun rapf' str = 
    let val f = rapf str 
        val fvs = HOLset.listItems (fvf f)
        val _ = check_wffv fvs 
    in f
    end

fun read_axiom thstr = 
    let
        val f = rapf' thstr
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm essps [] f
    end

val idL = read_axiom "!B A f:B -> A. id (A) o f = f"

val idR = read_axiom "!A B f: A -> B. f o id(A) = f"

val o_assoc = read_axiom "!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f";


val to1_def = read_axiom "!one.is1(one) ==> !X.!t1x:X->one.t1x =to1(X,one)";

val const1_def = read_axiom "is1(1)";

val ax1_1 = const1_def |> existsI ("one",mk_ob_sort) one (rapf "is1(one)")
 
val from0_def = read_axiom "!zero.is0(zero) ==> !X.!f0x:zero->X.f0x=from0(zero,X)"

val const0_def = read_axiom "is0(0)";

val ax1_2 = const0_def |> existsI ("zero",mk_ob_sort) zero (rapf "is0(zero)")


val pr_def = read_axiom "!A.!B.!AB.!p1:AB->A.!p2:AB->B.ispr(p1,p2)<=>!X.!f:X->A.!g:X->B.?fg:X->AB.!fg':X->AB.p1 o fg' = f & p2 o fg' = g <=> fg' = fg";

val pa_def = read_axiom "!A.!B.!AB.!p1:AB->A.!p2:AB->B.ispr(p1,p2)==>!X.!f:X->A.!g:X->B.!fg:X->AB.p1 o fg = f & p2 o fg = g <=> fg = pa(p1,p2,f,g)";

val pr_ex = read_axiom "!A.!B.?AB.?p1:AB->A.?p2:AB->B.ispr(p1,p2)";

val ax1_3 = pr_ex 

val copa_def = read_axiom "!A.!B.!AB.!i1:A->AB.!i2:B->AB.iscopr(i1,i2)==>!X.!f:A->X.!g:B->X.!fg:AB->X.fg o i1 = f & fg o i2 = g <=> fg = copa(i1,i2,f,g)"

val copr_ex = read_axiom "!A.!B.?AB.?i1:A->AB.?i2:B->AB.iscopr(i1,i2)";

val ax1_4 = copr_ex

val eqind_def = read_axiom "!A.!B.!f:A->B.!g:A->B.!E.!e:E->A.iseq(e,f,g)==> f o e = g o e & !X.!x:X->A.f o x = g o x ==> (!x0:X->E.e o x0 = x <=> x0 = eqind(e,f,g,x))"

val eq_ex = read_axiom "!A.!B.!f:A->B.!g:A->B.?E.?e:E->A.iseq(e,f,g)";

val ax1_5 = eq_ex

val coeqind_def = read_axiom "!A.!B.!f:A->B.!g:A->B.!cE.!ce:B->cE.iscoeq(ce,f,g)==> ce o f = ce o g & !X.!x:B->X. x o f = x o g ==> (!x0:cE->X.x0 o ce = x <=> x0 = coeqind(ce,f,g,x))"

val coeq_ex = read_axiom "!A.!B.!f:A->B.!g:A->B.?cE.?ce:B->cE.iscoeq(ce,f,g)"

val ax1_6 = coeq_ex

val tp_def = read_axiom "!A.!B.!A2B.!efs.!p1:efs ->A.!p2:efs ->A2B.!ev:efs->B.isexp(p1,p2,ev)==> ispr(p1,p2) & !X.!AX.!p1':AX->A.!p2':AX->X. ispr(p1',p2') ==> !f:AX->B.!h:X->A2B. ev o pa(p1,p2,p1',h o p2') = f <=> h = tp(p1,p2,ev,p1',p2',f)"

val exp_ex = read_axiom "!A.!B.?A2B efs p1:efs ->A p2:efs ->A2B ev:efs->B.isexp(p1,p2,ev)"

val ax2 = exp_ex

val Nind0_def = read_axiom "!N0 one z0:one -> N0 s0:N0->N0. isN0(z0,s0) ==> is1(one) & !X x0:one -> X t:X -> X x:N0 -> X. x o z0 = x0 & x o s0 = t o x <=> x = Nind0(z0,s0,x0,t)";


val constN_def = read_axiom "!X x0:1->X t:X ->X x:N->X.(x o z = x0 & x o s = t o x) <=> x = Nind(x0,t)"

(*to be edited, switch the ordrr of s0 and z0*)
val ax3 = constN_def

val ax_wp = read_axiom "!A B f: A -> B g:A ->B.(~(f = g)) ==> ?a: 1 -> A. ~(f o a = g o a)";

val ax4 = ax_wp


val ismono_def = read_axiom "!A B f: A -> B. ismono(f) <=> !X g:X -> A h. f o g = f o h ==> h = g"

val ax_el = read_axiom "!X.(~is0(X)) ==> ?x:1->X.T";

val ax6 = ax_el

val ac = read_axiom "!A one a: one -> A B f: A -> B. is1(one) ==> ?g : B -> A. f o g o f = f"

val ax5 = ac

val ismem_def = read_axiom "!A x:1-> A A0 a:A0 -> A. ismem(x,a) <=> ismono(a) & ?x0:1 -> A0. a o x0 = x";

new_pred "ismem0" ([("x",mk_ar_sort (mk_ob "one") (mk_ob "A")),("a",mk_ar_sort (mk_ob "A0") (mk_ob "A"))]);

val ismem0_def = read_axiom "!A one x:one-> A A0 a:A0 -> A. ismem0(x,a) <=> is1(one) & ismono(a) & ?x0:one -> A0. a o x0 = x";

val ax_incfac0 = read_axiom "!A B AB i1:A->AB i2:B->AB one f:one -> AB. iscopr(i1,i2) & is1(one) ==> ismem0(f,i1)| ismem0(f,i2)";

val ax7 = ax_incfac0 

val ax_2el = read_axiom "?X x1: 1 -> X x2: 1 -> X. ~ (x1 = x2)"


val ax8 = ax_2el


val _ = new_fun "*" (mk_ar_sort (mk_ob "X") (mk_ob "two"),[("i1",mk_ar_sort one (mk_ob "two")),("i2",mk_ar_sort one (mk_ob "two")),("a",mk_ar_sort (mk_ob "A") (mk_ob "X"))])

val prsym_def = ex2fsym "*" ["A","B"] (iffRL $ eqT_intro $ spec_all pr_ex)
                        |> C mp (trueI []) |> gen_all

val p1_def = ex2fsym "p1" ["A","B"] (iffRL $ eqT_intro $ spec_all prsym_def)
                        |> C mp (trueI []) |> gen_all

val p2_def = ex2fsym "p2" ["A","B"] (iffRL $ eqT_intro $ spec_all p1_def)
                        |> C mp (trueI []) |> gen_all


val coprsym_def = ex2fsym "+" ["A","B"] (iffRL $ eqT_intro $ spec_all copr_ex)
                        |> C mp (trueI []) |> gen_all

val i1_def = ex2fsym "i1" ["A","B"] (iffRL $ eqT_intro $ spec_all prsym_def)
                        |> C mp (trueI []) |> gen_all

val i2_def = ex2fsym "i2" ["A","B"] (iffRL $ eqT_intro $ spec_all p1_def)
                        |> C mp (trueI []) |> gen_all

val expsym_def = ex2fsym "^" ["A","B"] (iffRL $ eqT_intro $ spec_all exp_ex)
                        |> C mp (trueI []) |> gen_all



fun po A B = mk_fun "*" [A,B]

val _ = new_fun "p1" (ar_sort (po (mk_ob "A") (mk_ob "B")) (mk_ob "A"),[("A",ob_sort),("B",ob_sort)])

val _ = new_fun "p2" (ar_sort (po (mk_ob "A") (mk_ob "B")) (mk_ob "B"),[("A",ob_sort),("B",ob_sort)])


val _ = new_fun "+" (ob_sort,[("A",ob_sort),("B",ob_sort)])

fun copo A B = mk_fun "+" [A,B]

val _ = new_fun "i1" (ar_sort (mk_ob "A") (copo (mk_ob "A") (mk_ob "B")),[("A",ob_sort),("B",ob_sort)])

val _ = new_fun "i2" (ar_sort (mk_ob "B") (copo (mk_ob "A") (mk_ob "B")),[("A",ob_sort),("B",ob_sort)])


val _ = new_fun "exp" (ob_sort,[("A",ob_sort),("B",ob_sort)])

fun exp A B = mk_fun "exp" [A,B]

val _ = new_fun "ev" (ar_sort (po (mk_ob "A") (exp (mk_ob "A") (mk_ob "B"))) (mk_ob "B"),[("A",ob_sort),("B",ob_sort)])




val prod_def = new_ax “!A B. ispr(p1(A,B),p2(A,B))” 

val exp_def = mk_ax 
“!A B.isexp(p1(A,exp(A,B)),p2(A,exp(A,B)),ev(A,B))”


(*
fun all_distinct l = 
    case l of [] => true
            | h :: ts => if List.exists (fn t => eq_term(t,h)) ts then false
                         else true

fun no_ukn_psym f = HOLset.isEmpty (HOLset.filter (not o is_pred) (psymsf f))

fun no_ukn_fsym f = HOLset.isEmpty (HOLset.filter (not o is_fun) (fsymsf f))

fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_pred l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = case lookup_pred (psyms0) P of NONE => () | _ => raise simple_fail("redefining predicate: " ^ P)
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val _ = no_ukn_psym r orelse raise simple_fail"RHS contains unknown predicate"
        val _ = no_ukn_fsym r orelse raise simple_fail"RHS contains unknown function"
        (*check P is a fresh name if not then fail*)
        (*check RHS variables are subset of LHS ones*)
        (*check arguments are all distinct*)
        (*store P in psymd*)
        val _ = new_pred P (List.map dest_var args)
    in mk_thm essps [] f
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
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_eq body 
        val (nf,sf,args) = dest_fun l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvt r,fvt l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = case lookup_fun fsyms0 nf of NONE => () | _ => raise simple_fail("redefining predicate: " ^ nf)
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val fsyms0 = new_fun nf (sf,(List.map dest_var args))
    in mk_thm essps [] f
    end
*)
