
fun all_distinct l = 
    case l of [] => true
            | h :: ts => if List.exists (fn t => eq_term(t,h)) ts then false
                         else true

fun ukn_psym p = Binarymap.peek (!fpdict,p) = NONE

fun no_ukn_psym f = HOLset.isEmpty (HOLset.filter ukn_psym (psymsf f))

fun ctn_ukn_psym f = (no_ukn_psym f = false)

fun ukn_fsym f = Binarymap.peek (!fpdict,f) = NONE

fun no_ukn_fsym f = HOLset.isEmpty (HOLset.filter ukn_fsym (fsymsf f))

fun ctn_ukn_fsym f = not $ no_ukn_fsym f 

fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_pred l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = case lookup_pred (!psyms) P of NONE => () | _ => raise simple_fail("redefining predicate: " ^ P)
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

(*definition database*)

(*ETCS axioms*)

fun read_axiom thstr = 
    let
        val f = rapf thstr
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm essps [] f
    end

val idL = read_axiom "!B A f:B -> A. id (A) o f = f"

val idR = read_axiom "!A B f: A -> B. f o id(A) = f"

val o_assoc = read_axiom "!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f"

val psyms0 = insert_psym "istml";

val istml_def = define_pred (rapf "!one.istml(one) <=> !X.!t1x:X->one.t1x =to1(one,X)")


(*
val idL = read_axiom "!B A f:B -> A. id(A) o f = f"

val idR = read_axiom "!A B f: A -> B. f o id(A) = f"

val o_assoc = read_axiom "!A B f: A -> B C g:B -> C D h: C -> D.(h o g) o f = h o g o f"

val ax1_1 = read_axiom "!X tx:X->1. tx = to1(X)"

val ax1_2 = read_axiom "!X ix:0->X. ix = from0(X)"

val ax1_3 = read_axiom "!A B X fg: X -> (A * B) f: X -> A g: X -> B. p1(A,B) o fg = f & p2(A,B) o fg = g <=> fg = pa(f,g)"

val ax1_4 = read_axiom "!A B X fg: (A + B) -> X f: A -> X g. fg o i1(A,B) = f & fg o i2(A,B) = g <=> fg = copa(f,g)"

val ax1_5 = read_axiom "!A B f:A -> B g:A -> B. g o eqa(f,g) = f o eqa(f,g) &!X h: X -> A.(f o h = g o h ==> !x0: X -> eqo(f,g).(eqa(f,g) o x0 = h <=> x0 = eqinduce(f,g,h)))" 

val ax1_6 = read_axiom "!A B f: A -> B g: A -> B. coeqa(f,g) o f = coeqa(f,g) o g & !X h: B -> X. (h o f = h o g ==> !x0:coeqo(f,g) -> X.(x0 o coeqa(f,g) = h <=> x0 = coeqinduce(f,g,h)))"

 
val ax2 = read_axiom "!A B X f: (A * X) -> B h: X -> exp(A,B). ev(A,B) o pa(p1(A,X), h o p2(A,X)) = f <=> h = tp(f)"

val ax_exp = ax2

val ax3 = read_axiom "!X x0: 1 -> X x: N -> X t: X -> X. x o z = x0 & x o s = t o x <=> x = Nind(x0,t)"

val ax_N = ax3

val ax4 = read_axiom "!A B f: A -> B g:A ->B.~(f = g) ==> ?a: 1 -> A. ~(f o a = g o a)"

val ax_wp = ax4

val ax5 = read_axiom "!A a: 1 -> A B f: A -> B.?g : B -> A. f o g o f = f"

val ax_c = ax5

val psyms0 = insert_psym "ismono";
 
val ismono_def = define_pred (rapf "!A B f: A -> B. ismono(f) <=> !X g:X -> A h. f o g = f o h ==> h = g")

(*TODO: debug the define_pred*)

val psyms0 = insert_psym "areiso";

val areiso_def = define_pred (rapf "!A B. areiso(A,B) <=> ?f: A -> B g: B -> A. f o g = id(B) & g o f = id(A)") 

val ax6 = read_axiom "!X. (~ areiso(X,0)) ==> ?x: 1 -> X. T"

val ax_elt = ax6

val psyms0 = insert_psym "issubset";

val issubset_def = define_pred (rapf "!X A a: X -> A. issubset(a,A) <=> ismono(a)")


(*maybe not need such issubset at all*)


val psyms0 = insert_psym "ismem"

val ismem_def = define_pred (rapf "!A A0 a:A0 -> A x:1 -> A. ismem(x,a,A) <=> issubset(a,A) & ?x0:1 -> A0. a o x0 = x")


(*TODO: wrong err message, should be "redefine ismem" not "issubset"*)

val ax7 = read_axiom "!A B f: 1 -> (A + B). ismem(f,i1(A,B),A + B) | ismem(f,i2(A,B),A + B)"



val ax_mcp = ax7

val ax8 = read_axiom "?X x1: 1 -> X x2: 1 -> X. ~ x1 = x2"

val ax_delt = ax8
*)
