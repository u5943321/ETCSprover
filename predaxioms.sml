
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

val o_assoc = read_axiom "!A.!B.!f: A -> B.!C.!g:B -> C.!D.!h: C -> D.(h o g) o f = h o g o f";

val isone_def = read_axiom "!one.is1(one) <=> !X.!t1x:X->one.t1x =to1(X,one)";

val const1_def = read_axiom "is1(1)";

val ax1_1 = const1_def |> existsI ("one",mk_ob_sort) one (rapf "is1(one)")
 
val iszero_def = read_axiom "!zero.is0(zero) <=> !X.!f0x:zero->X.f0x=from0(zero,X)"

val const0_def = read_axiom "is0(0)";

val ax1_2 = const0_def |> existsI ("zero",mk_ob_sort) zero (rapf "is0(zero)")

val pr_def = read_axiom "!A.!B.!AB.!p1:AB->A.!p2:AB->B.ispr(p1,p2)<=>!X.!f:X->A.!g:X->B.!fg:X->AB.p1 o fg = f & p2 o fg = g <=> fg = pa(p1,p2,f,g)";

val pr_ex = read_axiom "!A.!B.?AB.?p1:AB->A.?p2:AB->A.ispr(p1,p2)";

val ax1_3 = pr_ex 

val copr_def = read_axiom "!A.!B.!AB.!i1:A->AB.!i2:B->AB.iscopr(i1,i2)<=>!X.!f:A->X.!g:B->X.!fg:AB->X.fg o i1 = f & fg o i2 = g <=> fg = copa(i1,i2,f,g)"

val copr_ex = read_axiom "!A.!B.?AB.?i1:A->AB.?i2:B->AB.iscopr(i1,i2)";

val ax1_4 = copr_ex

val eq_def = read_axiom "!A.!B.!f:A->B.!g:A->B.!E.!e:E->A.iseq(e,f,g)<=> f o e = g o e & !X.!x:X->A.f o x = g o x ==> (!x0:X->E.e o x0 = x <=> x0 = eqind(e,f,g,x))"

val eq_ex = read_axiom "!A.!B.!f:A->B.!g:A->B.?E.?e:E->A.iseq(e,f,g)";

val ax1_5 = eq_ex

val coeq_def = read_axiom "!A.!B.!f:A->B.!g:A->B.!cE.!ce:B->cE.iscoeq(ce,f,g)<=> ce o f = ce o g & !X.!x:B->X. x o f = x o g ==> (!x0:cE->X.x0 o ce = x <=> x0 = coeqind(ce,f,g,x))"

val coeq_ex = read_axiom "!A.!B.!f:A->B.!g:A->B.?cE.?ce:B->cE.iscoeq(ce,f,g)"

val ax1_6 = coeq_ex

val exp_def = read_axiom "!A.!B.!A2B.!efs.!p1:efs ->A.!p2:efs ->A2B.!ev:efs->B.isexp(p1,p2,ev)<=> ispr(p1,p2) & !X.!AX.!p1':AX->A.!p2':AX->X. ispr(p1',p2') ==> !f:AX->B.!h:X->A2B. ev o pa(p1,p2,p1',h o p2') = f <=> h = tp(p1,p2,ev,p1',p2',f)"

val exp_ex = read_axiom "!A.!B.?A2B efs p1:efs ->A p2:efs ->A2B ev:efs->B.isexp(p1,p2,ev)"

val ax2 = exp_ex

val N0_def = read_axiom "!N0 one z0:one -> N0 s0:N0->N0. isN0(z0,s0) <=> is1(one) & !X x0:one -> X t:X -> X x:N0 -> X. x o z0 = x0 & x o s0 = t o x <=> x = Nind0(z0,s0,x0,t)";


val constN_def = read_axiom "!X x0:1->X t:X ->X x:N->X.x o z = x0 & x o s = t o x <=> x = Nind(x0,t)"

(*to be edited, switch the ordrr of s0 and z0*)
val ax3 = constN_def

val ax_wp = read_axiom "!A B f: A -> B g:A ->B.~(f = g) ==> ?a: 1 -> A. ~(f o a = g o a)";

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

val ax_2el = read_axiom "?X x1: 1 -> X x2: 1 -> X. ~ x1 = x2"


val ax8 = ax_2el


fun dischl' l th = 
    case l of 
        [] => th
      | h :: t => dischl' t (disch h th |> gen_all)

fun dischl'' l th = 
    case l of 
        [] => th
      | h :: t => dischl'' t (gen_all th |> disch h)

fun disch_all' th = dischl' (ant th) th

fun disch_all'' th = dischl'' (ant th) th

val eq_eqn = eq_def |> iffLR |> strip_all_and_imp
                    |> conjE2 |> iffRL |> strip_all_and_imp
                    |> rewr_rule [assume (rapf "x0 = eqind(e:E->A, f:A->B, g, x:X->A)")] |> disch (rapf "x0 = eqind(e:E->A, f:A->B, g, x:X->A)")
                    |> gen_all 
                    |> allE (rastt "eqind(e:E->A, f:A->B, g, x:X->A)") 
                    |> C mp $ refl (rastt "eqind(e:E->A, f:A->B, g, x:X->A)")
                    |> disch_all''
 


(*TODO: a rule that repeat disch and gen until cannot *)


fun arw_rule thl th = rewr_rule ((List.map assume $ ant th) @ thl) th


(*∀A B X f. f∶A × X → B ⇒ ev A B ∘ ⟨p1 A X, tp f ∘ p2 A X⟩ = f*)

val ev_of_tp = 
exp_def |> iffLR |> strip_all_and_imp |> conjE2 |> strip_all_and_imp |> iffRL |>
undisch |> arw_rule [] |> disch (rapf "h = tp(p1:efs->A, p2:efs->A2B, ev:efs->B, p1':AX->A, p2':AX->X, f)") |> allI ("h",mk_ar_sort (mk_ob "X") (mk_ob "A2B"))|>
allE $ rastt "tp(p1:efs->A, p2:efs->A2B, ev:efs->B, p1':AX->A, p2':AX->X, f)"|>
C mp $ refl $ rastt "tp(p1:efs->A, p2:efs->A2B, ev:efs->B, p1':AX->A, p2':AX->X, f)" |> 
disch_all'' |> gen_all



(*∀A B C f g. f∶ A×B → C ∧ g∶ A×B → C ⇒ (tp f = tp g ⇔ f = g)*)
fun mp_canon th = 
    let val th0 = strip_all_and_imp th 
        val th1 = conj_all_assum th0
    in th1 |> disch_all'' |> gen_all
    end


val tp_eq =
e0
(strip_tac >> drule ev_of_tp >> first_x_assum drule >> 
 first_assum (specl_then [rastt "f:AX->B"] assume_tac) >>
 first_assum (specl_then [rastt "g:AX->B"] assume_tac) >>
 suffices_tac (rapf "ev o pa(p1:efs->A, p2:efs->A2B, p1':AX->A, tp(p1, p2, ev, p1', p2':AX->X, f:AX->B) o p2') = ev o pa(p1, p2, p1', tp(p1, p2, ev, p1', p2', g) o p2')") 
 >-- (once_arw_tac[] >> rw_tac[]) >>
 pop_assum (K all_tac) >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 arw_tac[])
(rapg "isexp(p1:efs->A,p2:efs->A2B,ev:efs->B) & ispr(p1':AX->A,p2':AX->X) & tp(p1, p2, ev, p1', p2', f) = tp(p1, p2, ev, p1', p2', g) ==> f = g")



(*
∀A B X f h. f∶ A × X → B ∧ h∶ X → exp A B ∧
            (ev A B) o ⟨p1 A X, h o (p2 A X)⟩ = f ⇒
            h = tp f
*)
val is_tp = exp_def |> iffLR |> strip_all_and_imp |> conjE2 |> iffLR
                    |> disch_all'' |> gen_all

(*
∀A B X f. f∶ (po A X) → B ⇒
          (∀h. (h∶ X → (exp A B) ∧
                (ev A B) o (pa (p1 A X) (h o (p2 A X))) = f) ⇔
                 h = tp f)
*)

val ax2_conj2 = exp_def |> iffLR |> strip_all_and_imp |> conjE2 |> disch_all'' |> gen_all

(*
∀X x0 t. x0∶ one → X ∧ t∶ X → X ⇒
                     !x. (x∶ N → X ∧ x o z = x0 ∧ x o s = t o x) ⇔
                         x = N_ind x0 t

ax3_conj2
*)

(*∀A B X f g. f∶ X →(exp A B) ∧ g∶X → (exp A B) ∧
            (ev A B) o ⟨p1 A X,f o (p2 A X)⟩ =
            (ev A B) o ⟨p1 A X,g o (p2 A X)⟩ ⇒
            f = g
*)

val exp_ispr = exp_def |> iffLR |> strip_all_and_imp |> conjE1 |> disch_all |> gen_all



val ev_eq_eq = 
e0
(repeat strip_tac >> 
 suffices_tac (rapf "f = tp (p1:efs->A,p2:efs->A2B,ev:efs->B,p1':AX->A,p2':AX->X,ev o pa(p1, p2, p1', f o p2')) & g = tp (p1,p2,ev,p1',p2',ev o pa(p1, p2, p1', f o p2'))")
 >-- (strip_tac >> once_arw_tac[] >> rw_tac[]) >> strip_tac
 >> (match_mp_tac $ irule_canon is_tp >> arw_tac[]))
(rapg "!A A2B B efs ev:efs->B p1:efs -> A p2:efs->A2B. isexp(p1,p2,ev) ==> !AX p1':AX->A X p2':AX->X. ispr(p1',p2') ==> !f: X -> A2B g. ev o pa(p1, p2, p1', f o p2')=ev o pa(p1, p2, p1', g o p2')==> f = g")

(*
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ⇒
            ((p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇔ f = g)
*)

val to_p_component = proved_th $
e0
(repeat strip_tac >> match_mp_tac (pr_def |> iffLR |> iffLR |> irule_canon) >>
 arw_tac[])
(rapg "!A B AB p1:AB->A p2:AB->B. ispr(p1, p2) ==>!X f:X->AB. f = pa(p1, p2, p1 o f, p2 o f)")

val to_p_eq = 
e0
(repeat strip_tac >> 
 suffices_tac (rapf "f = pa(p1:AB->A,p2:AB->B,p1 o (f:X->AB),p2 o f) & g = pa(p1:AB->A,p2:AB->B,p1 o (g:X->AB),p2 o g)")
 >-- (strip_tac >> once_arw_tac[] >> arw_tac[]) >> strip_tac
 >> match_mp_tac to_p_component >> arw_tac[])
(rapg "!A B AB p1:AB->A p2:AB->B.ispr(p1,p2) ==> !X f:X ->AB g. p1 o f = p1 o g & p2 o f = p2 o g ==> f = g ")

rapf "!p1AN:AN->A p2AN:AN->N. "
∀g h A B. g∶ A → B ∧ h∶ (po (po A N) B) → B ⇒
          ∃!f. f∶ po A N → B ∧
               f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one) ∧
               h o ⟨id (po A N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩

(*fun strip_all_and_imp th = 
    if is_forall (concl th) then 
        strip_all_and_imp (spec_all th)
    else if is_imp (concl th) then 
        strip_all_and_imp (undisch th)
(*before the undisch, check two cases:
1.conjunction -> strip
2.existential -> pull extential quantifier out
otherwise just undisch, keep the disjs*)
    else th*)
