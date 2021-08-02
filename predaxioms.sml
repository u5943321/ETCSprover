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


val constN_def = read_axiom "!X x0:1->X t:X ->X x:N->X.x o z = x0 & x o s = t o x <=> x = Nind(x0,t)"

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

val eq_eqn = eqind_def |> strip_all_and_imp
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
tp_def |> strip_all_and_imp |> conjE2 |> strip_all_and_imp |> iffRL |>
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
val is_tp = tp_def |> strip_all_and_imp |> conjE2 |> iffLR
                    |> disch_all'' |> gen_all

(*
∀A B X f. f∶ (po A X) → B ⇒
          (∀h. (h∶ X → (exp A B) ∧
                (ev A B) o (pa (p1 A X) (h o (p2 A X))) = f) ⇔
                 h = tp f)
*)

val ax2_conj2 = tp_def |> strip_all_and_imp |> conjE2 |> disch_all'' |> gen_all

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

val exp_ispr = tp_def |> strip_all_and_imp |> conjE1 |> disch_all |> gen_all



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
(repeat strip_tac >> match_mp_tac (pa_def |> iffLR |> irule_canon) >>
 arw_tac[])
(rapg "!A B AB p1:AB->A p2:AB->B. ispr(p1, p2) ==>!X f:X->AB. f = pa(p1, p2, p1 o f, p2 o f)")

val to_p_eq = proved_th $
e0
(repeat strip_tac >> 
 suffices_tac (rapf "f = pa(p1:AB->A,p2:AB->B,p1 o (f:X->AB),p2 o f) & g = pa(p1:AB->A,p2:AB->B,p1 o (g:X->AB),p2 o g)")
 >-- (strip_tac >> once_arw_tac[] >> arw_tac[]) >> strip_tac
 >> match_mp_tac to_p_component >> arw_tac[])
(rapg "!A B AB p1:AB->A p2:AB->B.ispr(p1,p2) ==> !X f:X ->AB g. p1 o f = p1 o g & p2 o f = p2 o g ==> f = g ")

val from_copr_components = proved_th $
e0
(repeat strip_tac >> match_mp_tac (copa_def |> iffLR |> irule_canon) >>
arw_tac[])
(rapg "!A B AB i1:A->AB i2:B->AB. iscopr(i1, i2) ==>!X f:AB->X. f = copa(i1, i2, f o i1, f o i2)")



(*i1 one one ≠ i2 one one*)
(*val i1_ne_i2 = proved_th $
e0
(repeat strip_tac >> ccontra_tac >> 
 x_choosel_then ["X","x1","x2"])
(rapg "!one oneone i1:one -> oneone i2:one -> oneone. is1(one) & iscopr(i1,i2) ==> ~i1 = i2")
*)

(*∀A B X f g. f∶ A → X ∧ g∶ B → X ⇒ copa f g o i1 A B = f*)

val i12_of_copa = copa_def |> iffRL |> spec_all |> undisch
                          |> specl (List.map rastt ["X","f:A->X","g:B->X","copa(i1:A->AB,i2:B->AB,f:A->X,g)"]) |> C mp $ refl (rastt "copa(i1:A->AB,i2:B->AB,f:A->X,g)") 
                          |> gen_all |> disch_all |> gen_all
                         

val i1_of_copa = copa_def |> iffRL |> spec_all |> undisch
                          |> specl (List.map rastt ["X","f:A->X","g:B->X","copa(i1:A->AB,i2:B->AB,f:A->X,g)"]) |> C mp $ refl (rastt "copa(i1:A->AB,i2:B->AB,f:A->X,g)") 
                          |> conjE1 |> gen_all |> disch_all |> gen_all

val i2_of_copa = copa_def |> iffRL |> spec_all |> undisch
                          |> specl (List.map rastt ["X","f:A->X","g:B->X","copa(i1:A->AB,i2:B->AB,f:A->X,g)"]) |> C mp $ refl (rastt "copa(i1:A->AB,i2:B->AB,f:A->X,g)") 
                          |> conjE2 |> gen_all |> disch_all |> gen_all



(*may add once full simp *)
val i1_ne_i2 = proved_th $
e0
(repeat strip_tac >> ccontra_tac >> 
 x_choosel_then ["X","x1","x2"] assume_tac ax8 >> 
 by_tac (rapf "copa(i1:1->oneone,i2:1->oneone,x1:1->X,x2) o i1 = x1 &copa(i1,i2,x1,x2) o i2 = x2") >-- (drule i12_of_copa >> arw_tac[]) >>
 pop_assum (assume_tac o GSYM) >> 
 rev_full_simp_tac[] >> suffices_tac (rapf "x1:1->X = x2") 
 >-- (arw_tac[] >> first_assum accept_tac) >>
 pick_x_assum (rapf "~x1:1->X = x2") (K all_tac) >> once_arw_tac[] >> rw_tac[])
(rapg "!oneone i1:1 -> oneone i2:1 -> oneone. iscopr(i1,i2) ==> ~i1 = i2")

(*∀A B x. ¬(x∶one → (A + B) ∧ (∃x0 x0'. x0∶one → A ∧ x0'∶one → B ∧
                             i1 A B ∘ x0 = x ∧
                             i2 A B ∘ x0' = x))
*)

(* TODO:  i1_ne_i2|> spec_all |> undisch|> eqF_intro |> iffLR |> disch_all|> gen_all |>irule_canon
# Exception- ERR ("the given variable occurs unexpectedly", [], [], []) raised


*)

val eq_to1 = mp (allE one to1_def) const1_def 

val to1_unique = specl [rastt "X",rastt "f:X->1"] eq_to1 |> GSYM 
                       |> trans (specl [rastt "X",rastt "g:X->1"] eq_to1) |> gen_all

val prop_5_lemma = proved_th $
e0
(repeat strip_tac >> x_choosel_then ["oneone","one1","one2"] assume_tac  (specl (List.map rastt ["1","1"]) copr_ex) >> ccontra_tac >>
match_mp_tac (i1_ne_i2|> spec_all |> undisch|> eqF_intro |> iffLR |> undisch|> conj_all_assum |> disch_all|> gen_all) >>
exists_tac (rastt "oneone") >> exists_tac (rastt "one1:1->oneone") >>
exists_tac (rastt "one2:1->oneone") >> 
arw_tac[] >> pop_assum mp_tac >> pop_assum mp_tac >> drule i12_of_copa >>
first_x_assum (specl_then (List.map rastt ["oneone","(one1:1->oneone) o (to1(A,1))",
                                           "(one2:1->oneone) o (to1(B,1))"]) assume_tac) >>
repeat strip_tac >>
suffices_tac (rapf "(one1:1->oneone) o (to1(A,1)) o (x0:1->A) = (one2:1->oneone) o (to1(B,1)) o (x0':1->B)") 
>-- ((*by_tac (rapf " to1(A, 1) o (x0:1->A) = to1(B, 1) o x0'") TODO: do not understand why cannot use rw to1_unique to solve this by*)
      assume_tac (specl (List.map rastt ["1","id(1)","to1(A, 1) o (x0:1->A)"]) to1_unique) >>  assume_tac (specl (List.map rastt ["1","id(1)","to1(B, 1) o (x0':1->B)"]) to1_unique)>>
  arw_tac[] >> rw_tac[idR]) >>
suffices_tac (rapf "copa(i1:A->AB, i2:B->AB, ((one1:1->oneone) o to1(A, 1)), ((one2:1->oneone) o to1(B, 1))) o i1 o (x0:1->A) = copa(i1, i2, (one1 o to1(A, 1)), (one2 o to1(B, 1))) o i2 o x0'") 
>-- (rw_tac[GSYM o_assoc] >> arw_tac[]) >>
arw_tac[]
)
(rapg "!A B AB i1:A->AB i2:B->AB. iscopr(i1,i2) ==> !x0:1->A x0':1->B.~i1 o x0 = i2 o x0'")

val from_cop_eq = proved_th $
e0
(repeat strip_tac >> 
 suffices_tac (rapf "f = copa(i1:A->AB,i2:B->AB,(f:AB->X) o i1,f o i2) & g = copa(i1,i2,(g:AB->X) o i1,g o i2)")
 >-- (strip_tac >> once_arw_tac[] >> arw_tac[]) >> strip_tac
 >> match_mp_tac from_copr_components >> arw_tac[])
(rapg "!A B AB i1:A->AB i2:B->AB.iscopr(i1,i2) ==> !X f:AB ->X g. f o i1 = g o i1 & f o i2 = g o i2 ==> f = g ")

(*!X t. t∶ one → X ==> i1 X X o t <> i2 X X o t*)


val i1_i2_disjoint = proved_th $
e0
(repeat strip_tac >> match_mp_tac prop_5_lemma >> arw_tac[])
(rapg "!X XX i1:X->XX i2:X->XX. iscopr(i1,i2) ==> !t:1->X. ~i1 o t = i2 o t")

val pr_with_one = proved_th $
e0
(strip_tac >> rw_tac[pr_def] >> repeat strip_tac >> exists_tac (rastt "f:X->A") >>
repeat strip_tac >> dimp_tac (* 2 *)
>-- (strip_tac >> full_simp_tac[idL]) >>
strip_tac >> arw_tac[idL] >> rw_tac[specl (List.map rastt ["X","g:X->1"]) to1_unique])
(rapg "!A. ispr(id(A),to1(A,1))")

(*
∀A B C D P Q f g i j. f∶ A → C ∧ g∶ B → D ∧ i∶ C → P ∧ j∶ D → Q ⇒
                      ⟨i o p1 C D,j o p2 C D⟩ o ⟨f o p1 A B, g o p2 A B⟩ =
                      ⟨i o f o p1 A B, j o g o p2 A B⟩*)

fun dest_form_view fv = case fv of vQ("?",n,s,b) => (n,s,b)



val p12_of_pa = pa_def |> iffRL |> spec_all |> undisch
                       |> specl (List.map rastt ["X","f:X->A","g:X->B","pa(p1:AB->A,p2:AB->B,f:X->A,g)"]) |> C mp $ refl (rastt "pa(p1:AB->A,p2:AB->B,f:X->A,g)") 
                       |> gen_all |> disch_all |> gen_all
                       

val p1_of_pa =  pa_def |> iffRL |> spec_all |> undisch
                         |> specl (List.map rastt ["X","f:X->A","g:X->B","pa(p1:AB->A,p2:AB->B,f:X->A,g)"]) |> C mp $ refl (rastt "pa(p1:AB->A,p2:AB->B,f:X->A,g)")                
                         |> conjE1 |> gen_all |> disch_all |> gen_all

val p2_of_pa =  pa_def |> iffRL |> spec_all |> undisch
                         |> specl (List.map rastt ["X","f:X->A","g:X->B","pa(p1:AB->A,p2:AB->B,f:X->A,g)"]) |> C mp $ refl (rastt "pa(p1:AB->A,p2:AB->B,f:X->A,g)")                
                         |> conjE2 |> gen_all |> disch_all |> gen_all


(*AQ: massive conditional rw here *)

val parallel_p_compose = proved_th $
e0
(strip_tac >> match_mp_tac (irule_canon to_p_eq) >> 
 exists_tac (rastt "P") >> exists_tac (rastt "Q") >>
 exists_tac (rastt "pP:PQ->P") >> exists_tac (rastt "pQ:PQ->Q") >> strip_tac (* 2 *)
 >-- (drule p2_of_pa >> arw_tac[] >> arw_tac[GSYM o_assoc] >> 
      pick_x_assum (rapf "ispr(pC:CD->C, pD:CD->D)") assume_tac >> 
      drule p2_of_pa >> arw_tac[o_assoc]) >>
 drule p1_of_pa >> arw_tac[GSYM o_assoc] >> 
 pick_x_assum (rapf "ispr(pC:CD->C, pD:CD->D)") assume_tac >> 
 drule p1_of_pa >> arw_tac[o_assoc]
 )
(rapg "ispr(pM:MN->M,pN:MN->N1)& ispr(pC:CD->C,pD:CD->D) & ispr(pP:PQ->P,pQ:PQ->Q) ==> pa(pP,pQ, i o pC,j o pD) o pa(pC,pD,f o pM,g o pN) = pa(pP,pQ,i o f o pM,j o g o pN) ")



(*
∀A B C D P Q f g i j. f∶ A → C ∧ g∶ B → D ∧ i∶ C → P ∧ j∶ D → Q ⇒
                      ⟨i o p1 C D,j o p2 C D⟩ o ⟨f o p1 A B, g o p2 A B⟩ =
                      ⟨i o f o p1 A B, j o g o p2 A B⟩

(id A)∶A → A ∧ f∶B → C ∧ id A∶ A → A ∧ g∶ C → D ⇒
   ⟨(id A) ∘ p1 A C, g ∘ p2 A C⟩ ∘ ⟨id A ∘ p1 A B, f ∘ p2 A B⟩ =
   ⟨(id A) ∘ (id A) ∘ p1 A B,g ∘ f ∘ p2 A B⟩

∀A B C D f g.f∶ B → C ∧ g∶ C→ D ⇒
             ⟨p1 A B,g o f o p2 A B⟩ =
             ⟨p1 A C, g o p2 A C⟩ o ⟨p1 A B, f o p2 A B⟩
*)

val parallel_p_one_side = 
proved_th $ 
e0 
(strip_tac >> by_tac (rapf "ispr(pA:AB ->A,pB:AB->B) & ispr(pA':AC->A,pC:AC->C) & ispr(pA'':AD->A,pD:AD->D)")
>-- arw_tac[] >> 
drule (parallel_p_compose |> undisch |> gen_all |> disch_all |> gen_all) >>
first_x_assum (specl_then (List.map rastt ["id(A)","f:B->C","id(A)","g:C->D"]) assume_tac)>>
full_simp_tac[idL])
(rapg "ispr(pA:AB ->A,pB:AB->B) & ispr(pA':AC->A,pC:AC->C) & ispr(pA'':AD->A,pD:AD->D) ==>pa(pA'',pD,pA,(g:C->D) o (f:B->C) o pB) = pa(pA'',pD,pA',g o pC) o pa(pA',pC,pA,f o pB)")

val parallel_p_one_side' = proved_th $
e0
(strip_tac >> assume_tac (undisch parallel_p_one_side) >> arw_tac[o_assoc])
(rapg "ispr(pA:AB ->A,pB:AB->B) & ispr(pA':AC->A,pC:AC->C) & ispr(pA'':AD->A,pD:AD->D) ==>pa(pA'',pD,pA,((g:C->D) o (f:B->C)) o pB) = pa(pA'',pD,pA',g o pC) o pa(pA',pC,pA,f o pB)")


(*∀A B C D E f g h.
         f∶B → C ∧ g∶C → D /\ h ∶ D → E ⇒
         ⟨p1 A B,(h o g ∘ f) ∘ p2 A B⟩ =
         ⟨p1 A D, h ∘ p2 A D⟩ o ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩
*)
val parallel_p_one_side = parallel_p_one_side |> undisch|> gen_all |> disch_all |> gen_all

val parallel_p_one_side_three = proved_th $
e0
(strip_tac >> by_tac (rapf "ispr(pA:AB ->A,pB:AB->B) & ispr(pA'':AD->A,pD:AD->D) & ispr(pA''':AE->A,pE:AE->E)") >-- arw_tac[] >>
drule parallel_p_one_side >> first_x_assum (specl_then (List.map rastt ["(g:C->D) o (f:B->C)","h:D->E"]) assume_tac) >> full_simp_tac[o_assoc] >>
suffices_tac (rapf "pa(pA'':AD->A, pD:AD->D, pA:AB->A, (g:C->D) o (f:B->C) o (pB:AB->B)) = pa(pA'', pD, pA':AC->A, (g o pC)) o pa(pA', pC:AC->C, pA, f o pB)")
>-- (strip_tac >> arw_tac[]) >>
by_tac (rapf "ispr(pA:AB ->A,pB:AB->B) & ispr(pA':AC->A,pC:AC->C) & ispr(pA'':AD->A,pD:AD->D)") >-- arw_tac[] >> 
drule parallel_p_one_side >> arw_tac[])
(rapg "ispr(pA:AB ->A,pB:AB->B) & ispr(pA':AC->A,pC:AC->C) & ispr(pA'':AD->A,pD:AD->D) & ispr(pA''':AE->A,pE:AE->E)==>pa(pA''',pE,pA,(h:D->E) o (g:C->D) o (f:B->C) o pB) = pa(pA''',pE,pA'',h o pD) o pa(pA'',pD,pA',g o pC) o pa(pA',pC,pA,f o pB)")

(*
∀X A B C f g. (f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ∧ 
               (p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
               (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
               (p2 (A×B) C) o f = (p2 (A×B) C) o g) ⇒ f = g
*)

val iterated_p_eq_applied = proved_th $
e0
(repeat strip_tac >> match_mp_tac (irule_canon to_p_eq) >> 
exists_tac (rastt "PQ") >> exists_tac (rastt "C") >> exists_tac (rastt "pPQ:PQC->PQ") >>
exists_tac (rastt "pC:PQC->C") >> arw_tac[] >> match_mp_tac (irule_canon to_p_eq) >>
exists_tac (rastt "P") >> exists_tac (rastt "Q") >> 
exists_tac (rastt "pP:PQ->P")>> exists_tac (rastt "pQ:PQ->Q") >> arw_tac[])
(rapg "ispr(pPQ:PQC->PQ,pC:PQC->C) & ispr(pP:PQ->P,pQ:PQ->Q) ==> !X f:X->PQC g. pP o pPQ o f = pP o pPQ o g & pQ o pPQ o f = pQ o pPQ o g & pC o f = pC o g ==> f = g")


(*id N = N_ind z s*)

val N_ind_z_s_id = constN_def |> specl (List.map rastt ["N","z","s","id(N)"])
                              |> rewr_rule [idL,idR]


(*∀f. f∶ N → N ∧ f o z = z ∧ f o s = s o f ⇒ f = id N*)

val comm_with_s_id = 
    constN_def |> specl (List.map rastt ["N","z","s","f:N->N"])
               |> iffLR |> undisch |> GSYM |> trans N_ind_z_s_id |> disch_all |> gen_all

(*∀A B f g. f∶ A → B ∧ g∶ A → B ∧ ⟨id A,f⟩ = ⟨id A,g⟩ ⇒ f = g*)
val to_p_components = to_p_component;


(*AQ: once_arw_tac[] can cause :  # # # # # Exception- ERR ("extra variable involved", [A -> A], [f], []) raised, how to prevent this?*)

val to_p_eq_one_side = proved_th $
e0
(repeat strip_tac >> drule p2_of_pa >> pop_assum (assume_tac o GSYM) >> 
 first_assum (specl_then (List.map rastt ["A","id(A)","f:A->B"]) assume_tac) >> 
 first_x_assum (specl_then (List.map rastt ["A","id(A)","g:A->B"]) assume_tac) >>
 once_arw_tac[] >> pop_assum (K all_tac) >> pop_assum (K all_tac) >> arw_tac[])
(rapg "ispr(p1:AB ->A,p2:AB->B) ==> !f:A->B g. pa(p1,p2,id(A),f) = pa(p1,p2,id(A),g) ==> f = g")

val _ = new_pred "isinc" [("a",mk_ar_sort (mk_ob "A") (mk_ob "X")),
                          ("b",mk_ar_sort (mk_ob "B") (mk_ob "X"))]

(*is_inc a b A ⇔ is_subset a A ∧ is_subset b A ∧ ∃h. h∶(dom a) → (dom b) ∧ b o h = a*)

val isinc_def = read_axiom "!X A B a b.isinc(a:A->X,b:B->X) <=> ismono(a) & ismono(b) & ?h:A->B. b o h = a"

val ismono_applied = ismono_def |> iffRL

val ismono_property = ismono_def |> iffLR


(*∀A B m i. m∶ A → B ∧ i∶ B → A ∧ (i o m) = id A ⇒ is_mono m*)

val post_inv_mono = proved_th $
e0
(repeat strip_tac >> match_mp_tac ismono_applied >> repeat strip_tac >>
by_tac (rapf "(i:B->A) o (m:A->B) o (g:X->A) = i o m o h") >-- arw_tac[] >>
pop_assum mp_tac >> rw_tac[GSYM o_assoc] >> arw_tac[idL] >> strip_tac >> 
arw_tac[])
(rapg "!A B m:A->B i:B->A. i o m = id(A) ==> ismono(m)") 


(*is_epi f ⇔ ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = cod g2 ∧ dom g1 = cod f ∧ g1 o f = g2 o f ⇒ g1 = g2*)

val _ = new_pred "isepi" [("e",mk_ar_sort (mk_ob "A") (mk_ob "B"))]

val isepi_def = read_axiom "!A B e:A->B. isepi(e) <=> !X f:B->X g. f o e = g o e ==> f = g"

val isepi_applied = isepi_def |> iffRL

val isepi_property = isepi_def |> iffLR 

(*∀A B e i. e∶ A → B ∧ i∶ B → A ∧ e o i = id B ⇒ is_epi e*)

val pre_inv_epi = proved_th $
e0
(repeat strip_tac >> match_mp_tac isepi_applied >> repeat strip_tac >>
by_tac (rapf "(f:B->X) o (e:A->B) o (i:B->A) = g o e o i") >-- arw_tac[GSYM o_assoc] >>
pop_assum mp_tac >> arw_tac[idR])
(rapg "!A B e:A->B i:B->A. e o i = id(B) ==> isepi(e)") 

(*is_pb P p q f g <=> cod f = cod g /\ p∶ P → dom f ∧ q∶ P → dom g /\
                      f o p = g o q ∧
                      (∀A u v. u∶ A → dom f ∧ v∶ A → dom g ∧ f o u = g o v ⇒
                      ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)*)

val _ = new_pred "ispb" [("f",mk_ar_sort (mk_ob "X") (mk_ob "Z")),
                         ("g",mk_ar_sort (mk_ob "Y") (mk_ob "Z")),
                         ("p",mk_ar_sort (mk_ob "P") (mk_ob "X")),
                         ("q",mk_ar_sort (mk_ob "P") (mk_ob "Y"))]

val ispb_def = read_axiom "!X Z f:X->Z Y g:Y->Z P p:P->X q:P ->Y. ispb(f,g,p,q) <=> f o p = g o q & (!A u:A->X v:A->Y. f o u = g o v ==> ?a: A ->P. !a':A->P. p o a' = u & q o a' = v <=> a' = a)"

(*∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ f ∘ eqa f g = g ∘ eqa f g*)

val eq_equality = eqind_def |> strip_all_and_imp |> conjE1 |> disch_all |> gen_all

val coeq_equality = coeqind_def |> strip_all_and_imp |> conjE1 |> disch_all |> gen_all

(*f A B. f∶ A → B ==> ?ki. ki∶ coeqo f f → B /\ ki o (coeqa f f) = id B*)
val iscoeq_def = read_axiom "!A B f:A->B g:A->B cE ce:B->cE. iscoeq(ce,f,g) <=> ce o f = ce o g & !X x:B->X. x o f = x o g ==> (?x0:cE ->X. !x0'. x0' o ce = x <=> x0' = x0)"

(*TODO:

A , B , X ,   
   (f : A -> B), (x : B -> X), (x0' : B -> X)
   
   ----------------------------------------------------------------------
   x0' = x <=> x0' = x

cannot be solved by rw_tac

 rw_tac[frefl (mk_fvar "f0")]

loops

understand why it is finished by strip_tac
*)

val coeq_of_equal = proved_th $ 
e0
(rw_tac[iscoeq_def] >> repeat strip_tac >> exists_tac (rastt "x:B->X") >> 
 strip_tac >> rw_tac[idR] >> dimp_tac >> strip_tac)
(rapg "iscoeq(id(B),f:A->B,f:A->B)")

(*∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_mono (eqa f g)*)

val is_eqind = eqind_def |> strip_all_and_imp |> conjE2 |> iffLR |> strip_all_and_imp |> disch_all'' 

val is_coeqind = coeqind_def |> strip_all_and_imp |> conjE2 |> iffLR |> strip_all_and_imp |> disch_all'' 



val eqa_is_mono = proved_th $
e0 
(rw_tac[ismono_def] >> repeat strip_tac >> 
 suffices_tac  (rapf "h:X->E0 = eqind(e0:E0->A0,f0:A0->B0,g0, e0 o h) & g:X->E0 = eqind(e0:E0->A0,f0:A0->B0,g0, e0 o h) ") 
 >-- (strip_tac >> once_arw_tac[] >> rw_tac[]) >> 
 drule eq_equality >> 
 strip_tac (* 2 *)
 >> (match_mp_tac (irule_canon is_eqind) >> arw_tac[] >> arw_tac[GSYM o_assoc])
 )
(rapg "iseq(e0:E0->A0,f0:A0->B0,g0) ==> ismono(e0)")

(*∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_epi (coeqa f g)*)


val coeqa_is_epi = proved_th $
e0 
(rw_tac[isepi_def] >> repeat strip_tac >> 
 suffices_tac  (rapf "f:cE0->X = coeqind(ce0:B0->cE0,f0:A0->B0,g0, g o ce0) & g:cE0->X = coeqind(ce0:B0->cE0,f0:A0->B0,g0, g o ce0)") 
 >-- (strip_tac >> once_arw_tac[] >> rw_tac[]) >> 
 drule coeq_equality >> 
 strip_tac (* 2 *)
 >> (match_mp_tac (irule_canon is_coeqind) >> arw_tac[o_assoc]) 
 )
(rapg "iscoeq(ce0:B0->cE0,f0:A0->B0,g0) ==> isepi(ce0)")


(*∀X Y Z f g. f∶ X → Z ∧ g∶ Y → Z ⇒ ∃P p q. p∶ P → X ∧ q∶ P → Y ∧ f o p = g o q ∧
            (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
             ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)*)


(*TODO:,again: c = pa(pX, pY, u, v) <=> c = pa(pX, pY, u, v)*)

val eqind_def' = eqind_def |> strip_all_and_imp |> conjE2 |> disch_all |> gen_all


(* TODO: drule bug:
first_x_assum (specl_then (List.map rastt ["A","pa(pX:XY->X, pY:XY->Y, u:A->X, v)"]) assume_tac) >> first_x_assum drule

*)


val ispb_def_alt = proved_th $
e0
(repeat strip_tac >> rw_tac[ispb_def] >> dimp_tac >> strip_tac >> arw_tac[] >>
 repeat strip_tac >> first_x_assum drule >> 
 first_x_assum (x_choose_then "a" assume_tac) >> exists_tac (rastt "a:A->P") >>
 repeat strip_tac (* 4 *)
 >-- (pop_assum (assume_tac o (fn th => th |> allE (rastt "a:A->P") 
                                          |> (C dimp_mp_r2l) (refl (rastt "a:A->P")))) >>
      arw_tac[])
 >-- (pop_assum (assume_tac o (fn th => th |> allE (rastt "a:A->P") 
                                          |> (C dimp_mp_r2l) (refl (rastt "a:A->P")))) >>
      arw_tac[])
 >-- (suffices_tac (rapf "a1 = a & a2 = a:A->P") 
      >-- (strip_tac >> arw_tac[]) >> 
      strip_tac >> first_x_assum (match_mp_tac o iffLR) >> arw_tac[]) >>
 dimp_tac >> strip_tac >> arw_tac[] >> pop_assum_list (map_every strip_assume_tac) >>
 first_x_assum match_mp_tac >> arw_tac[])
(rapg "!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y. ispb(f, g, p, q) <=> f o p = g o q & !A u : A -> X v : A -> Y. f o u = g o v ==> ?a : A -> P. p o a = u & q o a = v & !a1 : A -> P a2:A->P. p o a1 = u & q o a1 = v& p o a2 = u & q o a2 = v ==> a1 = a2")

val long_induced_map = rastt "eqind(e:E->XY, (f:X->Z) o pX, (g:Y->Z) o pY, pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y))"

(*TODO: match_mp_bug  e o a1 = e o a2 ==> a1 = a2 ismono_property h is double bind to a1 and a2*)

val pb_exists = proved_th $ 
e0
(rw_tac[ispb_def_alt] >> repeat strip_tac  >> 
 (specl_then (List.map rastt ["X","Y"])
             (x_choosel_then ["XY","pX","pY"] assume_tac)) pr_ex >>
 (specl_then (List.map rastt ["XY","Z","(f:X->Z)o (pX:XY->X)","(g:Y->Z)o (pY:XY->Y)"])
             (x_choosel_then ["E","e"] assume_tac)) eq_ex >>
 exists_tac (rastt "E") >>  exists_tac (rastt "(pX:XY->X) o (e:E->XY)") >>
 exists_tac (rastt "(pY:XY->Y) o (e:E->XY)") >>
 by_tac (rapf "(f:X->Z) o pX o e = (g:Y->Z) o pY o (e:E->XY)")
 >-- (drule eq_equality >> arw_tac[GSYM o_assoc]) >>
 arw_tac[] >> repeat strip_tac >> rw_tac[o_assoc] >> 
 by_tac (rapf "!c:A->XY. (pX:XY->X) o c = u:A->X & (pY:XY->Y) o c = v:A->Y <=> c = pa(pX,pY,u,v)") 
 >-- (drule pa_def >> strip_tac >> arw_tac[] >> dimp_tac >> rw_tac[]) >>
 drule eqind_def' >> 
 by_tac (rapf "((f:X->Z) o pX) o pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y) = (g o pY) o pa(pX, pY, u, v)")
 >-- (rw_tac[o_assoc] >> drule p12_of_pa >> arw_tac[]) >>
 first_x_assum (specl_then (List.map rastt ["A","pa(pX:XY->X, pY:XY->Y, u:A->X, v)"]) assume_tac) >> first_x_assum drule >> 
 exists_tac long_induced_map >> 
 by_tac (rapf "pX o e o eqind(e:E->XY, (f:X->Z) o pX, (g:Y->Z) o pY, pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y)) = u & pY o e o eqind(e:E->XY, (f:X->Z) o pX, (g:Y->Z) o pY, pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y)) = v")
 >-- (pop_assum (assume_tac o (fn th => th |> allE long_induced_map |> (C dimp_mp_r2l) (refl long_induced_map))) >> arw_tac[]) >> repeat strip_tac (* 3 *)
 >-- arw_tac[]
 >-- arw_tac[] >>
 suffices_tac (rapf "e o a1 = (e:E->XY) o (a2:A->E)") 
 >-- (suffices_tac (rapf "ismono(e:E->XY)") 
      >-- (strip_tac >> drule ismono_property >> 
           strip_tac >> first_x_assum drule >> arw_tac[]) >>
      drule eqa_is_mono >> arw_tac[]) >>
 suffices_tac (rapf "(e:E->XY) o a1 = pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y) & e o a2 = pa(pX, pY, u, v)")
 >-- (strip_tac >> arw_tac[]) >>
 strip_tac (* 2 *)
 >> (first_x_assum (match_mp_tac o iffLR) >> arw_tac[])
 )
(rapg "!X Z f:X->Z Y g:Y->Z.?P p:P->X q. ispb(f,g,p,q)")

(*∀X Y Z f g. g∶ Y → Z ∧  f∶ X → Z  ⇒ ∃P p q. p∶ P → X ∧ q∶ P → Y ∧ f o p = g o q ∧
            (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
             ∃a. a∶ A → P ∧ p o a = u ∧ q o a = v)*)

val pb_fac_exists = proved_th $
e0
(repeat strip_tac >> 
 x_choosel_then ["P","p","q"] assume_tac (pb_exists |> rewr_rule [ispb_def_alt] |> strip_all_and_imp) >> 
 exists_tac (rastt "P") >> exists_tac (rastt "p:P->X") >> exists_tac (rastt "q:P->Y") >>
 pop_assum strip_assume_tac >> arw_tac[] >> repeat strip_tac >> first_x_assum drule >>
 arw_tac[] >> pop_assum (x_choosel_then ["a"] assume_tac) >> exists_tac (rastt "a:A->P")>>
 arw_tac[])
(rapg "!X Z f:X->Z Y g:Y->Z.?P p:P->X q:P->Y. f o p = g o q & !A u:A->X v:A->Y. f o u = g o v ==> ?a:A->P. p o a = u & q o a = v")




val ispb_def_alt' = proved_th $
e0
(repeat strip_tac >> rw_tac[ispb_def_alt] >> dimp_tac >> strip_tac >> arw_tac[] >>
 repeat strip_tac >> first_x_assum drule (* 3 *)
 >-- (pop_assum (x_choosel_then ["a"] assume_tac) >> exists_tac (rastt "a:A->P") >>
     arw_tac[])
 >-- (pop_assum (x_choosel_then ["a"] strip_assume_tac) >>
      first_x_assum match_mp_tac >> arw_tac[]) >> 
 pop_assum strip_assume_tac >> exists_tac (rastt "a:A->P") >>
 arw_tac[])
(rapg "!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y. ispb(f, g, p, q) <=> f o p = g o q & !A u : A -> X v : A -> Y. f o u = g o v ==> (?a : A -> P. p o a = u & q o a = v) & !a1 : A -> P a2:A->P. p o a1 = u & q o a1 = v& p o a2 = u & q o a2 = v ==> a1 = a2")

(*!P p q f g. is_pb P p q f g /\ is_mono g ==> is_mono p*)
val pb_equality = ispb_def_alt' |> iffLR |> strip_all_and_imp
                                |> conjE1 |> disch_all|> gen_all

val pb_fac_unique = 
    ispb_def_alt' |> iffLR |> strip_all_and_imp |> conjE2 
                  |> strip_all_and_imp |> conjE2
                  |> disch (rapf "(f:X->Z) o (u:A->X) = (g:Y->Z) o v")
                  |> gen_all |> disch_all |> gen_all


val pb_mono_mono = proved_th $
e0
(repeat strip_tac >> match_mp_tac ismono_applied >> repeat strip_tac >>
 by_tac (rapf "(q:P->Y) o (g':X'->P) = q o h")
 >-- (suffices_tac (rapf "(g:Y->Z) o (q:P->Y) o (g':X'->P) = g o q o h")
      >-- (drule ismono_property >> strip_tac >> first_x_assum drule >>
          arw_tac[]) >>
      drule (GSYM pb_equality) >> arw_tac[GSYM o_assoc] >> arw_tac[o_assoc]) >>
 drule pb_fac_unique >> 
 suffices_tac (rapf "(f:X->Z) o (p:P->X) o (h:X'->P) = (g:Y->Z) o q o h")
 >-- (strip_tac >> first_x_assum drule >> first_x_assum match_mp_tac >> arw_tac[]) >>
 drule pb_equality >> arw_tac[GSYM o_assoc]
 (*drule ismono_property >> *) )
(rapg "ispb(f:X->Z,g:Y->Z,p:P->X,q:P->Y) ==> ismono(g) ==> ismono(p)")

(*∀A B f. f∶ A → B ∧ ¬(A ≅ zero) ⇒ ∃g. g∶B → A ∧ f ∘ g ∘ f = f*)

val non_zero_pinv = proved_th $
e0
(strip_tac >> drule ax6 >> pop_assum strip_assume_tac >> strip_tac >>
 match_mp_tac ax5 >> exists_tac one >> exists_tac (rastt "x:1->A") >> 
 rw_tac[const1_def])
(rapg "(~is0(A)) ==>!B f:A->B.?g:B->A. f o g o f = f")

(*∀A B f g. f∶ A → B ∧ g∶B → A ∧ is_epi f ∧ f ∘ g ∘ f = f ⇒ f o g = id B*)

val epi_pinv_pre_inv = proved_th $
e0
(repeat strip_tac >> drule isepi_property >> first_x_assum match_mp_tac >> 
arw_tac[o_assoc,idL])
(rapg "!A B f:A->B. isepi(f) ==> !g:B->A. f o g o f = f ==> f o g = id(B)")


(*∀A B f g. f∶ A → B ∧ g∶B → A ∧ is_mono f ∧ f ∘ g ∘ f = f ⇒
          g o f = id A*)

val mono_pinv_post_inv = proved_th $
e0
(repeat strip_tac >> drule ismono_property >> first_x_assum match_mp_tac >> 
arw_tac[o_assoc,idR])
(rapg "!A B f:A->B. ismono(f) ==> !g:B->A. f o g o f = f ==> g o f = id(A)")

(*∀A B f. f∶ A → B ∧ is_epi f ∧ ¬(A ≅ zero) ⇒ ∃g. g∶ B → A ∧ f o g = id B*)

val epi_non_zero_pre_inv = proved_th $
e0 
(repeat strip_tac >> drule non_zero_pinv >> 
 first_x_assum (specl_then (List.map rastt ["B","f:A->B"]) strip_assume_tac) >>
 drule epi_pinv_pre_inv >> first_x_assum drule >> exists_tac (rastt "g:B->A") >>
 arw_tac[])
(rapg "!A B f:A->B. isepi(f) ==> (~is0(A)) ==> ?g:B->A. f o g = id(B)")

(*∀A B f. f∶ A → B ∧ is_mono f ∧ ¬(A ≅ zero) ⇒ ∃g. g∶ B → A ∧ g o f = id A*)

val mono_non_zero_post_inv = proved_th $
e0 
(repeat strip_tac >> drule non_zero_pinv >> 
 first_x_assum (specl_then (List.map rastt ["B","f:A->B"]) strip_assume_tac) >>
 drule mono_pinv_post_inv >> first_x_assum drule >> exists_tac (rastt "g:B->A") >>
 arw_tac[])
(rapg "!A B f:A->B. ismono(f) ==> (~is0(A)) ==> ?g:B->A. g o f = id(A)")

(*∀A B C f g. is_mono f ∧ is_mono g ∧ f∶ A → B ∧ g∶ B → C ⇒ is_mono (g o f)*)

val o_mono_mono = proved_th $
e0
(repeat strip_tac >> match_mp_tac ismono_applied >> repeat strip_tac >> 
 drule ismono_property >> full_simp_tac[o_assoc] >> first_x_assum drule >> 
 pick_x_assum (rapf "ismono(g:B->C)") (K all_tac) >> 
 drule ismono_property >> first_x_assum drule >> arw_tac[])
(rapg "!A B f:A->B. ismono(f) ==> !C g:B->C. ismono(g) ==> ismono(g o f)")

(*∀f A B. f∶ A → B ⇒
        (is_iso f ⇔
         ∃f'. f'∶ B → A ∧ f' o f = id A ∧ f o f' = id B)*)
val _ = new_pred "isiso" [("f",mk_ar_sort (mk_ob "A") (mk_ob "B"))]

val isiso_def = read_axiom "!A B f:A->B. isiso(f) <=> ?f':B->A. f' o f = id(A) & f o f' = id(B)"

(*!A B X f i. is_iso i /\ is_mono f /\ f∶ A → B /\ i∶ X → A ==> (is_mono (f o i))*)

val iso_is_mono = proved_th $ 
e0
(rw_tac[isiso_def,ismono_def] >> repeat strip_tac >> 
 suffices_tac (rapf "(f':B->A) o (f:A->B) o (g:X->A) = f' o f o h")
 >-- (arw_tac[GSYM o_assoc,idL] >> strip_tac >> arw_tac[]) >>
 arw_tac[])
(rapg "isiso(f) ==> ismono(f)")

val mono_o_iso_mono = proved_th $
e0
(repeat strip_tac >> match_mp_tac (irule_canon o_mono_mono) >> drule iso_is_mono >>
 arw_tac[])
(rapg "!X A i:X->A.isiso(i) ==> !B f:A->B. ismono(f) ==> ismono(f o i)")

(*∀A B C f m. f∶ A → B ∧ m∶ B → C ∧ is_mono (m o f) ⇒ is_mono f*)

val o_mono_imp_mono = proved_th $
e0
(repeat strip_tac >> match_mp_tac ismono_applied >> repeat strip_tac >> 
 drule ismono_property >> first_x_assum match_mp_tac >> arw_tac[o_assoc])
(rapg "!A B f:A->B C m:B->C. ismono(m o f) ==> ismono(f)")

(*∀A B C f e. f∶ A → B ∧ e∶ C → A ∧ is_epi (f o e) ⇒ is_epi f*)

val o_epi_imp_epi = 
proved_th $
e0
(repeat strip_tac >> match_mp_tac isepi_applied >> repeat strip_tac >> 
 drule isepi_property >> first_x_assum match_mp_tac >> arw_tac[GSYM o_assoc])
(rapg "!A B f:A->B C e:C->A. isepi(f o e) ==> isepi(f)")

(*∀A B f g. f∶ A → B ∧ g∶ A → B ∧ (∀a. a∶ one → A ⇒ f o a = g o a) ⇒ f = g*)

val fun_ext = proved_th $
e0
(repeat strip_tac >> ccontra_tac >> drule ax4 >> pop_assum strip_assume_tac >> 
 first_x_assum (specl_then [rastt "a:1->A"] assume_tac) >> full_simp_tac[])
(rapg "!A B f:A->B g. (!a:1->A. f o a = g o a) ==> f = g")

(*∀A B f. f∶ A → B ∧ (∀b. b∶ one → B ⇒ ∃b0. b0∶ one → A ∧ f o b0 = b) ⇒ is_epi f*)


val surj_is_epi = proved_th $
e0
(repeat strip_tac >> match_mp_tac isepi_applied >> repeat strip_tac >> 
 match_mp_tac fun_ext >> strip_tac >> 
 first_x_assum (specl_then [rastt "a:1->B"] assume_tac) >> 
 pop_assum (strip_assume_tac o GSYM) >> arw_tac[GSYM o_assoc])
(rapg "!A B f:A->B. (!b:1->B. ?b0:1->A. f o b0 = b) ==> isepi(f)")

(*∀A B. A ≅ B ⇔ ∃f. f∶ A → B ∧ is_iso f*)

val _ = new_pred "areiso" [("A",mk_ob_sort),("B",mk_ob_sort)]

val areiso_def = read_axiom "!A B. areiso(A,B) <=> ?f:A->B g:B->A. f o g = id(B) & g o f = id(A)"

val areiso_isiso = proved_th $
e0
(rw_tac[areiso_def,isiso_def] >> dimp_tac >> strip_tac >>
 pop_assum strip_assume_tac (*2  *)
 >-- (exists_tac (rastt "f:A->B") >> exists_tac (rastt "g:B->A") >> arw_tac[]) >>
 exists_tac (rastt "f:A->B") >> exists_tac (rastt "f':B->A") >> arw_tac[])
(rapg "areiso(A,B) <=> ?f:A->B. isiso(f)")

(*∀A B. A ≅ B ⇔ ∃f. f∶ B → A ∧ is_iso f*)

val areiso_isiso' = proved_th $
e0
(rw_tac[areiso_def,isiso_def] >> dimp_tac >> strip_tac >>
 pop_assum strip_assume_tac (*2  *)
 >-- (exists_tac (rastt "g:B->A") >> exists_tac (rastt "f:A->B") >> arw_tac[]) >>
 exists_tac (rastt "f':A->B") >> exists_tac (rastt "f:B->A") >> arw_tac[])
(rapg "areiso(A,B) <=> ?f:B->A. isiso(f)")

val iso_is_epi = proved_th $ 
e0
(rw_tac[isiso_def,isepi_def] >> repeat strip_tac >> 
 suffices_tac (rapf "(f'':B->X) o (f:A->B) o (f':B->A) = g o f o f'")
 >-- arw_tac[idR] >>
 arw_tac[GSYM o_assoc])
(rapg "isiso(f) ==> isepi(f)")


(*∀A B X f g i. is_iso i ∧ f∶ A→ B ∧ g∶ A → B ∧ i∶ X → A ∧ f o i = g o i ⇒ f = g*)

val o_iso_eq_eq = proved_th $
e0
(rw_tac[isiso_def] >> repeat strip_tac >> 
 suffices_tac (rapf "(f:A->B) o i o (f':A->X) = g o i o f'")
 >-- arw_tac[idR] >> arw_tac[GSYM o_assoc])
(rapg "!X A i:X->A. isiso(i) ==> !B f:A->B g. f o i = g o i ==> f = g")

(*TODO: !B f:A->B g. f o i = g o i ==> f = g if g is not quantified, there will be a free variable g whose sort is bounded variables, is that bad?*)

(*∀A B f g. A≅ zero ∧ f∶ A → B ∧ g∶ A → B ⇒ f = g*)

val is0_def = read_axiom "!zero. is0(zero) <=> !X. ?f0x:zero ->X.!f0x':zero->X. f0x'= f0x"


val iso_0_is0 = proved_th $
e0
(rw_tac[areiso_def,is0_def] >> strip_tac >> strip_tac >> 
 strip_assume_tac (const0_def |> rewr_rule [is0_def] |> allE (rastt "X")) >>
 exists_tac (rastt "(f0x:0->X) o (f:A->0)") >> strip_tac >> 
 suffices_tac (rapf "f0x' o g o f = (f0x:0->X) o (f:A->0) o (g:0->A) o (f:A->0)")
 >-- arw_tac[idR] >>
 rw_tac[GSYM o_assoc] >> arw_tac[])
(rapg "areiso(A,0) ==> is0(A)")


(*
A , B ,   
   (f : A -> B), (g : A -> B)
   1.areiso(A, 0)
   2.is0(A)
   3.!X (f0x : A -> X#). f0x# = from0(A, X#)
   ----------------------------------------------------------------------
   f = g
arw_tac[]
loops
*)

val from_iso_zero_eq = proved_th $
e0
(repeat strip_tac >> drule iso_0_is0 >> drule (is0_def|> iffLR) >> 
first_x_assum (specl_then [rastt "B"] strip_assume_tac) >>
arw_tac[])
(rapg "!A. areiso(A,0) ==> !B f:A->B g. f = g")

val iso_zero_is_zero = proved_th $
e0
(rw_tac[areiso_def,is0_def] >> strip_tac >> dimp_tac >> repeat strip_tac 
 >-- (assume_tac const0_def >> drule (iffLR is0_def) >> 
      first_x_assum (specl_then [rastt "X"] strip_assume_tac) >>
      exists_tac (rastt "(f0x:0->X) o f:A->0") >> strip_tac >>
      suffices_tac (rapf "f0x' o g o f = (f0x:0->X) o (f:A->0) o (g:0->A) o f") 
      >-- arw_tac[idR] >> arw_tac[GSYM o_assoc]) >>
 first_assum (specl_then [zero] strip_assume_tac) >>
 exists_tac (rastt "f0x:A->0") >> assume_tac const0_def >> drule (iffLR is0_def) >>
 first_assum (specl_then [rastt "A"] strip_assume_tac) >> 
 exists_tac (rastt "f0x':0->A") >> 
 first_assum (specl_then [zero] strip_assume_tac) >> once_arw_tac[] >>
 last_assum (specl_then [rastt "A"] strip_assume_tac) >>  once_arw_tac[] >>
 rw_tac[])
(rapg "!A.areiso(A,0) <=> is0(A)")

(*∀f. f∶ one → one ⇒ f = id one*)
val is1_def = read_axiom "!one. is1(one) <=> !X. ?t1x:X ->one.!t1x':X->one. t1x' = t1x"


val one_to_one_id = proved_th $
e0
(strip_tac >> assume_tac const1_def >> drule (iffLR is1_def) >>
 first_x_assum (specl_then [one] strip_assume_tac) >>
 arw_tac[])
(rapg "!f:1->1.f = id(1)")

(*∀f A B. is_epi f ∧ f∶ A → B ∧ ¬(B≅ zero) ⇒ ¬(A ≅ zero)*)


(*TODO:rw with one_to_one_id from            (x : 1 -> B)
   1.isepi(f)
   2.~is0(B)
   3.is0(A)
   4.iscopr(i1, i2)
   5.is1(1)
   6.!(t1x' : B -> 1). t1x'# = t1x
   7.T
   8.i1 o t1x = i2 o t1x
   ----------------------------------------------------------------------
   t1x o x = id(1)
   : gstk
causes loop

*)

val no_epi_from_zero = proved_th $
e0
(repeat strip_tac >> ccontra_tac >> 
   specl_then [one,one] (x_choose_then "oneone" strip_assume_tac) copr_ex >> 
 suffices_tac (rapf "i1:1->oneone = i2") 
 >-- (drule i1_ne_i2 >> strip_tac) >> 
 assume_tac const1_def >> drule (iffLR is1_def) >> pop_assum strip_assume_tac >>
 first_x_assum (specl_then [rastt "B"] strip_assume_tac) >> 
 suffices_tac (rapf "i1 o t1x = (i2:1->oneone) o t1x:B->1")
 >-- (drule ax6 >> pop_assum strip_assume_tac >>
      strip_tac >> 
      by_tac (rapf "(t1x:B->1) o x = id(1)") 
      >-- accept_tac (one_to_one_id|> allE (rastt "(t1x:B->1) o (x:1->B)")) >>
      suffices_tac (rapf "i1 o t1x o (x:1->B) = (i2:1->oneone) o t1x:B->1 o x") 
      >-- arw_tac[idR] >>
      arw_tac[GSYM o_assoc]) >>
 drule isepi_property >> first_x_assum match_mp_tac >> 
 drule (iffLR is0_def) >> first_x_assum (specl_then [rastt "oneone"] strip_assume_tac) >>
 arw_tac[]
 )
(rapg "!A B f:A->B. isepi(f) ==> (~is0(B)) ==> ~is0(A)")

(*∀A B f. is_epi f /\ f∶ A → B /\ ¬(B ≅ zero)⇒ ∃g. g∶ B → A ∧ f o g = id B*)


val epi_pre_inv = proved_th $
e0
(repeat strip_tac >> drule no_epi_from_zero >> first_x_assum drule >> 
 drule epi_non_zero_pre_inv >> first_x_assum drule >> arw_tac[])
(rapg "!A B f:A->B. isepi(f) ==> (~is0(B)) ==> ?g:B->A. f o g = id(B)")

(*∀f. ¬(f∶ one → zero)*)

(* (f : 1 -> 0), (x1 : 1 -> X), (x2 : 1 -> X)
   1.T
   2.~x1 = x2
   ----------------------------------------------------------------------
   ~x1 = x2 
TODO: arw do not use eqn as predicates, so arw does nothing onthis
*)

val from0_unique = proved_th $
e0
(repeat strip_tac >> drule (iffLR is0_def) >> 
first_x_assum (specl_then [rastt "X"] strip_assume_tac) >> 
arw_tac[])
(rapg "!zero.is0(zero) ==> !X f:zero ->X g. f = g")

val from0_exists = proved_th $
e0
(repeat strip_tac >> exists_tac (rastt "from0(zero,X)") >> rw_tac[])
(rapg "!zero.is0(zero) ==> !X.?f:zero->X.T")

val zero_no_mem = proved_th $
e0
(ccontra_tac >> pop_assum strip_assume_tac >> 
 strip_assume_tac ax8 >>
 suffices_tac (rapf "x1:1->X = x2") >-- (arw_tac[] >> first_x_assum accept_tac) >>
 assume_tac const0_def >> drule from0_exists >> 
 first_assum (specl_then [one] strip_assume_tac) >> 
 suffices_tac (rapf "x1 o f':0->1 o f:1->0 = (x2:1->X) o f' o f") 
 >-- (assume_tac (one_to_one_id |> allE (rastt "f':0->1 o f:1->0")) >>
      arw_tac[idR]) >>
 suffices_tac (rapf "x1 o f':0->1 = (x2:1->X) o f'")
 >-- (strip_tac >> arw_tac[] >> arw_tac[GSYM o_assoc]) >>
 match_mp_tac from0_unique >> rw_tac[const0_def])
(rapg "~?f:1->0.T")


(rapg "!X Z f:X->Z Y g:Y->Z. ?P p:P->X q:P->Y. f o p = g o q & ")

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
