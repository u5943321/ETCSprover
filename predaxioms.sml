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

val _ = new_fun "SUC" (ar_sort N N,[])

val _ = new_fun "ZERO" (ar_sort one N,[])

val constN_def = read_axiom "!X x0:1->X t:X ->X x:N->X.(x o ZERO = x0 & x o SUC = t o x) <=> x = Nind(x0,t)"

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


val eq_eqn = eqind_def |> strip_all_and_imp
                    |> conjE2 |> iffRL |> strip_all_and_imp
                    |> rewr_rule [assume (rapf "x0 = eqind(e:E->A, f:A->B, g, x:X->A)")] |> disch (rapf "x0 = eqind(e:E->A, f:A->B, g, x:X->A)")
                    |> gen_all 
                    |> allE (rastt "eqind(e:E->A, f:A->B, g, x:X->A)") 
                    |> C mp $ refl (rastt "eqind(e:E->A, f:A->B, g, x:X->A)")
                    |> gen_disch_all
 
val coeq_eqn = coeqind_def |> strip_all_and_imp
                    |> conjE2 |> iffRL |> strip_all_and_imp
                    |> rewr_rule [assume (rapf "x0 = coeqind(ce:B->cE, f:A->B, g, x:B->X)")] |> disch (rapf "x0 = coeqind(ce:B->cE, f:A->B, g, x:B->X)")
                    |> gen_all 
                    |> allE (rastt "coeqind(ce:B->cE, f:A->B, g, x:B->X)") 
                    |> C mp $ refl (rastt "coeqind(ce:B->cE, f:A->B, g, x:B->X)")
                    |> gen_disch_all
 


(*∀A B X f. f∶A × X → B ⇒ ev A B ∘ ⟨p1 A X, tp f ∘ p2 A X⟩ = f*)

val ev_of_tp = 
tp_def |> strip_all_and_imp |> conjE2 |> strip_all_and_imp |> iffRL |>
undisch |> arw_rule [] |> disch (rapf "h = tp(p1:efs->A, p2:efs->A2B, ev:efs->B, p1':AX->A, p2':AX->X, f)") |> allI ("h",mk_ar_sort (mk_ob "X") (mk_ob "A2B"))|>
allE $ rastt "tp(p1:efs->A, p2:efs->A2B, ev:efs->B, p1':AX->A, p2':AX->X, f)"|>
C mp $ refl $ rastt "tp(p1:efs->A, p2:efs->A2B, ev:efs->B, p1':AX->A, p2':AX->X, f)" |> 
gen_disch_all |> gen_all



(*∀A B C f g. f∶ A×B → C ∧ g∶ A×B → C ⇒ (tp f = tp g ⇔ f = g)*)
fun mp_canon th = 
    let val th0 = strip_all_and_imp th 
        val th1 = conj_all_assum th0
    in th1 |> gen_disch_all |> gen_all
    end


val tp_eq = proved_th $
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
                    |> gen_disch_all |> gen_all

(*
∀A B X f. f∶ (po A X) → B ⇒
          (∀h. (h∶ X → (exp A B) ∧
                (ev A B) o (pa (p1 A X) (h o (p2 A X))) = f) ⇔
                 h = tp f)
*)

val ax2_conj2 = tp_def |> strip_all_and_imp |> conjE2 |> gen_disch_all |> gen_all

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




val ev_eq_eq = proved_th $
e0
(repeat strip_tac >> 
 suffices_tac (rapf "f = tp (p1:efs->A,p2:efs->A2B,ev:efs->B,p1':AX->A,p2':AX->X,ev o pa(p1, p2, p1', f o p2')) & g = tp (p1,p2,ev,p1',p2',ev o pa(p1, p2, p1', f o p2'))")
 >-- (strip_tac >> once_arw_tac[] >> rw_tac[]) >> strip_tac
 >> (irule is_tp >> arw_tac[]))
(rapg "!A A2B B efs ev:efs->B p1:efs -> A p2:efs->A2B. isexp(p1,p2,ev) ==> !AX p1':AX->A X p2':AX->X. ispr(p1',p2') ==> !f: X -> A2B g. ev o pa(p1, p2, p1', f o p2')=ev o pa(p1, p2, p1', g o p2')==> f = g")

(*
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ⇒
            ((p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇔ f = g)
*)

val to_p_component = proved_th $
e0
(repeat strip_tac >> match_mp_tac (pa_def |> iffLR |> ir_canon) >>
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
(repeat strip_tac >> match_mp_tac (copa_def |> iffLR |> ir_canon) >>
arw_tac[])
(rapg "!A B AB i1:A->AB i2:B->AB. iscopr(i1, i2) ==>!X f:AB->X. f = copa(i1, i2, f o i1, f o i2)")



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
 qby_tac ‘copa(i1,i2,x1,x2) o i1 = x1 &copa(i1,i2,x1,x2) o i2 = x2’
 >-- (drule i12_of_copa >> arw_tac[]) >>
 pop_assum (assume_tac o GSYM) >> 
 rev_full_simp_tac[] >> 
 qsuff_tac ‘x1 = x2’
 >-- (arw_tac[]) >>
 qpick_x_assum ‘~(x1 = x2)’ (K all_tac) >> once_arw_tac[] >> rw_tac[] >>
 rw_tac[])
(rapg "!oneone i1:1 -> oneone i2:1 -> oneone. iscopr(i1,i2) ==> ~(i1 = i2)")

(*∀A B x. ¬(x∶one → (A + B) ∧ (∃x0 x0'. x0∶one → A ∧ x0'∶one → B ∧
                             i1 A B ∘ x0 = x ∧
                             i2 A B ∘ x0' = x))
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
>-- (assume_tac (specl (List.map rastt ["1","id(1)","to1(A, 1) o (x0:1->A)"]) to1_unique) >>  assume_tac (specl (List.map rastt ["1","id(1)","to1(B, 1) o (x0':1->B)"]) to1_unique)>>
  arw_tac[] >> rw_tac[idR]) >>
suffices_tac (rapf "copa(i1:A->AB, i2:B->AB, ((one1:1->oneone) o to1(A, 1)), ((one2:1->oneone) o to1(B, 1))) o i1 o (x0:1->A) = copa(i1, i2, (one1 o to1(A, 1)), (one2 o to1(B, 1))) o i2 o x0'") 
>-- (rw_tac[GSYM o_assoc] >> arw_tac[]) >>
arw_tac[]
)
(rapg "!A B AB i1:A->AB i2:B->AB. iscopr(i1,i2) ==> !x0:1->A x0':1->B.~(i1 o x0 = i2 o x0')")

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
(rapg "!X XX i1:X->XX i2:X->XX. iscopr(i1,i2) ==> !t:1->X. ~(i1 o t = i2 o t)")

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
(*AQ: why is pb proof so slow*)

val parallel_p_compose = proved_th $
e0
(strip_tac >> irule to_p_eq >> 
 exists_tac (rastt "P") >> exists_tac (rastt "pP:PQ->P") >> exists_tac (rastt "Q") >>
 exists_tac (rastt "pQ:PQ->Q") >> strip_tac (* 2 *)
 >-- (drule p2_of_pa >> arw_tac[] >> arw_tac[GSYM o_assoc] >> 
      pick_x_assum (rapf "ispr(pC:CD->C, pD:CD->D)") assume_tac >> 
      drule p2_of_pa >> arw_tac[o_assoc]) >>
 drule p1_of_pa >> arw_tac[GSYM o_assoc] >> 
 pick_x_assum (rapf "ispr(pC:CD->C, pD:CD->D)") assume_tac >> 
 drule p1_of_pa >> arw_tac[o_assoc]
 )
(form_goal “ispr(pM:MN->M,pN:MN->N1)& ispr(pC:CD->C,pD:CD->D) & ispr(pP:PQ->P,pQ:PQ->Q) ==> pa(pP,pQ, i o pC,j o pD) o pa(pC,pD,f o pM,g o pN) = pa(pP,pQ,i o f o pM,j o g o pN)”)


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
(repeat strip_tac >> irule to_p_eq >> 
exists_tac (rastt "PQ") >>  exists_tac (rastt "pPQ:PQC->PQ") >> exists_tac (rastt "C") >>
exists_tac (rastt "pC:PQC->C") >> arw_tac[] >> irule to_p_eq >>
exists_tac (rastt "P") >>
exists_tac (rastt "pP:PQ->P")>>
 exists_tac (rastt "Q") >>  exists_tac (rastt "pQ:PQ->Q") >> arw_tac[])
(form_goal “ispr(pPQ:PQC->PQ,pC:PQC->C) & ispr(pP:PQ->P,pQ:PQ->Q) ==> !X f:X->PQC g. pP o pPQ o f = pP o pPQ o g & pQ o pPQ o f = pQ o pPQ o g & pC o f = pC o g ==> f = g”)


(*id N = N_ind z s*)

val N_ind_Z_s_id = constN_def |> specl (List.map rastt ["N","ZERO","SUC","id(N)"])
                              |> rewr_rule [idL,idR]


(*∀f. f∶ N → N ∧ f o z = z ∧ f o s = s o f ⇒ f = id N*)

val comm_with_s_id = 
    constN_def |> specl (List.map rastt ["N","ZERO","SUC","f:N->N"])
               |> iffLR |> undisch |> GSYM |> trans N_ind_Z_s_id |> disch_all |> gen_all

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

(*TO-DO:

A , B , X ,   
   (f : A -> B), (x : B -> X), (x0' : B -> X)
   
   ----------------------------------------------------------------------
   x0' = x <=> x0' = x

cannot be solved by rw_tac

 rw_tac[frefl (mk_fvar "f0")]

loops

understand why it is finished by strip_tac solved
*)

val coeq_of_equal = proved_th $ 
e0
(rw_tac[iscoeq_def] >> repeat strip_tac >> exists_tac (rastt "x:B->X") >> 
 strip_tac >> rw_tac[idR])
(rapg "iscoeq(id(B),f:A->B,f:A->B)")

(*∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_mono (eqa f g)*)

val is_eqind = eqind_def |> strip_all_and_imp |> conjE2 |> iffLR |> strip_all_and_imp |> gen_disch_all 

val is_coeqind = coeqind_def |> strip_all_and_imp |> conjE2 |> iffLR |> strip_all_and_imp |> gen_disch_all 



val eqa_is_mono = proved_th $
e0 
(rw_tac[ismono_def] >> repeat strip_tac >> 
 suffices_tac  (rapf "h:X->E0 = eqind(e0:E0->A0,f0:A0->B0,g0, e0 o h) & g:X->E0 = eqind(e0:E0->A0,f0:A0->B0,g0, e0 o h) ") 
 >-- (strip_tac >> once_arw_tac[] >> rw_tac[]) >> 
 drule eq_equality >> 
 strip_tac (* 2 *)
 >> (irule is_eqind >> arw_tac[] >> arw_tac[GSYM o_assoc])
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
 >> (irule is_coeqind >> arw_tac[o_assoc]) 
 )
(rapg "iscoeq(ce0:B0->cE0,f0:A0->B0,g0) ==> isepi(ce0)")


(*∀X Y Z f g. f∶ X → Z ∧ g∶ Y → Z ⇒ ∃P p q. p∶ P → X ∧ q∶ P → Y ∧ f o p = g o q ∧
            (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
             ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)*)



val eqind_def' = eqind_def |> strip_all_and_imp |> conjE2 |> disch_all |> gen_all


(* TO-DO: drule bug:
first_x_assum (specl_then (List.map rastt ["A","pa(pX:XY->X, pY:XY->Y, u:A->X, v)"]) assume_tac) >> first_x_assum drule--cannot find it...

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
(rapg "!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y.\
      \ ispb(f, g, p, q) <=> \
      \  f o p = g o q & \
      \  !A u : A -> X v : A -> Y. \
      \      f o u = g o v ==> ?a : A -> P. p o a = u & q o a = v & !a1 : A -> P a2:A->P. p o a1 = u & q o a1 = v& p o a2 = u & q o a2 = v ==> a1 = a2")

val long_induced_map = rastt "eqind(e:E->XY, (f:X->Z) o pX, (g:Y->Z) o pY, pa(pX:XY->X, pY:XY->Y, u:A->X, v:A->Y))"

(*TO-DO: match_mp_bug  e o a1 = e o a2 ==> a1 = a2 ismono_property h is double bind to a1 and a2 because ismono_property is not in correct order!!!!!*)

val pb_exists = proved_th $ (*val (ct,asl,w) = cg $*)
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
 >-- (drule pa_def >> strip_tac >> arw_tac[] (*>> dimp_tac >> rw_tac[]*)) >>
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
 (*drule ismono_property >> *))
(rapg "ispb(f:X->Z,g:Y->Z,p:P->X,q:P->Y) ==> ismono(g) ==> ismono(p)")

(*∀A B f. f∶ A → B ∧ ¬(A ≅ zero) ⇒ ∃g. g∶B → A ∧ f ∘ g ∘ f = f*)

val non_zero_pinv = proved_th $
e0
(strip_tac >> drule ax6 >> pop_assum strip_assume_tac >> strip_tac >>
 match_mp_tac ax5 >> exists_tac one >> exists_tac (rastt "x:1->A") >> 
 rw_tac[const1_def])
(rapg "~is0(A)==>!B f:A->B.?g:B->A. f o g o f = f")

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
(rapg "!A B f:A->B. ismono(f) ==> ~is0(A) ==> ?g:B->A. g o f = id(A)")

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
(repeat strip_tac >> irule o_mono_mono >> drule iso_is_mono >>
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

(*edited SUC ...*)
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

(*TO-DO: !B f:A->B g. f o i = g o i ==> f = g if g is not quantified, there will be a free variable g whose sort is bounded variables, is that bad?- yes, should edit parser*)

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
      exists_tac (rastt "(f0x:0->X) o (f:A->0)") >> strip_tac >>
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



val no_epi_from_zero = proved_th $
e0
(repeat strip_tac >> ccontra_tac >> 
   specl_then [one,one] (x_choose_then "oneone" strip_assume_tac) copr_ex >> 
 suffices_tac (rapf "i1:1->oneone = i2") 
 >-- (drule i1_ne_i2 >> strip_tac) >> 
 assume_tac const1_def >> drule (iffLR is1_def) >> pop_assum strip_assume_tac >>
 first_x_assum (specl_then [rastt "B"] strip_assume_tac) >> 
 suffices_tac (rapf "i1 o t1x = (i2:1->oneone) o (t1x:B->1)")
 >-- (drule ax6 >> pop_assum strip_assume_tac >>
      strip_tac >> 
      by_tac (rapf "(t1x:B->1) o x = id(1)") 
      >-- accept_tac (one_to_one_id|> allE (rastt "(t1x:B->1) o (x:1->B)")) >>
      suffices_tac (rapf "i1 o t1x o (x:1->B) = (i2:1->oneone) o (t1x:B->1) o x") 
      >-- arw_tac[idR] >>
      arw_tac[GSYM o_assoc]) >>
 drule isepi_property >> first_x_assum match_mp_tac >> 
 drule (iffLR is0_def) >> first_x_assum (specl_then [rastt "oneone"] strip_assume_tac) >>
 arw_tac[]
 )
(rapg "!A B f:A->B. isepi(f) ==> ~is0(B) ==> ~is0(A)")

(*∀A B f. is_epi f /\ f∶ A → B /\ ¬(B ≅ zero)⇒ ∃g. g∶ B → A ∧ f o g = id B*)


val epi_pre_inv = proved_th $
e0
(repeat strip_tac >> drule no_epi_from_zero >> first_x_assum drule >> 
 drule epi_non_zero_pre_inv >> first_x_assum drule >> arw_tac[])
(rapg "!A B f:A->B. isepi(f) ==> ~is0(B) ==> ?g:B->A. f o g = id(B)")

(*∀f. ¬(f∶ one → zero)*)

(* (f : 1 -> 0), (x1 : 1 -> X), (x2 : 1 -> X)
   1.T
   2.~x1 = x2
   ----------------------------------------------------------------------
   ~x1 = x2 
TO-DO: arw do not use eqn as predicates, so arw does nothing onthis
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
 suffices_tac (rapf "x1:1->X = x2") 
 >-- arw_tac[] >>
 assume_tac const0_def >> drule from0_exists >> 
 first_assum (specl_then [one] strip_assume_tac) >> 
 suffices_tac (rapf "x1 o (f':0->1) o (f:1->0) = (x2:1->X) o f' o f") 
 >-- (assume_tac (one_to_one_id |> allE (rastt "(f':0->1) o (f:1->0)")) >>
      arw_tac[idR]) >>
 suffices_tac (rapf "x1 o (f':0->1) = (x2:1->X) o f'")
 >-- (strip_tac >> arw_tac[] >> arw_tac[GSYM o_assoc]) >>
 match_mp_tac from0_unique >> rw_tac[const0_def])
(rapg "~(?f:1->0.T)")

(*∀A. A≅ zero ⇒ ¬(∃x. x∶ one → A)*)

val iso_zero_no_mem = proved_th $
e0
(rw_tac[areiso_def] >> repeat strip_tac >> ccontra_tac 
 >> pop_assum strip_assume_tac >> 
 suffices_tac (rapf "?f:1->0.T")
 >-- (strip_tac >> contr_tac (zero_no_mem |> eqF_intro |> iffLR |> undisch)) >>
 exists_tac (rastt "(f:A->0) o (f':1->A)") >> rw_tac[])
(rapg "!A. areiso(A,0) ==> ~(?f:1->A.T)")

(*∀A B f. is_epi f /\ f∶ A → B ==> (∀b. b∶ one → B ⇒ ∃b0. b0∶ one → A ∧ f o b0 = b)*)


val no_epi_from_iso_zero = contrapos (no_epi_from_zero |> spec_all |> undisch) |> neg_neg_elim |> rewr_rule [GSYM iso_zero_is_zero] |> contrapos|> disch_all |> gen_all


(*maybe TO-DO:This one is messy, should consistently use one of the predicates*) 

val is_epi_surj = proved_th $
e0
(repeat strip_tac >>
 by_tac (rapf "~areiso(B,0)")
 >-- (by_tac (rapf "?(f : 1 -> B). T")
      >-- (exists_tac (rastt "b:1->B") >> rw_tac[]) >>
      ccontra_tac >> assume_tac (allE (rastt "B") iso_zero_no_mem) 
      >> last_assum drule >> full_simp_tac[]) >>
 by_tac (rapf "~areiso(A,0)")
 >-- (irule no_epi_from_iso_zero >> exists_tac (rastt "B") >>
      exists_tac (rastt "f:A->B") >> arw_tac[] >> first_assum accept_tac) >>
 drule epi_non_zero_pre_inv >> 
 by_tac (rapf "~is0(A)") >-- (ccontra_tac >> full_simp_tac[GSYM iso_zero_is_zero]) >>
 first_assum drule  >> pop_assum strip_assume_tac >>
 exists_tac (rastt "(g:B->A) o (b:1->B)") >>
 arw_tac[GSYM o_assoc,idL]
 )
(rapg "!A B f:A->B. isepi(f) ==> (!b:1->B. ?b0:1->A. f o b0 = b)")

(*copa (i1 one one) (i2 one one) ∶ (one + one) → (one + one) ∧
copa (i2 one one) (i1 one one) ∶ (one + one) → (one + one) ∧
copa (i1 one one) (i2 one one) ≠ copa (i2 one one) (i1 one one)*)

val distinct_endo_2 = proved_th $
e0
(repeat strip_tac >> ccontra_tac >> 
 suffices_tac (rapf "i1 = i2:1->oneone")
 >-- (strip_tac >> contr_tac (i1_ne_i2 |> spec_all |> undisch 
                                       |> eqF_intro |> iffLR |> undisch)) >>
 by_tac (rapf "copa(i1:1->oneone, i2:1->oneone, i1, i2) o i1 = copa(i1, i2, i2, i1) o i1")
 >-- arw_tac[] >> pop_assum mp_tac >> drule i1_of_copa >>
 arw_tac[])
(rapg "!oneone i1:1->oneone i2:1->oneone. iscopr(i1,i2) ==> ~(copa(i1,i2,i1,i2) = copa(i1,i2,i2,i1))") 


(*∃X e1 e2. e1∶ X → X ∧ e2∶ X → X ∧ e1 ≠ e2*)

val distinct_endo_exists = proved_th $
e0
(assume_tac distinct_endo_2 >> x_choosel_then ["oneone","i1","i2"] assume_tac (copr_ex|> allE one |> allE one) >> first_x_assum drule >> 
exists_tac (rastt "oneone") >> 
exists_tac (rastt "copa(i1:1->oneone, i2:1->oneone, i1, i2)") >>
exists_tac (rastt "copa(i1:1->oneone, i2:1->oneone, i2, i1)") >>
first_x_assum accept_tac)
(rapg "?X e1:X->X e2. ~(e1 = e2)")

(*∀f A. f∶ A → zero ⇒ A ≅ zero*)

val not_to_zero = proved_th $
e0
(strip_tac >> rw_tac[iso_zero_is_zero] >> ccontra_tac >> drule ax6 >>
 pop_assum strip_assume_tac >> 
 by_tac (rapf "?f:1->0.T") >-- (exists_tac (rastt "(f:A->0) o (x:1->A)") >> rw_tac[])>>
 full_simp_tac[zero_no_mem])
(rapg "!f:A->0. areiso(A,0)")

(*∀f A B. f∶ A → B /\ B ≅ zero ==> A ≅ zero*)

(*AQ: irule on context!, rw with context, as below:*)

val to_zero_zero = proved_th $
e0
(repeat strip_tac >> suffices_tac (rapf "?g:A->0.T")
 >-- (strip_tac >> accept_tac (allE (rastt "g:A->0") not_to_zero)) >>
 full_simp_tac[areiso_def] >> exists_tac (rastt "(f':B->0) o (f:A->B)") >>
 rw_tac[])
(rapg "!A B f:A->B.areiso(B,0) ==> areiso(A,0)")

(*!X A f. X ≅ zero /\  f∶ A → X ==> is_iso f*)

val to_iso_zero_iso = proved_th $ 
e0
(repeat strip_tac >> drule to_zero_zero >> 
 full_simp_tac[iso_zero_is_zero] >> drule (is0_def|> iffLR) >>
 pop_assum mp_tac >> pop_assum mp_tac >> drule (is0_def|> iffLR) >>
 repeat strip_tac >> rw_tac[isiso_def] >>
 last_assum (specl_then [rastt "A"] strip_assume_tac) >>
 exists_tac (rastt "f0x:X->A") >> once_arw_tac[] >>
 first_x_assum (specl_then [rastt "A"] strip_assume_tac) >>
 first_x_assum (specl_then [rastt "X"] strip_assume_tac) >>
 first_assum (specl_then [rastt "(f0x:X->A) o (f:A->X)"] strip_assume_tac) >>
 first_assum (specl_then [rastt "id(X)"] strip_assume_tac) >>
 arw_tac[])
(rapg "!X. areiso(X,0) ==> !A f:A->X. isiso(f)")

(*∀a. is_mono a ∧ is_epi a ⇒ is_iso a*)


val mono_epi_is_iso = proved_th $
e0
(cases_on (rapf "areiso(B,0)")
 >-- (drule to_iso_zero_iso >> arw_tac[]) >>
 strip_tac >> drule no_epi_from_iso_zero >> first_x_assum drule >>
 rw_tac[isiso_def] >> full_simp_tac[iso_zero_is_zero] >> 
 drule ax6 >> pop_assum strip_assume_tac >> assume_tac const1_def >>
 by_tac (rapf "?g:B->A. (a:A->B) o g o a = a") 
 >-- (match_mp_tac ax5 >> exists_tac one >> exists_tac (rastt "x:1->A") >>
     arw_tac[]) >>
 pop_assum strip_assume_tac >> exists_tac (rastt "g:B->A") >> 
 drule epi_pinv_pre_inv >> drule mono_pinv_post_inv >>
first_x_assum drule >> first_x_assum drule >> arw_tac[])
(rapg "ismono(a) & isepi(a) ==> isiso(a)")

(*∀x A B.
         x∶one → A + B ⇒
         ∃x0. x0∶ one → A ∧ (i1 A B) o x0 = x ∨
         ∃x0. x0∶ one → B ∧ (i2 A B) o x0 = x*)

val ax7' = ax7 |> strip_all_and_imp |> gen_all |> disch_all|> gen_all

val to_copa_fac = proved_th $
e0
(repeat strip_tac >> 
 by_tac (rapf "iscopr(i1:A->AB,i2:B->AB) & is1(1)")
 >-- (strip_tac >> arw_tac[const1_def]) >>
 drule ax7' >> first_x_assum (specl_then [rastt "x:1->AB"] assume_tac) >>
 pop_assum strip_assume_tac >> full_simp_tac[ismem0_def] 
 >-- (disj1_tac >> exists_tac (rastt "x0:1->A") >> arw_tac[]) >>
 disj2_tac >> exists_tac (rastt "x0:1->B") >> arw_tac[])
(rapg "!i1:A->AB i2:B->AB. iscopr(i1,i2) ==> !x:1->AB. (?x0:1->A. i1 o x0 = x) | (?x0:1->B. i2 o x0 = x)")

(*¬(one ≅ zero)*)

val one_ne_zero = proved_th $
e0
(ccontra_tac >> drule iso_zero_no_mem >> 
by_tac (rapf "?x:1->1.T") >-- (exists_tac (rastt "id(1)") >> rw_tac[]) >>
first_x_assum opposite_tac)
(rapg "~areiso(1,0)")

(*∀X Y f x. f∶ X→ Y ∧ x∶ one→ X ⇒
          ev X Y o ⟨x, tp (f o p1 X one)⟩ = f o x*)


(*AQ: example of name clash issue again*)

(*AQ: if not use once rw, but use rw, then will loop*)

val tp_elements_ev = proved_th $
e0
(repeat strip_tac >>
 by_tac (rapf "ispr(p1:efs->X,p2:efs->X2Y)")
 >-- (drule exp_ispr >> arw_tac[]) >>
 by_tac (rapf "pa(p1:efs->X, p2:efs->X2Y, x:1->X, tp(p1, p2, ev:efs->Y, pX:X1->X, pone:X1->1, f o pX)) = pa(p1,p2,pX,tp(p1, p2, ev, pX, pone, f o pX) o pone) o pa(pX,pone,x,id(1))")
 >-- (irule to_p_eq >> 
qexistsl_tac ["X","p1:efs->X","X2Y","p2:efs->X2Y"]
(*exists_tac (rastt "X") >>
      exists_tac (rastt "X2Y") >> exists_tac (rastt "p1:efs->X") >> 
      exists_tac (rastt "p2:efs->X2Y")*) >> arw_tac[] >> repeat strip_tac (* 2 *) 
      >-- (drule p2_of_pa >> arw_tac[GSYM o_assoc] >> rw_tac[o_assoc] >>
           by_tac (rapf "pone o pa(pX:X1->X, pone:X1->1, x:1->X, id(1)) = id(1)")
           >-- (once_rw_tac[one_to_one_id] >> rw_tac[]) >>
           arw_tac[idR])
      >-- (drule p1_of_pa >> arw_tac[GSYM o_assoc] >> 
           pick_x_assum (rapf "ispr(pX:X1->X, pone:X1->1)") assume_tac >>
           drule p1_of_pa >> arw_tac[])) >>
 by_tac (rapf "(f:X->Y) o pX = ev o pa(p1:efs->X,p2:efs->X2Y,pX:X1->X, tp(p1, p2, ev:efs->Y, pX, pone:X1->1, f o pX) o pone)")
 >-- (drule ev_of_tp >> first_x_assum (specl_then [rastt "X1"] assume_tac) >>
       first_x_assum drule >> arw_tac[]) >>
 pop_assum (assume_tac o GSYM) >> once_arw_tac[] >>
 rw_tac[GSYM o_assoc] >> once_arw_tac[] >> rw_tac[o_assoc] >> 
 pick_x_assum (rapf "ispr(p1:efs->X,p2:efs->X2Y)") (K all_tac) >>
 drule p1_of_pa >> once_arw_tac[] >> rw_tac[]
)
(form_goal “!X Y X2Y efs ev p1 p2. isexp(p1:efs ->X,p2:efs->X2Y,ev:efs -> Y) ==> !X1 pX:X1->X pone:X1->1. ispr(pX,pone) ==>!x:1->X f:X->Y.ev o pa(p1,p2,x,tp (p1,p2,ev,pX,pone,f o pX)) = f o x”)

(*last_x_assum (first_assum o mp_then Any mp_tac) rev_drule 
use mp_then, but a better style is to use spec first.

or jusr write a rev_drule FREEZE_THEN
*)
(*is_mono a ∧ a∶ A → X ∧ x∶ one → X ∧
 ¬(∃x0. x0∶ one → A ∧ a o x0 = x) ⇒ is_mono (copa a x)*)

(*TO-DO: a drule such that if !x.~ P(x) in assumption, then know p(a) is false,isnt it rw_canon? can do this sort of thing*)

fun neg_disch t th =
   if eq_form(concl th,FALSE) then negI t th 
   else disch t th



fun disch_then (ttac: thm_tactic): tactic = 
 fn ((ct,asl,w):goal) =>
   let
      val (ant, conseq) = dest_imp w
      val (gl, prf) = ttac (assume ant) (ct,asl,conseq)
   in
      (gl, (if is_neg w then neg_disch ant else disch ant) o prf):(goal list * validation)
   end
 

fun disch_tac g = disch_then assume_tac g 
val copa_not_mem_mono_mono = proved_th $
e0
(repeat strip_tac >> match_mp_tac ismono_applied >> repeat strip_tac >>
 match_mp_tac fun_ext >> drule to_copa_fac >> strip_tac >>
 first_assum (specl_then [rastt "(h:X'->A1) o (a':1->X')"] strip_assume_tac)
 (* 2 *)
 >-- (first_assum 
          (specl_then [rastt "(g:X'->A1) o (a':1->X')"] strip_assume_tac) 
      (*generates 2 more subgoals, 3 subgoals in total*)
      >-- (suffices_tac (rapf "x0':1->A = x0")
          >-- (strip_tac >> full_simp_tac[]) >>
          irule ismono_property >>
          exists_tac (rastt "X") >> exists_tac (rastt "a:A->X") >>
          drule i1_of_copa >>
          by_tac (rapf "a = copa(iA:A->A1,ione:1->A1,a:A->X, x:1->X) o iA")
          >-- arw_tac[] >> 
          once_arw_tac[] >> rw_tac[o_assoc] >> arw_tac[] >> 
          rw_tac[GSYM o_assoc] >> 
          pop_assum (K all_tac) >> pop_assum (K all_tac) >> 
          once_arw_tac[] >> rw_tac[]) >>
      assume_tac (specl (List.map rastt ["1","id(1)","x0':1->1"]) to1_unique) >>
      suffices_tac (rapf "?x0:1->A. (a:A->X) o x0 = x") 
      >-- (disch_tac >> first_assum opposite_tac) >> 
      exists_tac (rastt "x0:1->A") >>
      by_tac (rapf "copa(iA,ione,a,x) o ione o (x0':1->1) = copa(iA:A->A1,ione:1->A1,a:A->X,x:1->X) o iA o (x0:1->A)") 
      >-- (arw_tac[] >> arw_tac[GSYM o_assoc]) >>
      pop_assum mp_tac >> rw_tac[GSYM o_assoc] >> drule i12_of_copa >> 
      arw_tac[idR] >> strip_tac >> arw_tac[]) >> 
first_assum 
          (specl_then [rastt "(g:X'->A1) o (a':1->X')"] strip_assume_tac)
>-- (assume_tac (specl (List.map rastt ["1","id(1)","x0:1->1"]) to1_unique) >>
     suffices_tac (rapf "?x0:1->A. (a:A->X) o x0 = x") 
     >-- (disch_tac >> first_assum opposite_tac) >> 
     exists_tac (rastt "x0':1->A") >> 
     by_tac (rapf "copa(iA,ione,a,x) o ione o (x0:1->1) = copa(iA:A->A1,ione:1->A1,a:A->X,x:1->X) o iA o (x0':1->A)")
     >-- (arw_tac[] >> arw_tac[GSYM o_assoc]) >>
     pop_assum mp_tac >> rw_tac[GSYM o_assoc] >> drule i12_of_copa >> 
     arw_tac[idR] >> strip_tac >> arw_tac[]) >>
pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >> strip_tac >> 
pop_assum (assume_tac o GSYM) >> arw_tac[] >> 
once_rw_tac[one_to_one_id] >> rw_tac[idR])
(rapg "!A X a.ismono(a:A->X) ==> !x:1->X.(~(?x0:1->A.a o x0 = x))==> !A1 iA:A->A1 ione:1->A1. iscopr(iA,ione) ==> ismono(copa(iA,ione,a,x))")

(*∀X Y. X ≅ Y ⇔ Y ≅ X*)
val rw = rw_tac 
val once_rw = once_rw_tac

val iso_symm = proved_th $
e0
(rw[areiso_def] >> dimp_tac >> strip_tac (* 2 *)
 >-- (exists_tac (rastt "g:Y->X") >> exists_tac (rastt "f:X->Y") >>
      arw_tac[]) >>
(exists_tac (rastt "g:X->Y") >> exists_tac (rastt "f:Y->X") >>
 arw_tac[]))
(rapg "areiso(X,Y) <=> areiso(Y,X)")

(*∀X Y Z f g. is_iso f ∧ is_iso g ∧ f∶ X → Y ∧ g∶ Y → Z ⇒
            is_iso (g o f)*)

val iso_o_iso = proved_th $
e0
(rw[isiso_def] >> repeat strip_tac >> 
 exists_tac (rastt "(f':Y->X) o (f'':Z-> Y)") >> 
 by_tac (rapf "((g:Y->Z) o (f:X->Y)) o (f':Y->X) o (f'':Z->Y) = g o (f o f') o f''") >-- rw[o_assoc] >> 
 by_tac (rapf "((f':Y->X) o (f'':Z->Y)) o (g:Y->Z) o (f:X->Y) = f' o (f'' o g) o f") >-- rw[o_assoc] >> arw_tac[] >> rw_tac[idL,idR] >> arw_tac[])
(rapg "!X Y f:X->Y. isiso(f) ==> !Z g:Y->Z.isiso(g) ==> isiso(g o f)")

(*∀X Y Z. X ≅ Y ∧ Y ≅ Z ⇒ X ≅ Z*)

val iso_trans = proved_th $ 
e0
(rw[areiso_def] >> strip_tac >> 
 exists_tac (rastt "(f':Y->Z) o (f:X-> Y)") >>
 exists_tac (rastt "(g:Y->X) o (g':Z-> Y)") >>
 by_tac (rapf "(f' o f) o g o g' = (f':Y->Z) o ((f:X->Y) o (g:Y->X)) o (g':Z->Y)")
 >-- rw[o_assoc] >>
 by_tac (rapf "(g o g') o f' o f = (g:Y->X) o ((g':Z->Y) o (f':Y->Z)) o (f:X->Y)")
 >-- rw[o_assoc] >>
 arw_tac[idL,idR])
(rapg "areiso(X,Y) & areiso(Y,Z) ==> areiso(X,Z)")

(*∀X Y A. X ≅ A ∧ Y ≅ A ⇒ X ≅ Y*)

(*how to prevent symmetry things like P(a,b) <=> P(b,a)*)

(*TO-DO: AQ match_mp_tac iso_trans solved*)
val iso_to_same = proved_th $
e0
(strip_tac >> by_tac (rapf "areiso(A,Y)")
 >-- (once_rw_tac[iso_symm] >> arw_tac[]) >>
 suffices_tac (rapf "areiso(X, A) & areiso(A, Y)") >> 
 rw[iso_trans] >> strip_tac >> arw_tac[])
(rapg "areiso(X,A) & areiso(Y,A) ==> areiso(X,Y)")

(*∀A X Y a b h1 h2. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
                  h1∶ X → Y ∧ h2∶ Y → X ∧
                  b o h1 = a ∧ a o h2 = b ⇒
         h1 o h2 = id Y ∧ h2 o h1 = id X*)

fun try_done tac (G,fl,l) = 
    case tac (G,fl,l) of 
        ([],pf) => ([],pf)
       | _ => ([(G,fl,l):goal],sing I)

(*TO-DO: gen_all in to_zero_zero |> strip_all_and_imp  does not do the correct thing solved*)

val to_zero_zero' = 
    to_zero_zero |> strip_all_and_imp 
                 |> allI ("f",mk_ar_sort (mk_ob "A") (mk_ob "B"))
                 |> gen_all |> disch_all |> gen_all

val arw = arw_tac

val inc_inc_iso_as_subobj = proved_th $
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 cases_on (rapf "areiso(X,0)") >> cases_on (rapf "areiso(Y,0)") >> 
 repeat strip_tac
 >> try_done (match_mp_tac from_iso_zero_eq >> arw_tac[]) 
 >-- (drule to_zero_zero' >> first_x_assum (specl_then (List.map rastt ["Y","h2:Y->X"]) opposite_tac))
 >-- (drule to_zero_zero' >> first_x_assum (specl_then (List.map rastt ["X","h1:X->Y"]) opposite_tac))
 >> full_simp_tac[iso_zero_is_zero] >>
 drule mono_non_zero_post_inv >> first_x_assum drule >> 
 pop_assum strip_assume_tac 
 >-- (suffices_tac (rapf "(g:A->Y) o (b:Y->A) o (h1:X->Y) o h2 = id(Y)")
      >-- arw[GSYM o_assoc,idL] >>
      by_tac (rapf "g o b o h1 o h2 = (g:A->Y) o (b o (h1:X->Y)) o (h2:Y->X)")
      >-- rw[o_assoc] >> arw_tac[idL]) >>
 pick_x_assum (rapf "ismono(b:Y->A)") (K all_tac) >>
 drule mono_non_zero_post_inv >> first_x_assum drule >> 
 pop_assum strip_assume_tac >>
 suffices_tac (rapf "(g':A->X) o (a:X->A) o (h2:Y->X) o (h1:X->Y) = id(X)")
 >-- arw[GSYM o_assoc,idL] >> 
 by_tac 
 (rapf "(g':A->X) o (a:X->A) o (h2:Y->X) o (h1:X->Y) = g' o (a o h2) o h1")
 >-- rw[o_assoc] >> arw_tac[]
 )
(rapg "!X A a:X->A.ismono(a) ==>!Y b:Y->A. ismono(b) ==> !h1:X->Y h2:Y->X. b o h1 = a & a o h2 = b ==> h1 o h2 = id(Y) & h2 o h1 = id(X)")

(*∀X Y A a b. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
            (∀x xb. x∶ one → A ∧ xb∶ one → X ∧ a o xb = x ⇒
                    ∃xb'. xb'∶ one → Y ∧ b o xb' = x) ⇒
            (∃h. h∶ X → Y ∧ b o h = a)*)

val prop_2_half2 = proved_th $
e0
(repeat strip_tac >> cases_on (rapf "areiso(Y,0)")
 >-- (by_tac (rapf "areiso(X,0)")
      >-- (rw[iso_zero_is_zero] >> ccontra_tac >>
           drule ax6 >> pop_assum strip_assume_tac >> 
           drule iso_zero_no_mem >>
           suffices_tac (rapf "?xb':1->Y.T")
           >-- (disch_tac >> first_x_assum opposite_tac) >> 
           first_x_assum (specl_then (List.map rastt ["(a:X->A) o (x:1->X)","x:1->X"]) assume_tac) >> pop_assum mp_tac >> rw[] >> strip_tac >> 
           exists_tac (rastt "xb':1->Y") >> rw[]) >>
      drule from_iso_zero_eq  >> 
      pick_x_assum (rapf "areiso(Y, 0)") (assume_tac o (rewr_rule[areiso_def]))>>
      pick_x_assum (rapf "areiso(X, 0)") (assume_tac o (rewr_rule[areiso_def]))>>
      pop_assum mp_tac >> pop_assum mp_tac >> repeat strip_tac >>
      exists_tac (rastt "(g:0->Y) o (f':X->0)") >>
      first_x_assum (specl_then (List.map rastt ["A","(b:Y->A) o (g:0->Y) o (f':X->0)","a:X->A"]) assume_tac) >>
      arw_tac[]) >> 
 full_simp_tac[iso_zero_is_zero] >> drule mono_non_zero_post_inv >>
 first_x_assum drule >> pop_assum strip_assume_tac >> 
 exists_tac (rastt "(g:A->Y) o (a:X->A)") >> 
 match_mp_tac fun_ext >> strip_tac >> rw[o_assoc] >> 
 first_x_assum (specl_then (List.map rastt ["(a:X->A) o (a':1->X)","a':1->X"]) assume_tac) >> pop_assum mp_tac >> rw[] >> strip_tac >> 
 pop_assum (assume_tac o GSYM) >> arw[] >>
 by_tac (rapf "b o g o b o xb' = (b:Y->A) o ((g:A->Y) o (b:Y->A)) o (xb':1->Y)")
 >-- rw[o_assoc] >> arw[idL])
(rapg "!X A a:X->A. ismono(a) ==> !Y b:Y->A. ismono(b) ==> (!x:1->A xb:1->X. a o xb = x ==> ?xb':1->Y. b o xb' = x) ==> ?h:X->Y. b o h = a")

(*∀X Y A a b. a∶ X → A ∧ b∶ Y → A ∧ is_mono a ∧ is_mono b ∧
            (∀y. y∶ one → Y ⇒ ∃x. x∶ one → X ∧ a o x = b o y) ∧
            (∀x. x∶ one → X ⇒ ∃y. y∶ one → Y ∧ a o x = b o y) ⇒
           ?h1 h2. b o h1 = a /\ a o h2 = b /\ h1∶X → Y ∧ h2∶Y → X ∧ h1 ∘ h2 = id Y ∧ h2 ∘ h1 = id X
*)

val prop_2_corollary_as_subobj = proved_th $
e0
(repeat strip_tac >> 
 by_tac (rapf "?h1:X->Y. (b:Y->A) o h1 = a") 
 >-- (irule prop_2_half2 >> arw_tac[] >> 
      repeat strip_tac >> 
      first_x_assum (specl_then [rastt "xb:1->X"] assume_tac) >> 
      pop_assum strip_assume_tac >> exists_tac (rastt "y:1->Y") >>
      full_simp_tac[]) >> 
 by_tac (rapf "?h2:Y->X. (a:X->A) o h2 = b") 
 >-- (irule prop_2_half2 >> arw_tac[] >> 
      repeat strip_tac >>
      first_x_assum (specl_then [rastt "xb:1->Y"] assume_tac) >>
      pop_assum strip_assume_tac >> qexists_tac "x':1->X" >>
      full_simp_tac[]) >>
 pop_assum_list (map_every strip_assume_tac) >> 
 exists_tac (rastt "h1:X->Y") >> exists_tac (rastt "h2:Y->X") >>
 arw[] >> irule inc_inc_iso_as_subobj >>
 exists_tac (rastt "A") >> exists_tac (rastt "a:X->A") >> exists_tac (rastt "b:Y->A") >> arw[])
(rapg "!X A a:X->A.ismono(a) ==> !Y b:Y->A. ismono(b) & (!y:1->Y. ?x:1->X.a o x = b o y) & (!x:1->X.?y:1->Y.a o x = b o y) ==> ?h1:X->Y h2:Y->X. b o h1 = a & a o h2 = b & h1 o h2 = id(Y) & h2 o h1 = id(X)") 



val prop_2_corollary = proved_th $
e0
(repeat strip_tac >> rw[areiso_def] >> rev_drule prop_2_corollary_as_subobj >>
first_x_assum (qspecl_then ["Y","b"] assume_tac) >> rev_full_simp_tac[] >>
qexistsl_tac ["h1","h2"] >> arw[]
 )
(rapg "!X A a:X->A.ismono(a) ==> !Y b:Y->A. ismono(b) & (!y:1->Y. ?x:1->X.a o x = b o y) & (!x:1->X.?y:1->Y.a o x = b o y) ==> areiso(X,Y)") 


(*is_refl f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃d. d∶ cod f1 → dom f1 ∧
                 f0 o d = id (cod f1) ∧
                 f1 o d = id (cod f1)*)

val iso_zero_zero = assume (rapf "areiso(A,0)") 
                           |> rewr_rule[iso_zero_is_zero,is0_def]
                           |> disch_all |> gen_all

(*∀e A B. is_epi e ∧ e∶ A → B ⇒ ∃s. s∶ B → A ∧ e o s = id B*)



(*

e0
(repeat strip_tac >> cases_on (rapf "areiso(B,0)")
 >-- (drule iso_zero_zero >> 
      first_assum (specl_then [rastt "B"] strip_assume_tac) >> 
      first_x_assum (specl_then [rastt "A"] strip_assume_tac) >>
      exists_tac (rastt "f0x:B->A") >> 
      first_assum (specl_then [rastt "(e:A->B) o (f0x':B->A)"] assume_tac) >>
      first_x_assum (specl_then [rastt "id(B)"] assume_tac) >>
      pick_x_assum (rapf "!f0x' : B -> A. f0x' = f0x'") (K all_tac)
  
))
(rapg "!A B e.isepi(e) ==> ?s0:B->A.e o s0 = id(B)")

Exception-
   HOL_ERR
     {message = "predicate not satisfied", origin_function = "pluck",
      origin_structure = "Lib"} raised

WHY?!
*)

(*

exists_tac (rastt "f0x:B->A")  bug! does not complain here, but complain later in validation check!
*)

val epi_has_section = proved_th $
e0
(repeat strip_tac >> cases_on (rapf "areiso(B,0)")
 >-- (drule iso_zero_zero >> 
      first_assum (specl_then [rastt "B"] strip_assume_tac) >> 
      first_x_assum (specl_then [rastt "A"] strip_assume_tac) >>
      exists_tac (rastt "f0x':B->A") >> 
      first_assum (specl_then [rastt "(e:A->B) o (f0x':B->A)"] assume_tac) >>
      first_x_assum (specl_then [rastt "id(B)"] assume_tac) >>
      remove_asm_tac (rapf "!f0x0: B -> A. f0x0 = f0x'") >>
      arw_tac[]) >>
 irule epi_pre_inv >> full_simp_tac[iso_zero_is_zero])
(rapg "!A B e.isepi(e) ==> ?s0:B->A.e o s0 = id(B)")

(*∀f g h h0 A B X. f∶ A → B ∧ g∶ A → B ∧ h∶ X → A ∧ h0∶ X → eqo f g ∧
           eqa f g o h0 = h ⇒
           f o h = g o h*)

val fac_through_eq = proved_th $
e0
(repeat strip_tac >> 
 suffices_tac (rapf "f o e = (g:A->B) o (e:E->A)")
 >-- (strip_tac >> rule_assum_tac (fn th => sym th handle _ => th)
      >> arw[GSYM o_assoc]) >> 
 drule eq_equality >> arw_tac[])
(rapg "iseq(e:E->A,f:A->B,g) ==> e o h0 = h ==> f o h = g o h")                      
val fac_through_coeq = proved_th $
e0
(repeat strip_tac >> 
 suffices_tac (rapf "ce o f = (ce:B->cE) o (g:A->B)")
 >-- (strip_tac >> rule_assum_tac (fn th => sym th handle _ => th)
      >> arw[GSYM o_assoc]) >> 
 drule coeq_equality >> arw_tac[] >> pop_assum (K all_tac) >>
 arw[o_assoc])
(rapg "iscoeq(ce:B->cE,f:A->B,g) ==> h0 o ce = h ==> h o f = h o g")                      


(*∀f g h. f∶ A → B ∧ g∶ A → B ∧ h∶ X → A ⇒
        ((∃h0. h0∶ X → eqo f g ∧ (eqa f g) o h0 = h) ⇔
         f o h = g o h)*)
val fac_through_eq' = fac_through_eq |> undisch |> gen_all |> disch_all|> gen_all

val fac_through_coeq' = fac_through_coeq |> undisch |> gen_all |> disch_all|> gen_all

val fac_through_eq_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac 
 >-- (drule fac_through_eq' >> first_x_assum drule >> arw[]) >> 
exists_tac (rastt "eqind(e:E->A,f:A->B,g,h:X->A)") >>
drule eq_eqn >> first_x_assum drule >> arw[])
(rapg "iseq(e:E->A,f:A->B,g) ==> ((?h0: X-> E.e o h0 = h) <=> f o h = g o h)")


val fac_through_coeq_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac 
 >-- (drule fac_through_coeq' >> first_x_assum drule >> arw[]) >> 
exists_tac (rastt "coeqind(ce:B->cE,f:A->B,g,h:B->X)") >>
drule coeq_eqn >> first_x_assum drule >> arw[])
(rapg "iscoeq(ce:B->cE,f:A->B,g) ==> ((?h0: cE->X.h0 o ce = h) <=> h o f = h o g)")

 
(*∀B f g. f∶ N → B ∧ g∶ one → B ⇒
          (f o z = g  ⇔ ⟨id N,f⟩ o z = ⟨z,g⟩)*)

(*?A B (p1 : NB -> A#)  (p2 : NB -> B). p2 o pa(pN, pB, id(N), f) o z =
               p2 o pa(pN, pB, z, g) & ispr(p1, p2) &
               p1 o pa(pN, pB, id(N), f) o z = p1 o pa(pN, pB, z, g)

TO-DO: ppbug*)


val Thm1_case1_comm_condition_left = proved_th $
e0
(repeat strip_tac >> dimp_tac >> strip_tac
 >-- (drule to_p_eq >> first_x_assum match_mp_tac >> 
      drule p12_of_pa >> arw_tac[GSYM o_assoc,idL]) >>
 drule p2_of_pa >>
 first_assum (specl_then (List.map rastt ["N","id(N)","f:N->B"])
 (assume_tac o GSYM)) >>
 first_assum (specl_then (List.map rastt ["1","ZERO","g:1->B"])
 (assume_tac o GSYM)) >> once_arw_tac[] >> rw_tac[o_assoc] >>
 once_arw_tac[] >> first_assum (accept_tac o GSYM)
 )
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B g:1->B.f o ZERO = g <=> (pa(pN,pB,id(N),f) o ZERO = pa(pN,pB,ZERO,g))")


(*∀B f h. f∶ N → B ∧ h∶ N×B → B ⇒
        (h o ⟨id N,f⟩ = f o s ⇔ ⟨s o p1 N B, h⟩ o ⟨id N, f⟩ = ⟨id N, f⟩ o s)
cannot use different choice of products for two N* B, because of the h.
*)

val Thm1_case1_comm_condition_right = proved_th $
e0
(repeat strip_tac >> dimp_tac >> strip_tac
 >-- (drule to_p_eq >> first_x_assum match_mp_tac >> 
     drule p12_of_pa >> arw[GSYM o_assoc] >> arw[o_assoc,idL,idR]) >>
 drule p2_of_pa >> first_assum (specl_then (List.map rastt ["NB","SUC o (pN:NB->N)","h:NB->B"]) (assume_tac o GSYM)) >> 
first_x_assum (specl_then (List.map rastt ["N","id(N)","f:N->B"]) (assume_tac o GSYM)) >> pop_assum mp_tac >> once_arw_tac[] >> rw_tac[o_assoc] >>
strip_tac >> drule p2_of_pa >> once_arw[] >> rw[o_assoc])
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B h:NB->B. h o pa(pN,pB,id(N),f) = f o SUC <=> pa(pN,pB,SUC o pN,h) o pa(pN,pB,id(N),f) = pa(pN,pB,id(N),f) o SUC")



val Thm1_case1_comm_condition_right' = proved_th $
e0
(repeat strip_tac >> dimp_tac >> strip_tac
 >-- (rev_drule to_p_eq >> first_x_assum match_mp_tac >> 
     rev_drule p12_of_pa >> arw[GSYM o_assoc] >> arw[o_assoc,idL,idR] >>
     drule p1_of_pa >> arw[idR]) >>
 rev_drule p2_of_pa >> first_assum (specl_then (List.map rastt ["NB'","SUC o (pN':NB'->N)","h:NB'->B"]) (assume_tac o GSYM)) >> once_arw[] >> 
 rw[o_assoc] >> once_arw[] >> once_arw[]>> 
first_x_assum (specl_then (List.map rastt ["N","id(N)","f:N->B"]) assume_tac) >>
rw[GSYM o_assoc] >> once_arw[] >> rw[])
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !NB' pN':NB'->N pB':NB'->B. ispr(pN',pB') ==> !f:N->B h:NB'->B. h o pa(pN',pB',id(N),f) = f o SUC <=> pa(pN,pB,SUC o pN',h) o pa(pN',pB',id(N),f) = pa(pN,pB,id(N),f) o SUC")


(* "(f0 o z = g & f0 o s = h o <id(N),f0>) <=> (<id(N),f0> o z = <z,g> & <s o p1(N,B),h> o <id(N),f0> = <id(N),f0> o s)" *)

(*(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B g:1->B.f o z = g <=> (pa(pN,pB,id(N),f) o z = pa(pN,pB,z,g))")

rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B h:NB->B. h o pa(pN,pB,id(N),f) = f o s <=> pa(pN,pB,s o pN,h) o pa(pN,pB,id(N),f) = pa(pN,pB,id(N),f) o s"

*)

(*pa(pN, pB, id(N), f) o z
             =
             pa(pN, pB, z, g)
             &
             f o s
             =
             h o pa(pN, pB, id(N), f)
             <=>
             pa(pN, pB, id(N), f) o z
             =
             pa(pN, pB, z, g)
             &
             pa(pN, pB, (s o pN), h) o pa(pN, pB, id(N), f)
             =
             pa(pN, pB, id(N), f) o s

TO-DO: rw does not do anything to this *)

val Thm1_case1_comm_condition_right'' = 
dimpI
(Thm1_case1_comm_condition_right |> strip_all_and_imp |> dimpl2r 
|> undisch |> prove_hyp (sym (assume (rapf "f o SUC = h o pa(pN:NB->N, pB:NB->B, id(N), f:N->B)"))) |> disch (rapf "f o SUC = h o pa(pN:NB->N, pB:NB->B, id(N), f:N->B)")) 
(Thm1_case1_comm_condition_right |> strip_all_and_imp |> dimpr2l 
|> undisch |> sym |> disch (rapf "pa(pN, pB, (SUC o pN), h:NB->B) o pa(pN, pB, id(N), f) = pa(pN:NB->N, pB:NB->B, id(N), f:N->B) o SUC"))|> gen_all |> disch_all
|> gen_all



val Thm1_case1_comm_condition = proved_th $
e0
(repeat strip_tac >> drule Thm1_case1_comm_condition_left >>
 first_x_assum (specl_then (List.map rastt ["f:N->B","g:1->B"]) assume_tac) >>
 arw[] >> rw_tac[] >> drule Thm1_case1_comm_condition_right'' >>
 first_x_assum (specl_then (List.map rastt ["f:N->B","h:NB->B"]) assume_tac) >>
 arw[])
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B h:NB->B g:1->B. f o ZERO = g & f o SUC = h o pa(pN,pB,id(N),f) <=> pa(pN,pB,id(N),f) o ZERO = pa(pN,pB,ZERO,g) & pa(pN,pB,SUC o pN,h) o pa(pN,pB,id(N),f) = pa(pN,pB,id(N),f) o SUC")


(*∀B g h. g∶ one → B ∧ h∶ po N B → B ⇒
        ∃!f. f∶ N → B ∧ f o z = g ∧ f o s = h o ⟨id N, f⟩*)

val Neqn_zs = constN_def |> 
specl (List.map rastt ["X","x0:1->X","t:X->X","Nind(x0:1->X,t:X->X)"])|> (C dimp_mp_r2l) (refl (rastt "Nind(x0:1->X,t:X->X)"))|> gen_all


val Neqn_z = constN_def |> 
specl (List.map rastt ["X","x0:1->X","t:X->X","Nind(x0:1->X,t:X->X)"])|> (C dimp_mp_r2l) (refl (rastt "Nind(x0:1->X,t:X->X)")) |> conjE1 |> gen_all

val Neqn_s = constN_def |> 
specl (List.map rastt ["X","x0:1->X","t:X->X","Nind(x0:1->X,t:X->X)"])|> (C dimp_mp_r2l) (refl (rastt "Nind(x0:1->X,t:X->X)")) |> conjE2 |> gen_all


(*
last x assume does nothing to 
B , NB ,   
   (f : N -> B),
             (f' : N -> NB),
             (g : 1 -> B),
             (h : NB -> B),
             (pB : NB -> B),
             (pN : NB -> N)
   1.Nind(pa(pN, pB, z, g), pa(pN, pB, s o pN, h)) = f'
   2.pN o f' = id(N)
   3.f' = pa(pN, pB, id(N), f)
   4.f = pB o f'
   5.ispr(pN, pB)
   ----------------------------------------------------------------------
   (pB o f') o z = g
   : gstk
*)

val longf' = rastt "Nind(pa(pN:NB->N,pB:NB->B,ZERO,g:1->B),pa(pN,pB,SUC o pN,h:NB->B))" 

val longf = mk_fun "o" [rastt "pB:NB->B",longf']

val ZERO = mk_fun "ZERO" []

val SUC = mk_fun "SUC" []


val Thm1_case_1 = proved_th $
e0
(repeat strip_tac >> 
 abbrev_tac (rapf "Nind(pa(pN:NB->N,pB:NB->B,ZERO,g:1->B),pa(pN,pB,SUC o pN,h:NB->B)) = f'") >> 
 by_tac (rapf "(pN: NB->N) o (f':N->NB) = id(N)")
 >-- (match_mp_tac (GSYM comm_with_s_id) >> pop_assum (assume_tac o GSYM) >>
      assume_tac
      (Neqn_zs |> specl (List.map rastt ["NB","pa(pN:NB->N, pB:NB->B, SUC o pN, h:NB->B)","pa(pN:NB->N, pB:NB->B, ZERO, g:1->B)"])) >>
      pop_assum strip_assume_tac >> rw_tac[o_assoc] >> 
      arw[] >> drule p1_of_pa >> arw[GSYM o_assoc]) >>
 abbrev_tac (rapf "(pB:NB->B) o (f':N->NB) = f") >>
 exists_tac (rastt "f:N->B") >> 
 by_tac (rapf "f' = pa(pN:NB->N,pB:NB->B,id(N),f:N->B)")
 >-- (drule to_p_eq >> first_x_assum match_mp_tac >>
      drule p12_of_pa >> arw[]) >>
 by_tac (rapf "(f:N->B) o ZERO = g & f o SUC = h o pa(pN:NB->N,pB:NB->B,id(N),f)")
 >-- (suffices_tac (mk_conj (mk_eq (mk_fun "o" [longf,ZERO]) (rastt "g:1->B")) 
                 (mk_eq (mk_fun "o" [longf,SUC]) 
                        (mk_fun "o" [rastt "h:NB->B",mk_fun "pa" ((List.map rastt ["pN:NB->N","pB:NB->B","id(N)"]) @ [longf])])))
      >-- (once_arw[] >> once_arw[] >> disch_tac >> 
          first_x_assum accept_tac) >>
      assume_tac
      (Neqn_zs |> specl (List.map rastt ["NB","pa(pN:NB->N, pB:NB->B, SUC o pN, h:NB->B)","pa(pN:NB->N, pB:NB->B, ZERO, g:1->B)"])) >>
      pop_assum strip_assume_tac >> rw_tac[o_assoc] >>
      once_arw[] >> drule p2_of_pa >> once_arw[] >>
      rw_tac[GSYM o_assoc] >> once_arw[] >> rw[]) >> 
 strip_tac >> dimp_tac >> disch_tac >>
 drule Thm1_case1_comm_condition >> full_simp_tac[] >>
 pop_assum (K all_tac) >> 
 drule to_p_eq_one_side >> first_x_assum match_mp_tac >>
 suffices_tac (mk_eq (rastt "pa(pN:NB->N, pB:NB->B, id(N), f0:N->B)") longf') 
 >-- (once_arw[] >> rw[]) >> 
 match_mp_tac (constN_def |> iffLR) >> once_arw[] >> rw[])
(rapg "!NB pN:NB->N B pB:NB->B. ispr(pN,pB) ==> !g:1->B h:NB->B. ?f:N->B.!f0. (f0 o ZERO = g & f0 o SUC = h o pa(pN,pB,id(N),f0)) <=> f0 = f")



(*∀A B f g. g∶ A → B ∧ f∶ A×N → B ⇒
          (tp f o z = tp (g o (p1 A one)) ⇔
           f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one))*)




val parallel_p_one_side_split = 
 parallel_p_one_side |> strip_all_and_imp
                     |> split_assum |> split_assum |> gen_disch_all |> gen_all

val f0 = rastt "(f:AN->B) o pa(pA:AN->A, pN:AN->N, pA':A1->A, ZERO o (pone:A1->1))"
val f0' = rastt "ev o pa(p1:efs->A,p2:efs->A2B,pA':A1->A,tp(p1,p2,ev:efs->B,pA:AN->A,pN:AN->N,f:AN -> B) o ZERO o (pone:A1->1))"



fun pexistsl_tac l = map_every (exists_tac) (List.map rastt l)

fun pspecl_then l ttac = specl_then (List.map rastt l) ttac

fun pspecl l th = specl (List.map rastt l) th

val Thm1_comm_eq_left = proved_th $
 e0
(repeat strip_tac >> drule exp_ispr >>
 by_tac (rapf "ispr(pA':A1->A, pone:A1->1) & ispr(pA:AN->A, pN:AN->N) & ispr(p1:efs->A, p2:efs->A2B)") >-- arw[] >>
 drule parallel_p_one_side >> 
 first_x_assum (specl_then (List.map rastt ["ZERO","tp(p1:efs->A,p2:efs->A2B,ev:efs->B,pA:AN->A,pN:AN->N,f:AN->B)"]) assume_tac) >> 
 dimp_tac >> strip_tac 
 >-- (by_tac (mk_eq f0 f0') 
      >-- (once_arw[]  >> 
      drule ev_of_tp >> 
      first_x_assum 
       (specl_then ([rastt "AN"]) assume_tac) >> 
      first_x_assum drule >>
      first_x_assum 
       (specl_then (List.map rastt ["f:AN->B"]) (assume_tac o GSYM)) >>
      pop_assum (assume_tac o (fn th => EQ_fsym "o" [th,refl (rastt "pa(pA:AN->A, pN:AN->N, pA':A1->A, ZERO o pone)")])) >>
      once_arw[] >> rw[o_assoc]) >>
      once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >>
      drule ev_of_tp >>
      first_x_assum 
       (specl_then ([rastt "A1"]) assume_tac) >>
      first_x_assum drule >> 
      first_x_assum 
       (specl_then ([rastt "(g:A->B) o (pA':A1->A)"]) accept_tac)) >>
 irule ev_eq_eq >>
 qexistsl_tac ["A","A1","pA':A1->A","pone:A1->1",
              "B","efs","ev:efs->B",
              "p1:efs->A","p2:efs->A2B"]
 (*pexistsl_tac ["A","A1","B","efs","ev:efs->B","p1:efs->A",
               "pA':A1->A","p2:efs->A2B","pone:A1->1"]*) >>
 once_arw[] >> rw[] >>
 drule ev_of_tp >> first_x_assum (pspecl_then ["A1"] assume_tac) >>
 first_x_assum drule >> once_arw[] >>
 rw[o_assoc] >> once_arw[] >> rw[GSYM o_assoc] >> 
 drule ev_of_tp >> 
 first_x_assum (specl_then ([rastt "AN"]) assume_tac) >> 
 first_x_assum drule >>
      first_x_assum 
       (specl_then (List.map rastt ["f:AN->B"]) assume_tac) >>
 once_arw[] >> first_x_assum accept_tac)
(form_goal “!A AN pA:AN->A pN:AN->N. ispr(pA,pN) ==> !A2B B efs p1:efs->A p2:efs->A2B ev:efs->B. isexp(p1,p2,ev) ==> !A1 pA':A1->A pone:A1->1. ispr(pA',pone) ==> !g:A->B f:AN->B.tp(p1,p2,ev,pA,pN,f) o ZERO = tp(p1,p2,ev,pA',pone,g o pA') <=> f o pa(pA,pN,pA',ZERO o pone) = g o pA'”)




fun sym_tac (G,fl,f) = 
    case view_form f of
        vPred("=",[t1,t2]) => 
        ([(G,fl,mk_eq t2 t1)], sing sym)
      | _ => raise ERR ("sym_tac.not an equation",[],[],[f])


val Thm1_comm_eq_right_lemma_short = proved_th $
 e0
(repeat strip_tac >> sym_tac >> irule is_tp >> arw[] >>
 (*split the pa(p1, p2, pA, (tp(p1, p2, ev, pA, pN, f) o s) o pN)*) 
 drule exp_ispr >>
 by_tac 
 “ispr(pA, pN) & ispr(pA:AN->A, pN:AN->N) & ispr(p1:AA2B->A, p2:AA2B->A2B)” >> 
 arw[] >> drule parallel_p_one_side >> 
 first_x_assum (pspecl_then ["SUC","tp(p1:AA2B->A,p2:AA2B->A2B,ev:AA2B->B,pA:AN->A,pN:AN->N,f:AN->B)"] assume_tac) >>
 arw[o_assoc] >> drule ev_of_tp >> first_x_assum rev_drule >>
 arw[GSYM o_assoc])
(rapg "!A B A2B AA2B p1:AA2B->A p2:AA2B->A2B ev:AA2B->B. isexp(p1,p2,ev) ==> !AN pA:AN->A pN:AN->N. ispr(pA,pN) ==> !f:AN->B.tp(p1,p2,ev,pA,pN,f o pa(pA,pN,pA,SUC o pN)) = tp(p1,p2,ev,pA,pN,f) o SUC")



(*(pick_x_assum “ispr(Ap:AP->P, aP:AP->A)” mp_tac) if the input not in the asumption list, then HOL error instead of pick x assum err TODO*)


val Thm1_comm_eq_right_lemma_long = proved_th $ 
e0 
(repeat strip_tac >> pop_assum (assume_tac o sym) >> arw[] >>
 sym_tac >> irule is_tp >> arw[] >>
 pspecl_then ["A","AN","pA:AN->A","AP","Ap:AP->A","AA2B"] assume_tac parallel_p_one_side >>
 drule exp_ispr >>
 by_tac “ispr(pA:AN->A,pN:AN->N) & ispr(Ap:AP->A, aP:AP->P) & ispr(p1:AA2B->A, p2:AA2B->A2B)” >-- arw[] >>
 first_x_assum drule >> 
 arw[o_assoc] >> rw[GSYM o_assoc] >>
 (*(ev o pa(p1, p2, Ap, tp(p1, p2, ev, Ap, aP, (h o l)) o aP)) into h o l*)
 drule ev_of_tp >> first_x_assum (pspecl_then ["AP"] assume_tac) >>
 first_x_assum drule >> arw[] >> rw[o_assoc] >>
 suffices_tac “l o
               pa(Ap:AP->A, aP:AP->P, pA:AN->A,
                pa(Na2b:P->N, nA2B:P->A2B, id(N), tp(p1:AA2B->A, p2:AA2B->A2B, ev:AA2B->B, pA:AN->A, pN:AN->N, f)) o pN) = 
         pa(pAN:ANB->AN, pB:ANB->B, id(AN), f:AN->B)” 
 >-- (strip_tac >> arw[]) >>
 by_tac “ispr(pAN:ANB->AN,pB:ANB->B) & ispr(pA:AN->A,pN:AN->N)”
 >-- arw[] >> 
 drule (iterated_p_eq_applied|> gen_all) >>
 first_x_assum match_mp_tac >>
 by_tac “pAN o pa(pAN:ANB->AN, pB:ANB->B, id(AN), f:AN->B) = id(AN)”
 >-- (match_mp_tac p1_of_pa >> arw[]) >>
 by_tac “pB o pa(pAN:ANB->AN, pB:ANB->B, id(AN), f) = f:AN->B”
 >-- (match_mp_tac p2_of_pa >> arw[]) >>
 arw[] >>
 by_tac 
  “(pAN:ANB->AN) o (l:AP->ANB) = 
   pa(pA:AN->A, pN:AN->N, Ap:AP->A, (Na2b:P->N) o aP) &
    pB o l = ev o pa(p1:AA2B->A, p2:AA2B->A2B, Ap, (nA2B:P->A2B) o (aP:AP->P)) ”
 >-- (pick_assum “pa(pAN:ANB->AN, pB:ANB->B, pa(pA:AN->A, pN:AN->N, Ap:AP->A, (Na2b:P->N) o aP), (ev:AA2B->B) o pa(p1:AA2B->A, p2:AA2B->A2B, Ap:AP->A, (nA2B:P->A2B) o (aP:AP->P))) = l” (assume_tac o GSYM) >>
      once_arw[] >> match_mp_tac p12_of_pa >> first_x_assum accept_tac) >>
 by_tac “(pA:AN->A) o (pAN:ANB->AN) o (l:AP->ANB) = Ap & 
         (pN:AN->N) o pAN o l = (Na2b:P->N) o aP”
 >-- (once_arw[] >> match_mp_tac p12_of_pa >> first_x_assum accept_tac) >>
 rw[GSYM o_assoc,idR] >> 
 by_tac “(pA o pAN) o l = (pA:AN->A) o pAN o (l:AP->ANB) &
         (pN o pAN) o l = (pN:AN->N) o pAN o l”
 >-- rw[o_assoc] >> 
 once_arw[] >> once_arw[] >> rw[o_assoc] >>
 repeat strip_tac (* 3 *)
 >-- (match_mp_tac p1_of_pa >> first_x_assum accept_tac) 
 >-- (pick_x_assum “ispr(Ap:AP->A, aP:AP->P)” mp_tac >>
      strip_tac >> drule p2_of_pa >> once_arw[] >>
      pick_x_assum “ispr(Na2b:P->N, nA2B:P->A2B)” mp_tac >>
      strip_tac >> drule p1_of_pa >> rw[GSYM o_assoc] >>
      once_arw[] >> rw[idL]) >>
 suffices_tac “pa(p1:AA2B->A, p2:AA2B->A2B, Ap:AP->A, ((nA2B:P->A2B) o (aP:AP->P))) o
               pa(Ap, aP, pA:AN->A,
                pa(Na2b:P->N, nA2B, id(N), tp(p1, p2, ev:AA2B->B, pA:AN->A, pN:AN->N, f:AN->B)) o pN) = 
               pa(p1,p2,pA,tp(p1, p2, ev, pA, pN, f) o pN)”
 >-- (strip_tac >> once_arw[] >> drule ev_of_tp >>
      pick_x_assum “ispr(pA:AN->A,pN:AN->N)” assume_tac >>
      first_x_assum drule >> once_arw[] >> rw[]) >>
 irule to_p_eq >> 
 pexistsl_tac ["A","p1 : AA2B ->A","A2B","p2 : AA2B -> A2B"] >>
 drule p12_of_pa >> once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >>
 pick_x_assum “ispr(Ap:AP->A, aP:AP->P)” assume_tac >>
 drule p12_of_pa >> rw[o_assoc] >> once_arw[] >>
 rw[GSYM o_assoc] >> 
 pick_x_assum “ispr(Na2b:P->N, nA2B:P->A2B)” assume_tac >>
 drule p2_of_pa >> once_arw[] >> rw[]
 )
(form_goal
 “!A B A2B AA2B p1:AA2B->A p2:AA2B->A2B ev:AA2B->B. 
      isexp(p1,p2,ev) ==> 
      !AN pA:AN->A pN:AN->N.
          ispr(pA,pN) ==> 
          !ANB pAN:ANB->AN pB:ANB-> B. 
            ispr(pAN,pB) ==>
            !NB Nb:NB->N nB:NB->B.
               ispr(Nb,nB) ==>
 !f:AN->B h:ANB->B abr.
  abr = tp(p1,p2,ev,pA,pN,h o pa(pAN,pB,id(AN),f)) ==>
 !P Na2b:P->N nA2B:P->A2B.
                   ispr(Na2b,nA2B) ==>
 !AP Ap:AP->A aP:AP->P.
                         ispr(Ap,aP) ==>
!l. l = pa(pAN,pB,pa(pA,pN,Ap,Na2b o aP),ev o pa(p1,p2,Ap,nA2B o aP)) ==>
          abr = tp(p1,p2,ev,Ap,aP,h o l) o
        pa(Na2b,nA2B,id(N),tp(p1,p2,ev,pA,pN,f))”)


val Thm1_comm_eq_right_lemma_long' = 
 Thm1_comm_eq_right_lemma_long |> spec_all |> undisch 
 |> spec_all |> undisch |> spec_all |> undisch|> spec_all |> undisch |> 
 pspecl ["f:AN->B","h:ANB->B",
         "tp(p1:AA2B->A, p2:AA2B->A2B, ev:AA2B->B, pA:AN->A, pN:AN->N, (h:ANB->B) o pa(pAN:ANB->AN, pB:ANB->B, id(AN), f:AN->B))"] |>
 undisch |> prove_hyp (refl (rastt "tp(p1:AA2B->A, p2:AA2B->A2B, ev:AA2B->B, pA:AN->A, pN:AN->N, (h:ANB->B) o pa(pAN:ANB->AN, pB:ANB->B, id(AN), f:AN->B))"))
 |> spec_all |> undisch|> spec_all |> undisch

(*))
(form_goal
 “!A B A2B AA2B p1:AA2B->A p2:AA2B->A2B ev:AA2B->B. 
      isexp(p1,p2,ev) ==> 
      !AN pA:AN->A pN:AN->N.
          ispr(pA,pN) ==> 
          !ANB pAN:ANB->AN pB:ANB-> B. 
            ispr(pAN,pB) ==>
            !NB Nb:NB->N nB:NB->B.
               ispr(Nb,nB) ==>
 !P Na2b:P->N nA2B:P->A2B.
                   ispr(Na2b,nA2B) ==>
 !AP Ap:AP->A aP:AP->P.
                         ispr(Ap,aP) ==>
!l. l = pa(pAN,pB,pa(pA,pN,Ap,Na2b o aP),ev o pa(p1,p2,Ap,nA2B o aP)) ==>
!f:AN->B h:ANB->B. tp(p1,p2,ev,pA,pN,h o pa(pAN,pB,id(AN),f)) = tp(p1,p2,ev,Ap,aP,h o l) o
        pa(Na2b,nA2B,id(N),tp(p1,p2,ev,pA,pN,f))”)
*)

val Thm1_comm_eq_right = proved_th $
e0
(repeat strip_tac >> assume_tac Thm1_comm_eq_right_lemma_long' >>
 first_x_assum drule >> 
 pop_assum mp_tac >> pop_assum (K all_tac) >> 
 strip_tac >>
 assume_tac (Thm1_comm_eq_right_lemma_short |> strip_all_and_imp) >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (full_simp_tac[]) >>
 match_mp_tac (gen_all tp_eq) >>
 pexistsl_tac ["A","A2B","pA:AN->A","N","pN:AN->N","AA2B","ev:AA2B->B",
               "p1:AA2B->A","p2:AA2B->A2B"] >>
 arw[])
(form_goal 
“!A B A2B AA2B p1:AA2B->A p2:AA2B->A2B ev:AA2B->B. 
      isexp(p1,p2,ev) ==> 
      !AN pA:AN->A pN:AN->N.
          ispr(pA,pN) ==> 
          !ANB pAN:ANB->AN pB:ANB-> B. 
            ispr(pAN,pB) ==>
            !NB Nb:NB->N nB:NB->B.
               ispr(Nb,nB) ==>
 !P Na2b:P->N nA2B:P->A2B.
                   ispr(Na2b,nA2B) ==>
 !AP Ap:AP->A aP:AP->P.
                         ispr(Ap,aP) ==>
!l. l = pa(pAN,pB,pa(pA,pN,Ap,Na2b o aP),ev o pa(p1,p2,Ap,nA2B o aP)) ==>
 !f:AN->B h:ANB->B.
 h o pa(pAN,pB,id(AN),f) = f o pa(pA,pN,pA,SUC o pN) <=>
 tp(p1,p2,ev,Ap,aP,h o l) o pa(Na2b,nA2B,id(N),tp(p1,p2,ev,pA,pN,f)) = 
 tp(p1,p2,ev,pA,pN,f) o SUC”
)


val Thm1_comm_eq_left' = 
 Thm1_comm_eq_left |> spec_all |> undisch 
 |> pspecl ["A2B","B","AA2B"]|> strip_all_and_imp |> GSYM

fun disch_first th = disch (List.hd (ant th)) th
fun disch_last th = disch (List.hd (rev $ ant th)) th

fun disch_nth n th = disch (List.nth (rev $ ant th,n)) th

val Thm1_comm_eq_condition = proved_th $
e0
(repeat strip_tac >> assume_tac Thm1_comm_eq_left' >>
 assume_tac
  (Thm1_comm_eq_right |> strip_all_and_imp |> disch_last 
             |> allI ("l",mk_ar_sort (mk_ob "AP") (mk_ob "ANB"))) >>
 once_arw[] >> dimp_tac >> strip_tac >> once_arw[] >> rw[] 
 >-- (repeat strip_tac >> first_x_assum drule >> full_simp_tac[]) >>
 last_x_assum (pspecl_then ["pa(pAN:ANB->AN,pB:ANB->B,pa(pA:AN->A,pN:AN->N,Ap:AP->A,(Na2b:P->N) o (aP:AP->P)),(ev:AA2B->B) o pa(p1:AA2B->A,p2:AA2B->A2B,Ap,nA2B o aP))"] assume_tac) >> full_simp_tac[] >>
 assume_tac (refl (rastt "pa(pAN:ANB->AN,pB:ANB->B,pa(pA:AN->A,pN:AN->N,Ap:AP->A,(Na2b:P->N) o (aP:AP->P)),(ev:AA2B->B) o pa(p1:AA2B->A,p2:AA2B->A2B,Ap,nA2B o aP))")) >>
 first_x_assum drule >> first_x_assum accept_tac
)
(form_goal 
“!A B A2B AA2B p1:AA2B->A p2:AA2B->A2B ev:AA2B->B. 
      isexp(p1,p2,ev) ==> 
      !AN pA:AN->A pN:AN->N.
          ispr(pA,pN) ==> 
          !ANB pAN:ANB->AN pB:ANB-> B. 
            ispr(pAN,pB) ==>
            !NB Nb:NB->N nB:NB->B.
               ispr(Nb,nB) ==>
 !P Na2b:P->N nA2B:P->A2B.
                   ispr(Na2b,nA2B) ==>
 !AP Ap:AP->A aP:AP->P.
                         ispr(Ap,aP) ==>
!A1 pA':A1 -> A  pone : A1 -> 1. ispr(pA', pone) ==> 
 !f:AN->B g:A->B h:ANB->B.
   f o pa(pA, pN, pA', ZERO o pone) = g o pA' & 
   h o pa(pAN,pB,id(AN),f) = f o pa(pA,pN,pA,SUC o pN) <=>
(tp(p1, p2, ev, pA, pN, f) o ZERO =
tp(p1, p2, ev, pA', pone, g o pA') &
(!l. l = pa(pAN,pB,pa(pA,pN,Ap,Na2b o aP),ev o pa(p1,p2,Ap,nA2B o aP)) ==>
 tp(p1,p2,ev,Ap,aP,h o l) o pa(Na2b,nA2B,id(N),tp(p1,p2,ev,pA,pN,f)) = 
 tp(p1,p2,ev,pA,pN,f) o SUC))”)

fun pick_nth_assum n ttac = fn (ct,asl, w) => ttac (assume (List.nth(rev asl,Int.-(n,1)))) (ct,asl, w)

fun undisch_then f (ttac:thm_tactic): tactic = fn (ct,asl, w) =>
      let val (_, A) = Lib.pluck ((curry eq_form) f) asl in ttac (assume f) (ct,A, w) end

local
    fun f ttac th = undisch_then (concl th) ttac
in
fun pick_xnth_assum n = (pick_nth_assum n) o f
end


val Thm1 = proved_th $
 e0
(repeat strip_tac >> 
 x_choosel_then ["A2B","AA2B","p1","p2","ev"] assume_tac (spec_all exp_ex) >>
 drule Thm1_comm_eq_condition >> first_x_assum rev_drule >> 
 first_x_assum (pspecl_then ["ANB","pAN:ANB->AN","pB:ANB->B"] assume_tac) >>
 first_x_assum drule >>
 x_choosel_then ["NB","Nb","nB"] assume_tac (pr_ex |> pspecl ["N","B"]) >>
 first_x_assum drule >>
 x_choosel_then ["P","Na2b","nA2B"] assume_tac (pr_ex |> pspecl ["N","A2B"]) >>
 first_x_assum drule >>
 x_choosel_then ["AP","Ap","aP"] assume_tac (pr_ex |> pspecl ["A","P"]) >>
 first_x_assum drule >> 
 first_x_assum drule >> once_arw[] >> pop_assum (K all_tac) >>
 drule Thm1_case_1 >>
 abbrev_tac “pa(pAN:ANB->AN,pB:ANB->B,pa(pA:AN->A,pN:AN->N,Ap:AP->A,(Na2b:P->N) o (aP:AP->P)),(ev:AA2B->B) o pa(p1:AA2B->A,p2:AA2B->A2B,Ap,nA2B o aP)) = l” >>
 pop_assum (assume_tac o GSYM) >>
 x_choose_then "fb" assume_tac 
 (Thm1_case_1 |> pspecl ["P","Na2b:P->N","A2B","nA2B:P->A2B"]
  |> undisch |> pspecl ["tp(p1:AA2B->A,p2:AA2B->A2B,ev:AA2B->B,pA':A1->A,pone:A1->1,(g:A->B) o pA')","tp(p1:AA2B->A,p2:AA2B->A2B,ev:AA2B->B,Ap:AP->A,aP:AP->P,(h:ANB->B) o (l:AP->ANB))"]) >> 
 pexistsl_tac ["(ev:AA2B->B) o pa(p1:AA2B->A,p2:AA2B->A2B,pA:AN->A,(fb:N->A2B) o (pN:AN->N))"] >>
 abbrev_tac “(ev:AA2B->B) o pa(p1:AA2B->A,p2:AA2B->A2B,pA:AN->A,(fb:N->A2B) o (pN:AN->N)) = f” >>
 by_tac “tp(p1:AA2B->A,p2:AA2B->A2B,ev:AA2B->B,pA:AN->A,pN:AN->N,f:AN->B) = fb”
 >-- (sym_tac >> irule is_tp >> once_arw[] >> rw[]) >>
 strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (once_arw[] >> match_mp_tac (gen_all tp_eq) >>
      pexistsl_tac ["A","A2B","pA:AN->A","N","pN:AN->N",
                    "AA2B","ev:AA2B->B","p1:AA2B->A","p2:AA2B->A2B"] >>
      once_arw[] >> rw[] >> first_x_assum drule  >>
      pick_xnth_assum 10 (assume_tac o GSYM) >>
      once_arw[] >> strip_tac >-- first_x_assum accept_tac
      >-- first_x_assum (accept_tac o GSYM)) >>
 suffices_tac
 “tp(p1:AA2B->A, p2:AA2B->A2B, ev:AA2B->B, pA:AN->A, pN:AN->N, f':AN->B) o ZERO = tp(p1, p2, ev, pA':A1->A, pone:A1->1, (g:A->B) o pA') & 
  tp(p1, p2, ev, pA, pN, f') o SUC = 
  tp(p1, p2, ev, Ap:AP->A, aP:AP->P, ((h:ANB->B) o (l:AP->ANB))) o pa(Na2b, nA2B, id(N), tp(p1, p2, ev, pA, pN, f'))” 
 >-- (strip_tac >> once_arw[] >> rw[] >> repeat strip_tac >>
     by_tac “l' = l:AP->ANB” >-- (once_arw[] >> rw[]) >>
     pick_xnth_assum 15 mp_tac >> pop_assum mp_tac >> 
     pop_assum_list (map_every (K all_tac)) >>
     repeat strip_tac >> rev_full_simp_tac[]) >>
 once_arw[] >> sym_tac >> irule is_tp >>
 once_arw[] >> once_arw[] >> rw[])
(form_goal
 “!A AN pA:AN->A pN:AN->N.
  ispr(pA,pN) ==> 
  !ANB B pAN:ANB->AN pB:ANB-> B. 
  ispr(pAN,pB) ==>
  !A1 pA':A1 -> A pone:A1 -> 1. ispr(pA', pone) ==> 
  !g:A->B h:ANB->B.
  ?f:AN->B. !f'. (f' o pa(pA,pN,pA',ZERO o pone) = g o pA' &
            h o pa(pAN,pB,id(AN),f') = f' o pa(pA,pN,pA,SUC o pN)) <=> f' = f”)

(*∃p. p∶ N → N ∧ p o z = z ∧ p o s = id N*)

val pred_exists = proved_th $
e0
(x_choosel_then ["NN","p1","p2"] assume_tac (pr_ex |> pspecl ["N","N"]) >>
 drule Thm1_case_1 >> 
 first_x_assum (pspecl_then ["ZERO","p1:NN->N"] assume_tac) >>
 first_x_assum (x_choose_then "p" assume_tac) >> 
 pexistsl_tac ["p:N->N"] >>
 first_x_assum (pspecl_then ["p:N->N"] assume_tac) >>
 drule p1_of_pa >> full_simp_tac[])
(form_goal “?p:N->N. p o ZERO = ZERO & p o SUC = id(N)”)

(*∀n. n∶ one → N ⇒ (s o n) ≠ z*)

(*TO-DO, may AQ, ~!X (e1 : X# -> X#)  (e1 : X# -> X#). ~~e1# = e1#: thm elim the double neg

rapf' "~!X e1 : X -> X  e2 : X -> X. ~~e1 = e2" basic_fconv can do it

*)


val distinct_endo_exists' = 
 distinct_endo_exists |>
 rewr_rule[exists_forall ("X",mk_ob_sort),
 exists_forall ("e1",mk_ar_sort (mk_ob "X") (mk_ob "X"))] |> neg_neg_elim
 |> eqF_intro |> dimpl2r


val Thm2_1 = proved_th $
e0
(strip_tac >> ccontra_tac >> match_mp_tac distinct_endo_exists' >>
 repeat strip_tac >> rw[] >> 
 strip_assume_tac pred_exists >>
 by_tac “SUC o ZERO = ZERO”
 >-- (by_tac “p o SUC o n = (p:N->N) o ZERO” 
      >-- arw[] >>
      pop_assum mp_tac >> rw[GSYM o_assoc]>> arw[idL] >> 
      strip_tac >> full_simp_tac[]) >>
 suffices_tac “e1 = id(X) & e1'= id(X)”
 >-- (strip_tac >> arw[]) >> strip_tac >> match_mp_tac fun_ext >>
 strip_tac >> rw[idL]
 >-- (strip_assume_tac 
     (Neqn_zs |> pspecl ["X","e1:X->X","a:1->X"] |> GSYM) >>
     once_arw[] >> rw[GSYM o_assoc] >>
     suffices_tac “(Nind(a, e1) o SUC)  o ZERO = Nind(a:1->X, e1:X->X) o ZERO”
     >-- (strip_tac >> pick_xnth_assum 5 mp_tac >> rev_full_simp_tac[]) >>
     rw[o_assoc] >> once_arw[] >> rw[]
     ) >>
strip_assume_tac 
 (Neqn_zs |> pspecl ["X","e1':X->X","a:1->X"] |> GSYM) >>
     once_arw[] >> rw[GSYM o_assoc] >>
     suffices_tac “(Nind(a, e1') o SUC)  o ZERO = Nind(a:1->X, e1':X->X) o ZERO”
     >-- (strip_tac >> pick_xnth_assum 5 mp_tac >> rev_full_simp_tac[]) >>
     rw[o_assoc] >> once_arw[] >> rw[]
 )
(form_goal “!n:1->N. ~ (SUC o n = ZERO)”)

(*is_mono s*)

val Thm2_2 = proved_th $
e0
(match_mp_tac post_inv_mono >> strip_assume_tac pred_exists >>
 pexistsl_tac ["p:N->N"] >> arw[])
(form_goal “ismono(SUC)”)

(*∀A a s' z'. a∶ A → N ∧ is_mono a ∧ s'∶ A → A ∧ z'∶ one → A ∧
            a o s' = s o a ∧ a o z' = z ⇒ A ≅ N*)



val Thm2_3_alt = proved_th $ 
e0
(rpt strip_tac >> 
 strip_assume_tac (Neqn_zs |> pspecl ["A","s':A->A","z':1->A"]) >>
 rw[areiso_isiso] >> pexistsl_tac ["a:A->N"] >> 
 match_mp_tac mono_epi_is_iso >> arw[] >> 
 match_mp_tac pre_inv_epi >> pexistsl_tac ["Nind(z':1->A,s':A->A)"] >>
 sym_tac >>
 match_mp_tac comm_with_s_id >> arw[o_assoc] >> rw[GSYM o_assoc] >>
 once_arw[] >> rw[])
(form_goal 
“!A a:A->N. ismono(a) ==> 
  !s':A->A z':1->A. (a o s' = SUC o a & a o z' = ZERO ==> areiso(A,N))”)

val Thm2_3_alt' = proved_th $ 
e0
(rpt strip_tac >> 
 strip_assume_tac (Neqn_zs |> pspecl ["A","s':A->A","z':1->A"]) >>
 match_mp_tac mono_epi_is_iso >> arw[] >> 
 match_mp_tac pre_inv_epi >> pexistsl_tac ["Nind(z':1->A,s':A->A)"] >>
 sym_tac >>
 match_mp_tac comm_with_s_id >> arw[o_assoc] >> rw[GSYM o_assoc] >>
 once_arw[] >> rw[])
(form_goal 
“!A a:A->N. ismono(a) ==> 
  !s':A->A z':1->A. (a o s' = SUC o a & a o z' = ZERO ==> isiso(a))”)
(*Thm2_3_alt/' slow*)

(*∀A a. a∶ A → N ∧ is_mono a ∧ (∀n. is_mem n a N ⇒ is_mem (s ∘ n) a N) ⇒
        ∃t. t∶ A → A ∧ a o t = s o a*)

val ind_fac = proved_th $
 e0
(rpt strip_tac >> 
 strip_assume_tac (pb_exists |> pspecl ["A","N","SUC o (a:A->N)","A","a:A->N"]) >>
 drule pb_equality >>
 suffices_tac “isiso(p:P->A)”
 >-- (rw[isiso_def] >> strip_tac >> pexistsl_tac ["(q:P->A) o (f':A->P)"] >>
      pick_xnth_assum 4 (assume_tac o GSYM) >> arw[GSYM o_assoc] >>
      arw[o_assoc,idR]) >>
 match_mp_tac mono_epi_is_iso >> strip_tac
 >-- (drule pb_mono_mono >> first_x_assum drule >> first_x_assum accept_tac) >>
 match_mp_tac surj_is_epi >> strip_tac >> 
 by_tac “ismem(SUC o (a:A->N) o (b:1->A),a)”
 >-- (first_x_assum match_mp_tac >> arw[ismem_def] >>
      pexistsl_tac ["b:1->A"] >> rw[]) >>
 full_simp_tac[ismem_def] >> pop_assum (assume_tac o GSYM) >> 
 rev_drule (ispb_def_alt' |> iffLR) >> 
 pop_assum strip_assume_tac >> full_simp_tac[GSYM o_assoc] >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 pexistsl_tac ["a':1->P"] >> arw[])
(form_goal “!A a:A->N. ismono(a) ==> (!n:1->N. ismem(n,a) ==> ismem(SUC o n,a)) ==>
 ?t:A->A. a o t = SUC o a”)

(*Theorem Thm2_3:        
∀A a. is_subset a N ∧ (∀n. is_mem n a N ⇒ is_mem (s o n) a N) ∧
    is_mem z a A ⇒ dom a ≅ N
*)

val Thm2_3 = proved_th $
e0
(repeat strip_tac >> irule Thm2_3_alt >> 
 drule ind_fac >> first_x_assum drule >> pop_assum strip_assume_tac >>
 full_simp_tac[ismem_def] >> 
 pexistsl_tac ["a:A->N","t:A->A","x0:1->A"] >> arw[])
(form_goal “!A a:A->N. (ismono(a) & (!n:1->N. ismem(n,a) ==> ismem(SUC o n,a)) & ismem(ZERO,a)) ==>
           areiso(A,N)”)

val Thm2_3' = proved_th $
                        e0
                        (repeat strip_tac >> irule Thm2_3_alt' >> 
                                drule ind_fac >> first_x_assum drule >> pop_assum strip_assume_tac >>
                                full_simp_tac[ismem_def] >> strip_tac
                                >-- (qexistsl_tac ["x0"] >> arw[]) >>
                                qexistsl_tac ["t"] >> arw[])
                        (form_goal “!A a:A->N. (ismono(a) & (!n:1->N. ismem(n,a) ==> ismem(SUC o n,a)) & ismem(ZERO,a)) ==> isiso(a)”)


(*MaybeTODO: machinary of prove isN from areiso(A,0)*)
(*?C P PQ Q (pC : ANB -> C#)  (pP : PQ -> P)  (pPQ : ANB -> PQ)
               (pQ : PQ -> Q). pC o l o
                 pa(Ap, aP, pA,
                  pa(Na2b, nA2B, id(N), tp(p1, p2, ev, pA, pN, f)) o pN) =
               pC o pa(pAN, pB, id(AN), f) & ispr(pPQ, pC) & ispr(pP, pQ) &
               pP o pPQ o l o
                 pa(Ap, aP, pA,
                  pa(Na2b, nA2B, id(N), tp(p1

TO-DO: huge ppbug!*)

val coeq_of_equal_post_inv = proved_th $
e0
(rpt strip_tac >> 
 drule coeqind_def >> pop_assum strip_assume_tac >>
 by_tac “id(B) o f = id(B) o (f:A->B)” >-- rw[] >> first_x_assum drule >>
 pexistsl_tac ["coeqind(e:B->cE, f, f:A->B, id(B))"] >>
 arw[])
(form_goal 
“!f:A->B cE e:B->cE. iscoeq(e,f,f) ==> 
 ?e':cE->B. e' o e = id(B)”)

val fs = full_simp_tac
val rfs = rev_full_simp_tac

val Thm3_A_zero_I_zero = proved_th $
e0
(rpt strip_tac >> rw[iso_zero_is_zero] >> ccontra_tac >> drule ax6 >>
 first_x_assum (x_choose_then "t" assume_tac) >> drule i1_i2_disjoint >>
 suffices_tac “(i1:B->BB) o (q':I0->B) o (t:1->I0) = (i2:B->BB) o (q':I0->B) o (t:1->I0)” 
 >-- arw[] >>
 by_tac “i1 o f = (i2:B->BB) o (f:A->B)”
 >-- (match_mp_tac from_iso_zero_eq >> arw[]) >>
 by_tac “iscoeq(k':BB->R', (i2:B->BB) o (f:A->B), i2 o f)” >-- fs[] >>
 drule coeq_of_equal_post_inv >> 
 first_x_assum (x_choose_then "k''" assume_tac) >>
 drule eq_equality >>
 suffices_tac “k'' o (k' o i1) o q' o t = (k'':R'->BB) o (k' o (i2:B->BB)) o q' o (t:1->I0)” 
 >-- (rw[GSYM o_assoc] >> once_arw[] >> rw[idL]) >>
 by_tac “k'' o (k' o i1) o q' o t = (k'':R'->BB) o ((k' o (i1:B->BB)) o q') o (t:1->I0) & 
         k'' o (k' o i2) o q' o t = (k'':R'->BB) o ((k' o (i2:B->BB)) o q') o (t:1->I0)”
 >-- rw[o_assoc] >>
 once_arw[] >> once_arw[] >> rw[]
 )
(form_goal 
“!A B f:A->B. areiso(A,0) ==> 
 !BB i1:B->BB i2:B->BB. iscopr(i1,i2) ==>
 !R' k':BB->R'. iscoeq(k',i1 o f,i2 o f) ==>
 !I0 q':I0->B. iseq(q',k' o i1, k' o i2) ==> areiso(I0,0) 
”)

(*
qabbrev_tac ‘I' = (coeqo ((p1 A A) o (eqa (f o p1 A A) (f o p2 A A)))
                  ((p2 A A) o (eqa (f o p1 A A) (f o p2 A A))))’ >>
qabbrev_tac ‘I0 = (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B)))’ >>
qabbrev_tac ‘k = eqa (f o p1 A A) (f o p2 A A)’ >>
qabbrev_tac ‘k' = coeqa (i1 B B o f) (i2 B B o f)’ >>
qabbrev_tac ‘q = coeqa (p1 A A o k) (p2 A A o k)’ >>
qabbrev_tac ‘q' = eqa (k' o i1 B B) (k' o i2 B B)’ >>
qabbrev_tac ‘R = eqo (f o (p1 A A)) (f o (p2 A A))’ >>
qabbrev_tac ‘R' = coeqo ((i1 B B) o f) ((i2 B B) o f)’

∀A B f h. f∶ A → B ∧ A≅ zero ∧
          h∶ (coeqo ((p1 A A) o k)
                    ((p2 A A) o k)) →
             (eqo (k' o (i1 B B))
                  (k' o (i2 B B))) ∧
          (eqa (k' o (i1 B B))
               (k' o (i2 B B))) o h o
          (coeqa (p1 A A o k)
                 (p2 A A o k))  = f ⇒
          is_iso h  
*)

val Thm3_case_zero = proved_th $ 
e0
(rpt strip_tac >> match_mp_tac to_iso_zero_iso >> drule Thm3_A_zero_I_zero >>
 first_x_assum drule >> first_x_assum drule >>first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal 
“!A B f:A->B. areiso(A,0) ==> 
 !BB i1:B->BB i2:B->BB. iscopr(i1,i2) ==>
 !R' k':BB->R'. iscoeq(k',i1 o f,i2 o f) ==>
 !I0 q':I0->B. iseq(q',k' o i1, k' o i2) ==>
 !AA p1:AA->A p2:AA->A. ispr(p1,p2) ==>
 !R k:R->AA. iseq(k,f o p1,f o p2) ==>
 !I' q:A->I'.iscoeq(q,p1 o k, p2 o k) ==>
 !h:I' ->I0. q' o h o q = f ==> isiso(h)”)



val Thm3_case_non_zero = proved_th $ 
e0
(rpt strip_tac >> match_mp_tac mono_epi_is_iso >>
 drule eqa_is_mono >> rev_drule eqa_is_mono >>
 drule coeqa_is_epi >> rev_drule coeqa_is_epi >> 
 by_tac “~(areiso(I0,0))”
 >-- (ccontra_tac >> suffices_tac “areiso(A,0)” >-- arw[] >>
      match_mp_tac to_zero_zero >> pexistsl_tac ["I0","(h:I'->I0) o (q:A->I')"] >>
      arw[]) >>
 strip_tac  (* 2 *)
 >-- (suffices_tac “ismono((q':I0->B) o h:I'->I0)” 
      >-- (strip_tac >> drule o_mono_imp_mono >> first_x_assum accept_tac) >>
      by_tac “?t.(q:A->I') o t = id(I')”
      >-- (irule epi_non_zero_pre_inv >>
           fs[iso_zero_is_zero]) >>
      pop_assum strip_assume_tac >>
      match_mp_tac ismono_applied >> rpt strip_tac >>
      by_tac
     “?w. (k:R->AA) o w = pa(p1:AA->A,p2:AA->A,(t:I'->A) o (h':X->I'), t o g)”
      >-- (drule
           (fac_through_eq_iff |> undisch|> gen_disch_all |> gen_all |> iffRL) >>
           first_x_assum match_mp_tac >>
           rw[o_assoc] >> drule p12_of_pa >> arw[] >>
           pick_xnth_assum 8 (assume_tac o GSYM) >> once_arw[] >>
           by_tac “(q':I0->B o h:I'->I0 o q:A->I') o t:I'->A o h':X->I' =
                    q' o h o (q o t) o h' & 
            (q' o h o q) o t o g = q' o h o (q o t) o (g:X->I')”
           >-- rw[o_assoc] >> arw[idL] >> fs[o_assoc]) >>
     pop_assum strip_assume_tac >> 
     suffices_tac “q:A->I' o p1:AA->A o pa(p1,p2:AA->A,t:I'->A o h', t o g:X->I')= h':X->I'  &
                   q o p2 o pa(p1,p2,t o h', t o g) = g &
                   q o p1 o pa(p1,p2,t o h', t o g) = 
                   q o p2 o pa(p1,p2,t o h', t o g)”
     >-- (strip_tac >> arw[] >> rfs[]) >> rpt strip_tac  (* 3 *)
     >-- (drule p12_of_pa >> arw[] >> arw[GSYM o_assoc,idL])
     >-- (drule p12_of_pa >> arw[] >> arw[GSYM o_assoc,idL]) >>
     pop_assum (assume_tac o GSYM) >> once_arw[] >>
     suffices_tac “(q:A->I' o p1:AA->A o k:R->AA) o w:X->R = (q o p2 o k) o w”
     >-- rw[o_assoc] >>
     drule coeq_equality >> arw[]
     ) >>
suffices_tac “isepi (h:I'->I0 o q:A->I')”
>-- (strip_tac >> drule o_epi_imp_epi >> first_x_assum accept_tac) >>
match_mp_tac isepi_applied >> rpt strip_tac >>
drule mono_non_zero_post_inv >> fs[iso_zero_is_zero] >>
first_x_assum drule >> 
pop_assum (x_choose_then "qi" assume_tac) >>
by_tac “?w.w o k':BB->R' = copa (i1:B->BB,i2:B->BB,f':I0->X o qi:B->I0,g o qi)”
>-- (rev_drule
           (fac_through_coeq_iff |> undisch|> gen_disch_all |> gen_all |> iffRL) >>
     first_x_assum match_mp_tac >> 
     drule i12_of_copa >> arw[GSYM o_assoc] >>
     pick_xnth_assum 8 (assume_tac o GSYM) >>
     arw[] >>
     suffices_tac 
     “(f' o qi) o q' o h o q = f':I0->X o (qi:B->I0 o q':I0->B) o h:I'->I0 o q:A->I' &
      (g o qi) o q' o h o q =  g:I0->X o (qi o q') o h o q”
     >-- (strip_tac >> arw[idL]) >>
     rw[o_assoc]) >>
pop_assum strip_assume_tac >>
suffices_tac
“copa(i1:B->BB,i2:B->BB,f':I0->X o qi:B->I0,g:I0->X o qi:B->I0) o i1 o q':I0->B = f' &
 copa(i1,i2,f' o qi,g o qi) o i2 o q' = g:I0->X &
 copa(i1,i2,f' o qi,g o qi) o i1 o q' = 
 copa(i1,i2,f' o qi,g o qi) o i2 o q'”
>-- (strip_tac >> arw[] >> rfs[]) >> repeat strip_tac (* 3 *)
>-- (rw[GSYM o_assoc] >> drule i12_of_copa >> arw[] >>
     arw[o_assoc,idR])
>-- (rw[GSYM o_assoc] >> drule i12_of_copa >> arw[] >>
     arw[o_assoc,idR]) >>
pop_assum (assume_tac o GSYM) >> once_arw[] >>
rw[o_assoc] >> rev_drule eq_equality >> fs[o_assoc] >> arw[]
 )
(form_goal 
“!A B f:A->B. (~areiso(A,0)) ==> 
 !BB i1:B->BB i2:B->BB. iscopr(i1,i2) ==>
 !R' k':BB->R'. iscoeq(k',i1 o f,i2 o f) ==>
 !I0 q':I0->B. iseq(q',k' o i1, k' o i2) ==>
 !AA p1:AA->A p2:AA->A. ispr(p1,p2) ==>
 !R k:R->AA. iseq(k,f o p1,f o p2) ==>
 !I' q:A->I'.iscoeq(q,p1 o k, p2 o k) ==>
 !h:I' ->I0. q' o h o q = f ==> isiso(h)”)

(*Theorem unique_h_lemma:
∀A B C D f g q k h. f∶ A → B ∧ g∶D → B ∧ q∶ A → C ∧  
              (∀k'. (k'∶ A→ D ∧ g o k' = f) ⇔ k' = k) ∧
              (∀h'. (h'∶ C → D ∧ h' o q = k) ⇔ h' = h) ⇒
              ∃!h. h∶ C → D ∧ g o h o q = f
Proof
rw[EXISTS_UNIQUE_ALT] >> qexists_tac ‘h’ >> rw[EQ_IMP_THM] >>
metis_tac[compose_assoc,compose_hom]
QED*)

val unique_h_lemma = proved_th $
e0
(rpt strip_tac >> pexistsl_tac ["h:C->D"] >> strip_tac >>
 dimp_tac >> strip_tac >> rfs[])
(form_goal 
“!A B f:A->B C q:A->C D g:D->B k:A->D h:C->D.
 (!k'. g o k' = f <=> k' = k) &
 (!h'. h' o q = k <=> h' = h) ==>
 (?h:C->D. !h0. g o h0 o q = f <=> h0 = h)”)

(*
Theorem Thm3_h_exists:
∀A B f.
         f∶A → B ⇒
       ∃!h.  h∶coeqo (p1 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A))
           (p2 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A)) →
         eqo (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i1 B B)
           (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i2 B B) ∧
         eqa (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i1 B B)
           (coeqa (i1 B B ∘ f) (i2 B B ∘ f) ∘ i2 B B) ∘ h ∘
         coeqa (p1 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A))
           (p2 A A ∘ eqa (f ∘ p1 A A) (f ∘ p2 A A)) =
         f
*)


val Thm3_h_exists = proved_th $
e0
(rpt strip_tac >> match_mp_tac unique_h_lemma >>
 pexistsl_tac
 ["eqind(q':I0->B,k':BB->R' o i1:B->BB,k' o i2:B->BB,f:A->B)",
 "coeqind(q:A->I',p1:AA->A o k:R->AA,p2:AA->A o k,eqind(q':I0->B,k':BB->R' o i1:B->BB,k' o i2:B->BB,f:A->B))"] >>
 rev_drule eqind_def >> drule coeqind_def >> 
 pop_assum_list (map_every strip_assume_tac) >>
 strip_tac 
 >-- (first_x_assum match_mp_tac >> drule coeq_equality >> fs[o_assoc]) >>
 first_x_assum match_mp_tac >> 
 drule eqa_is_mono >> drule ismono_property >>
 first_x_assum match_mp_tac >> 
 suffices_tac “q' o eqind(q':I0->B, (k' o i1:B->BB), (k':BB->R' o i2:B->BB), f) = f:A->B”
 >-- (strip_tac >> arw[GSYM o_assoc] >> rev_drule eq_equality >> arw[]) >>
 drule eqind_def >> pop_assum strip_assume_tac >>
 first_x_assum (pspecl_then ["A","f:A->B"] assume_tac) >>
 drule coeq_equality >> fs[o_assoc] >> first_x_assum drule)
(form_goal 
“!A B f:A->B.
 !BB i1:B->BB i2:B->BB. iscopr(i1,i2) ==>
 !R' k':BB->R'. iscoeq(k',i1 o f,i2 o f) ==>
 !I0 q':I0->B. iseq(q',k' o i1, k' o i2) ==>
 !AA p1:AA->A p2:AA->A. ispr(p1,p2) ==>
 !R k:R->AA. iseq(k,f o p1,f o p2) ==>
 !I' q:A->I'.iscoeq(q,p1 o k, p2 o k) ==>
 ?h:I' ->I0.!h0. q' o h0 o q = f <=> h0 = h”)

val Thm3_without_assume_exists = proved_th $
e0
(rpt strip_tac >> assume_tac (Thm3_h_exists |> strip_all_and_imp) >>
 pop_assum strip_assume_tac >> pexistsl_tac ["h:I'->I0"] >> 
 by_tac “q':I0->B o h o q:A->I' = f” >-- arw[] >> 
 cases_on “areiso(A,0)”
 >-- (assume_tac 
      (Thm3_case_zero |> strip_all_and_imp |> disch_last|> gen_all)>>
     first_x_assum drule >> strip_tac >> dimp_tac >> strip_tac >> rfs[]) >>
 assume_tac 
      (Thm3_case_non_zero |> strip_all_and_imp |> disch_last|> gen_all)>>
     first_x_assum drule >> strip_tac >> dimp_tac >> strip_tac >> rfs[]
 )
(form_goal 
“!A B f:A->B.
 !BB i1:B->BB i2:B->BB. iscopr(i1,i2) ==>
 !R' k':BB->R'. iscoeq(k',i1 o f,i2 o f) ==>
 !I0 q':I0->B. iseq(q',k' o i1, k' o i2) ==>
 !AA p1:AA->A p2:AA->A. ispr(p1,p2) ==>
 !R k:R->AA. iseq(k,f o p1,f o p2) ==>
 !I' q:A->I'.iscoeq(q,p1 o k, p2 o k) ==>
 ?h:I' ->I0.!h0. q' o h0 o q = f & isiso(h0) <=> h0 = h”)

(*∀f A B. f∶ A → B ⇒ ∃X m e. e∶ A → X ∧ m∶ X → B ∧ is_epi e ∧ is_mono m ∧ f = m o e*)

val mono_epi_fac = proved_th $
e0
(rpt strip_tac >> 
 x_choosel_then ["BB","i1","i2"] assume_tac 
 (copr_ex|> pspecl ["B","B"]) >> 
 x_choosel_then ["R'","k'"] assume_tac 
 (coeq_ex|> pspecl ["A","BB","i1:B->BB o f:A->B","i2:B->BB o f:A->B"]) >>
 x_choosel_then ["I0","q'"] assume_tac 
 (eq_ex|> pspecl ["B","R'","k':BB->R' o i1:B->BB","k':BB->R' o i2:B->BB"]) >>
 x_choosel_then ["AA","p1","p2"] assume_tac 
 (pr_ex|> pspecl ["A","A"]) >>
 x_choosel_then ["R","k"] assume_tac 
 (eq_ex|> pspecl ["AA","B","f:A->B o p1:AA->A","f:A->B o p2:AA->A"]) >> 
 x_choosel_then ["I'","q"] assume_tac 
 (coeq_ex|> pspecl ["R","A","p1:AA->A o k:R->AA","p2:AA->A o k:R->AA"]) >>
 assume_tac (Thm3_without_assume_exists |> strip_all_and_imp) >>
 pop_assum strip_assume_tac >> 
 by_tac “q':I0->B o h o q:A->I' = f & isiso(h)” >-- arw[] >>
 rev_drule eqa_is_mono >> drule coeqa_is_epi >>
 fs[GSYM o_assoc] >> 
 pexistsl_tac ["I'","q':I0->B o h:I'->I0","q:A->I'"] >>
 arw[] >> irule mono_o_iso_mono >> arw[])
(form_goal “!A B f:A->B. ?X m:X->B e:A->X. isepi(e) & ismono(m) & f = m o e”)




val isepi_surj = is_epi_surj

val Thm4 = proved_th $
 e0
(rpt strip_tac >> 
 x_choosel_then ["XJ","pX","pJ"] assume_tac (pr_ex |> pspecl ["X","J"]) >>
 assume_tac const1_def >>
 abbrev_tac “ev:P->two o pa(p1:P->X,p2:P->X2two,pX:XJ->X,ss:J->X2two o pJ:XJ->J) = s0” >>
 abbrev_tac “i2:1->two o to1(XJ,1) = i2t” >>
 x_choosel_then ["E","k"] assume_tac 
 (eq_ex |> pspecl ["XJ","two","s0:XJ->two","i2t:XJ->two"]) >>
 x_choosel_then ["U","a","q"] assume_tac  
 (mono_epi_fac |> pspecl ["E","X","pX:XJ->X o k:E->XJ"]) >>
 pexistsl_tac ["U","a:U->X"] >> arw[] >> strip_tac >> 
 by_tac “!j:1->J. ev:P->two o pa(p1:P->X,p2:P->X2two,x:1->X,ss:J->X2two o j:1->J) = s0:XJ->two o pa(pX:XJ->X,pJ:XJ->J,x,j)” 
 >-- (strip_tac >> 
      by_tac “pa(p1:P->X,p2:P->X2two,x:1->X,ss:J->X2two o j:1->J) = 
              pa(p1,p2,pX:XJ->X,ss o pJ:XJ->J) o pa(pX,pJ,x,j)”
      >-- (irule to_p_eq >> pexistsl_tac ["X","p1:P->X","X2two","p2:P->X2two"]>>
           drule exp_ispr >> drule p12_of_pa >> arw[GSYM o_assoc] >>
           rev_drule p12_of_pa >> arw[o_assoc]) >>
      once_arw[] >> arw[GSYM o_assoc]) >>
arw[] >>
dimp_tac >> strip_tac (* 2 *) >-- 
(fs[ismem_def] >> drule isepi_surj >> 
 first_x_assum (pspecl_then ["x0:1->U"] (x_choose_then "xb" assume_tac)) >>
 pexistsl_tac ["pJ:XJ->J o k:E->XJ o xb:1->E"] >>
 by_tac 
 “pa(pX:XJ->X,pJ:XJ->J,x,pJ:XJ->J o k:E->XJ o xb:1->E) = k:E->XJ o xb:1->E”
 >-- (irule to_p_eq >> pexistsl_tac ["X","pX:XJ->X","J","pJ:XJ->J"] >>
     drule p12_of_pa >> arw[] >>
     arw[GSYM o_assoc] >> arw[o_assoc]) >>
 drule eq_equality >> 
 by_tac “i2t o k:E->XJ o xb:1->E = i2:1->two”
 >-- (pick_xnth_assum 6 (assume_tac o GSYM) >>
      once_arw[] >> rw[o_assoc] >>
      once_rw_tac[one_to_one_id] >> rw[idR]) >>
 arw[] >> rw[GSYM o_assoc] >> arw[] >> arw[o_assoc]) >>
arw[ismem_def] >> 
pexistsl_tac ["q:E->U o eqind(k:E->XJ,s0:XJ->two,i2t:XJ->two,pa(pX:XJ->X,pJ:XJ->J,x:1->X,j:1->J))"] >> 
pick_xnth_assum 8 (strip_assume_tac o GSYM) >> arw[GSYM o_assoc] >> 
rw[o_assoc] >> drule eq_eqn >> 
suffices_tac “k o eqind(k:E->XJ, s0:XJ->two, i2t:XJ->two, pa(pX, pJ, x, j)) = pa(pX:XJ->X, pJ:XJ->J, x:1->X, j:1->J)”
>-- (drule p1_of_pa >> strip_tac >> arw[]) >>
first_x_assum irule >> once_arw[] >>
pick_xnth_assum 6 (assume_tac o GSYM) >> once_arw[] >> rw[o_assoc] >>
once_rw[one_to_one_id] >> rw[idR]
)
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !X P p1:P->X X2two p2:P->X2two ev:P->two. isexp(p1,p2,ev) ==> 
 !J ss:J->X2two.
  (?U a:U->X.ismono(a) & 
   (!x:1->X.ismem(x,a) <=> ?j:1->J. ev o pa(p1,p2,x,ss o j) = i2))”)

(*TO-DO: pull exists
?A. (?(f : 1 -> A#). T) & areiso(A#, 0) now have
*)

val Thm5_lemma_1 = proved_th $
e0
(rpt strip_tac >>
 pspecl_then ["A","1"] (x_choosel_then ["A1","iA","ione"] assume_tac) copr_ex >>
assume_tac const1_def >>
drule (ax5 |> pspecl ["A1","1","ione:1->A1","X","copa(iA:A->A1,ione:1->A1,a:A->X,x:1->X)"]) >>
pop_assum (x_choose_then "u" assume_tac) >> 
pexistsl_tac ["copa(iA:A->A1,ione:1->A1,i1:1->two o to1(A,1),i2:1->two) o u:X->A1"] >>
drule i12_of_copa >> 
first_x_assum (pspecl_then ["X","a:A->X","x:1->X"] assume_tac) >>
pop_assum (strip_assume_tac o GSYM) >> 
once_arw[] >> rw[o_assoc] >> 
pop_assum (K all_tac) >> pop_assum (K all_tac) >>
suffices_tac
 “copa(iA:A->A1, ione:1->A1, (i1:1->two o to1(A, 1)), i2:1->two) o (u:X->A1 o copa(iA, ione, a:A->X, x:1->X)) o ione = i2 &
 copa(iA, ione, (i1 o to1(A, 1)), i2) o (u o copa(iA, ione, a, x)) o iA = i1 o to1(A, 1)” >-- rw[o_assoc] >>
 by_tac “ismono(copa(iA:A->A1,ione:1->A1,a:A->X,x:1->X))”
 >-- (irule copa_not_mem_mono_mono >> arw[]) >>
 drule mono_pinv_post_inv >> first_x_assum drule >> arw[idL] >>
 drule i12_of_copa >> arw[])
(form_goal 
“!A X a:A->X. ismono(a) ==>
 !x:1->X. (~(?x0:1->A. a o x0 = x)) ==>
 !two i1:1->two i2:1->two.iscopr(i1,i2) ==>
 ?phi:X->two. phi o x = i2 & phi o a = i1 o to1(A,1)”)

(*


AQ1: example:
(rapg "!X x:1->X Y f:X->Y ev X2Y efs p1 p2. isexp(p1:efs ->X,p2:efs->X2Y,ev:efs -> Y) ==> !X1 pX:X1->X pone:X1->1. ispr(pX,pone) ==> ev o pa(p1,p2,x,tp (p1,p2,ev,pX,pone,f o pX)) = f o x")

if after strip, have some free variables whose dom/cod is bound, then raise error. in type checking in parsing.


rapg "!a.ismono(a) & ismono(a)"

should I introduce a constaint so it never happens?



AQ4. pick_assum / pick_xnth_assum okay (like it anyway...)? would like qpat assum, how basically does it work? (have not make attempt to look at its code though, any key thing to know about it? guess it is parsing & matching, but how far does the parsing go/ how to parse the partial formulas like a = _, another special parser other than pwc?)  how would we allow qpick assum? cannot think of a higher order function for it.

first_x_assume with (fn => which can match the given formula which is obtaibed by parsing in cont, or use _ )


AQ7. talked about "do not allow more free variables on RHS", but if the variables are in the context and it is once arw then it is okay, say once arw using GSYM p12_of_pa. discussed before for things like “?x:A->B <=>T” maybe give the conv access to the cont. should the restriction on rw be "no free var outside the cont" in conv, instead of no more fv on RHS? or how else should we once rw with GSYM p12_of_pa?


g:A->B
 ispr(p1#, p2#)

P(f)
------
f (f# = p1# o pa(p1#, p2#, f#, g#) |> )= f' 



*)



val Thm5_constructions = proved_th $
e0
(rpt strip_tac >>
 pexistsl_tac ["tp(p1:AA2->A, p2:AA2->A2, ev:AA2->two, pA:A1->A, pone:A1->1, i1:1->two o to1(A1, 1))"] >> rw[] >> repeat strip_tac >>
 pexistsl_tac ["tp(p1:AA2->A, p2:AA2->A2, ev:AA2->two, Ax2:AX2->A, aX2:AX2->X2, ev':XX2->two o pa(p1':XX2->X, p2':XX2->X2, a:A->X o Ax2, aX2))"] >>
 rw[] >> rpt strip_tac >> 
 pexistsl_tac ["ev':XX2->two o pa(p1':XX2->X, p2':XX2->X2, pX:XL->X, u:L->X2 o pL:XL->L)"] >> rw[] >> rpt strip_tac >> 
 accept_tac (mono_epi_fac |> pspecl ["E","X","pX:XL->X o k:E->XL"]))
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !AA2 p1:AA2 -> A A2 p2:AA2 -> A2 ev:AA2 -> two. isexp(p1,p2,ev) ==>
 ?j0:1->A2. tp(p1,p2,ev,pA,pone,i1 o to1(A1,1)) = j0 &
 !XX2 p1':XX2->X X2 p2':XX2->X2 ev':XX2->two. isexp(p1',p2',ev') ==>
 !AX2 Ax2:AX2->A aX2:AX2->X2.ispr(Ax2,aX2) ==>
 ?a2:X2->A2.tp(p1,p2,ev,Ax2,aX2,ev' o pa(p1',p2',a o Ax2,aX2)) = a2 &
 !L u:L->X2. iseq(u,a2,j0 o to1(X2,1)) ==>
 !XL pX:XL->X pL:XL ->L.ispr(pX,pL) ==>
 ?ub:XL->two. ev' o pa(p1',p2',pX,u o pL) = ub & 
 !E k:E->XL.iseq(k,ub,i2 o to1(XL,1)) ==>
 ?A' a':A'->X q:E->A'.isepi(q) & ismono(a') & pX o k = a' o q”)


val Thm5_epi_ex_xp_a2phi0 = proved_th $
e0
(rpt strip_tac >> rev_drule ev_eq_eq >> 
 first_x_assum irule >> pexistsl_tac ["A1","pA:A1->A","pone:A1->1"] >>
 once_arw[] >> rw[o_assoc] >> (*once_rw[one_to_one_id] >> rw[idR] *)
 by_tac “j0 o to1(X2, 1) o phi0 o pone = j0:1->A2 o (to1(X2, 1) o phi0:1->X2) o pone:A1->1” >-- rw[o_assoc] >> once_arw[] >>
 once_rw[one_to_one_id] >> rw[idL] >> 
 by_tac “pa(p1, p2, pA, a2 o phi0 o pone) = 
         pa(p1:AA2->A, p2:AA2->A2, Ax2:AX2->A, a2:X2->A2 o aX2:AX2->X2) o
         pa(Ax2,aX2,pA:A1->A,phi0:1->X2 o pone:A1->1)” 
 >-- (irule parallel_p_one_side >> rev_drule exp_ispr >> once_arw[] >>
      rw[]) >>
 once_arw[] >> rw[GSYM o_assoc] >>
 pick_xnth_assum 8 (assume_tac o GSYM) >> once_arw[] >>
 rev_drule ev_of_tp >> pick_xnth_assum 7 assume_tac >>
 first_x_assum drule >> once_arw[] >> rw[o_assoc] >> 
 by_tac “pa(p1', p2', (a o Ax2:AX2->A), aX2:AX2->X2) o pa(Ax2, aX2, pA:A1->A, phi0 o pone:A1->1) = 
        pa(p1':XX2->X,p2':XX2->X2,pX':X1->X, phi0:1->X2 o pone':X1->1) o pa(pX',pone',a:A->X o pA:A1->A, pone)”
 >-- (irule to_p_eq >> 
     pexistsl_tac ["X","p1':XX2->X","X2","p2':XX2->X2"] >>
     drule exp_ispr >> drule p12_of_pa >> rw[GSYM o_assoc] >>
     once_arw[] >> rw[o_assoc] >> 
     pop_assum (K all_tac) >> pop_assum (K all_tac) >>
     drule p12_of_pa >> once_arw[] >> 
     pick_xnth_assum 16 (assume_tac o GSYM) >> 
     drule p12_of_pa >> once_arw[] >> rw[]) >>
once_arw[] >> pick_xnth_assum 19 (assume_tac o GSYM) >> once_arw[] >>
drule ev_of_tp >> pick_xnth_assum 16 assume_tac >> first_x_assum drule >>
rw[GSYM o_assoc] >> once_arw[] >> 
pick_xnth_assum 5 (assume_tac o GSYM) >> once_arw[] >> rw[GSYM o_assoc] >>
rev_drule ev_of_tp >> first_x_assum rev_drule >> once_arw[] >>
drule p1_of_pa >> rw[o_assoc] >> once_arw[] >> rw[GSYM o_assoc] >>
once_arw[] >> rw[o_assoc] >> pspecl_then ["A1","to1(A1,1)","to1(A,1) o pA:A1->A"] assume_tac to1_unique >> once_arw[] >> rw[])
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !AA2 p1:AA2 -> A A2 p2:AA2 -> A2 ev:AA2 -> two. isexp(p1,p2,ev) ==>
 !j0:1->A2. tp(p1,p2,ev,pA,pone,i1 o to1(A1,1)) = j0 ==>
 !XX2 p1':XX2->X X2 p2':XX2->X2 ev':XX2->two. isexp(p1',p2',ev') ==>
 !AX2 Ax2:AX2->A aX2:AX2->X2.ispr(Ax2,aX2) ==>
 !a2:X2->A2.tp(p1,p2,ev,Ax2,aX2,ev' o pa(p1',p2',a o Ax2,aX2)) = a2 ==>
 !L u:L->X2. iseq(u,a2,j0 o to1(X2,1)) ==>
 !XL pX:XL->X pL:XL ->L.ispr(pX,pL) ==>
 !ub:XL->two. ev' o pa(p1',p2',pX,u o pL) = ub ==>
 !E k:E->XL.iseq(k,ub,i2 o to1(XL,1)) ==>
 !A' a':A'->X q:E->A'.isepi(q) ==>
     ismono(a') ==> pX o k = a' o q ==>
 !AA' iA:A->AA' iA':A'->AA'. iscopr(iA,iA') ==> 
 !b:1->X.(~(?b0:1 -> A. a o b0 = b)) ==> 
         !X1 pX':X1->X pone':X1->1.ispr(pX',pone') ==>
 !phi. phi o a = i1 o to1(A, 1) ==> phi o b = i2 ==>
 !phi0.tp(p1', p2', ev', pX', pone', phi o pX') = phi0 ==>
   a2 o phi0 = (j0 o to1 (X2,1)) o phi0”)



val Thm5_epi_ex_xp = proved_th $
e0
(rpt strip_tac >>
 assume_tac (Thm5_epi_ex_xp_a2phi0 |> strip_all_and_imp) >>
 by_tac “?phi0':1->L. u:L->X2 o phi0' = tp(p1':XX2->X,p2':XX2->X2,ev':XX2->two,pX':X1->X,pone':X1->1,phi:X->two o pX')”
>-- (pexistsl_tac 
     ["eqind(u:L->X2,a2:X2->A2,j0:1->A2 o to1(X2, 1),phi0:1->X2)"] >>
     pick_xnth_assum 21 (assume_tac o GSYM) >> once_arw[] >>
     rev_drule (eq_eqn|> gen_all)  >> first_x_assum irule >>
     pop_assum (assume_tac o GSYM) >> once_arw[] >>
     first_x_assum accept_tac) >>
pop_assum strip_assume_tac >>
by_tac “ub:XL->two o pa(pX:XL->X, pL:XL->L, b:1->X, phi0':1->L) = (i2:1->two o to1 (XL,1)) o pa(pX, pL, b, phi0')”  
>-- (by_tac “pa(p1':XX2->X,p2':XX2->X2,pX:XL->X,u:L->X2 o pL:XL->L) o pa(pX, pL, b:1->X, phi0':1->L) = 
            pa(p1', p2', b, u o phi0')”
     >-- (irule to_p_eq >> 
          pexistsl_tac ["X","p1':XX2->X","X2","p2':XX2->X2"] >>
          drule exp_ispr >> drule p12_of_pa >> rw[GSYM o_assoc] >>
          once_arw[] >> 
          assume_tac (assume “ispr(pX:XL->X, pL:XL->L)”) >>
          drule p12_of_pa >> rw[o_assoc] >> once_arw[] >> 
          rw[] >> first_x_assum accept_tac) >>
     suffices_tac “ev':XX2->two o pa(p1':XX2->X,p2':XX2->X2,b,phi0:1->X2) = phi:X->two o b:1->X”
     >-- (strip_tac >> rw[o_assoc] >> once_rw[one_to_one_id] >>
         rw[idR] >> pick_xnth_assum 11 (assume_tac o GSYM) (*unabr ub*) >>
         once_arw[] >> rw[o_assoc] >> once_arw[] >> once_arw[] >>
         drule ev_of_tp >> first_x_assum drule >> once_arw[] >>
         (assume_tac o GSYM) (assume “phi o b:1->X = i2:1->two”) >>
         once_arw[] >> rw[]) >>
     pick_xnth_assum 21 (assume_tac o GSYM) (*unabr phi0*) >>
     once_arw[] >> drule tp_elements_ev >> first_x_assum drule >>
     once_arw[] >> first_x_assum accept_tac) >>
by_tac “?bp0:1->E.k:E->XL o bp0 = pa(pX:XL->X,pL:XL->L,b:1->X,phi0':1->L)”
>-- (pexistsl_tac ["eqind(k:E->XL,ub:XL->two,i2:1->two o to1(XL,1),pa(pX:XL->X, pL:XL->L, b:1->X, phi0':1->L))"] >> 
     drule eq_eqn >> first_x_assum drule >> once_arw[] >> rw[]) >>
pop_assum strip_assume_tac >> pexistsl_tac ["bp0:1->E"] >> 
irule to_p_eq >> drule exp_ispr >> 
pexistsl_tac ["X","p1':XX2->X","X2","p2':XX2->X2"] >> once_arw[] >>
drule p12_of_pa >> rw[GSYM o_assoc] >> once_arw[] >>
assume_tac (assume “ispr(pX:XL->X, pL:XL->L)”) >>
drule p12_of_pa >> rw[o_assoc] >> once_arw[] >> once_arw[] >>
once_arw[] >> first_x_assum accept_tac
)
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !AA2 p1:AA2 -> A A2 p2:AA2 -> A2 ev:AA2 -> two. isexp(p1,p2,ev) ==>
 !j0:1->A2. tp(p1,p2,ev,pA,pone,i1 o to1(A1,1)) = j0 ==>
 !XX2 p1':XX2->X X2 p2':XX2->X2 ev':XX2->two. isexp(p1',p2',ev') ==>
 !AX2 Ax2:AX2->A aX2:AX2->X2.ispr(Ax2,aX2) ==>
 !a2:X2->A2.tp(p1,p2,ev,Ax2,aX2,ev' o pa(p1',p2',a o Ax2,aX2)) = a2 ==>
 !L u:L->X2. iseq(u,a2,j0 o to1(X2,1)) ==>
 !XL pX:XL->X pL:XL ->L.ispr(pX,pL) ==>
 !ub:XL->two. ev' o pa(p1',p2',pX,u o pL) = ub ==>
 !E k:E->XL.iseq(k,ub,i2 o to1(XL,1)) ==>
 !A' a':A'->X q:E->A'.isepi(q) ==>
     ismono(a') ==> pX o k = a' o q ==>
 !AA' iA:A->AA' iA':A'->AA'. iscopr(iA,iA') ==> 
 !b:1->X.(~(?b0:1 -> A. a o b0 = b)) ==> 
         !X1 pX':X1->X pone':X1->1.ispr(pX',pone') ==>
 !phi. phi o a = i1 o to1(A, 1) ==> phi o b = i2 ==>
 !phi0.tp(p1', p2', ev', pX', pone', phi o pX') = phi0 ==>
   ?xp:1->E. pa(p1',p2',pX,u o pL) o k o xp = pa(p1',p2',b, phi0)”)


val Thm5_epi = proved_th $ 
e0
(rpt strip_tac >> irule surj_is_epi >> strip_tac >>
cases_on “?b0:1->A. a:A->X o b0 = b”
>-- (pop_assum strip_assume_tac >> 
     pexistsl_tac ["iA:A->AA' o b0:1->A"] >>
     drule i1_of_copa >> arw[GSYM o_assoc]) >>
suffices_tac “?b0':1->A'. a':A'->X o b0' = b”
>-- (strip_tac >> pexistsl_tac ["iA':A'->AA' o b0':1->A'"] >>
     drule i2_of_copa >> arw[GSYM o_assoc]) >>
rev_drule Thm5_lemma_1 >> first_x_assum drule >> first_x_assum drule >>
pop_assum strip_assume_tac >>
x_choosel_then ["X1","pX'","pone'"] assume_tac (pr_ex |> pspecl ["X","1"]) >>
abbrev_tac “tp(p1':XX2->X,p2':XX2->X2,ev':XX2->two,pX',pone':X1->1,phi:X->two o pX':X1->X) = phi0” >> pop_assum_list (map_every strip_assume_tac) >>
assume_tac (strip_all_and_imp Thm5_epi_ex_xp) >>
pop_assum strip_assume_tac >>
pexistsl_tac ["q:E->A' o xp:1->E"] >> 
by_tac “p1':XX2->X o pa(p1', p2':XX2->X2, b:1->X, phi0:1->X2) = b:1->X”
>-- (rev_drule exp_ispr >> drule p1_of_pa >> once_arw[] >> rw[]) >>
pop_assum (assume_tac o GSYM) >> once_arw[] >> pop_assum (K all_tac) >> 
pick_xnth_assum 7 (assume_tac o GSYM) >> rw[GSYM o_assoc] >> once_arw[] >>
rw[o_assoc] >>
by_tac “pX = p1' o pa(p1':XX2->X,p2':XX2->X2,pX:XL->X, u:L->X2 o pL:XL->L)”
>-- (sym_tac >> rev_drule exp_ispr >> drule p1_of_pa >> once_arw[] >> rw[]) >>
once_arw[] >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>
pop_assum (assume_tac o GSYM) >> once_arw[] >> rw[o_assoc]
)
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !AA2 p1:AA2 -> A A2 p2:AA2 -> A2 ev:AA2 -> two. isexp(p1,p2,ev) ==>
 !j0:1->A2. tp(p1,p2,ev,pA,pone,i1 o to1(A1,1)) = j0 ==>
 !XX2 p1':XX2->X X2 p2':XX2->X2 ev':XX2->two. isexp(p1',p2',ev') ==>
 !AX2 Ax2:AX2->A aX2:AX2->X2.ispr(Ax2,aX2) ==>
 !a2:X2->A2.tp(p1,p2,ev,Ax2,aX2,ev' o pa(p1',p2',a o Ax2,aX2)) = a2 ==>
 !L u:L->X2. iseq(u,a2,j0 o to1(X2,1)) ==>
 !XL pX:XL->X pL:XL ->L.ispr(pX,pL) ==>
 !ub:XL->two. ev' o pa(p1',p2',pX,u o pL) = ub ==>
 !E k:E->XL.iseq(k,ub,i2 o to1(XL,1)) ==>
 !A' a':A'->X q:E->A'.isepi(q) & ismono(a') & pX o k = a' o q ==>
        !AA' iA:A->AA' iA':A'->AA'. iscopr(iA,iA') ==> isepi(copa(iA,iA',a,a'))”)


val Thm5_mono = proved_th $ 
e0
(rpt strip_tac >> 
 by_tac “(j0:1->A2 o to1 (X2,1)) o u:L->X2 = a2:X2->A2 o u”
 >-- (rev_drule eq_equality >> arw[]) >>
 by_tac “ev':XX2->two o pa(p1':XX2->X,p2':XX2->X2,a:A->X o Ax2:AX2->A, aX2:AX2->X2) =
         ev:AA2->two o pa(p1:AA2->A,p2:AA2->A2,Ax2, a2:X2->A2 o aX2)”
 >-- (pick_xnth_assum 8 (assume_tac o GSYM) >> once_arw[] >>
      rev_drule ev_of_tp >> pick_xnth_assum 7 assume_tac >>
      first_x_assum drule >> once_arw[] >> rw[]) >> 
x_choosel_then ["AL","Al","aL"] assume_tac (pr_ex |> pspecl ["A","L"]) >>
by_tac “pa(p1:AA2->A,p2:AA2->A2,Ax2:AX2->A,a2:X2->A2 o aX2:AX2->X2) o pa(Ax2,aX2,Al:AL->A,u:L->X2 o aL:AL->L) =
 pa(p1,p2,Al, a2 o u o aL)” >-- 
(rev_drule exp_ispr >> drule to_p_eq >> first_x_assum irule >>
 drule p12_of_pa >> rw[GSYM o_assoc] >> once_arw[] >>
 assume_tac (assume “ispr(Ax2:AX2->A, aX2:AX2->X2)”) >> 
 drule p12_of_pa >> rw[o_assoc] >> once_arw[] >> rw[]) >>
by_tac “!x:1->X.(?x0: 1-> A.a:A->X o x0 = x) ==>
        !t: 1 -> X2.(?t0:1 -> L. u:L->X2 o t0 = t) ==>
        ev':XX2->two o pa(p1':XX2->X,p2':XX2->X2,x,t) = i1:1->two”
>-- (rpt strip_tac >>
     by_tac “pa(p1',p2',a o x0,u o t0) = pa(p1':XX2->X,p2':XX2->X2,a:A->X o Ax2, aX2) o
                pa(Ax2:AX2->A,aX2:AX2->X2,Al, u:L->X2 o aL) o pa(Al:AL->A,aL:AL->L,x0:1->A,t0:1->L)”
     >-- (drule exp_ispr >> drule to_p_eq >> first_x_assum irule >>
          drule p12_of_pa >> rw[GSYM o_assoc] >> once_arw[] >>
          assume_tac (assume “ispr(Ax2:AX2->A, aX2:AX2->X2)”) >>
          drule p12_of_pa >> once_arw[] >>
          by_tac “(a:A->X o Ax2:AX2->A) o pa(Ax2, aX2:AX2->X2, Al:AL->A, u:L->X2 o aL:AL->L) = 
                  a o Ax2 o pa(Ax2, aX2, Al, u o aL)” 
          >-- rw[o_assoc] >>
          once_arw[] >> once_arw[] >>
          assume_tac (assume “ispr(Al:AL->A,aL:AL->L)”) >>
          drule p12_of_pa >> rw[o_assoc] >> once_arw[] >>
          once_arw[] >> rw[]) >> 
     pick_x_assum “a:A->X o x0:1->A = x” (assume_tac o GSYM) >>
     pick_x_assum “u:L->X2 o t0:1->L = t” (assume_tac o GSYM) >>
     once_arw[] >> once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >>
     by_tac “(ev:AA2->two o pa(p1:AA2->A, p2:AA2->A2, Ax2:AX2->A, a2:X2->A2 o aX2:AX2->X2)) o pa(Ax2, aX2, Al:AL->A, u:L->X2 o aL:AL->L) = ev o pa(p1, p2, Ax2, a2 o aX2) o pa(Ax2, aX2, Al, u o aL)” >-- rw[o_assoc] >>
    once_arw[] >> once_arw[] >>
    pick_x_assum “(j0:1->A2 o to1(X2, 1)) o u:L->X2 = a2 o u” (assume_tac o GSYM) >> rw[GSYM o_assoc] >> once_arw[] >>
    once_arw[] >> 
    by_tac “pa(p1:AA2->A, p2:AA2->A2, Al:AL->A, j0:1->A2 o to1(X2, 1) o u:L->X2 o aL:AL->L) = 
    pa(p1, p2, pA,j0 o pone:A1->1) o pa(pA:A1->A,pone:A1->1, Al,(to1(X2, 1) o u) o aL)”
    >-- (by_tac “j0:1->A2 o to1(X2, 1) o u:L->X2 o aL:AL->L = 
         j0 o (to1(X2, 1) o u) o aL” >-- rw[o_assoc] >>
         once_arw[] >> irule parallel_p_one_side >>
         rev_drule exp_ispr >> once_arw[] >> rw[]) >>
    rw[o_assoc] >> once_arw[] >> rw[GSYM o_assoc] >>
    by_tac “ev:AA2->two o pa(p1:AA2->A, p2:AA2->A2, pA:A1->A, j0:1->A2 o pone:A1->1) = i1:1->two o to1(A1,1)”
    >-- (pick_xnth_assum 5 (assume_tac o GSYM) >> once_arw[] >>
         rev_drule ev_of_tp >> first_x_assum irule >> once_arw[]) >>
    once_arw[] >> rw[o_assoc] >> once_arw[one_to_one_id] >> rw[idR]
    ) >>
by_tac “!x:1 -> X. (?xb: 1 -> A'. a':A'->X o xb = x) ==>
        ?t: 1-> X2. (?t0:1-> L.u o t0 = t) &
         ev':XX2->two o pa(p1':XX2->X,p2':XX2->X2,x,t) = i2:1->two” >--
(rpt strip_tac >>
 by_tac “?x0:1 -> E. q :E ->A' o x0 = xb”
 >-- (drule epi_has_section >> pop_assum strip_assume_tac >>
      pexistsl_tac ["g:A'->E o xb:1->A'"] >> rw[GSYM o_assoc] >>
      once_arw[] >> rw[idL]) >>
 pop_assum strip_assume_tac >>
 pexistsl_tac ["u:L->X2 o pL:XL->L o k:E->XL o x0:1->E"] >>
 strip_tac >--
 (pexistsl_tac ["pL:XL-> L o k:E->XL o x0:1->E"] >> rw[]) >>
 by_tac “pa(p1', p2', x, u o pL o k o x0) = 
         pa(p1':XX2->X, p2':XX2->X2, pX, u:L->X2 o pL) o pa(pX:XL->X,pL:XL->L,x:1->X,pL:XL->L o k:E->XL o x0:1->E)”
 >-- (irule to_p_eq >> drule exp_ispr >> drule p12_of_pa >>
     pexistsl_tac ["X","p1':XX2->X","X2","p2':XX2->X2"] >> once_arw[] >>
     rw[GSYM o_assoc] >> once_arw[] >>
     assume_tac (assume “ispr(pX:XL->X,pL:XL->L)”) >>
     drule p12_of_pa >> rw[o_assoc] >> once_arw[] >> rw[]) >>
 once_arw[] >> 
 drule eq_equality >> rw[GSYM o_assoc] >> once_arw[] >>
 by_tac “x = pX:XL->X o k o x0:1->E”
 >-- (pick_xnth_assum 22 (assume_tac o GSYM) >> once_arw[] >>
      pick_xnth_assum 22 (assume_tac o GSYM) >> once_arw[] >>
      rw[GSYM o_assoc] >> once_arw[] >> rw[]) >>
 once_arw[] >> 
 by_tac “pa(pX:XL->X, pL, pX o k o x0, (pL:XL->L o k) o x0) = k:E->XL o x0:1->E”
 >-- (irule to_p_eq >> pexistsl_tac ["X","pX:XL->X","L","pL:XL->L"] >>
      once_arw[] >> assume_tac (assume “ispr(pX:XL->X, pL:XL->L)”) >>
      drule p12_of_pa >> once_arw[] >> once_arw[] >>
      rw[o_assoc]) >>
 once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >> rw[o_assoc] >>
 once_arw[one_to_one_id] >> rw[idR]) >>
by_tac “!x:1->X. (~((?x0:1->A. a:A->X o x0 = x) &
                     ?x0:1->A'. a' o x0 = x))”
>-- (strip_tac >> ccontra_tac >>
     pop_assum strip_assume_tac >>  
     suffices_tac “i1 = i2:1->two”
     >-- (drule i1_ne_i2 >> strip_tac >> first_x_assum opposite_tac) >>
     by_tac “?xb : 1 -> A'. a':A'->X o xb = x”
     >-- (pexistsl_tac ["x0':1->A'"] >> once_arw[] >> rw[]) >>
     first_x_assum drule >> pop_assum strip_assume_tac >> 
     by_tac “?x0 : 1 -> A. a:A->X o x0 = x”
     >-- (pexistsl_tac ["x0:1->A"] >> once_arw[] >> rw[]) >>
     first_x_assum drule >>
     first_x_assum (pspecl_then ["t:1->X2"] assume_tac) >>
     by_tac “?(t0 : 1 -> L). u:L->X2 o t0 = t”
     >-- (pexistsl_tac ["t0:1->L"] >> once_arw[] >> rw[]) >>
     first_x_assum drule >> full_simp_tac[]) >>
by_tac “!Q q1:Q->AA' q2:Q->AA'.(~areiso(Q,0)) & 
           copa(iA:A->AA',iA':A'->AA',a:A->X,a':A'->X) o q1 = 
           copa(iA:A->AA',iA':A'->AA',a:A->X,a':A'->X) o q2 ==>
           ~(?q1':Q->A q2':Q->A'.
             iA o q1' = q1 & iA' o q2' = q2)”
>-- (rpt strip_tac >> ccontra_tac >> fs[iso_zero_is_zero] >> 
     drule ax6 >> pop_assum (x_choose_then "q0" assume_tac) >>
     suffices_tac 
     “(?x0:1->A. a:A->X o x0 = a o q1':Q->A o q0:1->Q) &
       ?x0:1->A'. a':A'->X o x0 = a o q1':Q->A o q0:1->Q”
     >-- (disch_tac >> first_x_assum (pspecl_then ["a:A->X o q1':Q->A o q0:1->Q"] assume_tac) >> first_x_assum opposite_tac) >>
     strip_tac (*2 *)
     >-- (pexistsl_tac ["q1':Q->A o q0:1->Q"] >> rw[])
     >-- (pexistsl_tac ["q2':Q->A' o q0:1->Q"] >> rw[] >>
          drule i12_of_copa >> 
          first_x_assum 
          (pspecl_then ["X","a:A->X","a':A'->X"] 
           (strip_assume_tac o GSYM)) >>
          once_arw[] >> rw[GSYM o_assoc] >> 
          suffices_tac “(copa(iA, iA', a:A->X, a':A'->X) o iA':A'->AA') o q2':Q->A' = 
                        (copa(iA, iA', a, a') o iA:A->AA') o q1':Q->A”
          >-- (strip_tac >> pop_assum mp_tac >>
               pop_assum_list (map_every (K all_tac)) >> strip_tac >>
               arw[]) >>
          arw[o_assoc])) >>
irule ismono_applied >> rpt strip_tac >> irule fun_ext >>
suffices_tac “!x': 1 -> X'. h o x' = g:X'->AA' o x'”
>-- (disch_tac >> first_x_assum accept_tac) >>
strip_tac >> drule to_copa_fac >>
first_x_assum (pspecl_then ["h:X'->AA' o x':1->X'"] strip_assume_tac) >--
(*case for ?x0.iA o x0 = h o x'*)
(drule to_copa_fac >>
 first_x_assum (pspecl_then ["g:X'->AA' o x':1->X'"] strip_assume_tac)
 (*case for iA o x0' = g o x'*) 
 >-- (suffices_tac “x0 = x0':1->A”
      >-- (strip_tac >> fs[]) >>
      rev_drule ismono_property >> first_x_assum irule >>
      suffices_tac “copa(iA:A->AA',iA':A'->AA',a, a') o iA o x0 = copa(iA:A->AA',iA':A'->AA',a:A->X, a':A'->X) o iA o x0':1->A”
      >-- (drule i1_of_copa >> rw[GSYM o_assoc] >> once_arw[] >>
           strip_tac >> sym_tac >> first_x_assum accept_tac) >>
      arw[] >> rw[GSYM o_assoc] >> once_arw[] >> rw[]) >> (*another case*)
 by_tac “(~areiso(1,0)) & 
              copa(iA:A->AA', iA':A'->AA', a:A->X, a':A'->X) o h:X'->AA' o x':1->X' =
              copa(iA, iA', a, a') o g o x'”
 >-- (strip_tac >-- accept_tac one_ne_zero >> arw[GSYM o_assoc]) >>
 first_x_assum drule  >>
 by_tac “?q1' : 1 -> A q2' : 1 -> A'. 
               iA:A->AA' o q1' = h o x' & 
               iA':A'->AA' o q2' = g o x':1->X'”
  >-- (pexistsl_tac ["x0:1->A","x0':1->A'"] >> arw[]) >>
  first_x_assum opposite_tac) (* snd big case split*) >>
drule to_copa_fac >> 
first_x_assum (pspecl_then ["g:X'->AA' o x':1->X'"] strip_assume_tac) >--
(by_tac “(~areiso(1,0)) & 
  copa(iA:A->AA', iA':A'->AA', a:A->X, a':A'->X) o g:X'->AA' o x':1->X' =
              copa(iA, iA', a, a') o h o x'”
 >-- (strip_tac >-- accept_tac one_ne_zero >> arw[GSYM o_assoc]) >>
 first_x_assum drule >>
 by_tac “?q1' : 1 -> A q2' : 1 -> A'. 
               iA:A->AA' o q1' = g o x' & 
               iA':A'->AA' o q2' = h o x':1->X'”
 >-- (pexistsl_tac ["x0':1->A","x0:1->A'"] >> arw[]) >>
 first_x_assum opposite_tac) >> (*last of 4 cases*)
suffices_tac “x0 = x0':1->A'”
>-- (strip_tac >> fs[]) >>
drule ismono_property >> first_x_assum irule >>
suffices_tac
 “copa(iA:A->AA',iA':A'->AA',a, a') o iA' o x0 = 
 copa(iA:A->AA',iA':A'->AA',a:A->X, a':A'->X) o iA' o x0':1->A'”
      >-- (drule i2_of_copa >> rw[GSYM o_assoc] >> once_arw[] >>
           strip_tac >> sym_tac >> first_x_assum accept_tac) >>
arw[] >> rw[GSYM o_assoc] >> once_arw[] >> rw[]
)
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !AA2 p1:AA2 -> A A2 p2:AA2 -> A2 ev:AA2 -> two. isexp(p1,p2,ev) ==>
 !j0:1->A2. tp(p1,p2,ev,pA,pone,i1 o to1(A1,1)) = j0 ==>
 !XX2 p1':XX2->X X2 p2':XX2->X2 ev':XX2->two. isexp(p1',p2',ev') ==>
 !AX2 Ax2:AX2->A aX2:AX2->X2.ispr(Ax2,aX2) ==>
 !a2:X2->A2.tp(p1,p2,ev,Ax2,aX2,ev' o pa(p1',p2',a o Ax2,aX2)) = a2 ==>
 !L u:L->X2. iseq(u,a2,j0 o to1(X2,1)) ==>
 !XL pX:XL->X pL:XL ->L.ispr(pX,pL) ==>
 !ub:XL->two. ev' o pa(p1',p2',pX,u o pL) = ub ==>
 !E k:E->XL.iseq(k,ub,i2 o to1(XL,1)) ==>
 !A' a':A'->X q:E->A'.isepi(q) & ismono(a') & pX o k = a' o q ==>
        !AA' iA:A->AA' iA':A'->AA'. iscopr(iA,iA') ==> ismono(copa(iA,iA',a,a'))”)

val Thm5_iso = proved_th $
e0
(rpt strip_tac >> assume_tac (Thm5_mono |> strip_all_and_imp) >>
 assume_tac (Thm5_epi |> strip_all_and_imp) >>
 irule mono_epi_is_iso >> arw[])
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !AA2 p1:AA2 -> A A2 p2:AA2 -> A2 ev:AA2 -> two. isexp(p1,p2,ev) ==>
 !j0:1->A2. tp(p1,p2,ev,pA,pone,i1 o to1(A1,1)) = j0 ==>
 !XX2 p1':XX2->X X2 p2':XX2->X2 ev':XX2->two. isexp(p1',p2',ev') ==>
 !AX2 Ax2:AX2->A aX2:AX2->X2.ispr(Ax2,aX2) ==>
 !a2:X2->A2.tp(p1,p2,ev,Ax2,aX2,ev' o pa(p1',p2',a o Ax2,aX2)) = a2 ==>
 !L u:L->X2. iseq(u,a2,j0 o to1(X2,1)) ==>
 !XL pX:XL->X pL:XL ->L.ispr(pX,pL) ==>
 !ub:XL->two. ev' o pa(p1',p2',pX,u o pL) = ub ==>
 !E k:E->XL.iseq(k,ub,i2 o to1(XL,1)) ==>
 !A' a':A'->X q:E->A'.isepi(q) & ismono(a') & pX o k = a' o q ==>
        !AA' iA:A->AA' iA':A'->AA'. iscopr(iA,iA') ==> isiso(copa(iA,iA',a,a'))”)


val Thm5 = proved_th $ 
e0
(rpt strip_tac >> drule Thm5_constructions >>
 x_choosel_then ["A1","pA","pone"] assume_tac (pspecl ["A","1"] pr_ex) >>
 first_x_assum drule >>
 x_choosel_then ["two","i1","i2"] assume_tac (pspecl ["1","1"] copr_ex) >>
 first_x_assum drule >> 
 x_choosel_then ["A2","AA2","p1","p2","ev"] assume_tac (pspecl ["A","two"] exp_ex) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 x_choosel_then ["X2","XX2","p1'","p2'","ev'"] assume_tac (pspecl ["X","two"] exp_ex) >>
 first_x_assum drule >>
 x_choosel_then ["AX2","Ax2","aX2"] assume_tac (pspecl ["A","X2"] pr_ex) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 x_choosel_then ["L","u"] assume_tac (pspecl ["X2","A2","a2:X2->A2","j0 :1-> A2 o to1(X2, 1)"] eq_ex) >>
 first_x_assum drule >>
 x_choosel_then ["XL","pX","pL"] assume_tac (pspecl ["X","L"] pr_ex) >>
 first_x_assum drule >> 
 pop_assum strip_assume_tac >>
 x_choosel_then ["E","k"] assume_tac (pspecl ["XL","two","ub:XL->two","i2:1->two o to1(XL, 1)"] eq_ex) >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["A'","a'","q"] assume_tac) >>
 pexistsl_tac ["A'","a':A'->X"] >> arw[] >> rpt strip_tac >>
 assume_tac (Thm5_iso |> strip_all_and_imp) >>
 first_x_assum accept_tac)
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 ?A' a':A'->X. ismono(a') &
        !AA' iA:A->AA' iA':A'->AA'. iscopr(iA,iA') ==> isiso(copa(iA,iA',a,a'))”)




val Thm5 = proved_th $ 
e0
(rpt strip_tac >> drule Thm5_constructions >>
 qspecl_then ["A","1"] (x_choosel_then ["A1","pA","pone"] assume_tac) 
 pr_ex >>
 first_x_assum drule >>
 qspecl_then ["1","1"] (x_choosel_then ["two","i1","i2"] assume_tac) copr_ex >>
 first_x_assum drule >> 
 qspecl_then ["A","two"] (x_choosel_then ["A2","AA2","p1","p2","ev"] assume_tac) exp_ex >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qspecl_then ["X","two"] (x_choosel_then ["X2","XX2","p1'","p2'","ev'"] assume_tac) exp_ex >>
 first_x_assum drule >>
 qspecl_then ["A","X2"] (x_choosel_then ["AX2","Ax2","aX2"] assume_tac) pr_ex >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qspecl_then ["X2","A2","a2","j0 o to1(X2, 1)"] (x_choosel_then ["L","u"] assume_tac) eq_ex >>
 first_x_assum drule >>
 qspecl_then ["X","L"] (x_choosel_then ["XL","pX","pL"] assume_tac) pr_ex >>
 first_x_assum drule >> 
 pop_assum strip_assume_tac >>
 qspecl_then ["XL","two","ub","i2 o to1(XL, 1)"] (x_choosel_then ["E","k"] assume_tac) eq_ex >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["A'","a'","q"] assume_tac) >>
 pexistsl_tac ["A'","a':A'->X"] >> arw[] >> rpt strip_tac >>
 assume_tac (Thm5_iso |> strip_all_and_imp) >>
 first_x_assum accept_tac)
(form_goal 
“!A X a:A->X.ismono(a) ==> 
 ?A' a':A'->X. ismono(a') &
        !AA' iA:A->AA' iA':A'->AA'. iscopr(iA,iA') ==> isiso(copa(iA,iA',a,a'))”)

val _ = new_pred "istrans" [("f0",mk_ar_sort (mk_ob "R") (mk_ob "A")),
                          ("f1",mk_ar_sort (mk_ob "R") (mk_ob "A"))]

(*
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ⇒
         (is_trans f0 f1 ⇔
         ∀X h0 h1.
             h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
             ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)
*)

val istrans_def = read_axiom "!R A f0:R->A f1:R->A.istrans(f0,f1) <=> !X h0:X->R h1:X->R. f1 o h0 = f0 o h1 ==> ?u:X->R. f0 o u = f0 o h0 & f1 o u = f1 o h1"

(*∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ⇒
         (is_refl f0 f1 ⇔
         ∃d. d∶ A → R ∧ f0 ∘ d = id A ∧ f1 ∘ d = id A)*)

val _ = new_pred "isrefl" [("f0",mk_ar_sort (mk_ob "R") (mk_ob "A")),
                          ("f1",mk_ar_sort (mk_ob "R") (mk_ob "A"))]

val isrefl_def = 
read_axiom "!R A f0:R->A f1. isrefl(f0,f1) <=> ?d:A->R. f0 o d = id(A) & f1 o d = id(A)"

(*is_symm f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃t. t∶ dom f1 → dom f1 ∧
                 f0 o t = f1 ∧
                 f1 o t = f0*)

val _ = new_pred "issymm" [("f0",mk_ar_sort (mk_ob "R") (mk_ob "A")),
                          ("f1",mk_ar_sort (mk_ob "R") (mk_ob "A"))]

val issymm_def = 
read_axiom "!R A f0:R->A f1. issymm(f0,f1) <=> ?t:R->R. f0 o t = f1 & f1 o t = f0"

(*

Theorem Thm6_first_sentence:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_refl f0 f1 ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
            is_mono ⟨f0, f1⟩ ∧
            (∀a0 a1. a0∶ one → A ∧ a1∶ one → A ∧
                     (coeqa f0 f1) o a0 = (coeqa f0 f1) o a1 ⇒
                     ∃r. r∶ one → R ∧ f0 o r = a0 ∧
                         f1 o r = a1) ⇒
            R ≅ eqo ((coeqa f0 f1) o p1 A A)
                    ((coeqa f0 f1) o p2 A A)
*)



val Thm6_first_sentence = proved_th $
 e0
(rpt strip_tac >> irule prop_2_corollary >>
 qexistsl_tac ["AA","pa(p1, p2, f0, f1)","e"] >>
 drule eqa_is_mono >> arw[] >> rpt strip_tac (* 2 *)
 >-- (qexists_tac "eqind(e,ce o p1,ce o p2,pa(p1, p2, f0, f1) o x)" >>
      sym_tac >> drule eq_eqn >> first_x_assum irule >>
      drule p12_of_pa  >>
      qby_tac ‘(ce o p1) o pa(p1, p2, f0, f1) o x = 
               ce o (p1 o pa(p1, p2, f0, f1)) o x & 
               (ce o p2) o pa(p1, p2, f0, f1) o x = 
               ce o (p2 o pa(p1, p2, f0, f1)) o x’
      >-- rw[o_assoc] >> 
      arw[] >> drule coeq_equality >> arw[GSYM o_assoc]) >>
 first_x_assum (qspecl_then ["p1 o e o y","p2 o e o y"] assume_tac) >>
 drule eq_equality >>
 fs[GSYM o_assoc] >> qexists_tac "r" >> 
 irule to_p_eq >> qexistsl_tac ["A","p1","A","p2"] >> 
 drule p12_of_pa >> arw[GSYM o_assoc]
)
(form_goal “!R A f0:R->A f1. isrefl(f0,f1) & issymm(f0,f1) & istrans(f0,f1)==> !AA p1:AA->A p2:AA->A. ispr(p1,p2) ==> ismono(pa(p1,p2,f0,f1)) ==> 
!cE ce:A->cE.iscoeq(ce,f0,f1) ==>
(!a0:1->A a1:1->A. ce o a0 = ce o a1 ==> ?r:1->R. f0 o r = a0 & f1 o r = a1) ==> !E e:E->AA. iseq(e,ce o p1,ce o p2) ==> areiso(R,E)”)

(*
∀psi R r. psi∶ R → two ∧ r∶ one → R ⇒
               (psi o r = i2 one one ⇔
                ∃r'. r'∶ one → eqo (ev R two) (i2 one one o to1 (R × exp R two)) ∧
                    eqa (ev R two) (i2 one one o to1 (R × exp R two)) o r' = ⟨r, tp (psi ∘ p1 R one)⟩) *)

val mem_of_name_eqa = proved_th $
e0
(rpt strip_tac >> drule (fac_through_eq_iff |> undisch |> gen_disch_all
                                            |> gen_all) >>
 first_x_assum (qspecl_then ["1","pa(p1, p2, r, tp(p1, p2, ev, pR, pone, psi o pR))"] assume_tac) >> arw[] >>
rw[o_assoc] >> once_arw[one_to_one_id] >> rw[idR] >>
drule tp_elements_ev >> first_x_assum drule >>
arw[])
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !R R1 pR:R1->R pone:R1->1.ispr(pR,pone) ==>
 !efs p1:efs->R R2t p2:efs-> R2t ev:efs->two. isexp(p1,p2,ev) ==>
 !psi:R->two r:1-> R. 
  !E e:E->efs. iseq(e,ev,i2 o to1(efs,1)) ==>
 (psi o r = i2 <=> ?r':1->E. e o r' = pa(p1,p2,r,tp(p1,p2,ev,pR,pone,psi o pR)))”)


(* char_thm:
∀a A X.
    is_mono a ∧ a∶ A → X ⇒
         char a∶ X → one + one ∧
         ∀x.
             x∶one → X ⇒
             ((∃x0. x0∶one → A ∧ a ∘ x0 = x) ⇔ char a ∘ x = i2 one one)
*)

(*TODO: if in exists, feed "copa(i1,i2,i2:1->two o to1(A,1),i1:1->two o to1(A',1)) o f':X->AA'", is wrong ,but get wrong error message*)

(*TODO, if input of f' o x is f o x, which is wrong , the error message is err find, not the q parsing*)

val char_exists = proved_th $
   e0
(rpt strip_tac >> drule Thm5 >> pop_assum strip_assume_tac >>
 qspecl_then ["A","A'"] 
 (x_choosel_then ["AA'","iA","iA'"] assume_tac) copr_ex >>
 first_x_assum drule >> fs[isiso_def] >>
 exists_tac (rastt "copa(iA:A->AA',iA':A'->AA',i2:1->two o to1(A,1),i1:1->two o to1(A',1)) o f':X->AA'") >> strip_tac >> dimp_tac >> strip_tac(* 2 *)
 >-- (qby_tac 
      ‘(copa(iA, iA', (i2 o to1(A, 1)), (i1 o to1(A', 1))) o f') o a o x0 =     copa(iA, iA', (i2 o to1(A, 1)), (i1 o to1(A', 1))) o (f' o a) o x0’ 
     >-- rw[o_assoc] >>
     qpick_x_assum ‘a o x0 = x’ (assume_tac o GSYM) >> arw[] >>
     qby_tac ‘f' o a = iA’
     >-- (qby_tac ‘f' o copa(iA, iA', a, a') o iA = id(AA') o iA’
         >-- (rw[GSYM o_assoc] >> arw[]) >>
         pop_assum mp_tac >> drule i1_of_copa >>
         once_arw[] >> rw[idL]) >>
     once_arw[] >> rw[GSYM o_assoc] >> drule i1_of_copa >> once_arw[] >>
     rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
drule to_copa_fac >> 
first_x_assum (qspecl_then ["f' o x"] strip_assume_tac) (* 2 *)
>-- (qexists_tac "x0" >> drule i1_of_copa >>
     first_x_assum (qspecl_then ["X","a","a'"] (assume_tac o GSYM)) >>
     once_arw[] >>pop_assum (K all_tac) >> rw[o_assoc] >> arw[] >>
     rw[GSYM o_assoc] >> once_arw[] >> rw[idL]) >>
qsuff_tac ‘(copa(iA,iA',i2 o to1(A,1),i1 o to1(A',1)) o f') o x = 
           i1 o to1(A',1) o x0’
>-- (once_rw[one_to_one_id] >> rw[idR] >> once_arw[] >>
     strip_tac >> pop_assum (assume_tac o GSYM) >> 
     drule i1_ne_i2 >> first_x_assum opposite_tac) >>
rw[o_assoc] >> pop_assum (assume_tac o GSYM) >> once_arw[] >>
rw[GSYM o_assoc] >> drule i2_of_copa >> once_arw[] >> rw[]
 )
(form_goal 
“!A X a:A->X. ismono(a) ==> !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 ?phi:X->two. (!x:1->X.(?x0:1->A.a o x0 = x) <=> phi o x = i2)”)

val _ = new_fun "char" (mk_ar_sort (mk_ob "X") (mk_ob "two"),[("i1",mk_ar_sort one (mk_ob "two")),("i2",mk_ar_sort one (mk_ob "two")),("a",mk_ar_sort (mk_ob "A") (mk_ob "X"))])

val compose_with_id_to1 = proved_th $
e0
(rpt strip_tac >> irule to_p_eq >> qexistsl_tac ["A","pA","1","pone"] >>
arw[GSYM o_assoc] >> drule p12_of_pa >> once_arw[] >>
rw[idL] >> once_rw[one_to_one_id] >> rw[])
(form_goal
“!A A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==> 
 !x:1->A. pa(pA,pone,id(A),to1(A,1)) o x = pa(pA,pone,x,id(1))”)

val ev_compose_split = proved_th $
e0
(rpt strip_tac >> drule exp_ispr >>
 qby_tac ‘ispr(Ab,aB) & ispr(Ax,aX) & ispr(p1,p2)’
 >-- arw[] >>
 drule parallel_p_one_side >> arw[])
(form_goal 
“!A B AB Ab:AB->A aB:AB->B. ispr(Ab,aB) ==>
 !X AX Ax:AX->A aX:AX->X. ispr(Ax,aX) ==>
 !Y A2Y efs p1:efs->A p2:efs->A2Y ev:efs -> Y. isexp(p1,p2,ev) ==>
 !g: X-> A2Y f:B->X. ev o pa(p1,p2,Ab,g o f o aB) = 
                    ev o pa(p1,p2,Ax,g o aX) o pa(Ax,aX,Ab,f o aB)”)



val ev_compose_split' = proved_th $
e0
(rpt strip_tac >> assume_tac (ev_compose_split |> strip_all_and_imp) >>
 first_x_assum accept_tac)
(form_goal 
“!Y A A2Y efs p1:efs->A p2:efs->A2Y ev:efs -> Y. isexp(p1,p2,ev) ==>
 !B AB Ab:AB->A aB:AB->B. ispr(Ab,aB) ==>
 !X AX Ax:AX->A aX:AX->X. ispr(Ax,aX) ==>
 !g: X-> A2Y f:B->X. ev o pa(p1,p2,Ab,g o f o aB) = 
                    ev o pa(p1,p2,Ax,g o aX) o pa(Ax,aX,Ab,f o aB)”)


val two_steps_compose_combine = proved_th $
e0
(rpt strip_tac >> irule to_p_eq >> qexistsl_tac ["A","Ay","Y","aY"] >>
 rw[GSYM o_assoc] >> drule p12_of_pa >> once_arw[] >>
 rw[o_assoc] >> rev_drule p12_of_pa >> once_arw[] >> rw[idR])
(form_goal 
“!A X AX Ax:AX->A aX:AX->X.ispr(Ax,aX) ==>
 !Y AY Ay:AY->A aY:AY->Y. ispr(Ay,aY) ==>
 !f:X->A g:X->Y. pa(Ay,aY,Ax,g o aX) o pa(Ax,aX,f,id(X)) = pa(Ay,aY,f,g)”)



val compose_partial_ev = proved_th $
e0
(rpt strip_tac >> 
 qby_tac ‘pa(pA,pone,id(A),to1(A,1)) o x = pa(pA:A1->A,pone:A1->1,x:1->A,id(1))’ >-- (rev_drule compose_with_id_to1 >> once_arw[] >> rw[]) >>
drule ev_compose_split' >> qpick_x_assum ‘ispr(pA, pone)’ assume_tac >>
first_x_assum drule >> first_x_assum rev_drule >> once_arw[] >>
first_x_assum 
 (qspecl_then ["tp(p1, p2, ev, Ax2y, aX2Y, phi)","tp(p1', p2', ev', pX, pone', (psi o pX))"] assume_tac) >> once_rw[GSYM o_assoc] >>
once_arw[] >> rw[GSYM o_assoc] >>
drule ev_of_tp >> first_x_assum rev_drule >> once_arw[] >>
rw[o_assoc] >>
qsuff_tac 
‘pa(Ax2y, aX2Y, x, tp(p1', p2', ev', pX, pone', psi o pX)) = 
 pa(Ax2y, aX2Y, pA, (tp(p1', p2', ev', pX, pone', (psi o pX)) o
 pone)) o pa(pA, pone, x, id(1))’ 
>-- (strip_tac >> once_arw[] >> rw[]) >>
irule to_p_eq >> rev_drule p12_of_pa >>
qexistsl_tac ["A","Ax2y","X2Y","aX2Y"] >> once_arw[] >>
rw[GSYM o_assoc] >> once_arw[] >> rw[o_assoc] >>
drule p12_of_pa >> once_arw[] >> rw[idR])
(form_goal 
“!X Y X2Y efs' p1':efs'->X p2':efs'->X2Y ev':efs'->Y. isexp(p1',p2',ev') ==>
 !A AX2Y Ax2y:AX2Y->A aX2Y:AX2Y->X2Y. ispr(Ax2y,aX2Y) ==>
 !A1 pA:A1-> A pone:A1->1. ispr(pA,pone) ==>
 !X1 pX:X1->X pone':X1->1. ispr(pX,pone') ==>
 !A2Y efs p1:efs->A p2:efs->A2Y ev:efs->Y.isexp(p1,p2,ev) ==>
 !x:1->A psi:X->Y phi:AX2Y->Y. 
  phi o pa(Ax2y,aX2Y,x,tp(p1',p2',ev',pX,pone',psi o pX)) = 
  ev o pa(p1,p2,pA,tp(p1,p2,ev,Ax2y,aX2Y,phi)  o tp(p1',p2',ev',pX,pone',psi o pX) o pone) o pa(pA,pone,id(A),to1(A,1)) o x”)

val isrefl_equiv_to_itself  = proved_th $
 e0
(rpt strip_tac >> fs[isrefl_def] >> qexistsl_tac ["d o a"] >>
 rw[GSYM o_assoc] >> arw[idL])
(form_goal “isrefl(f0:R->A,f1) ==> !a:1->A. ?r:1->R. f0 o r = a & f1 o r = a”)

val equiv_to_same_element = proved_th $
e0
(rpt strip_tac >> drule isrefl_equiv_to_itself >> 
 first_x_assum (qspecl_then ["a1"] assume_tac) >>
 first_x_assum (qspecl_then ["a1"] assume_tac) >> rfs[] >>
 qexistsl_tac ["r'"] >> arw[])
(form_goal 
“isrefl(f0:R->A,f1) ==> 
(!a':1->A.(?r:1->R.f0 o r = a1 & f1 o r = a') <=> (?r.f0 o r = a0 & f1 o r = a')) ==>
?r:1->R. f0 o r = a0 & f1 o r = a1”)

val symm_trans_rel_lemma = proved_th $
     e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >-- 
 (fs[issymm_def] >> fs[istrans_def] >> 
  first_x_assum (qspecl_then ["1","t o r'","r"] assume_tac) >>
  qby_tac ‘f1 o t o r' = f0 o r’
  >-- (rw[GSYM o_assoc] >> arw[]) >>
  first_x_assum drule >> pop_assum strip_assume_tac >>
  qexistsl_tac ["t o u"] >> rw[GSYM o_assoc] >> once_arw[] >>
  once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >> once_arw[] >>
  rw[])  >> fs[istrans_def] >>
 pick_xnth_assum 3 (assume_tac o GSYM) >> 
 first_x_assum drule >> pop_assum strip_assume_tac >> 
 qexistsl_tac ["u"] >> arw[])
(form_goal 
“issymm(f0:R->A,f1) & istrans(f0,f1) ==> 
!a:1->A r:1->R. 
((?r':1->R. f0 o r' = f0 o r & f1 o r' = a) <=> 
 (?r'':1->R. f0 o r'' = f1 o r & f1 o r'' = a))”)

val to_p_with_1 = proved_th $
e0
(rpt strip_tac >> qexistsl_tac ["pA o a"] >>
drule p12_of_pa >> irule to_p_eq >>
qexistsl_tac ["A","pA","1","pone"] >> arw[] >> once_rw[one_to_one_id] >>
rw[])
(form_goal
“!A A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==> 
 !a:1->A1.?a0:1->A. a = pa(pA,pone,a0,id(1))”)


val one_to_two_cases = proved_th $
 e0
(rpt strip_tac >> drule to_copa_fac >> 
 first_x_assum (qspecl_then ["f"] strip_assume_tac)
 >-- (pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR] >>
      strip_tac >> disj1_tac >> arw[]) >>
 pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR] >>
 strip_tac >> disj2_tac >> arw[])
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !f:1->two. f = i1 | f = i2”)

val one_to_two_eq = proved_th $
e0
(rpt strip_tac >> cases_on (rapf "f = i2:1->two")
 >-- fs[] >>
 fs[] >> drule one_to_two_cases >>
 first_assum (qspecl_then ["f"] strip_assume_tac) >>
 first_x_assum (qspecl_then ["g"] strip_assume_tac) >> arw[])
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !f:1->two g:1->two. (f = i2 <=> g = i2) ==> f = g”)


val char_def = read_axiom "!A X a:A->X. ismono(a) ==> !two i1:1->two i2:1->two. iscopr(i1,i2) ==> (!x:1->X.(?x0:1->A.a o x0 = x) <=> char(i1,i2,a) o x = i2)"

val fac_char = proved_th $
e0
(rpt strip_tac >> drule char_def >> first_x_assum drule >>
irule fun_ext >> strip_tac >> rw[o_assoc] >>
once_rw[one_to_one_id] >> rw[idR] >> 
pop_assum (assume_tac o iffLR) >> first_x_assum irule >>
qexistsl_tac ["f o a"] >> rw[GSYM o_assoc] >> once_arw[] >> rw[])
(form_goal 
“!A X m.ismono(m:A->X)==>!P p:P->X f:P->A. m o f = p ==>
!two i1:1->two i2:1->two.iscopr(i1,i2) ==>
char(i1,i2,m) o p = i2 o to1(P,1)”)

val fac_char_via_any_map = proved_th $
  e0
(rpt strip_tac >> drule epi_has_section >> 
 drule char_def >> first_x_assum drule >> 
 first_x_assum (qspecl_then ["b"] assume_tac) >>
 rfs[] >> qexistsl_tac ["g o x0"] >>
 qby_tac ‘(m o e) o g o x0 = m o (e o g) o x0’
 >-- rw[o_assoc] >> arw[idL])
(form_goal 
“!A M e:A->M. isepi(e) ==> !B m:M->B.ismono(m) ==>
 !f:A->B. f = m o e ==> 
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !b:1->B.char(i1,i2,m) o b = i2 ==>
 ?a:1->A. f o a = b”)




(*ir_canon char_exists is wrong*)

(*
∀h R A. h∶ R → A ⇒
        ∃hb. hb∶ exp R (one + one) → exp A (one + one) ∧
             (∀psi. psi∶ R → one + one ⇒
                    ∀x. x∶ one → A ⇒
                        (ev A (one + one) o ⟨p1 A one, hb o tp (psi o p1 R one) o p2 A one⟩ o ⟨id A, to1 A⟩ o x = i2 one one ⇔
                         ∃r. r∶ one → R ∧
                             psi o r = i2 one one ∧
                             h o r = x))
*)

val Thm6_lemma_3 = proved_th $
 e0
(rpt strip_tac >> 
abbrev_tac (rapf "i2:1->two o to1(RR2,1) = t") >>
qspecl_then ["RR2","two","ev'","t"] assume_tac eq_ex >>
pop_assum (x_choosel_then ["R'","Psi"] assume_tac) >>
qspecl_then ["A","R2"] (x_choosel_then ["AR2","Ar2","aR2"] assume_tac) pr_ex >>
abbrev_tac (rapf "pa(Ar2:AR2->A,aR2:AR2->R2,h:R->A o p1':RR2->R,p2':RR2->R2) = h2R") >>
qspecl_then ["R'","AR2","h2R o Psi"] (x_choosel_then ["M","m","e"] assume_tac) mono_epi_fac >>
abbrev_tac (rapf "char(i1:1->two,i2:1->two,m:M->AR2) = phi") >> 
by_tac (rapf "!x:1->AR2. (?x0:1->M. m:M->AR2 o x0 = x) <=> phi:AR2->two o x = i2:1->two")
>-- (pop_assum_list (map_every strip_assume_tac) >>
     drule char_def >> first_x_assum drule >> 
     last_x_assum (assume_tac o GSYM) >> once_arw[] >> rw[]) >>
qexistsl_tac ["tp(p1,p2,ev,Ar2,aR2,phi)"] >> 
strip_tac >> 
by_tac (rapf "!r:1->R.(psi:R->two o r = i2:1->two <=> ?r':1->R'. Psi:R'->RR2 o r' = pa(p1':RR2->R,p2':RR2->R2,r,tp(p1', p2', ev':RR2->two, pR:R1->R, pone':R1->1, (psi o pR))))")
>-- (strip_tac >> drule mem_of_name_eqa >> first_x_assum irule >>
     arw[]) >>
strip_tac >> dimp_tac >> strip_tac (* 2 *)>-- 
(qby_tac ‘phi o pa(Ar2,aR2,x,tp(p1',p2',ev',pR,pone',psi o pR)) = 
          ev o pa(p1,p2,pA,tp(p1,p2,ev,Ar2,aR2,phi) o tp (p1',p2',ev',pR,pone',psi o pR) o pone) o pa(pA,pone,id(A),to1(A,1)) o x’ 
 >-- (irule compose_partial_ev >> arw[]) >>
 (*qby_tac ‘phi o pa(Ar2,aR2,x,tp(p1',p2',ev',pR,pone',psi o pR)) = i2’*)
 rfs[] >>
 drule fac_char_via_any_map >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum (qspecl_then ["pa(Ar2,aR2,x,tp(p1', p2', ev', pR, pone', psi o pR))"] assume_tac) >>
 rfs[] >> (*already have ‘∃r'. r'∶one → R' ∧ (h2R ∘ ψ) ∘ r' = ⟨x,tp (psi ∘ p1 R one)⟩’ here the r' is called a*)
 qexistsl_tac ["p1' o Psi o a"] >> strip_tac (* 2 *)
 >-- (qexistsl_tac ["a"] >> irule to_p_eq >>
      qexistsl_tac ["R","p1'","R2","p2'"] >> 
      drule exp_ispr >> drule p12_of_pa >> once_arw[] >> rw[] >> 
      qby_tac ‘p2' = aR2 o h2R’
      >-- (qpick_x_assum ‘pa(Ar2, aR2, h o p1', p2') = h2R’ 
           (assume_tac o GSYM) >> once_arw[] >> 
           qpick_x_assum ‘ispr(Ar2, aR2)’ assume_tac >>
           drule p2_of_pa >> once_arw[] >> rw[]) >>
      once_arw[] >>
      qby_tac ‘(aR2 o h2R) o Psi o a = aR2 o (h2R o Psi) o a’
      >-- rw[o_assoc] >> arw[] >> 
      qpick_x_assum ‘ispr(Ar2, aR2)’ assume_tac >>
      drule p2_of_pa >> once_arw[] >> rw[]) >>
 qby_tac ‘h o p1' = Ar2 o h2R’
 >-- (qpick_x_assum ‘pa(Ar2, aR2, h o p1', p2') = h2R’ 
      (assume_tac o GSYM) >> once_arw[] >> 
      qpick_x_assum ‘ispr(Ar2, aR2)’ assume_tac >>
      drule p1_of_pa >> once_arw[] >> rw[]) >>
 rw[GSYM o_assoc] >> once_arw[] >> 
 qby_tac ‘((Ar2 o h2R) o Psi) o a = Ar2 o (h2R o Psi) o a’
 >-- rw[o_assoc] >> arw[] >>
 qpick_x_assum ‘ispr(Ar2, aR2)’ assume_tac >>
 drule p1_of_pa >> once_arw[] >> rw[]) >>
qby_tac ‘phi o pa(Ar2,aR2,x,tp(p1',p2',ev',pR,pone',psi o pR)) = 
          ev o pa(p1,p2,pA,tp(p1,p2,ev,Ar2,aR2,phi) o tp (p1',p2',ev',pR,pone',psi o pR) o pone) o pa(pA,pone,id(A),to1(A,1)) o x’ 
>-- (irule compose_partial_ev >> arw[]) >> 
pop_assum (assume_tac o GSYM) >> once_arw[] >>
rfs[] >> pick_xnth_assum 15 (K all_tac) >> 
qby_tac ‘(h2R o Psi) o r' = h2R o pa(p1', p2', r, tp(p1', p2', ev', pR, pone', psi o pR))’ >-- (arw[o_assoc]) >>
(*above step may do not need*)
qby_tac ‘m o e o r' = h2R o pa(p1', p2', r, tp(p1', p2', ev', pR, pone', psi o pR))’
>-- (rw[GSYM o_assoc] >> 
     qpick_x_assum ‘h2R o Psi = m o e’ (assume_tac o GSYM) >>
     once_arw[] >> first_x_assum accept_tac) >>
qby_tac ‘h2R o pa(p1', p2', r, tp(p1', p2', ev', pR, pone', psi o pR)) = 
pa(Ar2, aR2, x, tp(p1', p2', ev', pR, pone', psi o pR))’
>-- (irule to_p_eq >> qexistsl_tac ["A","Ar2","R2","aR2"] >>
     drule p12_of_pa >> once_arw[] >> 
     qpick_x_assum 
     ‘pa(Ar2, aR2, h o p1', p2') = h2R’ (assume_tac o GSYM) >>
     once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >> 
     drule exp_ispr >> drule p12_of_pa >> once_arw[] >>
     rw[o_assoc] >> once_arw[] >> first_x_assum accept_tac) >>
qby_tac ‘phi o h2R o pa(p1', p2', r, tp(p1', p2', ev', pR, pone', psi o pR)) =  i2’
>-- (qpick_x_assum ‘char(i1, i2, m) = phi’ (assume_tac o GSYM) >>
     once_arw[] >> drule fac_char >>
     first_x_assum 
     (qspecl_then ["1","pa(Ar2, aR2, x, tp(p1', p2', ev', pR, pone', psi o pR))"] assume_tac) >>
     qby_tac ‘to1(1,1) = id(1)’ 
     >-- (once_rw[one_to_one_id] >> rw[]) >> 
     qsuff_tac ‘char(i1, i2, m) o pa(Ar2, aR2, x, tp(p1', p2', ev', pR, pone', psi o pR)) = i2 o to1(1, 1)’
     >-- (once_arw[] >> rw[idR]) >>
     qsuff_tac ‘m o e o r' =
               pa(Ar2, aR2, x, tp(p1', p2', ev', pR, pone', psi o pR))’
     >-- (strip_tac >> first_x_assum drule >> 
         first_x_assum (qspecl_then ["two","i1","i2"] assume_tac) >>
         first_x_assum drule >> first_x_assum accept_tac) >>
     once_arw[] >> first_x_assum accept_tac) >>
rfs[]
)
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
!A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
!R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
!R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
!h:R->A.?hb:R2->A2. 
!psi:R-> two x:1->A.
 (ev o pa(p1,p2,pA,hb o tp(p1',p2',ev',pR,pone',psi o pR) o pone) o pa(pA,pone,id(A),to1(A,1)) o x = i2 <=> ?r:1->R. psi o r = i2 & h o r = x)”)

val qread_ax = read_axiom o q2str

val _ = new_fun "bar" (mk_ar_sort (mk_ob "R2") (mk_ob "A2"),
[("i1",mk_ar_sort one (mk_ob "two")),
 ("i2",mk_ar_sort one (mk_ob "two")),
 ("p1",mk_ar_sort (mk_ob "AA2") (mk_ob "A")),
 ("p2",mk_ar_sort (mk_ob "AA2") (mk_ob "A2")),
 ("ev",mk_ar_sort (mk_ob "AA2") (mk_ob "two")),
 ("pA",mk_ar_sort (mk_ob "A1") (mk_ob "A")),
 ("pone",mk_ar_sort (mk_ob "A1") one),
 ("p1'",mk_ar_sort (mk_ob "RR2") (mk_ob "R")),
 ("p2'",mk_ar_sort (mk_ob "RR2") (mk_ob "R2")),
 ("ev'",mk_ar_sort (mk_ob "RR2") (mk_ob "two")),
 ("pR",mk_ar_sort (mk_ob "R1") (mk_ob "R")),
 ("pone'",mk_ar_sort (mk_ob "R1") one),
 ("h",mk_ar_sort (mk_ob "R") (mk_ob "A"))])

val bar_def = 
qread_ax ‘!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
!A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
!R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
!R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
!h:R->A.
!psi:R-> two x:1->A.
 (ev o pa(p1,p2,pA,bar(i1,i2,p1,p2,ev,pA,pone,p1',p2',ev',pR,pone',h) o tp(p1',p2',ev',pR,pone',psi o pR) o pone) o pa(pA,pone,id(A),to1(A,1)) o x = i2 <=> ?r:1->R. psi o r = i2 & h o r = x)’

(*TODO: irule bug!
qsuff_tac ‘m o e o r' =
               pa(Ar2, aR2, x, tp(p1', p2', ev', pR, pone', psi o pR))’
     >-- (strip_tac >> first_x_assum drule >> 
         first_x_assum (qspecl_then ["two","i1","i2"] assume_tac) >>
         first_x_assum drule >> first_x_assum accept_tac)

exception find! and need qspecl, drule directly does not work, means that it does not find copr i1 i2 in assum
*)

(*for bar_exists, too many paramaters and I just want to use existence.*)

val diag_is_mono = proved_th $
e0
(rpt strip_tac >> irule ismono_applied >> rpt strip_tac >>
drule p1_of_pa >> 
qby_tac ‘pA1 o pa(pA1, pA2, id(A), id(A)) o g = pA1 o pa(pA1, pA2, id(A), id(A)) o h’
>-- (arw[]) >> pop_assum mp_tac >> rw[GSYM o_assoc] >> once_arw[] >>
rw[idL] >> strip_tac >> once_arw[] >> rw[])
(form_goal “!A AA pA1:AA->A pA2:AA->A. ispr(pA1,pA2) ==> ismono(pa(pA1,pA2,id(A),id(A)))”)

val fac_diag_eq = proved_th $
e0
(rpt strip_tac >> drule p12_of_pa >>
 qby_tac 
 ‘pA1 o pa(pA1, pA2, id(A), id(A)) o x0 = pA1 o pa(pA1, pA2, y, x) & 
  pA2 o pa(pA1, pA2, id(A), id(A)) o x0 = pA2 o pa(pA1, pA2, y, x)’
 >-- arw[] >>
 pop_assum mp_tac >> rw[GSYM o_assoc] >> once_arw[] >> rw[idL] >>
 disch_tac >> (pop_assum (assume_tac o GSYM)) >> arw[])
(form_goal 
“!A AA pA1:AA->A pA2:AA->A. ispr(pA1,pA2) ==> 
 !x:1->A y:1->A x0:1->A.pa(pA1,pA2,id(A),id(A)) o x0 = pa(pA1,pA2,y,x) ==> y = x”)


(*TODO: if give wrong input here then wrong err message:
(x_choosel_then ["AA","pA1","pA2"] assume_tac) pr_ex >>
pexistsl_tac ["tp(p1:AA2->A,p2:AA2->A2,ev:AA2->two,pA1:AA->A,pA2:AA->A,char(i1,i2,pa(pA1,pA2,id(A),id(A))))"]

match_term.unexpected term constructor
*)

val Thm6_lemma_2 = proved_th $
  e0
(rpt strip_tac >> 
qspecl_then ["A","A"] 
 (x_choosel_then ["AA","pA1","pA2"] assume_tac) pr_ex >>
pexistsl_tac ["tp(p1:AA2->A,p2:AA2->A2,ev:AA2->two,pA1:AA->A,pA2:AA->A,char(i1,i2,pa(pA1,pA2,id(A),id(A))))"] >> 
drule diag_is_mono >> drule char_def >> first_x_assum drule >>
rpt strip_tac >>
(*fac this pa(p1, p2, pA,
                (tp(p1, p2, ev, pA1, pA2,
                 char(i1, i2, pa(pA1, pA2, id(A), id(A)))) o x o pone))*)
qby_tac ‘ispr(pA,pone) & ispr(pA1,pA2) & ispr(p1,p2)’
>-- (drule exp_ispr >>arw[]) >>
drule parallel_p_one_side >> 
first_x_assum (qspecl_then ["x","tp(p1, p2, ev, pA1, pA2,char(i1, i2, pa(pA1, pA2, id(A), id(A))))"] assume_tac) >>
once_arw[] >> drule ev_of_tp >> first_x_assum drule >>
arw[GSYM o_assoc] >> rw[o_assoc] >>
qby_tac ‘pa(pA1, pA2, pA, (x o pone)) o
         pa(pA, pone, id(A), to1(A, 1)) o y = pa(pA1,pA2,y,x)’
>-- (drule to_p_eq >> first_x_assum irule >>
     drule p12_of_pa >> rw[GSYM o_assoc] >> once_arw[] >>
     qpick_x_assum ‘ispr(pA,pone)’ assume_tac >> rw[o_assoc] >>
     drule p12_of_pa >> rw[GSYM o_assoc] >> once_arw[] >> rw[idL] >>
     rw[o_assoc] >>
     qby_tac ‘x o pone o pa(pA, pone, id(A), to1(A, 1)) o y = 
              x o (pone o pa(pA, pone, id(A), to1(A, 1))) o y’
     >-- rw[o_assoc] >> once_arw[] >> arw[idL] >>
     once_rw[one_to_one_id] >> rw[idR]) >>
first_x_assum (qspecl_then ["pa(pA1, pA2, y, x)"] assume_tac) >>
once_arw[] >> pop_assum (assume_tac o GSYM) >> once_arw[] >> 
dimp_tac >> strip_tac (* 2 *) >-- 
(qsuff_tac ‘x0 = y & x0 = x’
 >-- (disch_tac >> pop_assum (assume_tac o GSYM) >> once_arw[] >> rw[]) >>
 drule p12_of_pa >> 
 qby_tac ‘pA1 o pa(pA1, pA2, id(A), id(A)) o x0 = pA1 o pa(pA1, pA2, y, x)
& pA2 o pa(pA1, pA2, id(A), id(A)) o x0 = pA2 o pa(pA1, pA2, y, x)’
 >-- arw[] >>
 pop_assum mp_tac >> rw[GSYM o_assoc] >> once_arw[] >> rw[idL]) >>
 qexistsl_tac ["x"] >> drule to_p_eq >> first_x_assum irule >>
 drule p12_of_pa >> rw[GSYM o_assoc] >> once_arw[] >> rw[idL] >>
 arw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!A A2 AA2 p1:AA2->A p2:AA2->A2 ev:AA2->two.isexp(p1,p2,ev) ==>
!A1 pA:A1->A pone:A1->1.ispr(pA,pone) ==>
?sg:A->A2.!x:1->A y:1->A. ev o pa(p1,p2,pA,sg o x o pone)  o pa(pA,pone,id(A),to1(A,1)) o y = i2 <=> y = x”)



val _ = new_fun "sg" (mk_ar_sort (mk_ob "A") (mk_ob "A2"),
[("i1",mk_ar_sort one (mk_ob "two")),
 ("i2",mk_ar_sort one (mk_ob "two")),
 ("p1",mk_ar_sort (mk_ob "AA2") (mk_ob "A")),
 ("p2",mk_ar_sort (mk_ob "AA2") (mk_ob "A2")),
 ("ev",mk_ar_sort (mk_ob "AA2") (mk_ob "two")),
 ("pA",mk_ar_sort (mk_ob "A1") (mk_ob "A")),
 ("pone",mk_ar_sort (mk_ob "A1") one),
 ("A",mk_ob_sort)])

val sg_def = 
qread_ax ‘!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!A A2 AA2 p1:AA2->A p2:AA2->A2 ev:AA2->two.isexp(p1,p2,ev) ==>
!A1 pA:A1->A pone:A1->1.ispr(pA,pone) ==>
!x:1->A y:1->A. ev o pa(p1,p2,pA,sg(i1,i2,p1,p2,ev,pA,pone,A) o x o pone)  o pa(pA,pone,id(A),to1(A,1)) o y = i2 <=> y = x’


val parallel_p_one_side_three' = 
parallel_p_one_side_three |> strip_all_and_imp |> split_assum |>
split_assum |> split_assum |> gen_all |> disch_first |> gen_all
 |> disch_nth 1 |> gen_all |> disch_first |> gen_all
 |> disch_last |> gen_all

val Thm6_g_ev_lemma = proved_th $
e0
(rpt strip_tac >> irule ev_eq_eq >>
 qexistsl_tac ["R","R1","pR","pone'","two","RR2","ev'","p1'","p2'"]
 (*qexistsl_tac ["R","R1","two","RR2","ev'","p1'","pR","p2'","pone'"] *)>>
 arw[] >> pop_assum (assume_tac o GSYM) >> once_arw[] >>
 drule exp_ispr >> drule parallel_p_one_side_three' >>
 qpick_x_assum ‘ispr(pR, pone')’ assume_tac>>
 first_x_assum drule >> rw[o_assoc] >> 
 qpick_x_assum ‘ispr(Ra2, rA2)’ assume_tac >>
 first_x_assum drule >>
 qspecl_then ["R","A"] 
 (x_choosel_then ["RA","Ra","rA"] assume_tac) pr_ex >>
 first_x_assum drule >> once_arw[] >>
 rw[GSYM o_assoc] >> drule ev_of_tp >>
 qpick_x_assum ‘ispr(Ra2, rA2)’ assume_tac >> first_x_assum drule >>
 once_arw[] >> 
 drule ev_of_tp >>
 qpick_x_assum ‘ispr(pR, pone')’ assume_tac >>
 first_x_assum drule >> once_arw[] >>
 qpick_x_assum ‘ev o pa(p1, p2, pA, (sg(i1, i2, p1, p2, ev, pA, pone, A) o a o pone)) o pa(pA, pone, id(A), to1(A, 1)) o f0 = psi’ 
 (assume_tac o GSYM) >>
 once_arw[] >> rw[o_assoc] >> 
 qsuff_tac
 ‘pa(p1, p2, (f0 o Ra2), rA2) o
    pa(Ra2, rA2, Ra, (sg(i1, i2, p1, p2, ev, pA, pone, A) o rA)) o
    pa(Ra, rA, pR, a o pone') = 
 pa(p1, p2, pA, (sg(i1, i2, p1, p2, ev, pA, pone, A) o a o
 pone)) o pa(pA, pone, id(A), to1(A, 1)) o f0 o pR’
 >-- (strip_tac >> once_arw[] >> rw[]) >>
 irule to_p_eq >>
 qexistsl_tac ["A","p1","A2","p2"] >> 
 rev_drule exp_ispr >> drule p12_of_pa >> rw[GSYM o_assoc] >> 
 once_arw[] >>
 qby_tac 
 ‘(f0 o Ra2) o
               pa(Ra2, rA2, Ra, sg(i1, i2, p1, p2, ev, pA, pone, A) o rA) = f0 o Ra2 o
               pa(Ra2, rA2, Ra, sg(i1, i2, p1, p2, ev, pA, pone, A) o rA)’
 >-- rw[o_assoc] >>
 once_arw[] >>
 qpick_x_assum ‘ispr(Ra2, rA2)’ assume_tac >>
 drule p12_of_pa >> once_arw[] >> once_arw[] >> 
 qpick_x_assum ‘ispr(Ra, rA)’ assume_tac >>
 drule p12_of_pa >> rw[o_assoc] >> once_arw[] >>
 qby_tac ‘sg(i1, i2, p1, p2, ev, pA, pone, A) o a o pone o
          pa(pA, pone, id(A), to1(A, 1)) o f0 o pR = 
          sg(i1, i2, p1, p2, ev, pA, pone, A) o a o (pone o
          pa(pA, pone, id(A), to1(A, 1))) o f0 o pR’
 >-- rw[o_assoc] >> once_arw[] >>
 qpick_x_assum ‘ispr(pA, pone)’ assume_tac >> 
 drule p12_of_pa >> once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >>
 rw[idL] >> rw[o_assoc] >>
 qspecl_then ["R1","pone'","to1(A, 1) o f0 o pR"] assume_tac to1_unique >>
 once_arw[] >> rw[]
 )
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
!A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
!R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
!R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
!RA2 Ra2:RA2->R rA2:RA2 ->A2.ispr(Ra2,rA2) ==>
!a:1->A a':1->A f0:R->A f1:R->A.
!psi:R->two.psi = 
ev o pa(p1,p2,pA,sg(i1,i2,p1,p2,ev,pA,pone,A) o a o pone) o 
pa(pA,pone,id(A),to1(A,1)) o f0 ==>
tp(p1',p2',ev',Ra2,rA2,ev o pa(p1,p2,f0 o Ra2,rA2)) o sg(i1,i2,p1,p2,ev,pA,pone,A) o a = 
tp(p1',p2',ev',pR,pone', psi o pR)”)


val Thm6_g_ev = proved_th $
e0
(rpt strip_tac >> 
 abbrev_tac (rapf "ev o pa(p1:AA2->A,p2:AA2->A2,pA:A1->A,sg(i1:1->two,i2:1->two,p1,p2,ev:AA2->two,pA,pone:A1->1,A) o a o pone) o pa(pA,pone,id(A),to1(A,1)) o f0:R->A = psi") >> drule Thm6_g_ev_lemma >> 
 first_x_assum rev_drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >> 
 qby_tac 
 ‘tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2)))
  o sg(i1, i2, p1, p2, ev, pA, pone, A) o a o pone = 
 (tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2)))
  o sg(i1, i2, p1, p2, ev, pA, pone, A) o a) o pone’
 >-- rw[o_assoc] >> once_arw[] >> once_arw[]
 >> drule bar_def >> first_x_assum rev_drule >>
 first_x_assum drule >> first_x_assum drule >> 
 first_x_assum drule >> once_arw[] >> 
 by_tac (rapf "!r:1->R.f0:R->A o r = a <=> psi o r = i2:1->two")
 >-- (qpick_x_assum ‘ev o pa(p1, p2, pA, (sg(i1, i2, p1, p2, ev, pA, pone, A) o a o pone)) o pa(pA, pone, id(A), to1(A, 1)) o f0 = psi’
      (assume_tac o GSYM) >>
      once_arw[] >> drule sg_def >> first_x_assum rev_drule >>
      first_x_assum rev_drule >> rw[o_assoc] >> once_arw[] >>
      strip_tac (*>> dimp_tac *)>> rw[]) >>
 dimp_tac >> strip_tac >--
 (qexistsl_tac ["r"] >> rfs[]) >>
 qexistsl_tac ["r"] >> pop_assum mp_tac >> pop_assum mp_tac >>
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >> rpt strip_tac >> arw[]
 )
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
!A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
!R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
!R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
!RA2 Ra2:RA2->R rA2:RA2 ->A2.ispr(Ra2,rA2) ==>
!a:1->A a':1->A f0:R->A f1:R->A.
ev o 
pa(p1,p2,pA,
bar(i1,i2,p1,p2,ev,pA,pone,p1',p2',ev',pR,pone',f1) o 
tp(p1',p2',ev',Ra2,rA2,ev o pa(p1,p2,f0 o Ra2,rA2)) o sg(i1,i2,p1,p2,ev,pA,pone,A) o a o pone) o pa(pA,pone,id(A),to1(A,1)) o a' = i2 <=> ?r:1->R. f0 o r = a & f1 o r = a'”)

val Thm6_g_ev' = proved_th $
e0
(rpt strip_tac >> assume_tac (Thm6_g_ev |> strip_all_and_imp) >>
 qby_tac ‘pa(pA, pone, id(A), to1(A, 1)) o a' = 
         pa(pA, pone, a', id(1))’ 
 >-- (rev_drule compose_with_id_to1 >> once_arw[] >> rw[]) >>
 fs[])
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
!A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
!R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
!R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
!RA2 Ra2:RA2->R rA2:RA2 ->A2.ispr(Ra2,rA2) ==>
!a:1->A a':1->A f0:R->A f1:R->A.
ev o 
pa(p1,p2,pA,
bar(i1,i2,p1,p2,ev,pA,pone,p1',p2',ev',pR,pone',f1) o 
tp(p1',p2',ev',Ra2,rA2,ev o pa(p1,p2,f0 o Ra2,rA2)) o sg(i1,i2,p1,p2,ev,pA,pone,A) o a o pone) o pa(pA,pone,a',id(1)) = i2 <=> ?r:1->R. f0 o r = a & f1 o r = a'”)


val f0g_eq_f1g = proved_th $
 e0
(rpt strip_tac >> irule fun_ext >> strip_tac >> irule ev_eq_eq >>
 qexistsl_tac ["A","A1","pA","pone","two","AA2","ev","p1","p2"]
 (*qexistsl_tac ["A","A1","two","AA2","ev","p1","pA","p2","pone"] *) >> 
 arw[] >> irule fun_ext >> strip_tac >> 
 qpick_x_assum ‘ispr(pA, pone)’ assume_tac >>
 drule to_p_with_1 >> 
 first_x_assum (qspecl_then ["a'"] strip_assume_tac) >>
 rw[o_assoc] >> once_arw[] >> irule one_to_two_eq >>
 qexistsl_tac ["i1","i2"] >> arw[] >>
 qby_tac ‘issymm(f0, f1) & istrans(f0, f1)’ >-- arw[] >>
 drule symm_trans_rel_lemma >> 
 first_x_assum (qspecl_then ["a0","a"] assume_tac) >>
 drule Thm6_g_ev' >> first_x_assum rev_drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >> once_arw[] >>
 first_assum (qspecl_then ["f0 o a","a0","f0","f1"] assume_tac) >>
 fs[o_assoc] >> once_arw[] >>
 first_assum (qspecl_then ["f1 o a","a0","f0","f1"] assume_tac) >>
 fs[o_assoc] >> once_arw[])
(form_goal
“!R A f0:R->A f1:R->A. issymm(f0,f1) & istrans(f0,f1) ==> 
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
 !R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
 !RA2 Ra2:RA2->R rA2:RA2 -> A2. ispr(Ra2,rA2) ==>
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o f0 = 
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o f1”)

val Thm6_page29_means_just_that = proved_th $
e0
(rpt strip_tac >> 
 drule Thm6_g_ev' >> first_x_assum rev_drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_assum (qspecl_then ["a0","a'","f0","f1"] assume_tac) >>
 first_x_assum (qspecl_then ["a1","a'","f0","f1"] assume_tac) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 pop_assum (K all_tac) >>
 fs[GSYM o_assoc])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
 !R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
 !RA2 Ra2:RA2->R rA2:RA2 -> A2. ispr(Ra2,rA2) ==>
 !a0:1->A a1:1->A f0:R->A f1:R->A.
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o a0 = 
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o a1 ==>
 !a':1->A.(?r:1->R. f0 o r = a0 & f1 o r = a') <=>
          (?r:1->R. f0 o r = a1 & f1 o r = a')”)


(*TO-DO: let rw be able to solve f <=>f*)
val compose_with_g_eq_equiv = proved_th $
e0
(rpt strip_tac >>
 assume_tac (Thm6_page29_means_just_that |> strip_all_and_imp |> allI ("a'",mk_ar_sort one (mk_ob "A"))) >>
 irule equiv_to_same_element >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >> strip_tac >> rw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
 !R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
 !RA2 Ra2:RA2->R rA2:RA2 -> A2. ispr(Ra2,rA2) ==>
 !a0:1->A a1:1->A f0:R->A f1:R->A.
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o a0 = 
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o a1 ==>
 isrefl(f0,f1) ==>
 ?r:1->R. f0 o r = a0 & f1 o r = a1”)

val Thm6_page29_picture = proved_th $
e0
(rpt strip_tac >>
 qby_tac ‘issymm(f0, f1) & istrans(f0, f1)’ >-- arw[] >> 
 drule f0g_eq_f1g >> first_x_assum drule >> 
 first_x_assum rev_drule >> first_x_assum rev_drule >> 
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >>
 abbrev_tac (rapf "bar(i1:1->two, i2:1->two, p1:AA2->A, p2:AA2->A2, ev:AA2->two, pA:A1->A, pone:A1->1, p1':RR2->R, p2':RR2->R2, ev':RR2->two, pR:R1->R, pone':R1->1, f1:R->A) o tp(p1', p2', ev', Ra2:RA2->R, rA2:RA2->A2, (ev o pa(p1, p2, f0:R->A o Ra2, rA2))) o sg(i1, i2, p1, p2, ev, pA, pone, A) = l") >> fs[GSYM o_assoc] >> 
 suffices_tac (rapf "?u:cE->A2. u o ce = l:A->A2")
 >-- (strip_tac >> pop_assum (assume_tac o GSYM) >> fs[] >>
      arw[o_assoc]) 
 (*qsuff_tac ‘?u:cE->A2. u o ce = l’example of qsuff does not response *)>>
 qexistsl_tac ["coeqind(ce,f0,f1,l)"] >> drule coeq_eqn >>
 first_x_assum irule >>
 first_x_assum accept_tac
)
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !A AA2 p1:AA2->A A2 p2:AA2->A2 ev: AA2 -> two. isexp(p1,p2,ev) ==>
 !A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==>
 !R RR2 p1':RR2->R R2 p2':RR2 -> R2 ev':RR2->two. isexp(p1',p2',ev') ==>
 !R1 pR:R1->R pone':R1->1. ispr(pR,pone') ==>
 !RA2 Ra2:RA2->R rA2:RA2 -> A2. ispr(Ra2,rA2) ==>
 !f0:R->A f1:R->A. issymm(f0,f1) ==> istrans(f0,f1) ==> 
 !cE ce:A->cE. iscoeq(ce,f0,f1) ==>
 !a0:1->A a1:1->A.
 ce o a0 = ce o a1 ==>
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o a0 = 
 bar(i1, i2, p1, p2, ev, pA, pone, p1', p2',ev', pR, pone', f1) o 
 tp(p1', p2', ev', Ra2, rA2, (ev o pa(p1, p2, f0 o Ra2, rA2))) o 
 sg(i1, i2, p1, p2, ev, pA, pone, A) o a1”)

val Thm6 = proved_th $
e0
(rpt strip_tac >> irule Thm6_first_sentence >> 
 qexistsl_tac ["A","f0","f1","AA","e","pA1","pA2","cE","ce"] 
 (*qexistsl_tac ["A","AA","cE","ce","e","f0","f1","pA1","pA2"] *)>>
 arw[] >> rpt strip_tac >> irule equiv_to_same_element >> 
 once_arw[] >> rw[] >> 
 qspecl_then ["1","1"] 
 (x_choosel_then ["two","i1","i2"] assume_tac) copr_ex >>
 qspecl_then ["A","1"] 
 (x_choosel_then ["A1","pA","pone"] assume_tac) pr_ex >>
 qspecl_then ["R","1"] 
 (x_choosel_then ["R1","pR","pone'"] assume_tac) pr_ex >>
 qspecl_then ["A","two"] 
 (x_choosel_then ["A2","AA2","p1","p2","ev"] assume_tac) exp_ex >>
 qspecl_then ["R","two"] 
 (x_choosel_then ["R2","RR2","p1'","p2'","ev'"] assume_tac) exp_ex >>
 qspecl_then ["R","A2"] 
 (x_choosel_then ["RA2","Ra2","rA2"] assume_tac) pr_ex >>
 drule Thm6_page29_means_just_that >>
 first_x_assum rev_drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >> 
 first_x_assum drule >> 
 first_x_assum irule >> 
 drule Thm6_page29_picture >> first_x_assum rev_drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum irule >> 
 qexistsl_tac ["cE","ce"] >> arw[])
(form_goal
“!A AA pA1:AA->A pA2:AA->A. ispr(pA1,pA2) ==>
 !R f0:R->A f1:R->A. ismono(pa(pA1,pA2,f0,f1)) ==>
 isrefl(f0,f1) & issymm(f0,f1) & istrans(f0,f1) ==> 
 !cE ce:A->cE. iscoeq(ce,f0,f1) ==>
 !E e:E->AA. iseq(e,ce o pA1,ce o pA2) ==>
 areiso(R,E)”)


(*Theorem char_pb:
∀A X a. is_mono a ∧ a∶ A → X ⇒
        ∃h1 h2.
          (pb1 (char a) (i2 one one)) ∘ h1 = a ∧
          a ∘ h2 = pb1 (char a) (i2 one one) ∧
          h1∶ A → pbo (char a) (i2 one one) ∧
          h2∶ pbo (char a) (i2 one one) → A ∧
          h1 ∘ h2 = id (pbo (char a) (i2 one one)) ∧
          h2 ∘ h1 = id A*)

val dom_1_mono = proved_th $
e0
(rpt strip_tac >> irule ismono_applied >> rpt strip_tac >>
 qspecl_then ["X'","g","h"] accept_tac to1_unique)
(form_goal “!X f:1->X. ismono(f)”)


(*Theorem pb_fac_exists':
∀X Y Z f g.
         f∶X → Z ∧ g∶Y → Z ⇒
         ∀A u v.
             u∶A → X ∧ v∶A → Y ∧ f ∘ u = g ∘ v ⇒
             ∃a. a∶A → pbo f g ∧ pb1 f g ∘ a = u ∧ pb2 f g ∘ a = v
Proof
rw[] >>
‘pb1 f g∶pbo f g → X ∧ pb2 f g∶pbo f g → Y ∧
         f ∘ pb1 f g = g ∘ pb2 f g ∧
         ∀A u v.
             u∶A → X ∧ v∶A → Y ∧ f ∘ u = g ∘ v ⇒
             ∃!a. a∶A → pbo f g ∧ pb1 f g ∘ a = u ∧ pb2 f g ∘ a = v’
  by (irule pb_thm >> metis_tac[]) >>
fs[EXISTS_UNIQUE_ALT] >> metis_tac[]
QED*)

val pb_fac_exists' = proved_th $
e0
(rpt strip_tac >> fs[ispb_def] >> first_x_assum drule >> 
 pop_assum strip_assume_tac >> qexistsl_tac ["a"] >> 
 first_x_assum (qspecl_then ["a"] assume_tac) >> arw[])
(form_goal “!X Z f:X->Z Y g:Y->Z Pb p:Pb->X q:Pb->Y.ispb(f:X->Z,g:Y->Z,p,q) ==> 
 !A u v. f o u = g o v ==> ?a:A->Pb. p o a = u & q o a = v”)

val char_pb = proved_th $
e0
(rpt strip_tac >> irule prop_2_corollary_as_subobj >> arw[]>>
 drule pb_mono_mono >> 
 qspecl_then ["two","i2"] assume_tac dom_1_mono >>
 first_x_assum drule >> arw[] >>
 rpt strip_tac (* 2 *) >-- 
 (by_tac 
   (rapf "?y:1->Pb. pb1:Pb->X o y = a:A->X o x:1->A & pb2:Pb->1 o y = id(1)") >--
  (drule pb_fac_exists' >> (*TO-DO:irule bug,should use irule works*)
  first_x_assum (qspecl_then ["1","a o x","id(1)"] assume_tac) >>
  rev_drule char_def >> first_x_assum drule >>
  (*TO-DO: once have pull exists test here test pass*)
  first_x_assum (qspecl_then ["a o x"] assume_tac) >>
  qsuff_tac ‘char(i1, i2, a) o a o x = i2’
  >-- (strip_tac >> fs[idR] >> qexistsl_tac ["a'"] >> arw[]) >>
  pop_assum (assume_tac o GSYM) >> arw[] >>
  qexistsl_tac ["x"] >> rw[]) >>
  pop_assum strip_assume_tac >> qexistsl_tac ["y"] >> arw[]) >>
rev_drule char_def >> first_x_assum drule >>
drule (ispb_def |> iffLR) >> pop_assum strip_assume_tac >> arw[] >>
qby_tac ‘char(i1, i2, a) o pb1 o y = i2 o pb2 o y’
>-- (rw[GSYM o_assoc] >> arw[]) >> 
pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!A X a.ismono(a:A->X) ==> 
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !Pb pb1 pb2. ispb(char(i1,i2,a),i2,pb1,pb2) ==> 
    ?h1 h2.pb1 o h1 = a & a o h2 = pb1 & h1 o h2 = id(Pb) & h2 o h1 = id(A)”)

val char_square = proved_th $
e0
(rpt strip_tac >> irule fun_ext >> rpt strip_tac >> 
 drule char_def >> first_x_assum drule >> 
 first_x_assum (qspecl_then ["a o a'"] assume_tac) >> rw[o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 pop_assum (assume_tac o GSYM) >>
 arw[] >> qexistsl_tac ["a'"] >> rw[])
(form_goal
“!two i1 i2.iscopr(i1:1->two,i2:1->two) ==>!A X a:A->X. ismono(a) ==> char(i1,i2,a) o a = i2 o to1(A,1)”)

val pb_ex = pb_exists

val char_is_pb = proved_th $
e0
(rpt strip_tac >> drule char_pb >> first_x_assum drule >>
 (qspecl_then ["X","two","char(i1, i2, a)","1","i2"] assume_tac) pb_ex >>
 pop_assum (x_choosel_then ["Pb","pb1","pb2"] assume_tac) >>
 first_x_assum drule  >> pop_assum strip_assume_tac >> 
 drule (ispb_def |> iffLR) >> pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["A","a","to1(A,1)"] assume_tac) >>
 rw[ispb_def] >>
 qby_tac ‘char(i1, i2, a) o a = i2 o to1(A, 1)’
 >-- (qby_tac ‘char(i1, i2, a) o pb1 o h1 = i2 o pb2 o h1’
      >-- (arw[GSYM o_assoc]) >> rfs[] >> 
      qspecl_then ["A","pb2 o h1","to1(A,1)"] assume_tac to1_unique >>
      arw[]) >>
 arw[] >> rpt strip_tac >>
 (*here the goal is ?(a' : A' -> A). !(a' : A' -> A). a o a'# = u & to1(A, 1) o a'# = v <=>
                 a'# = a'# ... same name*) 
 suffices_tac (rapf "?a':A'->A. a:A->X o a' = u")
 >-- (strip_tac >> qexistsl_tac ["a'"] >> strip_tac >> dimp_tac >>
      strip_tac (* 2 *)
      >-- (irule ismono_property >> qexistsl_tac ["X","a"] >>
           arw[]) >>
      arw[] >> 
      qspecl_then ["A'","to1(A, 1) o a'","v"] assume_tac to1_unique >>
      arw[])  >>
 drule (ispb_def |> iffLR) >> pop_assum strip_assume_tac >> 
 last_x_assum drule >> pop_assum (K all_tac) (* drule this line is useless, just to kill the assumption*) >>
 first_x_assum (qspecl_then ["A'","u","v"] assume_tac) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexistsl_tac ["h2 o a'"] >> 
 first_x_assum (qspecl_then ["a'"] assume_tac) >> fs[] >>
 arw[GSYM o_assoc])
(form_goal 
“ismono(a:A->X) ==> iscopr(i1:1->two,i2) ==> ispb(char(i1,i2,a),i2,a,to1(A,1))”)

val char_is_pb_unique = proved_th $
e0
(rpt strip_tac >> irule fun_ext >> rpt strip_tac >>
 irule one_to_two_eq >> qexistsl_tac ["i1","i2"] >> 
 drule char_is_pb >> first_x_assum drule >> 
 drule (iffLR ispb_def) >> pop_assum strip_assume_tac >>
 rev_drule (iffLR ispb_def) >> pop_assum strip_assume_tac >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘c o a' = i2 o id(1)’ >-- arw[idR] >>
      first_x_assum drule >> 
      pop_assum strip_assume_tac >>
      first_x_assum (qspecl_then ["a''"] assume_tac) >> fs[] >>
      qby_tac ‘char(i1, i2, a) o a o a'' = i2 o to1(A, 1) o a''’
      >-- arw[GSYM o_assoc] >> pop_assum mp_tac >>
      once_rw[one_to_one_id] >> rw[idR] >> once_arw[] >> rw[]) >>
 qby_tac ‘char(i1, i2, a) o a' = i2 o id(1)’ >-- arw[idR] >>
 last_x_assum drule >>
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["a''"] assume_tac) >> fs[] >>
 qby_tac ‘c o a o a'' = i2 o to1(A, 1) o a''’ 
 >-- arw[GSYM o_assoc] >> pop_assum mp_tac >>
 once_rw[one_to_one_id] >> rw[idR] >> once_arw[] >> rw[]
 )
(form_goal
“!A X a:A->X. ismono(a) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !c:X->two. ispb(c,i2,a,to1(A,1)) ==> c = char(i1,i2,a)”)

val iso_subobj_same_char = proved_th $
e0
(rpt strip_tac >> irule char_is_pb_unique >> arw[] >>
 drule char_square >> first_x_assum drule >>
 (*qspecl_then ["X","two","char(i1,i2,a)",""] assume_tac pb_ex*)
 rw[ispb_def] >> 
 qby_tac ‘char(i1, i2, a) o b = i2 o to1(B, 1)’
 >-- (qpick_x_assum ‘a o h2 = b’ (assume_tac o GSYM) >>
     once_arw[] >> rev_drule char_def >> 
     first_x_assum drule >> irule fun_ext >> strip_tac >>
     rw[o_assoc] >> 
     first_x_assum (qspecl_then ["a o h2 o a'"] assume_tac) >>
     once_rw[one_to_one_id] >> rw[idR] >>
     pop_assum (assume_tac o iffLR) >> first_x_assum irule >>
     qexistsl_tac ["h2 o a'"] >> rw[]) >>
 arw[] >> rpt strip_tac >>
 rev_drule char_is_pb >> first_x_assum drule >> 
 drule (iffLR ispb_def) >> pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["A'"] assume_tac) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexistsl_tac ["h1 o a'"] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule ismono_property >> qexistsl_tac ["X","b"] >>
     arw[] >> first_x_assum (qspecl_then ["a'"] assume_tac) >> fs[] >>
     qpick_x_assum ‘a o a' = u’ mp_tac >>
     qpick_x_assum ‘b o h1 = a’ (assume_tac o GSYM) >>
     once_arw[] >> rw[o_assoc]) >>
 qspecl_then ["A'"] assume_tac to1_unique >>
 first_x_assum (qspecl_then ["v","to1(B,1) o a''"] assume_tac) >>
 arw[] >>
 first_x_assum (qspecl_then ["a'"] assume_tac) >> fs[] >>
 qpick_x_assum ‘a o a' = u’ mp_tac >>
 qpick_x_assum ‘b o h1 = a’ (assume_tac o GSYM) >>
 once_arw[] >> rw[o_assoc]
 )
(form_goal  
“!a.ismono(a:A->X) ==>!b.ismono(b:B->X) ==>
 !h1:A->B h2:B->A. h1 o h2 = id(B) & h2 o h1 = id(A) ==> 
 b o h1 = a & a o h2 = b ==> 
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 char(i1,i2,a) = char(i1,i2,b)”)

(* !NN (Nn : NN# -> N)  (nN : NN# -> N). ispr(Nn#, nN#) ==>
                 ?NE (ne : NE# -> NN#). ismono(ne) &
                   !Sum (iEQ : N -> Sum#)
                     (iNE : NE# -> Sum#). iscopr(iEQ#, iNE#) ==>
                     isiso(copa(iEQ#, iNE#, pa(Nn#, nN#, id(N), id(N)), ne))]

ppbug , see ne has no #*)

val ne_ex = proved_th $
e0
(rpt strip_tac >> drule diag_is_mono >> drule Thm5 >>
 first_x_assum accept_tac)
(form_goal
“!NN Nn:NN->N nN:NN->N. ispr(Nn,nN) ==> ?NE ne:NE->NN. ismono(ne) & 
 !Sum iEQ:N -> Sum iNE:NE->Sum. iscopr(iEQ:N->Sum,iNE:NE->Sum) ==>
 isiso(copa(iEQ,iNE,pa(Nn,nN,id(N),id(N)),ne))”)

val PRE_def = ex2fsym "PRE" [] $ iffRL $ eqT_intro pred_exists 
                       |> C mp (trueI [])

val minus_uex = proved_th $
e0
(rpt strip_tac >> rev_drule Thm1 >> first_x_assum drule >> 
 first_x_assum drule >> 
 first_x_assum (qspecl_then ["id(N)","PRE o nnN"] assume_tac) >>
 pop_assum strip_assume_tac >> qexistsl_tac ["f"] >> fs[idL,o_assoc])
(form_goal
“!NN Nn:NN->N nN:NN->N. ispr(Nn,nN) ==>
 !NNN NNn:NNN->NN nnN:NNN->N.ispr(NNn,nnN) ==>
 !N1 pN':N1->N pone:N1-> 1. ispr(pN',pone) ==>
 ?sub:NN->N.!sub':NN->N.sub' o pa(Nn,nN,pN',ZERO o pone) = pN' & 
 PRE o nnN o pa(NNn,nnN,id(NN),sub') = sub' o pa(Nn,nN,Nn,SUC o nN) <=> sub' = sub”)



val minus_ex = proved_th $ 
e0
(rpt strip_tac >> rev_drule minus_uex >> first_x_assum drule >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexistsl_tac ["sub"] >> first_x_assum (qspecl_then ["sub"] assume_tac) >>
 fs[])
(form_goal
“!NN Nn:NN->N nN:NN->N. ispr(Nn,nN) ==>
 !NNN NNn:NNN->NN nnN:NNN->N.ispr(NNn,nnN) ==>
 !N1 pN':N1->N pone:N1-> 1. ispr(pN',pone) ==>
 ?sub:NN->N.
 sub o pa(Nn,nN,pN',ZERO o pone) = pN' &
 PRE o nnN o pa(NNn,nnN,id(NN),sub) = sub o pa(Nn,nN,Nn,SUC o nN)”)


(*TODO: ppbug |-
   ?(p1 : NN -> N)  (p2 : NN -> N). ispr(p1#, p2): thm*)

val NN_def = pr_ex |> allE N |> allE N |> eqT_intro |> iffRL 
                   |> ex2fsym "NN" [] |> C mp (trueI [])

val NN = mk_fun "NN" []

val Nn_def = NN_def |> eqT_intro |> iffRL 
                    |> ex2fsym "Nn" [] |> C mp (trueI [])

val Nn = mk_fun "Nn" []


val nN_def = Nn_def |> eqT_intro |> iffRL 
                    |> ex2fsym "nN" [] |> C mp (trueI [])

(*

P(A,a:A->B) ==> ?c:B->A. Q(c,a)

Q(q(A,a))

!A. P(a,A) ==> ?c.Q(c,a)

TODO: think about if this, then 

then c |-> q(a,A)

but if 

P(a,A) ==> ?c.Q(c,a)

then c |-> q(a)




*)

val nN = mk_fun "nN" []

val NNN_def = pr_ex |> allE NN |> allE N |> eqT_intro |> iffRL 
                   |> ex2fsym "NNN" [] |> C mp (trueI [])

val NNN = mk_fun "NNN" []

val NNn_def = NNN_def |> eqT_intro |> iffRL 
                    |> ex2fsym "NNn" [] |> C mp (trueI [])

val NNn = mk_fun "NNn" []

val nnN_def = NNn_def |> eqT_intro |> iffRL 
                     |> ex2fsym "nnN" [] |> C mp (trueI [])

val nnN = mk_fun "nnN" []


(*TODO: want the resolve stuff*)

val sub_def = minus_ex |> specl [NN,Nn,nN] |> C mp nN_def 
                       |> specl [NNN,NNn,nnN] |> C mp nnN_def
                       |> specl [N,rastt "id(N)",rastt "to1(N,1)"]
                       |> C mp (allE N pr_with_one)
                       |> eqT_intro |> iffRL |> ex2fsym "sub" []
                       |> C mp (trueI [])

val sub = mk_fun "sub" []

val LE_def = pb_ex |> specl [NN,N,sub] |> specl [rastt "1",ZERO] 
                   |> eqT_intro |> iffRL |> ex2fsym "LE" []
                   |> C mp (trueI [])

val LE = mk_fun "LE" []

val le_def = LE_def |> eqT_intro |> iffRL |> ex2fsym "le" []
                    |> C mp (trueI [])

val le = mk_fun "le" []

val le_pb = proved_th $
e0
(strip_assume_tac le_def >>
 assume_tac (to1_unique |> specl [LE]) >>
 first_x_assum (qspecl_then ["to1(LE,1)","q"] assume_tac) >> 
 fs[])
(form_goal “ispb(sub,ZERO,le,to1(LE,1))”)

val NE_def = ne_ex |> specl [NN,Nn,nN] |> C mp nN_def 
                   |> eqT_intro |> iffRL 
                   |> ex2fsym "NE" []
                   |> C mp (trueI [])

val ne_def = NE_def |> eqT_intro |> iffRL |> ex2fsym "ne" []
                    |> C mp (trueI [])

val NE = mk_fun "NE" []

val ne = mk_fun "ne" []


val LT_def = pb_ex |> specl [LE,NN,le] |> specl [NE,ne] 
                   |> eqT_intro |> iffRL |> ex2fsym "LT" []
                   |> C mp (trueI [])

val ltle_def = LT_def |> eqT_intro |> iffRL |> ex2fsym "ltle" []
                      |> C mp (trueI [])


val ltne_def = ltle_def |> eqT_intro |> iffRL |> ex2fsym "ltne" []
                      |> C mp (trueI [])

(*TOdO:AQ slow!!!!!
rpt gen_tac >> rw[ispb_def]*)

(*forall_fconv(forall_fconv (forall_fconv (forall_fconv (forall_fconv (forall_fconv(imp_fconv (rewr_fconv (spec_all ispb_def)))))))) ``!A B f:A->B g h i.ispb(f,g,h,i) ==> ispb(g,f,i,h)``;
*)

fun readf f = (fvf f,[]:form list,f)

val pb_reorder = proved_th $ 
e0
(rw[ispb_def] >> rpt strip_tac 
 >-- (pop_assum (K all_tac) >> once_arw[] >> rw[]) >>
 first_x_assum (qspecl_then ["A","v","u"] assume_tac) >>
 pick_x_assum “g:Y->Z o u:A->Y = f:X->Z o v”
 (assume_tac o GSYM) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexists_tac "a" >> strip_tac >>
 first_x_assum (qspecl_then ["a'"] assume_tac) >>
 (*TODO: AQ: how to automatic on this?*)
 qby_tac ‘q0 o a' = u & p0 o a' = v <=> p0 o a' = v & q0 o a' = u’ >--
 (dimp_tac >> disch_tac >> arw[] >>
  fs[]) >>
 arw[]
)
(form_goal
“!X Z f:X->Z Y g:Y->Z P p0:P->X q0:P->Y.ispb(f,g,p0,q0) ==>
 ispb(g,f,q0,p0)”)

val lt_mono = proved_th $
e0
(irule o_mono_mono >>
 by_tac “ismono(ne)” >-- 
 accept_tac (conjE1 ne_def) >>
 assume_tac ltne_def >> arw[] >> 
 strip_assume_tac le_def >>
 by_tac “ismono(ZERO)”
 >-- (qspecl_then ["N","ZERO"] accept_tac dom_1_mono) >>
 drule pb_mono_mono >> first_x_assum drule >> 
 qby_tac ‘ispb(ne,le, ltne, ltle)’ 
 >-- (rev_drule pb_reorder >> first_x_assum accept_tac)>>
 drule pb_mono_mono >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal “ismono(ne o ltne)”)


val inc_ismono = proved_th $
e0
(rpt strip_tac (* 2 *) >--
 (irule ismono_applied >> rpt strip_tac >>
 irule fun_ext >> strip_tac >>
 qby_tac ‘copa(iA,iB,id(A),g o a o to1(B,1)) o iA o g = copa(iA,iB,id(A),g o a o to1(B,1)) o iA o h’
 >-- arw[] >> pop_assum mp_tac >>
 drule i1_of_copa >> rw[GSYM o_assoc] >>
 arw[idL] >> strip_tac >> arw[]) >>
 irule ismono_applied >> rpt strip_tac >>
 irule fun_ext >> strip_tac >>
 qby_tac ‘copa(iA,iB,g o a o to1(A,1),id(B)) o iB o g =
          copa(iA,iB,g o a o to1(A,1),id(B)) o iB o h’
 >-- arw[] >> pop_assum mp_tac >>
 drule i2_of_copa >> rw[GSYM o_assoc] >>
 arw[idL] >> strip_tac >> arw[])
(form_goal 
“!A B AB iA:A->AB iB:B->AB. iscopr(iA,iB) ==>
 ismono(iA) & ismono(iB)”)


val ax7'= 
 ax7 |> strip_all_and_imp |> gen_all |>
 split_assum |> disch_last |> gen_all |> disch_all |> gen_all


val ax7_const1 = proved_th $
e0
(rpt strip_tac >> drule ax7' >> assume_tac const1_def >>
 first_x_assum drule >> fs[ismem0_def] >>
 drule inc_ismono >> fs[] >> rfs[] >>
 rw[ismem_def] >> arw[]
 )
(form_goal 
“!A AB iA:A->AB B iB:B->AB. iscopr(iA,iB) ==>
 !f:1->AB. ismem(f,iA) | ismem(f,iB)”)

val copr_disjoint = proved_th $
e0
(rpt strip_tac >> drule prop_5_lemma >> 
 drule ax7_const1 >> drule inc_ismono >> fs[ismem_def] >>
 first_x_assum (qspecl_then ["x"] assume_tac) >>
 cases_on “?x0 : 1 -> A. x:1->AB = iA o x0” (* 2 *)
 >-- (arw[] >> pop_assum strip_assume_tac >>
     ccontra_tac >> pop_assum strip_assume_tac >>
     qby_tac ‘iA o x0 = iB o x0'’ 
     >-- (pop_assum mp_tac >> 
          pop_assum (assume_tac o GSYM) >>
          strip_tac >> pop_assum (assume_tac o GSYM) >>
          pick_xnth_assum 2 (K all_tac) >> arw[]) >>
     rfs[]) >>
 arw[] >> pop_assum_list (map_every strip_assume_tac) (* 2 *)
 >-- (by_tac “?(x0 : 1 -> A). x = iA:A->AB o x0”
      >-- (qexists_tac "x0" >> arw[]) >>
      first_x_assum opposite_tac) >>
 qexists_tac "x0" >> arw[])
(form_goal “!A B AB iA:A->AB iB:B->AB. iscopr(iA,iB) ==>
!x:1->AB. (~(?x0:1->A. x = iA o x0)) <=> (?x0:1->B. x = iB o x0)”)



val i1_xor_i2 = proved_th $
e0
(rpt strip_tac >> drule copr_disjoint >>
 cases_on “x = i1:1->two” (* 2 *)
 >-- (arw[] >> drule i1_ne_i2 >> first_x_assum accept_tac) >>
 arw[] >> first_x_assum (qspecl_then ["x"] assume_tac) >>
 by_tac “~(?x0.x = i1:1->two o x0:1->1)”
 >-- (ccontra_tac >> pop_assum strip_assume_tac >>
     pop_assum mp_tac >> 
     by_tac “x0 = id(1)”
     >-- once_rw[one_to_one_id] >> arw[] >>
     arw[idR]) >>
 rfs[] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal 
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
  !x:1->two. x = i1 <=> ~(x = i2)”)


val  two2two_cases = proved_th $
e0
(rpt strip_tac >> drule from_copr_components >>
 first_x_assum (qspecl_then ["two","f"] assume_tac) >> 
 drule i1_xor_i2 >> once_arw[] >>
 pop_assum mp_tac >> pop_assum (K all_tac) >>
 strip_tac >> 
 first_assum (qspecl_then ["f o i1"] assume_tac) >>
 first_x_assum (qspecl_then ["f o i2"] assume_tac) >>
 cases_on “f:two ->two o i1:1->two = i2” (* 2 *)
 >-- (once_arw[] >> 
      cases_on “f:two ->two o i2:1->two = i2” (*2  *) >--
      (once_arw[] >> rw[]) >>
      fs[]) >>
 fs[] >> cases_on “f:two ->two o i2:1->two = i2” (*2 *) >--
 (once_arw[] >> rw[]) >>
 fs[])  
(form_goal “!two i1:1->two i2:1->two.iscopr(i1,i2) ==>
!f:two->two. f = copa(i1,i2,i1,i1) | f = copa(i1,i2,i1,i2) | f = copa(i1,i2,i2,i2) | f = copa(i1,i2,i2,i1)”)


val lt_def0 = proved_th $
e0
(qexistsl_tac ["ne o ltne"]>> rw[])
(form_goal “?lt. lt = ne o ltne”)

val lt_def = lt_def0 |> eqT_intro |> iffRL
                     |> ex2fsym "lt" []
                     |> C mp (trueI [])



val iscopr_def = read_axiom $ q2str
‘!A B AB i1:A->AB i2:B->AB. iscopr(i1,i2) <=>
 !X f:A->X g:B->X.?fg:AB->X. fg o i1 = f & fg o i2 = g &
 (!fg'. (fg' o i1 = f & fg' o i2 = g) ==> fg' = fg)’


(*TODO: AQ: how does rename tac work?*)

val iso_copr_copr = proved_th $
e0
(rpt strip_tac >> rw[iscopr_def] >> rpt strip_tac >>
 drule $ iffLR isiso_def>> drule copa_def >> fs[] >>
 first_x_assum (qspecl_then ["X'","f","g"] assume_tac) >>
 qexists_tac "copa(iA,iB,f,g) o f'" >> rw[o_assoc] >>
 by_tac “f' o f0 = iA & f':X->AB o g0:B->X = iB:B->AB” >-- 
 (qby_tac ‘f' o copa(iA, iB, f0, g0) o iA = id(AB) o iA & 
           f' o copa(iA, iB, f0, g0) o iB = id(AB) o iB’
  >-- arw[GSYM o_assoc] >>
  pop_assum mp_tac >> drule i12_of_copa >> arw[idL]) >>
 arw[] >> 
 drule i12_of_copa >> arw[] >> 
 rpt strip_tac >> irule isepi_property >>
 qexistsl_tac ["AB","copa(iA, iB, f0, g0)"] >>
 drule iso_is_epi >> arw[o_assoc,idR] >>
 drule from_cop_eq >> first_x_assum irule >> 
 drule i12_of_copa >> arw[o_assoc]
 )
(form_goal “!A B AB iA:A->AB iB:B->AB. iscopr(iA,iB) ==>
 !X f0:A->X g0:B->X. isiso(copa(iA,iB,f0,g0)) ==> iscopr(f0,g0)”)

val fac_diag_eq_iff = proved_th $
e0
(rpt strip_tac >> drule fac_diag_eq >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum irule >> qexists_tac "a0" >>
      drule to_p_eq >> first_x_assum irule >>
      drule p12_of_pa >> arw[GSYM o_assoc]) >>
 qexists_tac "aA o aa" >> drule to_p_eq >>
 first_x_assum irule >> drule p12_of_pa >>
 arw[GSYM o_assoc,idL])
(form_goal
 “!A AA Aa:AA->A aA:AA->A. ispr(Aa,aA) ==>
 !aa:1->AA.(?a0:1->A. aa = pa(Aa,aA,id(A),id(A)) o a0) <=>
  Aa o aa = aA o aa”)

val ne_property = proved_th $
e0
(rpt strip_tac >> assume_tac ne_def >>
 pop_assum strip_assume_tac >>
 qspecl_then ["N","NE"] (x_choosel_then ["W","iN","iNE"] assume_tac) copr_ex >>
 first_x_assum drule >>
 drule iso_copr_copr >> first_x_assum drule >>
 drule copr_disjoint >>
 by_tac
 “(?nnb : 1 -> NE. ne o nnb = nn:1->NN) <=> (?nnb : 1 -> NE. nn:1->NN= ne o nnb)” >--
 (dimp_tac >> strip_tac >> qexists_tac "nnb" >> arw[]) >>
 (*TODO AQ: how to avoid this trivial steps?*)
 arw[] >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >>
 assume_tac nN_def >> drule fac_diag_eq_iff >>
 first_x_assum (qspecl_then ["nn"] assume_tac) >>
 arw[])
(form_goal 
 “!nn:1->NN.(?nnb:1->NE. ne o nnb = nn) <=> ~
 (Nn o nn = nN o nn)”)

(*n1 <= n2 <=> n1 - n2 = 0
TODO: maybe an iff version of ispb_def
*)

val sub_z_iff_le = proved_th $
e0
(rpt strip_tac >> 
 assume_tac le_def >> pop_assum strip_assume_tac >>
 drule $ iffLR ispb_def >> 
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["1","pa(Nn,nN,n1,n2)","id(1)"] assume_tac) >> fs[idR] >> dimp_tac >> strip_tac (* 2 *)
 >-- (arw[GSYM o_assoc] >> rw[o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR]) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexists_tac "a" >>
 first_x_assum (qspecl_then ["a"] assume_tac) >> fs[])
(form_goal 
“!n1:1->N n2:1->N.
 (?le0:1->LE. pa(Nn,nN,n1,n2) = le o le0) <=>
 sub o pa(Nn,nN,n1,n2) = ZERO”)

val sub_zero_id = proved_th $
e0
(strip_tac >> assume_tac sub_def >>
 pop_assum strip_assume_tac >> 
 by_tac “sub o pa(Nn, nN, id(N), ZERO o to1(N, 1)) o n:1->N = id(N) o n” >-- (rw[GSYM o_assoc] >> arw[]) >>
 fs[idL] >> 
 by_tac “pa(Nn, nN, id(N), ZERO o to1(N, 1)) o n:1->N = pa(Nn, nN, n, ZERO)” >-- 
 (assume_tac nN_def >> drule to_p_eq >> 
  first_x_assum irule >> 
  drule p12_of_pa >> arw[GSYM o_assoc] >>
  rw[o_assoc] >> once_rw[one_to_one_id] >>
  rw[idL,idR]) >>
 fs[])
(form_goal 
“!n:1->N. sub o pa(Nn,nN,n,ZERO) = n”)

val le_z = proved_th $
e0
(rpt strip_tac >> assume_tac sub_z_iff_le >>
 first_x_assum (qspecl_then ["n0","ZERO"] assume_tac) >>
 by_tac “?(le0 : 1 -> LE). pa(Nn, nN, n0, ZERO) = le o le0”
 >-- (qexists_tac "a" >> arw[]) >>
 fs[] >> 
 assume_tac sub_zero_id >> fs[]
 )
(form_goal
“!n0:1->N a:1->LE. pa(Nn,nN,n0,ZERO) = le o a ==>
 n0 = ZERO”)


val lt_le = proved_th $
e0
(rpt strip_tac >> assume_tac lt_def >>
 assume_tac ltne_def >> drule $ iffLR ispb_def >>
 pop_assum strip_assume_tac >> fs[] >>
 pick_x_assum “le o ltle = ne o ltne” (assume_tac o GSYM) >>
 fs[] >> 
 qexists_tac "ltle o lt0" >> rw[o_assoc])
(form_goal 
“
 !n1:1->N n2:1->N. 
 (?lt0: 1->LT. pa(Nn,nN,n1,n2) = lt o lt0) ==>
 (?le0: 1->LE. pa(Nn,nN,n1,n2) = le o le0) ”)

val lt_ne0 = proved_th $
e0
(rpt strip_tac >> assume_tac lt_def >>
 assume_tac ltne_def >> drule $ iffLR ispb_def >>
 pop_assum strip_assume_tac >> fs[] >>
 qexists_tac "ltne o lt0" >> rw[o_assoc])
(form_goal 
“
 !n1:1->N n2:1->N. 
 (?lt0: 1->LT. pa(Nn,nN,n1,n2) = lt o lt0) ==>
 (?ne0: 1->NE. pa(Nn,nN,n1,n2) = ne o ne0)”)


val lt_ne = proved_th $
e0
(strip_tac >> strip_tac >> disch_tac >>
 assume_tac lt_ne0 >> first_x_assum drule >>
 assume_tac ne_property >> pop_assum mp_tac >>
 pop_assum (assume_tac o GSYM) >> strip_tac >> 
 pop_assum (assume_tac o iffLR) >> first_x_assum drule >>
 pop_assum mp_tac >> assume_tac nN_def >> drule p12_of_pa >>
 arw[])
(form_goal 
“
 !n1:1->N n2:1->N. 
 (?lt0: 1->LT. pa(Nn,nN,n1,n2) = lt o lt0) ==>
 ~(n1 = n2)”)


(*TODO: ispb version of pb_fac_exists*)

val le_ne_lt = proved_th $ 
e0
(
 rpt strip_tac >>
 assume_tac lt_def >> assume_tac ltne_def >>
 drule $ iffLR ispb_def >> pop_assum strip_assume_tac >>
 assume_tac ne_property >>
 first_x_assum (qspecl_then ["pa(Nn,nN,n1,n2)"] assume_tac)>>
 assume_tac nN_def >> drule p12_of_pa >> fs[] >>
 pop_assum (K all_tac) >>
 pick_x_assum 
“(?nnb : 1 -> NE. ne o nnb = pa(Nn, nN, n1:1->N, n2)) <=> ~(n1 = n2)” (assume_tac o GSYM) >> fs[] >>
 first_x_assum (qspecl_then ["1","le0","nnb"] assume_tac) >>
 rfs[] >> qexists_tac "a" >> 
 first_x_assum (qspecl_then ["a"] assume_tac) >> fs[] >>
 arw[o_assoc])
(form_goal 
“
 !n1:1->N n2:1->N.
 ((?le0: 1->LE. pa(Nn,nN,n1,n2) = le o le0) & ~(n1 = n2))
 ==> (?lt0: 1->LT. pa(Nn,nN,n1,n2) = lt o lt0)”)

val lt_iff_le_ne = proved_th $
e0
(rpt strip_tac >> dimp_tac >> disch_tac (* 2 *)
 >-- (assume_tac lt_ne >> first_x_assum drule >>
      assume_tac lt_le >> first_x_assum drule >> arw[]) >>
 assume_tac le_ne_lt >> first_x_assum drule >> arw[])
(form_goal 
“
 !n1:1->N n2:1->N.
 (?lt0: 1->LT. pa(Nn,nN,n1,n2) = lt o lt0) <=> 
 ((?le0: 1->LE. pa(Nn,nN,n1,n2) = le o le0) & ~(n1 = n2))”)

val clt_iff_le_ne = proved_th $
e0
(rpt strip_tac >>
 assume_tac lt_iff_le_ne >> pop_assum (assume_tac o GSYM) >>
 arw[] >> 
 assume_tac lt_mono >>
 assume_tac $ GSYM lt_def >> fs[] >>
 drule char_def >> first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[]) >>
 qexists_tac "lt0" >> arw[])
(form_goal 
“!two i1:1->two i2:1->two.iscopr(i1,i2) ==> 
 !n1:1->N n2:1->N.
 (char(i1:1->two, i2:1->two, lt) o pa(Nn, nN, n1, n2) = i2) <=> 
 ((?le0: 1->LE. pa(Nn,nN,n1,n2) = le o le0) & ~(n1 = n2))”)


val not_lt_z = proved_th $
e0
(rpt strip_tac >>
 ccontra_tac >>
 by_tac “char(i1:1->two, i2:1->two, lt) o pa(Nn, nN, n0, ZERO) = i2 <=> (?a:1->LE.pa(Nn,nN,n0,ZERO) = le o a) & 
 ~(n0:1->N = ZERO)” 
 >-- (drule clt_iff_le_ne >> arw[]) >> fs[] >>
 drule le_z >> fs[]
 )
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
      !n0:1->N. ~(char(i1,i2:1->two,lt) o 
      pa(Nn,nN,n0,ZERO) = i2)”)


(*TODO: why slow?

if instead of the first_x_assum irule, use  (*qsuff_tac ‘!n0:1->N. ~char(i1, i2, lt) o pa(Nn, nN, n0, z) = i2’ *) then no output and stuck there.

in  suffices_tac “isiso(q:Q->N)”, can use irule o_epi_imp_epi, but give the wrong thing.
*)


(*TODO: a version of thm that check equal of maps to products without the projections.*)

(*
need
p o sub o pa(Nn,nN,s o n0, n0) = z
hence need

sub o pa(Nn,nN,s o n0, n0) = s o z
*)

val sub_def' = proved_th $
e0
(assume_tac sub_def >> assume_tac nnN_def >>
 drule p12_of_pa >> fs[])
(form_goal 
“sub o pa(Nn, nN, id(N), ZERO o to1(N, 1)) = id(N) &
 PRE o sub = sub o pa(Nn, nN, Nn, SUC o nN)”)


val SoE_lemma_2_5_5 = proved_th $
e0
(rw[iscopr_def] >> rpt strip_tac >>
 qspecl_then ["N","X"] (x_choosel_then ["NX","Nx","nX"] assume_tac) pr_ex >> 
 qspecl_then ["NX","pa(Nx,nX,ZERO,f)","pa(Nx,nX,SUC,g) o Nx"] assume_tac constN_def >>
 qexists_tac "nX o Nind(pa(Nx, nX, ZERO, f), pa(Nx, nX, SUC, g) o Nx)" >>
 first_assum (qspecl_then ["Nind(pa(Nx, nX, ZERO, f), pa(Nx, nX, SUC, g) o Nx)"] assume_tac) >>
 fs[] >>
 by_tac 
 “Nx o Nind(pa(Nx:NX->N, nX:NX->X, ZERO, f), pa(Nx, nX, SUC, g) o Nx) = id(N)”
 >-- (sym_tac >> irule comm_with_s_id >>
      qby_tac 
      ‘Nx o Nind(pa(Nx, nX, ZERO, f), (pa(Nx, nX, SUC, g) o Nx)) o SUC
       = Nx o (pa(Nx, nX, SUC, g) o Nx) o
       Nind(pa(Nx, nX, ZERO, f), pa(Nx, nX, SUC, g) o Nx)’ >-- arw[] >>
      arw[o_assoc] >> drule p12_of_pa >>
      arw[GSYM o_assoc]) >> 
 fs[o_assoc,idR] >> 
 by_tac 
 “nX o Nind(pa(Nx:NX->N, nX:NX->X, ZERO, f), (pa(Nx, nX, SUC, g:N->X) o Nx)) o ZERO = nX o pa(Nx, nX, ZERO, f)”
 >-- arw[] >> 
 drule p2_of_pa >> arw[] >> 
 suffices_tac 
“!fg:N->X. fg o ZERO = f:1->X & fg o SUC = g:N->X ==>
 pa(Nx:NX->N,nX:NX->X,id(N),fg) = Nind(pa(Nx, nX, ZERO, f), pa(Nx, nX, SUC, g) o Nx)” >-- 
 (strip_tac >> gen_tac >> disch_tac >>
 first_assum drule >>
 by_tac 
 “nX o pa(Nx:NX->N, nX:NX->X, id(N), fg':N->X) = nX o Nind(pa(Nx, nX, ZERO, f:1->X), pa(Nx, nX, SUC, g:N->X) o Nx)”
 >-- (pop_assum mp_tac >> pop_assum_list (map_every (K all_tac)) >> strip_tac >> arw[]) >>
 pop_assum mp_tac >> drule p2_of_pa >> arw[]) >>
 rpt strip_tac >> 
 last_x_assum mp_tac >> last_x_assum (assume_tac o GSYM)>>
 strip_tac >> arw[] >> strip_tac (* 2 *)
 >-- (drule to_p_eq >> first_assum irule >>
      drule p12_of_pa >> arw[GSYM o_assoc,idL]) >>
 drule to_p_eq >> first_assum irule >>
 drule p12_of_pa >> arw[GSYM o_assoc] >>
 arw[o_assoc,idL,idR])
(form_goal “iscopr(ZERO,SUC)”)

val z_xor_s = proved_th $
e0
(assume_tac SoE_lemma_2_5_5 >>
 drule copr_disjoint >>
 strip_tac >> 
 first_x_assum (qspecl_then ["n"] assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 cases_on “n = ZERO” >> arw[] >>
 ccontra_tac >> fs[] >> pop_assum mp_tac >>
 rw[] >> once_rw[one_to_one_id] >>
 arw[idR] >> qexists_tac "id(1)" >> rw[]
 )
(form_goal
“!n:1->N. ~(n = ZERO) <=> ?n0:1->N. n = SUC o n0”)
 


val char_diag = proved_th $
e0
(rpt strip_tac >> drule fac_diag_eq_iff >>
 first_x_assum (qspecl_then ["pa(Aa,aA,a1,a2)"] assume_tac) >>
 drule p12_of_pa >> fs[] >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 drule diag_is_mono >> drule char_def >> first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >> arw[] >> dimp_tac >> rpt strip_tac 
 >-- (qexists_tac "x0" >> arw[]) >>
 qexists_tac "a0" >> arw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !A AA Aa:AA->A aA:AA ->A. ispr(Aa,aA) ==>
 !a1:1->A a2:1->A. char(i1,i2,pa(Aa,aA,id(A),id(A))) o pa(Aa,aA,a1,a2) = i2 <=> a1 = a2”)

val distr_to_pa =proved_th $
e0
(rpt strip_tac >> drule p12_of_pa >> drule to_p_eq >> first_x_assum irule >>
 arw[GSYM o_assoc]  )
(form_goal
“!A AA Aa:AA->A aA:AA->A. ispr(Aa,aA) ==>
 !X0 X x:X0->X a1:X->A a2:X->A. pa(Aa,aA,a1,a2) o x = 
 pa(Aa,aA,a1 o x,a2 o x)”)



val distr_to_pa' =proved_th $
e0
(rpt strip_tac >> drule p12_of_pa >> drule to_p_eq >> first_x_assum irule >>
 arw[GSYM o_assoc]  )
(form_goal
“!A B AB Ab:AB->A aB:AB->B. ispr(Ab,aB) ==>
 !X0 X x:X0->X a1:X->A a2:X->B. pa(Ab,aB,a1,a2) o x = 
 pa(Ab,aB,a1 o x,a2 o x)”)


val pb_fac_iff = proved_th $
e0
(rpt strip_tac >> drule $ iffLR ispb_def >>
 pop_assum strip_assume_tac >>
 dimp_tac >> strip_tac >--
 (pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
 strip_tac >> pop_assum (assume_tac o GSYM) >>
 arw[GSYM o_assoc]) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["a"] assume_tac) >> fs[] >>
 qexists_tac "a" >> arw[])
(form_goal 
“!X Z f:X->Z Y g:Y->Z P p:P->X q.
 ispb(f,g,p,q) ==>
 !A u:A->X v:A->Y. 
 (?a:A->P. p o a = u & q o a = v) <=> f o u = g o v”)

val pb_fac_iff_1 = proved_th $
e0
(rpt strip_tac >> drule pb_fac_iff >>
 first_x_assum 
 (qspecl_then ["1","u","id(1)"] assume_tac) >>
 fs[idR] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac "a" >> arw[] >> once_rw[one_to_one_id]) >>
 qexists_tac "a" >> arw[])
(form_goal 
“!X Z f:X->Z g:1->Z P p0:P->X q.
 ispb(f,g,p0,q) ==>
 !u:1->X. 
 (?a:1->P. p0 o a = u) <=> f o u = g”)

val ind_principle = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["N","two","pred","1","i2"] (x_choosel_then ["A","a","At1"] assume_tac) pb_ex >>
 drule pb_fac_iff_1 >> 
 by_tac “ismono(a:A->N)”
 >-- (drule pb_mono_mono >> first_x_assum irule >>
      once_rw[dom_1_mono]) >>
 by_tac “pred = i2:1->two o to1(N,1) <=> isiso(a:A->N)” >-- (
 dimp_tac >> strip_tac (* 2 *) >--
 (irule Thm2_3' >> arw[] >> drule $ iffLR ispb_def >>
  pop_assum strip_assume_tac >> arw[ismem_def,o_assoc] >>
  once_rw[one_to_one_id] >> rw[idR]) >>
 fs[isiso_def] >> irule fun_ext >> strip_tac >>
 rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR] >>
 drule $ iffLR ispb_def >> pop_assum strip_assume_tac >>
 by_tac 
 “pred o (a:A->N o f':N->A) o a' = i2:1->two o At1:A->1 o f':N->A o a':1->N”
 >-- (rw[GSYM o_assoc] >> arw[]) >>
 rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
 arw[] >> pop_assum (K all_tac) >> dimp_tac >> strip_tac (* 2 *) >--
 (fs[isiso_def] >> drule $ iffLR ispb_def >> 
 pop_assum strip_assume_tac >> 
 by_tac 
  “!n0:1->N. pred o (a:A->N o f') o n0 = i2:1->two o At1:A->1 o f':N->A o n0” 
 >-- (strip_tac >> arw[GSYM o_assoc]) >>
 rpt strip_tac (* 2 *)
 >-- (first_x_assum (qspecl_then ["ZERO"] assume_tac) >> 
      rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
 first_x_assum (qspecl_then ["SUC o n"] assume_tac) >> 
 rfs[idL] >> once_rw[one_to_one_id] >> rw[idR]) >>
 irule Thm2_3' >> arw[ismem_def])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !pred:N->two. pred = i2 o to1(N,1) <=>
 (pred o ZERO = i2 & (!n:1->N. pred o n = i2 ==> pred o SUC o n = i2))”)


val ind_principle_elements = proved_th $
e0
(rpt strip_tac >> drule ind_principle >> pop_assum (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule fun_ext >> rpt strip_tac >> rw[o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR] >> arw[]) >>
 arw[] >> rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]
 )
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !pred:N->two. (!n.pred o n = i2) <=>
 (pred o ZERO = i2 & (!n:1->N. pred o n = i2 ==> pred o SUC o n = i2))”)


val equality_ind = proved_th $ 
e0
(rpt strip_tac >> 
 qspecl_then ["1","1"] (x_choosel_then ["two","i1","i2"] assume_tac) copr_ex >>
 qspecl_then ["A","A"] (x_choosel_then ["AA","Aa","aA"] assume_tac) pr_ex >> 
 drule char_diag >> first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >> 
 by_tac “(!n:1->N.f o pa(Xn:XN->X,xN:XN->N,x,n) = g o pa(Yn:YN->Y,yN:YN->N,y,n)) <=>
          !n. char(i1,i2,pa(Aa,aA,id(A),id(A))) o 
              pa(Aa:AA->A,aA:AA->A,f:XN->A o pa(Xn:XN->X,xN:XN->N,x,n), g:YN->A o pa(Yn:YN->Y,yN:YN->N,y:1->Y,n)) = i2:1->two”
 >-- (dimp_tac >> rpt strip_tac >-- 
      (pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
       strip_tac >> arw[]) >>
      arw[]) >>
 arw[] >> 
 by_tac 
“(!n. char(i1,i2,pa(Aa,aA,id(A),id(A))) o 
      pa(Aa:AA->A,aA:AA->A,f:XN->A o pa(Xn:XN->X,xN:XN->N,x,n), g:YN->A o pa(Yn:YN->Y,yN:YN->N,y:1->Y,n)) = i2:1->two) <=>
  !n. char(i1,i2,pa(Aa,aA,id(A),id(A))) o 
      pa(Aa:AA->A,aA:AA->A,f:XN->A o pa(Xn:XN->X,xN:XN->N,x o to1(N,1),id(N)), g:YN->A o pa(Yn:YN->Y,yN:YN->N,y:1->Y o to1(N,1),id(N))) o n = i2:1->two” >-- 
 (dimp_tac >> rpt strip_tac (* 2 *)
  >-- (drule distr_to_pa >> rev_drule distr_to_pa' >>
       pick_x_assum “ispr(Yn:YN->Y,yN:YN->N)” assume_tac >>
       drule distr_to_pa' >>  arw[o_assoc] >> once_rw[one_to_one_id] >> 
       rw[idL,idR] >> arw[]) >>
  drule distr_to_pa >> rev_drule distr_to_pa' >>
  pick_x_assum “ispr(Yn:YN->Y,yN:YN->N)” assume_tac >>
  drule distr_to_pa' >> fs[o_assoc] >>
  pick_xnth_assum 6 mp_tac(*to be edited*) >> 
  once_arw[one_to_one_id] >> rw[idL,idR] >>
  strip_tac >> arw[]) >>
once_arw[] >> pop_assum (K all_tac) >>
drule ind_principle_elements >> rw[GSYM o_assoc] >>
first_x_assum (qspecl_then [" (char(i1, i2, pa(Aa, aA, id(A), id(A))) o pa(Aa, aA, f o pa(Xn, xN, x o to1(N, 1), id(N)), g o  pa(Yn, yN, y o to1(N, 1), id(N))))"] assume_tac) >> once_arw[] >>
 pop_assum (K all_tac) >> 
 drule distr_to_pa' >> rev_drule distr_to_pa' >>
 pick_x_assum “ispr(Yn:YN->Y,yN:YN->N)” assume_tac >>
 drule distr_to_pa' >> fs[o_assoc] >>
 once_rw[one_to_one_id] >> rw[idL,idR])
(form_goal 
“!X XN Xn:XN->X xN:XN->N. ispr(Xn,xN) ==>
 !Y YN Yn:YN->Y yN:YN->N. ispr(Yn,yN) ==>
 !A f:XN->A g:YN->A.
 !x:1->X y:1->Y.(!n.f o pa(Xn,xN,x,n) = g o pa(Yn,yN,y,n)) <=>
 f o pa(Xn,xN,x,ZERO) = g o pa(Yn,yN,y,ZERO) & 
 !n0:1->N. f o pa(Xn,xN,x,n0) = g o pa(Yn,yN,y,n0) ==> 
 f o pa(Xn,xN,x,SUC o n0) = g o pa(Yn,yN,y,SUC o n0)”)


val ind_one_component = proved_th $
e0
(rpt strip_tac >> assume_tac nN_def >> drule equality_ind >>
 first_x_assum drule >> 
 arw[])
(form_goal
“!f:NN->N g:NN->N.
 !n0.(!n.f o pa(Nn,nN,n0,n) = g o pa(Nn,nN,n0,n)) <=>
 f o pa(Nn,nN,n0,ZERO) = g o pa(Nn,nN,n0,ZERO) & 
 !n:1->N. f o pa(Nn,nN,n0,n) = g o pa(Nn,nN,n0,n) ==> 
 f o pa(Nn,nN,n0,SUC o n) = g o pa(Nn,nN,n0,SUC o n)”)


val add_ex = proved_th $
e0
(assume_tac nN_def >> assume_tac nnN_def >> assume_tac pr_with_one >>
 first_x_assum (qspecl_then ["N"] assume_tac) >>
 rev_drule Thm1 >> first_x_assum drule >> first_x_assum drule >>
 first_x_assum (qspecl_then ["id(N)","SUC o nnN"] assume_tac) >>
 pop_assum strip_assume_tac  >>
 first_x_assum (qspecl_then ["f"] assume_tac) >> fs[] >>
 qexists_tac "f" >> fs[o_assoc,idL])
(form_goal 
“?add:NN->N.add o pa(Nn,nN,id(N),ZERO o to1(N,1)) = id(N) & 
 add o pa(Nn,nN,Nn,SUC o nN) = SUC o nnN o pa(NNn,nnN,id(NN),add)”)


val add_def0 = add_ex |> eqT_intro |> iffRL |> ex2fsym "add" []
                      |> C mp (trueI [])

val add = mk_fun "add" [] 

val add_def = proved_th $
e0
(assume_tac add_def0 >> assume_tac nnN_def >> drule p2_of_pa >>
 fs[])
(form_goal
“add o pa(Nn,nN,id(N),ZERO o to1(N,1)) = id(N) & 
 add o pa(Nn,nN,Nn,SUC o nN) = SUC o add”)


val add_elements = proved_th $
e0
(rpt strip_tac >> assume_tac add_def (* 2 *)
 >-- (by_tac “add o pa(Nn, nN, id(N), ZERO o to1(N, 1)) o n:1->N = id(N) o n”
      >-- arw[GSYM o_assoc] >>
      assume_tac nN_def >> drule distr_to_pa' >>
      fs[] >>
      pick_x_assum “add o pa(Nn, nN, id(N) o n:1->N, (ZERO o to1(N, 1)) o n) = 
      id(N) o n” mp_tac >>
      rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idL,idR]) >>
 by_tac “add o pa(Nn, nN, Nn, SUC o nN) o pa(Nn, nN, n, n0:1->N) = SUC o add o pa(Nn, nN, n, n0)” >-- arw[GSYM o_assoc] >>
 assume_tac nN_def >> drule distr_to_pa' >> fs[o_assoc] >>
 drule p12_of_pa >> fs[])
(form_goal 
“!n:1->N. add o pa(Nn,nN,n,ZERO) = n &
 !n0:1->N. add o pa(Nn,nN,n, SUC o n0) = SUC o add o pa(Nn,nN,n,n0)”)


val sub_elements = proved_th $
e0
(strip_assume_tac sub_def' >> rpt strip_tac >--
 (by_tac 
 “sub o pa(Nn, nN, id(N), ZERO o to1(N, 1)) o n:1->N = id(N) o n”
 >-- arw[GSYM o_assoc] >>
 assume_tac nN_def >> drule distr_to_pa >> fs[idL] >> 
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 pop_assum mp_tac >> rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
 by_tac 
 “PRE o sub o pa(Nn, nN, n:1->N, n0) = 
  sub o pa(Nn, nN, Nn, SUC o nN) o pa(Nn, nN, n, n0)”
 >-- arw[GSYM o_assoc] >>
 arw[] >> assume_tac nN_def >> drule distr_to_pa >> arw[] >>
 drule p12_of_pa >> arw[o_assoc])
(form_goal
“!n:1->N. sub o pa(Nn,nN,n,ZERO) = n & 
 !n0.sub o pa(Nn,nN,n,SUC o n0) = PRE o sub o pa(Nn,nN,n,n0)”)


val pxy_true = proved_th $
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (arw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) >>
 irule fun_ext >> rpt strip_tac >> rw[o_assoc] >> once_rw[one_to_one_id] >>
 rw[idR] >> drule to_p_components >>
 first_x_assum (qspecl_then ["1","a"] assume_tac) >>
 once_arw[] >> pop_assum (K all_tac) >> arw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !XY X Y Xy:XY->X xY:XY->Y.ispr(Xy,xY) ==>
 !X2t efs p1:efs->X p2:efs->X2t ev:efs ->two. isexp(p1,p2,ev) ==>
 !pred.pred = i2 o to1(XY,1) <=> !x:1->X y:1->Y. pred o pa(Xy,xY,x,y) = i2”)



val Uq_ex = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["X","1"] 
 (x_choosel_then ["X1","pX","pone"] assume_tac) pr_ex >>
 abbrev_tac “tp(p1:eps->X,p2:eps->ps,ev:eps->two,pX:X1->X,pone:X1->1,i2 o to1(X1,1)) = tXb” >>
 qexists_tac "char(i1,i2,tXb)" >>
 by_tac “ismono(tXb:1->ps)”
 >-- (qspecl_then ["ps","tXb"] accept_tac) dom_1_mono >>
 rpt strip_tac >>
 drule char_def >> first_x_assum drule >> 
 pop_assum (assume_tac o GSYM) >> arw[] >> 
 qby_tac ‘(?(x0 : 1 -> 1). tXb:1->ps o x0 = tp(p1:eps->X, p2:eps->ps, ev:eps->two, Xy:XY->X, xY:XY->Y, pxy:XY->two) o y) <=> tXb = tp(p1, p2, ev, Xy, xY, pxy) o y’
 >-- (dimp_tac >> rpt strip_tac (* 2 *)
     >-- (pop_assum mp_tac >> once_rw[one_to_one_id] >>
          rw[idR]) >>
     qexists_tac "id(1)" >> arw[idR]) >>
 once_arw[] >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (drule ev_of_tp >> first_x_assum drule >>
  first_x_assum (qspecl_then ["pxy"] (assume_tac o GSYM)) >>
  once_arw[] >> pop_assum (K all_tac) >>
  rw[o_assoc] >>
  by_tac 
  “ev:eps->two o 
   pa(p1:eps->X,p2:eps->ps,x,tXb:1->ps) = i2”
  >-- (pop_assum (K all_tac) >>
       by_tac “pa(p1:eps->X,p2:eps->ps,x,tXb:1->ps) = pa(p1,p2,pX:X1->X,tXb o pone:X1->1) o pa(pX,pone,x,id(1))”
       >-- (drule exp_ispr >> 
            drule to_p_eq >> first_x_assum irule >>
            drule p12_of_pa >> arw[GSYM o_assoc] >>
            rev_drule p12_of_pa >> arw[o_assoc,idR]) >>
       arw[] >> 
       pick_x_assum 
       “tp(p1:eps->X, p2:eps->ps, ev:eps->two, pX:X1->X, pone:X1->1, i2:1->two o to1(X1, 1)) = tXb” (assume_tac o GSYM) >> 
       once_arw[] >> drule ev_of_tp >> first_x_assum rev_drule >>
       rw[GSYM o_assoc] >> arw[] >> rw[o_assoc] >> 
       once_rw[one_to_one_id] >> rw[idR]) >>
  suffices_tac 
  “pa(p1, p2, Xy:XY->X, (tp(p1, p2, ev, Xy, xY:XY->Y, pxy:XY->two) o xY)) o pa(Xy, xY, x, y) = pa(p1:eps->X, p2:eps->ps, x:1->X, tXb:1->ps)”
  >-- (strip_tac >> once_arw[] >> first_x_assum accept_tac)>>
  drule exp_ispr >> drule to_p_eq >>
  first_x_assum irule >> 
  drule p12_of_pa >> rw[GSYM o_assoc] >> arw[] >>
  pick_x_assum “ispr(Xy:XY->X,xY:XY->Y)” assume_tac >>
  drule p12_of_pa >> rw[o_assoc] >> arw[]) >>
  drule ev_eq_eq >> 
  pick_x_assum “ispr(pX:X1->X,pone:X1->1)” assume_tac >>
  first_x_assum drule >> 
  first_x_assum irule >> 
  pick_x_assum 
  “tp(p1:eps->X, p2:eps->ps, ev:eps->two, pX:X1->X, pone:X1->1, i2:1->two o to1(X1, 1)) = tXb” (assume_tac o GSYM) >>
  once_arw[] >>
  drule ev_of_tp >> first_x_assum drule >> once_arw[] >>
  drule ev_of_tp >> first_x_assum rev_drule >>
  (*split  pa(p1, p2, pX, (tp(p1, p2, ev, Xy, xY, pxy) o y)*)  drule exp_ispr >> 
  by_tac “ispr(pX:X1->X,pone:X1->1) & ispr(Xy:XY->X,xY:XY->Y) & ispr(p1:eps->X,p2:eps->ps)”
  >-- arw[] >> drule parallel_p_one_side >>
  rw[o_assoc] >> once_arw[] >> rw[GSYM o_assoc] >>
  drule ev_of_tp >> first_x_assum rev_drule >> once_arw[] >>
  irule fun_ext >> strip_tac >> 
  pick_x_assum “ispr(pX:X1->X,pone:X1->1)” assume_tac >>
  drule to_p_component >>
  first_x_assum (qspecl_then ["1","a"] assume_tac) >>
  once_arw[] >> pop_assum (assume_tac o GSYM) >>
  rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR] >>
  first_x_assum (qspecl_then ["pX o a"] assume_tac) >>
  pop_assum (assume_tac o GSYM) >> once_arw[] >>
  suffices_tac
  “pa(Xy:XY->X, xY:XY->Y, pX:X1->X o a:1->X1, y) = 
   pa(Xy, xY, pX, (y o pone:X1->1)) o pa(pX, pone, pX o a, id(1))” >-- (strip_tac >> arw[]) >>
  rev_drule to_p_eq >> first_x_assum irule >>
  rev_drule p12_of_pa >> rw[GSYM o_assoc] >> arw[] >>
  drule p12_of_pa >> rw[o_assoc] >> arw[idR])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !X eps ps p1:eps->X p2:eps ->ps ev:eps->two.isexp(p1,p2,ev) ==>
 ?Uq:ps -> two. 
 !Y XY Xy:XY->X xY:XY->Y. ispr(Xy,xY) ==>
 !pxy:XY->two y:1->Y. 
 (Uq o tp(p1,p2,ev,Xy,xY,pxy) o y = i2  <=> 
  !x:1->X. pxy o pa(Xy,xY,x,y) = i2)”)

val ind_gen_principle = proved_th $
e0
(rpt strip_tac >> drule Uq_ex >>
 qspecl_then ["X","two"] (x_choosel_then ["Xt2","efs","p1","p2","ev"] assume_tac) exp_ex >> 
 first_x_assum drule >> pop_assum strip_assume_tac >> 
 first_x_assum drule >> 
 drule pxy_true >> first_x_assum drule >>
 first_x_assum drule >> once_arw[] >>
 pop_assum (K all_tac) >>
 first_x_assum (qspecl_then ["pred"] assume_tac) >>
 dimp_tac 
 >-- (rpt strip_tac >-- arw[] >-- arw[]) >>
 strip_tac >> 
 suffices_tac 
 “!y : 1 -> N  x : 1 -> X. pred:XN->two o pa(Xn:XN->X, xN:XN->N, x, y) = i2”
 >-- (strip_tac >> arw[]) >>
 strip_tac >> 
 first_assum (qspecl_then ["y"] (assume_tac o GSYM)) >>
 once_arw[] >>
 suffices_tac 
 “ Uq :Xt2->two o tp(p1:efs->X, p2:efs->Xt2, ev:efs->two, Xn:XN->X, xN, pred) = i2:1->two o to1(N,1)”
 >-- (strip_tac >>
      qpick_x_assum
‘!y : 1 -> N. Uq o tp(p1:efs->X, p2:efs->Xt2, ev, Xn:XN->X, xN:XN->N, pred:XN->two) o y = i2 <=>
       !x : 1 -> X. pred o pa(Xn, xN, x, y) = i2’
       (K all_tac) >>
      arw[GSYM o_assoc] >> rw[o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR]) >>
 drule ind_principle >> arw[] >>
 pop_assum mp_tac >> pop_assum (K all_tac) >> strip_tac >>
 strip_tac (* 2 *)
 >-- arw[o_assoc]  >> 
 rpt strip_tac >> fs[o_assoc] >> rfs[] >>
 strip_tac >> last_x_assum (qspecl_then ["x"] assume_tac) >>
 pop_assum strip_assume_tac >> first_assum irule >> arw[]
 )
(form_goal 
“!X XN Xn:XN->X xN:XN->N. ispr(Xn,xN) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !pred:XN->two. pred = i2 o to1(XN,1) <=>
 (!x:1->X. pred o pa(Xn,xN,x,ZERO) = i2 & 
  (!n:1->N. pred o pa(Xn,xN,x,n) = i2 ==> pred o pa(Xn,xN,x, SUC o n) = i2))”)



val ind_gen_principle' = proved_th $
e0
(rpt strip_tac >> drule ind_gen_principle >>
 first_x_assum drule >> once_arw[] >>
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- arw[] 
 >-- (first_x_assum (qspecl_then ["x"] assume_tac) >>
     fs[] >> first_x_assum rev_drule >> 
     first_x_assum accept_tac)
 >-- arw[] >>
 first_x_assum drule >> arw[])
(form_goal 
“!X XN Xn:XN->X xN:XN->N. ispr(Xn,xN) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !pred:XN->two. pred = i2 o to1(XN,1) <=>
 (!x:1->X. pred o pa(Xn,xN,x,ZERO) = i2) & 
 (!x n:1->N. pred o pa(Xn,xN,x,n) = i2 ==> pred o pa(Xn,xN,x, SUC o n) = i2)”)

val sub_mono_eq = proved_th $
e0
(assume_tac nN_def >>
 drule ind_gen_principle >>
 qspecl_then ["1","1"] (x_choosel_then ["two","i1","i2"] assume_tac) copr_ex >>
 first_assum drule >>
 drule char_diag >> first_assum drule >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 last_x_assum drule >>
 suffices_tac
 “char(i1,i2,pa(Nn, nN, id(N), id(N))) o 
  pa(Nn, nN, sub o pa(Nn, nN, SUC o Nn, SUC o nN), sub) = i2:1->two o to1(NN,1)” >-- (rpt strip_tac >> 
  by_tac 
  “char(i1, i2, pa(Nn, nN, id(N), id(N))) o
   pa(Nn, nN, sub o pa(Nn, nN, SUC o Nn, SUC o nN), sub) o 
   pa(Nn,nN,m:1->N,n) =
   i2:1->two o to1(NN, 1) o pa(Nn,nN,m,n)”
  >-- (rw[GSYM o_assoc] >> arw[]) >>
  pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR] >>
  by_tac 
  “pa(Nn, nN, (sub o pa(Nn, nN, SUC o Nn, SUC o nN)), sub) o pa(Nn, nN, m, n) =
   pa(Nn, nN, sub o pa(Nn, nN, SUC o m:1->N, SUC o n), sub o pa(Nn, nN, m, n))” >--
  (drule to_p_eq >> first_x_assum irule >> rw[GSYM o_assoc] >>
  drule p12_of_pa >> pop_assum mp_tac >>
  pop_assum_list (map_every (K all_tac)) >> strip_tac >> arw[] >>
  rw[o_assoc] >>
  suffices_tac “pa(Nn, nN, (SUC o Nn), (SUC o nN)) o pa(Nn, nN, m, n) =
  pa(Nn, nN, SUC o m, SUC o n:1->N)”
  >-- (strip_tac >> arw[]) >>
  assume_tac nN_def >> drule to_p_eq >> first_x_assum irule >>
  drule p12_of_pa >> arw[GSYM o_assoc] >> arw[o_assoc]) >>
  arw[]) >>
 arw[] >> drule distr_to_pa >> rw[o_assoc] >> once_arw[] >>
 pop_assum (K all_tac) >> pop_assum (K all_tac) >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 strip_tac >> pop_assum_list (map_every (K all_tac)) >> 
 assume_tac sub_elements >> rpt strip_tac (* 2 *) >-- (rw[o_assoc] >>
 assume_tac nN_def >> drule distr_to_pa >> once_arw[] >>
 rw[o_assoc] >> drule p12_of_pa >> arw[] >>
 rw[GSYM o_assoc,PRE_def,idL]) >>
 assume_tac nN_def >> drule distr_to_pa >> fs[o_assoc] >>
 drule p12_of_pa >> fs[]
 )
(form_goal 
“!m:1->N n:1->N. 
 sub o pa(Nn,nN,SUC o m, SUC o n) = sub o pa(Nn,nN,m,n)”) 

val add_sub0 = proved_th $
e0
(rw[ind_one_component] >>
 assume_tac nN_def >> drule distr_to_pa' >> fs[o_assoc] >>
 drule p12_of_pa >> fs[] >>
 assume_tac add_elements >> arw[] >> rpt strip_tac >--
 (assume_tac sub_elements >> fs[]) >>
 assume_tac sub_mono_eq >> fs[])
(form_goal 
“!a:1->N. (!c:1->N. (sub o pa(Nn,nN,add,nN)) o pa(Nn,nN,a,c) = Nn o pa(Nn,nN,a,c))”)

val add_sub = proved_th $
e0
(assume_tac add_sub0 >> assume_tac nN_def >> drule p12_of_pa >> fs[] >>
 drule distr_to_pa' >> fs[o_assoc])
(form_goal 
“!a:1->N c:1->N. sub o pa(Nn,nN,add o pa(Nn,nN,a,c),c) = a”)

(*
val plus_def = 

“plus(m,n) = add o pa(Nn,nN,m,n)”

TODO: turn the arrows about arith into function symbols.

*)


val ind_N_element = proved_th $
e0
(rpt strip_tac >> assume_tac ind_one_component >>
 first_x_assum (qspecl_then ["f o nN","g o nN","ZERO"] assume_tac) >>
 assume_tac nN_def >> drule p2_of_pa >>
 fs[o_assoc])
(form_goal
“!f:N->N g:N->N. (!n:1->N.f o n = g o n) <=>
  f o ZERO = g o ZERO & 
  !n:1->N. f o n = g o n ==> f o SUC o n = g o SUC o n”)


val add_z_n0 = proved_th $
e0
(once_rw[ind_N_element] >> rw[o_assoc] >> 
 assume_tac nN_def >> drule distr_to_pa' >> arw[o_assoc,idL] >>
 once_rw[one_to_one_id] >> rw[idR] >> assume_tac add_elements >> arw[] >>
 rpt strip_tac >> arw[])
(form_goal
“!n:1->N. (add o pa(Nn,nN,ZERO o to1(N,1),id(N))) o n = id(N) o n”)


val add_z_n = proved_th $
e0
(strip_tac >> assume_tac add_z_n0 >> fs[o_assoc] >> assume_tac nN_def >>
 drule distr_to_pa' >> fs[] >> last_x_assum mp_tac >> rw[o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR,idL] >> strip_tac >> arw[])
(form_goal
“!n:1->N. add o pa(Nn,nN,ZERO,n) = n”)

val add_clauses1 = add_z_n

val sub_equal_0 = proved_th $
e0
(strip_tac >> 
 assume_tac add_sub >>
 first_x_assum (qspecl_then ["ZERO","n"] assume_tac) >>
 assume_tac add_elements >> fs[] >>
 assume_tac add_z_n >> fs[])
(form_goal 
“!n. sub o pa(Nn,nN,n,n) = ZERO”)

val n_sub_n_z = sub_equal_0

val z_mono = proved_th $
e0
(assume_tac dom_1_mono >> once_arw[])
(form_goal “ismono(ZERO)”)

val le_mono = proved_th $
e0
(assume_tac le_def >> pop_assum strip_assume_tac >>
 drule pb_mono_mono >> first_x_assum irule >>
 accept_tac z_mono)
(form_goal “ismono(le)”)


val le_refl = proved_th $
e0
(rpt strip_tac >> assume_tac le_mono >>
 drule char_def >> 
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 arw[] >> strip_assume_tac le_def >> 
 drule pb_fac_iff_1 >>  arw[] >>
 assume_tac n_sub_n_z >>
 arw[]
 )
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !x:1->N. char(i1, i2, le) o pa(Nn, nN, x, x) = i2”)


val le_z_z = proved_th $
e0
(rpt strip_tac >> assume_tac le_mono >>
 drule char_def >> first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >>
 pick_x_assum “char(i1:1->two, i2, le) o pa(Nn, nN, n0:1->N, ZERO) = i2” mp_tac >> arw[] >> disch_tac >>
 strip_assume_tac le_def >> drule pb_fac_iff_1 >>
 fs[] >> assume_tac sub_zero_id >> fs[])
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !n0:1->N. char(i1, i2, le) o pa(Nn, nN, n0, ZERO) = i2 ==> n0 = ZERO”)


val le_cases = proved_th $
e0
(rpt strip_tac >> cases_on “n0 = n:1->N” (* 2 *)
 >-- arw[] >>
 assume_tac clt_iff_le_ne >> first_x_assum drule >>
 arw[] >> assume_tac le_mono >> drule char_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 fs[] >> qexists_tac "x0" >> arw[])
(form_goal “!two i1:1->two i2:1->two.iscopr(i1,i2) ==> 
 !n0:1->N n:1->N. char(i1, i2, le) o pa(Nn, nN, n0, n) = i2 ==> char(i1,i2,lt) o  pa(Nn, nN, n0, n) = i2 | n0 = n”)


val sub_s = proved_th $
e0
(rpt strip_tac >> assume_tac sub_def' >>
 by_tac
 “PRE o sub o pa(Nn, nN, a:1->N, b:1->N) = 
 sub o pa(Nn, nN, Nn, SUC o nN) o pa(Nn, nN, a, b)”
 >-- arw[GSYM o_assoc] >>
 assume_tac nN_def >> drule p12_of_pa >>
 arw[] >> 
 suffices_tac
 “pa(Nn, nN, a:1->N, SUC o b:1->N) = 
 pa(Nn, nN, Nn, (SUC o nN)) o pa(Nn, nN, a, b)”
 >-- (strip_tac >> arw[]) >>
 drule to_p_eq >> first_x_assum irule >>
 arw[GSYM o_assoc] >>
 arw[o_assoc])
(form_goal
“!a:1->N b:1->N.sub o pa(Nn,nN,a,SUC o b) = 
 PRE o sub o pa(Nn,nN,a,b)”)

(*TODO: prec parser bug! need () around <=> *)


val double_ind = proved_th $
e0
(rpt strip_tac >> drule ind_principle_elements >>
 drule Uq_ex >>
 qspecl_then ["N","two"] 
 (x_choosel_then ["Nt2","nps","p1","p2","ev"] assume_tac)
 exp_ex >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 assume_tac nN_def >> first_x_assum drule >>
 first_x_assum (qspecl_then ["pred"] (assume_tac o GSYM)) >>
 once_arw[] >>
 rw[GSYM o_assoc] >> once_arw[] >>
 suffices_tac
 “(!n:1->N. (Uq o tp(p1:nps->N, p2:nps-> Nt2, ev:nps->two, Nn, nN, pred)) o n = i2 ==> (Uq o tp(p1, p2, ev, Nn, nN, pred:NN->two)) o SUC o n = i2)
   <=>
  !n:1->N. (Uq o tp(p1, p2, ev, Nn, nN, pred)) o n = i2 ==>
   pred o pa(Nn, nN, ZERO, SUC o n) = i2 &
  !(m : 1 -> N). pred o pa(Nn, nN, m, SUC o n) = i2 ==>
    pred o pa(Nn, nN, SUC o m, SUC o n) = i2:1->two” >--
 (strip_tac >> dimp_tac (*2 *) >--
  (strip_tac >> arw[] >> fs[]) >> strip_tac >> arw[])
 (*TODO: why it is not automatic rw???*) >>
 suffices_tac
 “!n:1->N. (Uq o tp(p1:nps->N, p2:nps->Nt2, ev:nps->two, Nn, nN, pred)) o n = i2 ==>
  ((Uq o tp(p1, p2, ev, Nn, nN, pred)) o SUC o n = i2 <=>
   pred o pa(Nn, nN, ZERO, SUC o n) = i2 &
   !m:1->N. pred o pa(Nn, nN, m, SUC o n) = i2 ==>
   pred o pa(Nn, nN, SUC o m, SUC o n) = i2:1->two)” >--
 (strip_tac >> dimp_tac (* 2 *) >--
  (strip_tac >> strip_tac >> strip_tac >>
   last_x_assum drule >> pop_assum (assume_tac o GSYM) >>
   once_arw[] >> first_x_assum drule >>
   first_x_assum accept_tac) >> 
  rpt strip_tac >> last_x_assum drule >> once_arw[] >>
  first_x_assum drule >> first_x_assum accept_tac) >>
 rpt strip_tac >>
 pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
 strip_tac >> fs[GSYM o_assoc] >>
 first_x_assum (qspecl_then ["pred o pa(Nn,nN,id(N),SUC o n o to1(N,1))"] assume_tac) >>
 fs[o_assoc] >> drule distr_to_pa' >> fs[o_assoc] >>
 pop_assum (K all_tac) >> pop_assum mp_tac >>
 once_rw[one_to_one_id] >> rw[idR,idL])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
!pred:NN->two.(!n m:1->N. pred o pa(Nn,nN,m,n) = i2) <=>
 (!m.pred o pa(Nn,nN,m,ZERO) = i2) &
 (!n.(!m.pred o pa(Nn,nN,m,n) = i2) 
   ==>
   pred o pa(Nn,nN,ZERO,SUC o n) = i2 & 
   (!m.pred o pa(Nn,nN,m,SUC o n) = i2 ==> pred o pa(Nn,nN,SUC o m, SUC o n) = i2))”)

val triple_ind = proved_th $
e0
(rpt strip_tac >> 
 drule ind_principle_elements >> 
 drule Uq_ex >> 
 qspecl_then ["NN","two"] 
 (x_choosel_then ["NNt2","nnps","p1","p2","ev"] assume_tac)
 exp_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 assume_tac nnN_def >> first_x_assum drule >> 
 first_x_assum (qspecl_then ["pred"] assume_tac) >> 
 by_tac 
 “(!a:1->N m:1-> N n:1->N. pred:NNN->two o pa(NNn, nnN, pa(Nn, nN, n, m), a) = i2:1->two) <=> 
  (!a:1->N. Uq o tp(p1:nnps->NN, p2:nnps->NNt2, ev, NNn, nnN, pred) o a = i2)” >-- 
 (arw[] >> dimp_tac >> rpt strip_tac >--  
  (assume_tac nN_def >> drule to_p_components >> 
  first_x_assum (qspecl_then ["1","x"] assume_tac) >>
  once_arw[] >> pop_assum (K all_tac) >> 
  once_arw[]) >> arw[]) >>
 once_arw[] >> rw[GSYM o_assoc] >> 
 pick_xnth_assum 2 (pspecl_then ["(Uq:NNt2->two o tp(p1:nnps->NN, p2:nnps->NNt2, ev, NNn, nnN, pred:NNN->two))"] assume_tac) >> 
 once_arw[] >>
 by_tac 
 “!a:1->N.(Uq o tp(p1:nnps->NN, p2:nnps->NNt2, ev, NNn, nnN, pred:NNN->two)) o a = i2:1->two <=> 
  (!m:1->N n. pred o pa(NNn,nnN,pa(Nn,nN,n,m),a) = i2)” >--
 (strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
  rfs[o_assoc] >> arw[o_assoc] >>
  strip_tac >> assume_tac nN_def >> drule to_p_components >>
  first_x_assum (qspecl_then ["1","x"] assume_tac) >>
  once_arw[] >> pop_assum (K all_tac) >> once_arw[]) >>
 once_arw[] >> rw[] >> 
 suffices_tac 
 “(!a:1->N. (Uq:NNt2->two o tp(p1:nnps->NN, p2:nnps->NNt2, ev:nnps->two, NNn, nnN, pred:NNN->two)) o a = i2
   ==> (Uq o tp(p1, p2, ev, NNn, nnN, pred)) o SUC o a = i2)
  <=> 
  !a : 1 -> N. (!m n. pred o pa(NNn, nnN, pa(Nn, nN, n, m), a) =
                  i2) ==>
               (!n. pred o pa(NNn, nnN, pa(Nn, nN, n, ZERO), SUC o a)
                  = i2) &
               !m. (!n. pred o
                      pa(NNn, nnN, pa(Nn, nN, n, m), SUC o a) = i2) ==>
                 pred o pa(NNn, nnN, pa(Nn, nN, ZERO, SUC o m), SUC o a) = i2 &
                 !n. pred o
                     pa(NNn, nnN, pa(Nn, nN, n, SUC o m), SUC o a) = i2 ==>
                   pred o pa(NNn, nnN, pa(Nn, nN, SUC o n, SUC o m), SUC o a) =
                   i2” >--
 (strip_tac >> dimp_tac >> strip_tac >> arw[] >--
  (suffices_tac
  “(!(a : 1 -> N). (Uq o tp(p1:nnps->NN, p2:nnps->NNt2, ev, NNn, nnN, pred:NNN->two)) o a = i2:1->two ==> (Uq o tp(p1, p2, ev, NNn, nnN, pred)) o SUC o a = i2)”
  >-- (once_arw[] >> strip_tac) >>
  strip_tac >> once_arw[] >> strip_tac >> 
  first_x_assum drule >> first_x_assum accept_tac) >>
 pick_xnth_assum 7 (assume_tac o GSYM) >>
 once_arw[] >> pop_assum (K all_tac) >> once_arw[] >>
 first_x_assum accept_tac) 
 (*here does not use any technical lemma so it is problematic that it need hand*) >>
 once_arw[] >>
 suffices_tac
 “!a. (!m n. pred o pa(NNn, nnN, pa(Nn, nN, n, m), a) = i2)
  ==>
  ((Uq o tp(p1:nnps->NN, p2:nnps->NNt2, ev, NNn, nnN, pred)) o SUC o a = i2:1->two <=>
   (!n. pred o pa(NNn, nnN, pa(Nn, nN, n, ZERO), SUC o a)
                  = i2) &
               !m. (!n. pred o
                      pa(NNn, nnN, pa(Nn, nN, n, m), SUC o a) = i2) ==>
                 pred o pa(NNn, nnN, pa(Nn, nN, ZERO, SUC o m),SUC o a) = i2 &
                 !n. pred o
                     pa(NNn, nnN, pa(Nn, nN, n, SUC o m), SUC o a) = i2 ==>
                   pred o pa(NNn, nnN, pa(Nn, nN, SUC o n, SUC o m), SUC o a) =
                   i2) ” >-- 
 (strip_tac >> dimp_tac >> strip_tac (* 2 *)>--
  (strip_tac >> strip_tac >>
   pick_xnth_assum 8 drule >> rfs[] >>
   first_x_assum drule >> rfs[]) >> 
  rfs[] >> strip_tac >> strip_tac >>
  last_x_assum drule >> once_arw[] >> first_x_assum irule >>
  first_x_assum accept_tac) >>
 rpt strip_tac >> arw[o_assoc] >> 
 drule double_ind >>
 by_tac 
 “(!m:1->N n. pred o pa(NNn,nnN,pa(Nn,nN,n,m),SUC o a) = i2) <=>
  (!n m. pred o pa(NNn,nnN,id(NN), SUC o a o to1(NN,1)) o pa(Nn,nN,m,n) = i2:1->two)” >-- 
 (pop_assum_list (map_every (K all_tac)) >>
  assume_tac nnN_def >> drule distr_to_pa' >>
  arw[o_assoc] >> once_rw[one_to_one_id] >> rw[idL,idR]) >>
 arw[GSYM o_assoc] >> 
 first_x_assum 
 (qspecl_then ["pred o pa(NNn, nnN, id(NN), (SUC o a) o to1(NN, 1))"] assume_tac) >> once_arw[] >>
 rw[o_assoc] >>
 pop_assum_list (map_every (K all_tac)) >>
 assume_tac nnN_def >> drule distr_to_pa' >>
 arw[] >> rw[o_assoc] >> once_arw[one_to_one_id] >>
 rw[idL,idR])
(form_goal
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
  !pred:NNN->two. 
  (!a:1->N m n. pred o pa(NNn,nnN,pa(Nn,nN,n,m),a) = i2) <=>
   (!m:1->N n. pred o pa(NNn,nnN,pa(Nn,nN,n,m),ZERO) = i2) &
   (!a:1->N. 
     (!m:1->N n. pred o pa(NNn,nnN,pa(Nn,nN,n,m),a) = i2)==>
     (!n.pred o pa(NNn,nnN,pa(Nn,nN,n,ZERO),SUC o a) = i2) & 
     (!m.(!n.pred o pa(NNn,nnN,pa(Nn,nN,n,m),SUC o a) = i2) ==>
         pred o pa(NNn,nnN,pa(Nn,nN,ZERO,SUC o m),SUC o a) = i2 &
         (!n. pred o pa(NNn,nnN,pa(Nn,nN,n,SUC o m),SUC o a) = i2              ==> 
              pred o pa(NNn,nnN,pa(Nn,nN,SUC o n,SUC o m),SUC o a) = i2)))”)

val le_sub = proved_th $
e0
(rpt strip_tac >> assume_tac le_def >>
 pop_assum strip_assume_tac >> assume_tac le_mono >>
 drule char_def >> first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >> 
 drule pb_fac_iff_1 >> arw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 (!m:1->N n. char(i1,i2,le) o pa(Nn,nN,m,n) = i2 <=>
 sub o pa(Nn,nN,m,n) = ZERO)”)

val inv_suc_eq = proved_th $
e0
(assume_tac Thm2_2 >> drule ismono_property >>
 rpt strip_tac >> dimp_tac >> strip_tac >--
 (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal 
“!m n:1->N. SUC o m = SUC o n <=> m = n”)



val pa_eq = proved_th $
e0
(rpt strip_tac >> 
 dimp_tac >> strip_tac (* 2 *) >-- 
 (qby_tac
 ‘Ab o pa(Ab, aB, f1, g1) = Ab o pa(Ab, aB, f2, g2)’
 >-- arw[] >>
 qby_tac
 ‘aB o pa(Ab, aB, f1, g1) = aB o pa(Ab, aB, f2, g2)’
 >-- arw[] >>
 drule p12_of_pa >> fs[]) >>
 arw[])
(form_goal
“!A B AB Ab:AB->A aB:AB->B. ispr(Ab,aB) ==>
 !X f1:X->A g1 f2 g2. pa(Ab,aB,f1,g1) = pa(Ab,aB,f2,g2) <=>
 f1 = f2 & g1 = g2”)

val conj_ex = proved_th $
e0
(rpt strip_tac >> 
 qexists_tac "char(i1,i2,pa(Tt,tT,i2,i2))" >>
 assume_tac dom_1_mono >>
 first_x_assum 
  (qspecl_then ["TT","pa(Tt,tT,i2,i2)"] assume_tac) >>
 drule char_def >>
 first_x_assum drule >> 
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >>
 rpt strip_tac >> once_rw[one_to_one_id] (* 2 why rw[one_to_one_id] DOES the correct thing now? *) >>
 rw[idR] >> dimp_tac >> rpt strip_tac (* 3 *)
 >-- (drule pa_eq >> fs[] >>
     pick_x_assum “i2:1->two = p1” (assume_tac o GSYM) >>
     arw[]) 
 >-- (drule pa_eq >> fs[] >>
      pick_x_assum “i2:1->two = p1” (assume_tac o GSYM) >>
      arw[]) >>
 qexists_tac "id(1)" >> arw[])
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !TT Tt:TT->two tT:TT->two. ispr(Tt,tT) ==>
 ?conj:TT->two. 
 !p1:1->two p2:1->two. conj o pa(Tt,tT,p1,p2) = i2 <=>
 (p1 = i2 & p2 = i2)”)


val imp_ex = proved_th $
e0
(rpt strip_tac >> 
 by_tac “ismono(pa(Tt,tT:TT->two,i2:1->two,i1:1->two))”
 >-- (qspecl_then ["TT","pa(Tt, tT, i2, i1)"] accept_tac
      dom_1_mono) >>
 drule Thm5 >> 
 pop_assum (x_choosel_then ["M","imp0"] strip_assume_tac) >>
 drule char_def >> first_x_assum drule >>
 qexists_tac "char(i1,i2,imp0)" >> rpt strip_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 qspecl_then ["1","M"] (x_choosel_then ["W","ione","iM"] assume_tac) copr_ex >>
 first_x_assum drule >>
 fs[ismem_def] >> 
 drule inc_ismono >> fs[] >>
 drule iso_copr_copr >> first_x_assum drule >>
 drule copr_disjoint >> 
 first_x_assum 
 (qspecl_then ["pa(Tt, tT, p1, p2)"] (assume_tac o GSYM)) >>
 once_arw[] >>
 (*should not be done by hand*)
 by_tac
 “(?x0 : 1 -> M. imp0:M->TT o x0 = pa(Tt:TT->two, tT:TT->two, p1:1->two, p2:1->two)) <=> 
 (?x0 : 1 -> M. pa(Tt, tT, p1, p2) = imp0 o x0)”
 >-- ((*aqed, may need test new tool here*) dimp_tac >> strip_tac >>
      qexists_tac "x0" >> arw[]) >>
 arw[] >> once_rw[one_to_one_id] >> rw[idR] >>
 suffices_tac
 “~(pa(Tt, tT, p1, p2) = pa(Tt:TT->two, tT, i2, i1:1->two)) <=> 
  (p1 = i2 ==> p2:1->two = i2:1->two)”
 >-- (strip_tac >> dimp_tac>> strip_tac >--
      (by_tac “~(pa(Tt:TT->two, tT:TT->two, p1:1->two, p2) = pa(Tt, tT, i2:1->two, i1:1->two))” 
       >-- (ccontra_tac >>
           suffices_tac “?x0:1->1. pa(Tt:TT->two, tT:TT->two, p1:1->two, p2) = pa(Tt, tT, i2:1->two, i1:1->two)”
           >-- (disch_tac >> first_x_assum opposite_tac) >>
           qexists_tac "id(1)" >> first_x_assum accept_tac)>>
       fs[]
       ) >> 
       ccontra_tac >> pop_assum strip_assume_tac >>
       fs[]) >>
 suffices_tac
 “pa(Tt:TT->two, tT, p1, p2) = pa(Tt, tT, i2, i1) <=>
 p1 = i2:1->two & p2 = i1:1->two” >--
 (strip_tac >> once_arw[] >> drule i1_xor_i2 >> dimp_tac >>
  strip_tac (* 2 *)
  >-- (strip_tac >> ccontra_tac >>
      first_x_assum (qspecl_then ["p2"] assume_tac) >>
      fs[]) >>
  cases_on “p1 = i2:1->two” (* 2 *)
  >-- (first_x_assum drule >> ccontra_tac >>
       drule i1_ne_i2 >> fs[]) >>
  ccontra_tac >> fs[]) >>
 dimp_tac >> strip_tac (* 2 *) >-- 
(by_tac 
 “Tt o pa(Tt:TT->two, tT:TT->two, p1:1->two, p2:1->two) = Tt o pa(Tt, tT, i2, i1) & 
  tT o pa(Tt:TT->two, tT:TT->two, p1:1->two, p2:1->two) = tT o pa(Tt, tT, i2, i1)”
 >-- arw[] >>
 pop_assum mp_tac >> drule p12_of_pa >> arw[]) >>
 arw[]
 )
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !TT Tt:TT->two tT:TT->two. ispr(Tt,tT) ==>
 ?imp:TT->two. 
 !p1:1->two p2:1->two. imp o pa(Tt,tT,p1,p2) = i2 <=>
 (p1 = i2 ==> p2 = i2)”)



val iff_ex = proved_th $
e0
(rpt strip_tac >>
 drule imp_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 drule conj_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac "conj o pa(Tt,tT,imp,imp o pa(Tt,tT,tT,Tt))">>
 drule distr_to_pa' >> arw[o_assoc] >>
 drule p12_of_pa >> arw[] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac (* 2 *) >--
 (dimp_tac >> arw[]) >>
 fs[]
 )
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !TT Tt:TT->two tT:TT->two. ispr(Tt,tT) ==>
 ?iff:TT->two. 
 !p1:1->two p2:1->two. iff o pa(Tt,tT,p1,p2) = i2 <=>
 (p1 = i2 <=> p2 = i2)”)

(*i2
             =
             char(i1, i2, le) o pa(Nn, nN, a, n)
             &
             i2
             =
             char(i1, i2, le) o pa(Nn, nN, a, m)
             ==>
             (n
             =
             m
             <=>
             sub o pa(Nn, nN, n, a)
             =
             sub o pa(Nn, nN, m, a))

TODO: a version of GSYM top-down*)

val cancel_sub_pred = proved_th $
e0
(rpt strip_tac >> drule imp_ex >> drule iff_ex >>
 qspecl_then ["two","two"] assume_tac pr_ex >>
 pop_assum (x_choosel_then ["TT","Tt","tT"] assume_tac)
 (*if continuation then complain, todo*) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 drule conj_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >> 
 drule char_diag >> assume_tac nN_def >>
 first_x_assum drule >> 
 qexists_tac
 $ q2str
 ‘imp o 
  pa(Tt,tT,
     conj o 
       pa(Tt,tT,
          char(i1,i2,le) o 
          pa(Nn,nN,nnN,Nn o NNn),
          char(i1,i2,le) o
          pa(Nn,nN,nnN,nN o NNn)),
     iff o 
       pa(Tt,tT,
          char(i1,i2,pa(Nn,nN,id(N),id(N))) o 
          pa(Nn,nN,sub o pa(Nn,nN,Nn o NNn,nnN), 
                   sub o pa(Nn,nN,nN o NNn,nnN)),
          char(i1,i2,pa(Nn,nN,id(N),id(N))) o 
          pa(Nn,nN,Nn o NNn,nN o NNn)))’ >>
drule distr_to_pa' >> rev_drule distr_to_pa' >>
rw[o_assoc] >> once_arw[] >> 
drule p12_of_pa >> assume_tac nnN_def >>
drule p12_of_pa >> once_arw[] >> once_arw[] >> 
rw[o_assoc] >> once_arw[] >> once_arw[] >>
rw[o_assoc] >> once_arw[] >> once_arw[] >>
rw[o_assoc] >> once_arw[] >> rw[o_assoc] >> once_arw[] >>
once_arw[] >>
rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
(first_x_assum drule >> first_x_assum drule >>
 first_x_assum accept_tac) >>
fs[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
?pred:NNN->two. 
!a:1->N m n.(char(i1,i2,le) o pa(Nn,nN,a,n) = i2 ==>
char(i1,i2,le) o pa(Nn,nN,a,m) = i2 ==>
 (sub o pa(Nn,nN,n,a) = sub o pa(Nn,nN,m,a) <=> n = m)) <=>
 pred o pa(NNn,nnN,pa(Nn,nN,n,m),a) = i2:1->two”)

val cancel_sub00 = proved_th $
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >>
by_tac “?pred:NNN->two. 
!a:1->N m n.(char(i1,i2,le) o pa(Nn,nN,a,n) = i2 ==>
char(i1,i2,le) o pa(Nn,nN,a,m) = i2 ==>
 (sub o pa(Nn,nN,n,a) = sub o pa(Nn,nN,m,a) <=> n = m)) <=>
 pred o pa(NNn,nnN,pa(Nn,nN,n,m),a) = i2:1->two”
 >-- (drule cancel_sub_pred >> first_x_assum accept_tac) >>
 pop_assum strip_assume_tac >> once_arw[] >>
 drule triple_ind >> once_arw[] >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 strip_tac (* 2 *) >--
 (rpt strip_tac >> assume_tac sub_zero_id >> arw[]) >>
 strip_tac >> strip_tac >> strip_tac (* 2 *) >-- 
 (rpt strip_tac >> 
 drule le_sub >> fs[] >> 
 pop_assum mp_tac >> pop_assum mp_tac >>
 rw[sub_zero_id] (* 2 *) >> rpt strip_tac >>
 fs[Thm2_1]) >> 
 strip_tac >> strip_tac >> strip_tac (* 2 *) >--
 (rpt strip_tac >> drule le_sub >> fs[] >>
  fs[sub_zero_id]) >>
 rpt strip_tac >> rw[sub_mono_eq] >>
 rw[inv_suc_eq] >> first_x_assum irule >>
 drule le_sub >> fs[] >> fs[sub_mono_eq]
)
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !a m n. char(i1,i2,le) o pa(Nn,nN,a,n) = i2 ==>
 char(i1,i2,le) o pa(Nn,nN,a,m) = i2 ==>
 (sub o pa(Nn,nN,n,a) = sub o pa(Nn,nN,m,a)  <=> n = m)”)


val cancel_sub00' = proved_th $
e0
(rpt strip_tac >> drule cancel_sub00 >>
 first_x_assum rev_drule >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal 
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !a n. char(i1,i2,le) o pa(Nn,nN,a,n) = i2 ==>
 !m. char(i1,i2,le) o pa(Nn,nN,a,m) = i2 ==>
 (sub o pa(Nn,nN,n,a) = sub o pa(Nn,nN,m,a)  <=> n = m)”)


val sub_0 = proved_th $
e0
(suffices_tac
 “!n:1->N. (sub o pa(Nn,nN,ZERO o to1(N,1), id(N))) o n = ZERO o to1(N,1) o n” >--
 (rpt strip_tac >> assume_tac nN_def >> drule distr_to_pa' >>
 fs[o_assoc] >> last_x_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR,idL] >>
 strip_tac >> arw[]) >>
 rw[GSYM o_assoc] >> once_rw[ind_N_element] >>
 assume_tac sub_elements >> assume_tac nN_def >>
 drule distr_to_pa' >> fs[o_assoc] >> once_rw[one_to_one_id] >> rw[idL,idR] >>
 arw[] >> rpt strip_tac >> arw[] >> assume_tac PRE_def >> arw[])
(form_goal 
“!n:1->N. sub o pa(Nn,nN,ZERO,n) = ZERO”)


val zero_less_eq = proved_th $ 
e0
(rpt strip_tac >> drule le_sub >> arw[] >>
 rw[sub_0])
(form_goal
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==> 
  !x. char(i1, i2, le) o pa(Nn, nN, ZERO, x) = i2”)

val less_eq_mono = proved_th $
e0
(rpt strip_tac >> drule le_sub >> arw[] >>
 rw[sub_mono_eq]
 )
(form_goal
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==> 
  (!m n.char(i1, i2, le) o pa(Nn, nN, SUC o m, SUC o n) = i2 <=>
       char(i1, i2, le) o pa(Nn, nN, m, n) = i2)”)

val lt_char_LT = proved_th $
e0
(rpt strip_tac >> assume_tac $ GSYM lt_def >>
 assume_tac lt_mono >> rfs[] >> drule char_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[]) >>
 qexists_tac "x0" >> arw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==> 
 !x:1->NN. (?(x0 : 1 -> LT). x = lt o x0) <=>
               char(i1, i2, lt) o x = i2”)


val le_char_LE = proved_th $
e0
(rpt strip_tac >> strip_assume_tac le_def >>
 assume_tac le_mono >> drule char_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[]) >>
 qexists_tac "x0" >> arw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==> 
 !x:1->NN. (?(x0 : 1 -> LE). x = le o x0) <=>
               char(i1, i2, le) o x = i2”)


val less_0 = proved_th $
e0
(rpt strip_tac >> 
 drule lt_char_LT >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 pop_assum (K all_tac) >>
 assume_tac lt_iff_le_ne >> once_arw[] >>
 assume_tac Thm2_1 >>
 first_x_assum (qspecl_then ["n"] assume_tac) >>
 by_tac “~(ZERO = SUC o n)” >--
 (ccontra_tac >> fs[]) >>
 arw[] >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 drule le_char_LE >> arw[] >>
 drule zero_less_eq >> arw[]
 )
(form_goal
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==> 
  !n. char(i1, i2, lt) o pa(Nn, nN, ZERO, SUC o n) = i2”)

val less_mono_eq = proved_th $
e0
(rpt strip_tac >> assume_tac lt_iff_le_ne >>
 assume_tac lt_mono >> assume_tac lt_def >>
 pop_assum (assume_tac o GSYM) >> fs[] >>
 drule char_def >> first_x_assum drule >> 
 drule $ GSYM lt_char_LT >>
 arw[] >>
 drule le_char_LE >> arw[] >>
 drule less_eq_mono >> arw[] >>
 rw[inv_suc_eq])
(form_goal
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==> 
  (!m n.char(i1, i2, lt) o pa(Nn, nN, SUC o m, SUC o n) = i2 <=>
       char(i1, i2, lt) o pa(Nn, nN, m, n) = i2)”)

val or_ex = proved_th $
e0
(rpt strip_tac >> 
 by_tac “ismono(pa(Tt,tT:TT->two,i1:1->two,i1:1->two))”
 >-- (qspecl_then ["TT","pa(Tt, tT, i1, i1)"] accept_tac
      dom_1_mono) >>
 drule Thm5 >> 
 pop_assum (x_choosel_then ["O","or0"] strip_assume_tac) >>
 drule char_def >> first_x_assum drule >>
 qexists_tac "char(i1,i2,or0)" >> rpt strip_tac >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 qspecl_then ["1","O"] (x_choosel_then ["W","ione","iO"] assume_tac) copr_ex >>
 first_x_assum drule >>
 fs[ismem_def] >> 
 drule inc_ismono >> fs[] >>
 drule iso_copr_copr >> first_x_assum drule >>
 drule copr_disjoint >> 
 first_x_assum 
 (qspecl_then ["pa(Tt, tT, p1, p2)"] (assume_tac o GSYM)) >>
 (*should not be done by hand*)
 by_tac
 “(?x0 : 1 -> O. or0:O->TT o x0 = pa(Tt:TT->two, tT:TT->two, p1:1->two, p2:1->two)) <=> 
 (?x0 : 1 -> O. pa(Tt, tT, p1, p2) = or0 o x0)”
 >-- ((*aqed, may need test new tool here*) dimp_tac >> strip_tac >>
      qexists_tac "x0" >> arw[]) >>
 arw[] >> once_rw[one_to_one_id] >> rw[idR] >>
 suffices_tac
 “~(pa(Tt, tT, p1, p2) = pa(Tt:TT->two, tT, i1, i1:1->two)) <=> 
  (p1 = i2 | p2:1->two = i2:1->two)”
 >-- (strip_tac >> dimp_tac>> strip_tac >--
      (by_tac “~(pa(Tt:TT->two, tT:TT->two, p1:1->two, p2) = pa(Tt, tT, i1:1->two, i1:1->two))” 
       >-- (ccontra_tac >>
           suffices_tac “?x0:1->1. pa(Tt:TT->two, tT:TT->two, p1:1->two, p2) = pa(Tt, tT, i1:1->two, i1:1->two)”
           >-- (disch_tac >> first_x_assum opposite_tac) >>
           qexists_tac "id(1)" >> first_x_assum accept_tac)>>
       fs[]
       ) >> 
       ccontra_tac >> pop_assum strip_assume_tac >>
       fs[] ) >>
 suffices_tac
 “pa(Tt:TT->two, tT, p1, p2) = pa(Tt, tT, i1, i1) <=>
 p1 = i1:1->two & p2 = i1:1->two” >--
 (strip_tac >> once_arw[] >> drule i1_xor_i2 >> dimp_tac >>
  strip_tac (* 3 *)
  >-- (cases_on “p1 = i1:1->two” (* 2 *)
       >-- (fs[] >> rfs[]) >>
       first_x_assum (qspecl_then ["p1"] assume_tac) >>
       fs[] >> ccontra_tac >> fs[] >>
       drule i1_ne_i2 >> fs[]) 
  >-- (ccontra_tac >> fs[] >> drule i1_ne_i2 >> fs[]) >>
  ccontra_tac >> fs[] >> drule i1_ne_i2 >> fs[]) >>
 dimp_tac >> strip_tac (* 2 *) >-- 
(by_tac 
 “Tt o pa(Tt:TT->two, tT:TT->two, p1:1->two, p2:1->two) = Tt o pa(Tt, tT, i1, i1) & 
  tT o pa(Tt:TT->two, tT:TT->two, p1:1->two, p2:1->two) = tT o pa(Tt, tT, i1, i1)”
 >-- arw[] >>
 pop_assum mp_tac >> drule p12_of_pa >> arw[]) >>
 arw[]
 )
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !TT Tt:TT->two tT:TT->two. ispr(Tt,tT) ==>
 ?or:TT->two. 
 !p1:1->two p2. or o pa(Tt,tT,p1,p2) =i2 <=> 
  (p1 = i2 | p2 = i2)”)

val less_cases_pred = proved_th $
e0
(rpt strip_tac >>
 qspecl_then ["two","two"] 
 (x_choosel_then ["TT","Tt","tT"] assume_tac) pr_ex >>
 drule or_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac $ q2str
 ‘or o 
  pa(Tt,tT, 
     char(i1,i2,lt),char(i1,i2,le) o pa(Nn,nN,nN,Nn))’ >>
 rw[o_assoc] >> assume_tac nN_def >>
 drule distr_to_pa' >> rev_drule distr_to_pa' >>
 arw[] >>
 arw[o_assoc] >> drule p12_of_pa >> arw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==> 
  ?pred:NN->two.
  (!m n. (char(i1,i2,lt) o pa(Nn,nN,m,n) = i2 | 
         char(i1,i2,le) o pa(Nn,nN,n,m) = i2) <=> 
         pred o pa(Nn,nN,m,n) = i2)”)

val less_cases = proved_th $
e0
(strip_tac >> strip_tac >> strip_tac >> strip_tac >> 
 by_tac 
 “?pred:NN->two.
  (!m n. (char(i1,i2,lt) o pa(Nn,nN,m,n) = i2 | 
         char(i1,i2,le) o pa(Nn,nN,n,m) = i2) <=> 
         pred o pa(Nn,nN,m,n) = i2)”
 >-- (drule less_cases_pred >> first_x_assum accept_tac) >>
 pop_assum strip_assume_tac >> once_arw[] >>
 drule double_ind >>
 suffices_tac 
 “!n m. pred o pa(Nn, nN, m, n) = i2:1->two” >--
 (rpt strip_tac >> arw[]) >>
 once_arw[] >> pop_assum (K all_tac) >> strip_tac (* 2 *)
 >-- (strip_tac >> pop_assum (assume_tac o GSYM) >>
      arw[] >> disj2_tac >>
      drule zero_less_eq >> arw[]) >>
 strip_tac >> strip_tac >> strip_tac (* 2 *) >--
 (pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
 strip_tac >> once_arw[] >> disj1_tac >>
 drule less_0 >> arw[]) >>
 pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >>
 strip_tac >> strip_tac >> strip_tac >> once_arw[] >>
 pop_assum (K all_tac) >> rfs[] >>
 first_x_assum (qspecl_then ["m"] assume_tac) >>
 drule less_mono_eq >> drule less_eq_mono >> arw[])
(form_goal
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
  !m n.char(i1,i2,lt) o pa(Nn,nN,m,n) = i2 |
       char(i1,i2,le) o pa(Nn,nN,n,m) = i2”)

val less_eq_cases = proved_th $
e0
(rpt strip_tac >> drule less_cases >>
 cases_on “char(i1:1->two, i2, le) o pa(Nn, nN, m:1->N, n) = i2” (* 2 *)
 >-- arw[] >>
 fs[] >> 
 first_x_assum (qspecl_then ["n","m"] assume_tac) >>
 fs[] >>
 assume_tac lt_iff_le_ne >> assume_tac le_mono >>
 drule char_def >> first_x_assum drule >> 
 first_x_assum (qspecl_then ["n","m"] assume_tac) >>
 pick_xnth_assum 5 (assume_tac o GSYM) >>
 arw[] >>
 assume_tac lt_mono >> drule char_def >>
 first_x_assum drule >> assume_tac lt_def >>
 pop_assum (assume_tac o GSYM) >>
 fs[] >>
 first_x_assum (qspecl_then ["pa(Nn,nN,n,m)"] assume_tac) >>
 rfs[] >>
 by_tac 
 “?lt0:1->LT. pa(Nn,nN,n,m) = lt o lt0”
 >-- (qexists_tac "x0" >> arw[]) >>
 rfs[] >> qexists_tac "le0" >> rw[]
 )
(form_goal
 “!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
  !m n.char(i1,i2,le) o pa(Nn,nN,m,n) = i2 |
       char(i1,i2,le) o pa(Nn,nN,n,m) = i2”)

val cancel_sub0 = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["1","1"] (x_choosel_then ["two","i1","i2"]
 assume_tac) copr_ex >>
 drule cancel_sub00 >>
 drule less_eq_cases >>
 first_x_assum irule >>
 drule le_sub >> pop_assum (assume_tac o GSYM) >>
 fs[] >> 
 pop_assum (K all_tac) >>
 first_assum (qspecl_then ["n","a"] assume_tac) >>
 first_x_assum (qspecl_then ["m","a"] assume_tac) >>
 fs[]
 )
(form_goal 
“!a n m. ~(sub o pa(Nn,nN,n,a) = ZERO) & ~(sub o pa(Nn,nN,m,a) = ZERO) ==>
 (sub o pa(Nn,nN,n,a) = sub o pa(Nn,nN,m,a)  <=> n = m)”)

val equality_NN_ind = proved_th $
e0
(rpt strip_tac >> assume_tac nN_def >>
 drule equality_ind >> first_x_assum drule >> once_arw[] >>
 rw[])
(form_goal
“!f:NN->N g:NN->N.
 !m:1->N.(!n.f o pa(Nn,nN,m,n) = g o pa(Nn,nN,m,n)) <=>
 f o pa(Nn,nN,m,ZERO) = g o pa(Nn,nN,m,ZERO) & 
 !n0:1->N. f o pa(Nn,nN,m,n0) = g o pa(Nn,nN,m,n0) ==> 
 f o pa(Nn,nN,m,SUC o n0) = g o pa(Nn,nN,m,SUC o n0)”)


val add_suc0 = proved_th $
e0
(once_rw[equality_NN_ind] >>
 assume_tac nN_def >> drule p12_of_pa >> drule distr_to_pa'>>
 arw[o_assoc,idL,add_elements] >> rpt strip_tac >>
 arw[])
(form_goal
“!n m:1->N.(add o pa(Nn,nN,SUC o Nn,id(N) o nN)) o pa(Nn,nN,n,m) = (SUC o add) o pa(Nn,nN,n,m)”)

val add_suc = proved_th $
e0
(assume_tac add_suc0 >> fs[idL,o_assoc] >>
 assume_tac nN_def >> drule distr_to_pa' >>
 fs[] >> drule p12_of_pa >> fs[o_assoc])
(form_goal 
“!n:1->N m:1->N. add o pa(Nn,nN,SUC o n,m) = SUC o add o pa(Nn,nN,n,m)”)

val add_sym0 = proved_th $
e0
(once_rw[equality_NN_ind] >>
 strip_tac >> assume_tac add_elements >> 
 rw[o_assoc] >> assume_tac nN_def >> drule distr_to_pa' >>
 arw[] >> drule p12_of_pa >> arw[] >>
 rw[add_z_n] >> rpt strip_tac >> arw[] >>
 assume_tac add_suc >> arw[])
(form_goal “!m:1->N. (!n. add o pa(Nn,nN,m,n) = (add o pa(Nn,nN,nN,Nn)) o pa(Nn,nN,m,n))”)

val add_sym = proved_th $
e0
(assume_tac add_sym0 >> assume_tac nN_def >>
 drule p12_of_pa >> drule distr_to_pa' >> fs[o_assoc])
(form_goal 
“!m:1->N n:1->N. add o pa(Nn,nN,m,n) = add o pa(Nn,nN,n,m)”)

val suc_sub = proved_th $
e0
(assume_tac add_sub >> strip_tac >>
 first_x_assum (qspecl_then ["SUC o ZERO","n"] assume_tac) >>
 suffices_tac
 “add o pa(Nn, nN, SUC o ZERO, n) = SUC o n:1->N”
 >-- (strip_tac >> fs[]) >>
 once_rw[add_sym] >> rw[add_elements])
(form_goal
 “!n:1->N. sub o pa(Nn,nN,SUC o n,n) = SUC o ZERO”)

val sub_diff_1 = proved_th $
e0
(rpt strip_tac >> dimp_tac >--
 (strip_tac >> irule $ iffLR cancel_sub0 >> qexists_tac "b" >>
 assume_tac suc_sub >> once_arw[] >> arw[Thm2_1]) >>
 rpt strip_tac >> arw[suc_sub])
(form_goal 
“!a:1->N b. sub o pa(Nn,nN,a,b) = SUC o ZERO <=> a = SUC o b”)


val s_eq_iff_eq = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 assume_tac Thm2_2 >> drule ismono_property >>
 first_x_assum drule >> arw[])
(form_goal 
“!n1:1->N n2. SUC o n1 = SUC o n2 <=> n1 = n2”)

val p_z_cases = proved_th $
e0
(assume_tac PRE_def >> strip_tac >>
 cases_on “n = ZERO” >-- arw[] >>
 arw[] >> assume_tac z_xor_s >>
 first_x_assum (qspecl_then ["n"] assume_tac) >>
 rfs[] >> arw[GSYM o_assoc,idL] >>
 assume_tac s_eq_iff_eq >> arw[])
(form_goal
“!n:1->N. PRE o n = ZERO <=> (n = ZERO | n = SUC o ZERO)”)

(*correct thm wrong proof*)
val sub_s_z_cases = proved_th $
e0
(rpt strip_tac >> assume_tac sub_s >> fs[] >>
 by_tac “sub o pa(Nn, nN, a, b) = ZERO | 
         sub o pa(Nn, nN, a, b) = SUC o ZERO”
 >-- (drule $ iffLR p_z_cases >> arw[])>>
 pop_assum strip_assume_tac >-- arw[] >>
 disj1_tac >>
 fs[sub_diff_1] 
 )
(form_goal 
“!a:1->N b:1->N. sub o pa(Nn,nN,a,SUC o b) = ZERO ==>
 a = SUC o b | sub o pa(Nn,nN,a,b) = ZERO”)


(*TODO: aQ:
 5.!(x : 1 -> NN). (?(x0 : 1 -> LE). le o x0# = x#) <=>
               char(i1, i2, le) o x# = i2
   6.!(x : 1 -> N). char(i1, i2, le) o pa(Nn, nN, x#, x#) = i2
   ----------------------------------------------------------------------
   char(i1, i2, le) o pa(Nn, nN, n, n) = i2

why arw[] uses 5, but not 6? still give trivial goal though, so not too bad
*)


val le_cases_iff = proved_th $
e0
(rpt strip_tac >> cases_on “n0 = n:1->N” (* 2 *)
 >-- (arw[] >>
 assume_tac clt_iff_le_ne >> first_x_assum drule >>
 arw[] >> assume_tac le_mono >> drule char_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 fs[] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 drule le_refl >> first_x_assum (qspecl_then ["n"] assume_tac) >>
 first_x_assum accept_tac) >>
 arw[] >> assume_tac clt_iff_le_ne >>
 first_x_assum drule >> arw[] >> 
 assume_tac le_mono >> drule char_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 arw[] >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[])  >>
 qexists_tac "le0" >> arw[])
(form_goal “!two i1:1->two i2:1->two.iscopr(i1,i2) ==> 
 !n0:1->N n:1->N. char(i1, i2, le) o pa(Nn, nN, n0, n) = i2 <=> char(i1,i2,lt) o  pa(Nn, nN, n0, n) = i2 | n0 = n”)



val sub_eq_0 = proved_th $
e0
(rpt strip_tac >> assume_tac le_def >> pop_assum strip_assume_tac >>
 drule $ iffLR ispb_def >> pop_assum strip_assume_tac >>
 assume_tac le_mono >> drule char_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >> once_arw[] >>
 drule pb_fac_iff_1 >> once_arw[] >> rw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
(!m:1->N n:1->N. sub o pa(Nn,nN,m,n) = ZERO <=> char(i1,i2,le) o pa(Nn,nN,m,n) = i2)”)





val PRE_eq_0 = proved_th $
e0
(strip_tac >> assume_tac PRE_def >> cases_on “n = ZERO” >> arw[] >>
 dimp_tac >> strip_tac (* 2 *) >--
 (assume_tac z_xor_s >> first_x_assum (qspecl_then ["n"] assume_tac) >>
 rfs[] >> fs[GSYM o_assoc,idL] >> rfs[idL] >> arw[] >> arw[GSYM o_assoc,idL]) >>
 arw[GSYM o_assoc,idL])
(form_goal
“!n:1->N. PRE o n = ZERO <=> (n = ZERO | n = SUC o ZERO)”)

val lt_succ_le = proved_th $
e0
(rpt strip_tac >> drule clt_iff_le_ne >> arw[] >>
 pop_assum (K all_tac) >> assume_tac le_mono >>
 drule char_def >> first_x_assum drule >>
 drule le_cases_iff >> 
 first_x_assum (qspecl_then ["pa(Nn, nN, n0, SUC o n)"] assume_tac) >>
 by_tac 
 “(?le0 : 1 -> LE. pa(Nn, nN, n0:1->N, SUC o n:1->N) = le o le0) <=> 
  (?x0 : 1 -> LE. le o x0 = pa(Nn, nN, n0, SUC o n))”
 >-- (dimp_tac >> strip_tac
      >-- (qexists_tac "le0" >> arw[]) >>
      qexists_tac "x0" >> arw[]) >> arw[] >> 
 once_arw[] >> pop_assum (K all_tac) >> pop_assum mp_tac >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >> 
 strip_tac >> once_arw[] >> assume_tac (GSYM sub_eq_0) >>
 first_x_assum drule >> arw[] >>
 assume_tac sub_elements >> arw[] >> cases_on “sub o pa(Nn,nN,n0:1->N,n) = ZERO” 
 >-- (arw[] >> assume_tac PRE_def >> arw[] >>
      assume_tac (GSYM sub_diff_1) >> once_arw[] >>
      pop_assum (K all_tac) >> ccontra_tac >> fs[] >>
      fs[Thm2_1]) >>
 arw[] >> ccontra_tac >> pop_assum strip_assume_tac >>
 pop_assum mp_tac >> assume_tac (GSYM sub_diff_1) >>
 once_arw[] >> once_arw[] >> rw[] >> pop_assum (K all_tac) >> 
 assume_tac PRE_eq_0 >> fs[])
(form_goal “!two i1:1->two i2:1->two.iscopr(i1,i2) ==> 
 !n0:1->N n:1->N. char(i1, i2, lt) o pa(Nn, nN, n0, SUC o n) = i2 <=> char(i1,i2,le) o pa(Nn, nN, n0, n) = i2”)




val strong_ind_lemma = proved_th $ 
e0
(rpt strip_tac >> 
 suffices_tac “isiso(q:Q->N)”
 >-- (strip_tac >> irule mono_epi_is_iso >> arw[] >>
      drule iso_is_epi >>
      suffices_tac “?q2p:Q->P. p0:P->N o q2p = q” 
      >-- (strip_tac >> pop_assum (assume_tac o GSYM) >> 
           fs[] >> drule o_epi_imp_epi >>
           first_x_assum accept_tac) >>
      irule prop_2_half2 >> arw[] >> rpt strip_tac >>
      rev_drule char_def >> first_x_assum drule >>
      arw[] >> last_x_assum (qspecl_then ["x"] assume_tac) >>
      first_assum (assume_tac o iffLR) >>
      first_x_assum irule >> 
      by_tac “?(nb : 1 -> Q). x = q:Q->N o nb”
      >-- (qexistsl_tac ["xb"] >> arw[]) >>
      arw[] >> drule le_refl >> arw[]) >>
irule Thm2_3' >> arw[] >>
rw[ismem_def] >> arw[] >> strip_tac (* 2 *) >--
(suffices_tac “?(x0 : 1 -> Q). ZERO = q o x0”
 >-- (strip_tac >> qexistsl_tac ["x0"] >> arw[]) >>
 arw[] >> rpt strip_tac >> first_x_assum irule >>
 drule le_z_z >> first_x_assum drule >> arw[] >>
 suffices_tac 
 “!n0:1->N. ~(char(i1,i2:1->two,lt) o pa(Nn,nN,n0,ZERO) = i2)”
 >-- (strip_tac >> arw[]) >>
 drule not_lt_z >> first_x_assum accept_tac) >>
 rpt strip_tac >> 
 suffices_tac “?(x0 : 1 -> Q). SUC o n = q:Q->N o x0”
 >-- (strip_tac >> qexistsl_tac ["x0'"] >> arw[]) >>
 arw[] >> pop_assum mp_tac >> pop_assum mp_tac >>
 pop_assum (qspecl_then ["n"] assume_tac) >> 
 rpt strip_tac >> drule le_cases >>
 first_x_assum drule >> 
 first_x_assum strip_assume_tac (* 2 *) >-- 
 (by_tac “?nb:1->Q. n = q:Q->N o nb”
  >-- (qexists_tac "x0" >> sym_tac >> 
       first_x_assum accept_tac) >>
  pop_assum mp_tac >> arw[] >> strip_tac >> 
  first_x_assum irule >>
  drule lt_succ_le >> 
  pop_assum (assume_tac o GSYM) >> once_arw[] >>
  first_x_assum accept_tac) >> 
first_x_assum irule >> 
by_tac “?nb:1->Q. n = q:Q->N o nb”
>-- (qexists_tac "x0" >> sym_tac >> 
    first_x_assum accept_tac) >>
first_assum (assume_tac o iffLR) >>
first_x_assum drule >> once_arw[] >> rpt strip_tac >>
first_x_assum irule >> drule lt_succ_le >> fs[])
(form_goal 
“!P p0:P->N. ismono(p0) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !Q q:Q->N. 
  (ismono(q) & !n:1->N. (?nb:1->Q. n = q o nb) <=> 
            (!n0:1->N. char(i1,i2,le) o pa(Nn,nN,n0,n) = i2
==> char(i1,i2,p0) o n0 = i2))
 ==>
 (!n:1->N. 
  (!n0:1->N. 
    char(i1,i2,lt) o pa(Nn,nN,n0,n) = i2 ==> char(i1,i2,p0) o n0 = i2) ==> char(i1,i2,p0) o n = i2) ==> isiso(p0)”)






val char_diag_gen = proved_th $
e0
(rpt strip_tac >> drule char_diag >> first_x_assum drule >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (irule fun_ext >> strip_tac >> pop_assum mp_tac >>
      pop_assum (assume_tac o GSYM) >> once_arw[] >> 
      strip_tac >> 
      by_tac 
      “char(i1:1->two, i2:1->two, pa(Aa:AA->A, aA, id(A), id(A))) o pa(Aa, aA, a1, a2) o a = i2:1->two o to1(X,1) o a:1->X”
      >-- arw[GSYM o_assoc] >>
      pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR] >>
      drule distr_to_pa >> arw[]) >>
irule fun_ext >> strip_tac >> rw[o_assoc] >> once_rw[one_to_one_id] >>
rw[idR] >> drule distr_to_pa >> arw[idR])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !A AA Aa:AA->A aA:AA ->A. ispr(Aa,aA) ==>
 !X a1:X->A a2:X->A. char(i1,i2,pa(Aa,aA,id(A),id(A))) o pa(Aa,aA,a1,a2) = i2 o to1(X,1) <=> a1 = a2”)






(*TODO: wrong error message:
ismono(pa(Tt,tT:TT->two,i2:1->two,i1:1->two))

if forget the pa, then 

 Exception-
   HOL_ERR
     {message = "different length lists", origin_function = "zip",
      origin_structure = "Lib"} raised

*)


(*TODO: should eliminate the x0:

~(?(x0 : 1 -> 1). pa(Tt, tT, p1, p2) = pa(Tt, tT, i2, i1))*)





val Q_ex = proved_th $
e0
(rpt strip_tac >> drule Uq_ex >> 
 qspecl_then ["N","two"] (x_choosel_then ["N2","NN2","p1","p2","ev"] assume_tac) exp_ex >>
 first_x_assum drule >> 
 pop_assum (x_choosel_then ["Un"] assume_tac) >>
 drule imp_ex >> 
 qspecl_then ["two","two"] (x_choosel_then ["TT","Tt","tT"] assume_tac) pr_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >> 
 abbrev_tac “imp:TT->two o pa(Tt,tT,char(i1,i2,le),char(i1:1->two,i2:1->two,p0:P->N) o Nn) = lep0” >>
 abbrev_tac “Un:N2->two o tp(p1:NN2->N,p2:NN2->N2,ev:NN2->two,Nn,nN,lep0:NN->two) = cq” >>
 qspecl_then ["N","two","cq","1","i2"] (x_choosel_then ["Q","q","Qto1"] assume_tac) pb_ex >>
 qexistsl_tac ["Q","q"] >>
 by_tac “ismono(q:Q->N)”
 >-- (drule pb_mono_mono >> first_x_assum irule >>
     qspecl_then ["two","i2"] accept_tac dom_1_mono) >>
 arw[] >> strip_tac >>
 by_tac “(?nb:1->Q. n:1->N = q o nb) <=> cq:N->two o n = i2”
 >-- (drule pb_fac_iff_1 >> pop_assum (assume_tac o GSYM) >> arw[] >>
      dimp_tac >> strip_tac >-- (qexists_tac "nb" >> arw[]) >>
      qexists_tac "a" >> arw[]) >>
 arw[] >> 
 assume_tac nN_def >> first_x_assum drule >>
 qpick_x_assum ‘Un o tp(p1, p2, ev, Nn, nN, lep0) = cq’
 (assume_tac o GSYM) >>
 once_arw[] >> rw[o_assoc] >> arw[] >>
 qpick_x_assum 
 ‘imp o pa(Tt, tT, char(i1, i2, le), char(i1, i2, p0) o Nn) = lep0’ (assume_tac o GSYM) >>
 once_arw[] >> rw[o_assoc] >>
 by_tac
“!x.pa(Tt:TT->two, tT:TT->two, char(i1:1->two, i2:1->two, le), (char(i1, i2, p0:P->N) o Nn)) o pa(Nn, nN, x, n:1->N)= pa(Tt:TT->two,tT:TT->two, char(i1:1->two, i2:1->two, le) o pa(Nn, nN, x:1->N, n:1->N),char(i1,i2,p0) o x)”
 >-- (strip_tac >> rev_drule to_p_eq >>
      first_x_assum irule >> rev_drule p12_of_pa >>
      arw[GSYM o_assoc] >> rw[o_assoc] >>
      drule p1_of_pa >> arw[])>> 
 by_tac 
 “(!x : 1 -> N. imp o
                  pa(Tt:TT->two, tT:TT->two, char(i1:1->two, i2:1->two, le), (char(i1, i2, p0:P->N) o Nn)) o
                  pa(Nn, nN, x, n) = i2) <=> 
  (!x : 1 -> N. imp o
                  pa(Tt, tT, char(i1, i2, le) o pa(Nn, nN, x, n),
                  char(i1, i2, p0) o x) = i2)” >-- 
 (dimp_tac >> rpt strip_tac (* 2 *) >--
 (first_x_assum (qspecl_then ["x"] assume_tac) >>
  first_x_assum (qspecl_then ["x"] assume_tac) >> 
  fs[]) >>
 first_x_assum (qspecl_then ["x"] assume_tac) >>
 first_x_assum (qspecl_then ["x"] (assume_tac o GSYM)) >> 
 fs[]) >>
 once_arw[] >> dimp_tac (* 2 *) >--
 (strip_tac >> strip_tac >>
  first_x_assum (qspecl_then ["n0"] assume_tac) >>
  first_x_assum (qspecl_then ["char(i1, i2, le) o pa(Nn, nN, n0, n)","char(i1, i2, p0) o n0"] assume_tac) >>
 pop_assum (assume_tac o iffLR) >> 
 strip_tac >> first_x_assum irule >> arw[]) >>
 rpt strip_tac >>  
 first_x_assum (irule o iffRL) >> arw[])
(form_goal 
“!P p0:P->N. ismono(p0) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 ?Q q:Q->N. 
  ismono(q) & !n:1->N. (?nb:1->Q. n = q o nb) <=> 
            (!n0:1->N. char(i1,i2,le) o pa(Nn,nN,n0,n) = i2
==> char(i1,i2,p0) o n0 = i2)”)

val strong_ind = proved_th $
e0
(rpt strip_tac >> drule strong_ind_lemma >>
 first_x_assum drule >>
 drule Q_ex >>
 first_x_assum drule >> 
 pop_assum (x_choosel_then ["Q","q"] assume_tac) >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal 
“!P p0:P->N. ismono(p0) ==>
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 (!n:1->N. 
  (!n0:1->N. 
    char(i1,i2,lt) o pa(Nn,nN,n0,n) = i2 ==> char(i1,i2,p0) o n0 = i2) ==> char(i1,i2,p0) o n = i2) ==> isiso(p0)”)


val neg_ex = proved_th $
e0
(rpt strip_tac >> 
 qexists_tac "copa(i1,i2,i2,i1)" >> strip_tac >>
 drule i1_xor_i2 >> 
 cases_on “pred = i1:1->two” (* 2 *) >--
 (arw[] >> drule i1_of_copa >>arw[]) >>
 rfs[] >> pop_assum (K all_tac) >> pop_assum (assume_tac o GSYM)>>
 fs[] >> drule i2_of_copa >> arw[])
(form_goal
“!two i1:1->two i2:1->two.iscopr(i1,i2) ==>
 ?neg: two -> two.
 !pred:1->two. neg o pred = i2 <=> pred = i1”)


val o_assoc_middle = proved_th $
e0
(rpt strip_tac >> rw[o_assoc])
(form_goal 
“!A B f:A->B C g:B->C D h:C->D E i:D->E. 
 i o h o g o f = i o (h o g) o f”)


val exists_forall0 = 
exists_forall ("x",mk_ar_sort (mk_ob "A") (mk_ob "B"))

val Exq_ex = proved_th $
e0
(rpt strip_tac >> drule Uq_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >> 
 drule neg_ex >> pop_assum strip_assume_tac >>
 qexists_tac "neg o Uq o tp(p1,p2,ev,p1,p2,neg o ev)" >>
 rpt strip_tac >> first_x_assum drule >>
 rw[o_assoc] >> once_arw[] >> 
 qby_tac 
 ‘tp(p1, p2, ev, p1, p2, (neg o ev)) o tp(p1, p2, ev, Xy, xY, pxy)   = tp(p1,p2,ev,Xy,xY,neg o pxy)’ >-- 
 (drule is_tp >> first_x_assum drule >> 
  first_x_assum irule >> 
 (*ToDO: ppbug
   pa(p1, p2, Xy, (tp(p1, p2, ev, p1, p2, (neg o ev)) *)
  qby_tac 
  ‘pa(p1, p2, Xy, (tp(p1, p2, ev, p1, p2, (neg o ev)) o
   tp(p1, p2, ev, Xy, xY, pxy)) o xY) = 
   pa(p1, p2, p1,tp(p1, p2, ev, p1, p2, (neg o ev)) o p2) o 
   pa(p1, p2,Xy,tp(p1, p2, ev, Xy, xY, pxy) o xY)’ >--
  (drule exp_ispr >> drule to_p_eq >> first_x_assum irule >>
   drule p12_of_pa >> arw[GSYM o_assoc] >>
   arw[o_assoc]) >>
  once_arw[] >> rw[GSYM o_assoc] >>  
  drule ev_of_tp >> drule exp_ispr >> first_x_assum drule >>
  once_arw[] >> rw[o_assoc] >> drule ev_of_tp >> 
  first_x_assum rev_drule >> arw[]) >>
 once_rw[o_assoc_middle] >> once_arw[] >> 
 qby_tac 
 ‘Uq o tp(p1, p2, ev, Xy, xY, (neg o pxy)) o y = i1 <=>
  ~(Uq o tp(p1, p2, ev, Xy, xY, (neg o pxy)) o y = i2)’ >--
 (drule i1_xor_i2 >> arw[]) >>
 once_arw[] >> pop_assum (K all_tac) >> once_arw[] >>
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 arw[o_assoc] >> drule i1_xor_i2 >> once_arw[] >>
 once_rw[exists_forall0] >> rw[])
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !X eps ps p1:eps->X p2:eps ->ps ev:eps->two.isexp(p1,p2,ev) ==>
 ?Exq:ps -> two. 
 !Y XY Xy:XY->X xY:XY->Y. ispr(Xy,xY) ==>
 !pxy:XY->two y:1->Y. 
 (Exq o tp(p1,p2,ev,Xy,xY,pxy) o y = i2  <=> 
  ?x:1->X. pxy o pa(Xy,xY,x,y) = i2)”)

val Posym_def = ex2fsym "*" ["A","B"] (iffRL $ eqT_intro $ spec_all pr_ex)
                        |> C mp (trueI []) |> gen_all

val pi1_def = ex2fsym "π1" ["A","B"] (iffRL $ eqT_intro $ spec_all Posym_def)
                        |> C mp (trueI []) |> gen_all

val pi2_def = ex2fsym "π2" ["A","B"] (iffRL $ eqT_intro $ spec_all pi1_def) |> C mp (trueI []) |> gen_all

val ispr_def = new_ax
“!A B AB p1:AB->A p2:AB->B. ispr(p1,p2) <=>
 !X f:X->A g:X->B. 
 ?fg0:X->AB. !fg. p1 o fg = f  & p2 o fg = g <=> fg = fg0”

val pa_def0 = 
ex2fsym "pa" ["p1","p2","f","g"] 
(iffLR $ spec_all ispr_def |> strip_all_and_imp |>
 disch_all) 

val pa_def = 
    pa_def0 |> undisch 
            |> allI ("g",ar_sort (mk_ob "X") (mk_ob "B"))
            |> allI ("f",ar_sort (mk_ob "X") (mk_ob "A"))
            |> allI ("X",ob_sort) |> disch_all
            |> allI ("p2",ar_sort (mk_ob "AB") (mk_ob "B"))
            |> allI ("p1",ar_sort (mk_ob "AB") (mk_ob "A"))
            |> allI ("AB",ob_sort)
            |> allI ("B",ob_sort)
            |> allI ("A",ob_sort)

val Pa_ex = proved_th $
e0
(rpt strip_tac >> assume_tac pi2_def >>
 first_x_assum (qspecl_then ["A","B"] assume_tac) >>
 fs[ispr_def])
(form_goal 
“!X A f:X->A B g:X->B. ?fg:X->A * B. 
 !fg'. π1(A,B) o fg' = f & π2(A,B) o fg' = g <=> fg' = fg”)

val Pa_def = ex2fsym "Pa" ["f","g"] (iffRL $ eqT_intro $ spec_all Pa_ex) |> C mp (trueI []) |> gen_all


val isexp_def = new_ax
“!A B A2B efs p1:efs->A p2:efs-> A2B ev:efs -> B.
 isexp(p1,p2,ev) <=> 
 ispr(p1,p2) & 
 !X AX p1':AX->A p2':AX->X.ispr(p1',p2') ==>
 !f:AX->B.?h0:X-> A2B. !h. ev o pa(p1,p2,p1',h o p2') = f <=> h = h0”


val tp_def0 = ex2fsym "tp" ["p1","p2","ev","p1'","p2'","f"] 
(iffLR $ spec_all isexp_def |> strip_all_and_imp |>
 conjE2 |> strip_all_and_imp |> conj_all_assum |> disch_all)


val tp_def0' = 
    tp_def0 |> undisch |> gen_all |> split_assum 
            |> disch “ispr(p1':AX->A, p2':AX->X)”
            |> allI ("p2'",ar_sort (mk_ob "AX") (mk_ob "X"))
            |> allI ("p1'",ar_sort (mk_ob "AX") (mk_ob "A"))
            |> allI ("AX",ob_sort)
            |> allI ("X",ob_sort)
            |> disch_all 
            |> allI ("ev",ar_sort (mk_ob "efs") (mk_ob "B"))
            |> allI ("p2",ar_sort (mk_ob "efs") (mk_ob "A2B"))
            |> allI ("p1",ar_sort (mk_ob "efs") (mk_ob "A"))
            |> genl [("efs",ob_sort),("A2B",ob_sort)]
            |> allI ("B",ob_sort) |> allI ("A",ob_sort)

val tp_def = proved_th $
e0
(rpt strip_tac >-- (drule $ iffLR isexp_def >> arw[]) >>
 drule tp_def0' >> first_x_assum drule >> arw[])
(form_goal
 “!A B A2B efs p1: efs -> A p2 : efs -> A2B ev: efs -> B.
        isexp(p1, p2, ev) ==>
        ispr(p1,p2) &
        !X AX p1': AX -> A p2': AX -> X.
          ispr(p1', p2') ==>
          !f : AX -> B h : X -> A2B.
            ev o pa(p1, p2, p1', h o p2') = f <=>
            h = tp(p1, p2, ev, p1', p2', f)”)


val pa_iso = proved_th $
e0
(rpt strip_tac >> rw[isiso_def] >>
 qexists_tac "pa(p1,p2,p1',p2')" >> 
 strip_tac (* 2 *) >-- 
 (rev_drule to_p_eq >> first_x_assum irule >>
  rev_drule p12_of_pa >> arw[GSYM o_assoc] >>
  drule p12_of_pa >> arw[idR]) >>
 drule to_p_eq >> first_x_assum irule >>
 drule p12_of_pa >> arw[GSYM o_assoc,idR] >>
 rev_drule p12_of_pa >> arw[])
(form_goal
“!A B AB p1:AB->A p2:AB->B. ispr(p1,p2) ==>
 !AB' p1':AB'->A p2':AB'->B. ispr(p1',p2') ==>
 isiso(pa(p1',p2',p1,p2))”)



val exp_ex' = proved_th $
e0
(rpt strip_tac >> assume_tac exp_ex >>
 first_x_assum (qspecl_then ["A","B"] strip_assume_tac) >>
 qexists_tac "A2B" >> rpt strip_tac >>
 drule exp_ispr >> 
 rev_drule pa_iso >> first_x_assum drule >>
 qexists_tac "ev o pa(p1, p2, p1', p2')" >>
 fs[isexp_def] >> rpt strip_tac >>
 first_x_assum drule >>
 first_x_assum (qspecl_then ["f"] assume_tac) >>
 pop_assum strip_assume_tac >>
 qexists_tac "h0" >> 
 rw[o_assoc] >>
 qby_tac 
 ‘!h:X -> A2B.
  pa(p1, p2, p1'', h o p2'') = 
  pa(p1, p2, p1', p2') o pa(p1', p2', p1'', h o p2'')’ >--
 (strip_tac >> 
  qpick_x_assum ‘ispr(p1,p2)’ assume_tac >>
  drule to_p_eq >> first_x_assum irule >>
  drule p12_of_pa >> arw[GSYM o_assoc] >>
  rev_drule p12_of_pa >> arw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[]
 )
(form_goal
“!A B.?A2B.
 !efs p1:efs ->A p2:efs -> A2B. 
 ispr(p1,p2) ==> ?ev:efs ->B. isexp(p1,p2,ev)”)



val Exp_def =  ex2fsym "Exp" ["A","B"] (iffRL $ eqT_intro $ spec_all exp_ex')
                        |> C mp (trueI []) |> gen_all

val Ev_ex = proved_th $
e0
(rpt strip_tac >> assume_tac pi2_def >>
 first_x_assum (qspecl_then ["A","Exp(A,B)"] assume_tac) >>
 drule Exp_def >> arw[])
(form_goal
“!A B.?ev: A * Exp(A,B) -> B.
 isexp(π1(A,Exp(A,B)),π2(A,Exp(A,B)),ev)”)

val isexp_th = proved_th $
e0
cheat
(form_goal
“!A B A2B efs p1:efs->A p2:efs-> A2B ev:efs -> B.
 isexp(p1,p2,ev) <=> 
 ispr(p1,p2) & 
 !X AX p1':AX->A p2':AX->X.ispr(p1',p2') ==>
 !f:AX->B.?h0:X-> A2B. !h. ev o pa(p1,p2,p1',h o p2') = f <=> h = h0”)

val Ev_def =  ex2fsym "Ev" ["A","B"] (iffRL $ eqT_intro $ spec_all Ev_ex)
                      |> C mp (trueI []) |> gen_all

val pa2Pa = proved_th $
e0
(rpt strip_tac >> irule  $ iffLR Pa_def >>
 assume_tac pi2_def >> 
 first_x_assum (qspecl_then ["A","B"] assume_tac) >>
 drule p12_of_pa >> arw[]
 )
(form_goal
“!A B X f:X->A g:X->B.pa(π1(A,B),π2(A,B),f,g) = Pa(f,g)”)

val Tp_ex = proved_th $
e0
(rpt strip_tac >> assume_tac Ev_def >>
 fs[isexp_def] >> 
 first_x_assum (qspecl_then ["A","B"] assume_tac) >>
 pop_assum strip_assume_tac >>
 assume_tac pi2_def >> 
 first_x_assum (qspecl_then ["A","X"] assume_tac) >>
 first_x_assum drule >>
 first_x_assum (qspecl_then ["f"] assume_tac) >>
 qby_tac 
 ‘!h:X->Exp(A,B). 
  pa(π1(A, Exp(A, B)), π2(A, Exp(A, B)), π1(A, X), h o
                    π2(A, X)) =
  Pa(π1(A, X), h o π2(A, X))’ >-- rw[pa2Pa] >>
 fs[] >> qexists_tac "h0" >> rw[]
 )
(form_goal
“!A B X f: A * X -> B. ?fBar0:X-> Exp(A,B).!fBar.
 Ev(A,B) o Pa(π1(A,X),fBar o π2(A,X)) = f <=> fBar = fBar0”)

val Tp_def =  ex2fsym "Tp" ["f"] (iffRL $ eqT_intro $ spec_all Tp_ex)
                      |> C mp (trueI []) |> gen_all



val const2_def = copr_ex |> allE one |> allE one |> eqT_intro
                      |> iffRL |> ex2fsym "2" [] |> C mp (trueI [])

val two = mk_fun "2" []

val FALSE_def = ex2fsym "FALSE" [] (iffRL $ eqT_intro $ spec_all const2_def)
                       |> C mp (trueI []) |> gen_all


val TRUE_def = ex2fsym "TRUE" [] (iffRL $ eqT_intro $ spec_all FALSE_def)
                       |> C mp (trueI []) |> gen_all

(*TODO: Char is_pb

or the alternative way of defining char


as below, or should add ismono(a) ==> ?Char? *)

val Char_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac "char(FALSE,TRUE,a)" >> rw[])
(form_goal
“!A X a:A->X.
 ?ch. char(FALSE,TRUE,a) = ch”)

val Char_def = ex2fsym "Char" ["a"]
(iffRL $ eqT_intro $ spec_all Char_ex) |> C mp (trueI []) |> gen_all

val char_ispb = 
    char_is_pb |> strip_all_and_imp 
               |> gen_disch_all |> gen_all



val Char_property = proved_th $
e0
(rpt strip_tac >> 
     assume_tac TRUE_def >>
     drule char_ispb >>  
 first_x_assum drule >> fs[Char_def,To1_def]
 )
(form_goal
“!A X a:A->X. ismono(a) ==>
 ispb(Char(a),TRUE,a,To1(A))”)




val CONJ_ex = proved_th $
e0
(assume_tac TRUE_def >> drule conj_ex >>
 first_x_assum
  (qspecl_then ["2 * 2","π1(2,2)","π2(2,2)"] assume_tac) >>
 assume_tac pi2_def >> 
 first_x_assum (qspecl_then ["2","2"] assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac "conj" >> fs[pa2Pa])
(form_goal 
“?CJ.!pred1 pred2.CJ o Pa(pred1,pred2) = TRUE <=> 
 pred1 = TRUE & pred2 = TRUE”)

val CONJ_def =  CONJ_ex |> eqT_intro
                        |> iffRL |> ex2fsym "CONJ" [] |> C mp (trueI [])

val CONJ = mk_fun "CONJ" []


val DISJ_ex = proved_th $
e0
(assume_tac TRUE_def >> drule or_ex >>
 first_x_assum
  (qspecl_then ["2 * 2","π1(2,2)","π2(2,2)"] assume_tac) >>
 assume_tac pi2_def >> 
 first_x_assum (qspecl_then ["2","2"] assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac "or" >> fs[pa2Pa])
(form_goal 
“?DJ.!pred1 pred2.DJ o Pa(pred1,pred2) = TRUE <=> 
 pred1 = TRUE | pred2 = TRUE”)

val DISJ_def =  DISJ_ex |> eqT_intro
                        |> iffRL |> ex2fsym "DISJ" [] |> C mp (trueI [])

val DISJ = mk_fun "DISJ" []


val IMP_ex = proved_th $
e0
(assume_tac TRUE_def >> drule imp_ex >>
 first_x_assum
  (qspecl_then ["2 * 2","π1(2,2)","π2(2,2)"] assume_tac) >>
 assume_tac pi2_def >> 
 first_x_assum (qspecl_then ["2","2"] assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac "imp" >> fs[pa2Pa])
(form_goal 
“?IP.!pred1 pred2.IP o Pa(pred1,pred2) = TRUE <=> 
 (pred1 = TRUE ==> pred2 = TRUE)”)

val IMP_def =  IMP_ex |> eqT_intro
                      |> iffRL |> ex2fsym "IMP" [] |> C mp (trueI [])

val IMP = mk_fun "IMP" []


val IFF_ex = proved_th $
e0
(assume_tac TRUE_def >> drule iff_ex >>
 first_x_assum
  (qspecl_then ["2 * 2","π1(2,2)","π2(2,2)"] assume_tac) >>
 assume_tac pi2_def >> 
 first_x_assum (qspecl_then ["2","2"] assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac "iff" >> fs[pa2Pa])
(form_goal 
“?IF.!pred1 pred2.IF o Pa(pred1,pred2) = TRUE <=> 
 (pred1 = TRUE <=> pred2 = TRUE)”)

val IFF_def =  IFF_ex |> eqT_intro
                      |> iffRL |> ex2fsym "IFF" [] |> C mp (trueI [])

val IFF = mk_fun "IFF" []


val NEG_ex = proved_th $
e0
(assume_tac TRUE_def >> drule neg_ex >> 
 pop_assum strip_assume_tac >>
 qexists_tac "neg" >> fs[pa2Pa])
(form_goal 
“?NOT.!pred.NOT o pred = TRUE <=> pred = FALSE”)

val NEG_def =  NEG_ex |> eqT_intro
                      |> iffRL |> ex2fsym "NEG" [] |> C mp (trueI [])

val NEG = mk_fun "NEG" []

val tp2Tp = proved_th $
e0
(rpt strip_tac >> 
 assume_tac Ev_def >> 
 first_x_assum (qspecl_then ["A","B"] assume_tac) >>
 sym_tac >> drule is_tp >> 
 assume_tac pi2_def >>
 first_x_assum (qspecl_then ["A","X"] assume_tac) >>
 first_x_assum drule >>
 first_x_assum irule >> 
 assume_tac Tp_def >>
 first_x_assum 
  (qspecl_then ["A","B","X","f","Tp(f)"] assume_tac) >>
 fs[] >> arw[pa2Pa])
(form_goal
“!A B X f:A * X -> B.
 tp(π1(A,Exp(A,B)),π2(A,Exp(A,B)),Ev(A,B),
    π1(A,X),π2(A,X),f) = Tp(f)”)

val Ex_ex = proved_th $
e0
(assume_tac TRUE_def >> drule Exq_ex >> 
 assume_tac Ev_def >> strip_tac >>
 first_x_assum (qspecl_then ["X","2"] assume_tac) >>
 first_x_assum drule >> 
 first_x_assum strip_assume_tac >>
 qexists_tac "Exq" >> 
 assume_tac pi2_def >> rpt strip_tac >> 
 first_x_assum (qspecl_then ["X","Y"] assume_tac) >>
 first_x_assum drule >> 
 fs[pa2Pa] >> fs[tp2Tp])
(form_goal
“!X.?Ex. !Y pxy:X * Y -> 2 y:1-> Y. Ex o Tp(pxy) o y = TRUE <=>
 ?x:1->X. pxy o Pa(x,y) = TRUE”)

val Ex_def =  Ex_ex |> spec_all |> eqT_intro
                    |> iffRL |> ex2fsym "Ex" ["X"] |> C mp (trueI []) |> gen_all

val All_ex = proved_th $
e0
(assume_tac TRUE_def >> drule Uq_ex >> 
 assume_tac Ev_def >> strip_tac >>
 first_x_assum (qspecl_then ["X","2"] assume_tac) >>
 first_x_assum drule >> 
 first_x_assum strip_assume_tac >>
 qexists_tac "Uq" >> 
 assume_tac pi2_def >> rpt strip_tac >> 
 first_x_assum (qspecl_then ["X","Y"] assume_tac) >>
 first_x_assum drule >> 
 fs[pa2Pa] >> fs[tp2Tp])
(form_goal
“!X.?All. !Y pxy:X * Y -> 2 y:1-> Y. All o Tp(pxy) o y = TRUE <=>
 !x:1->X. pxy o Pa(x,y) = TRUE”)

val All_def =  All_ex |> spec_all |> eqT_intro
                      |> iffRL |> ex2fsym "All" ["X"] |> C mp (trueI []) |> gen_all

val Diag_ex = proved_th $
e0
(strip_tac >> qexists_tac "Pa(id(X),id(X))" >> rw[])
(form_goal
“!X.?dX:X->X * X. Pa(id(X),id(X)) = dX”)

val Diag_def = Diag_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "Diag" ["X"]
                       |> C mp (trueI []) |> gen_all


(*AQ: should abbrevation like this True_ex use the same schemata as well?*)

val To1_ex = proved_th $
e0
(strip_tac >> qexists_tac "to1(X,1)" >> rw[])
(form_goal
“!X.?to1X:X->1. to1(X,1) = to1X”)






(*current version of ex2fsym cannot produce To1,except for as this...*)
val To1_def = To1_ex |> spec_all |> eqT_intro 
                     |> iffRL |> ex2fsym "To1" ["X"] |> C mp (trueI []) |> gen_all


val True_ex = proved_th $
e0
(strip_tac >> qexists_tac "TRUE o To1(X)" >> rw[])
(form_goal
“!X. ?tX:X->2.TRUE o To1(X) = tX”)

val True_def = True_ex |> spec_all |> eqT_intro 
                       |> iffRL |> ex2fsym "True" ["X"] |> C mp (trueI []) |> gen_all

val False_ex = proved_th $
e0
(strip_tac >> qexists_tac "FALSE o To1(X)" >> rw[])
(form_goal
“!X. ?fX:X->2.FALSE o To1(X) = fX”)

val False_def = False_ex |> spec_all |> eqT_intro 
                         |> iffRL |> ex2fsym "False" ["X"] |> C mp (trueI []) |> gen_all




val Eq_ex = proved_th $
e0
(strip_tac >> qexists_tac "Char(Diag(X))" >> rw[])
(form_goal “!X.?eqX:X * X -> 2. Char(Diag(X)) = eqX”)


val Eq_def = Eq_ex |> spec_all |> eqT_intro
                   |> iffRL |> ex2fsym "Eq" ["X"]
                   |> C mp (trueI []) |> gen_all

val Pa_distr = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["A","A"] assume_tac pi2_def >>
 drule distr_to_pa >> fs[pa2Pa])
(form_goal
“!A X a1:X ->A a2:X->A X0 x:X0->X. Pa(a1,a2) o x = 
Pa(a1 o x,a2 o x) ”)

val pi1_of_Pa = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["A","B"] assume_tac pi2_def >>
 drule p1_of_pa >> fs[pa2Pa])
(form_goal
 “!A B X f:X->A g:X->B. π1(A,B) o Pa(f,g) = f”)



val pi2_of_Pa = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["A","B"] assume_tac pi2_def >>
 drule p2_of_pa >> fs[pa2Pa])
(form_goal
 “!A B X f:X->A g:X->B. π2(A,B) o Pa(f,g) = g”)

val pi12_of_Pa = 
conjI (spec_all pi1_of_Pa) (spec_all pi2_of_Pa) |> gen_all

val True2TRUE = proved_th $
e0
(rpt strip_tac >> rw[GSYM True_def,o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR])
(form_goal
“!X x:1->X. True(X) o x = TRUE”)

val conj_property = proved_th $
e0
(rpt strip_tac >> dimp_tac (* 2 *) >--
 (strip_tac >> strip_tac (* 2 *) >>
  (irule fun_ext >> strip_tac >>
   qby_tac ‘CONJ o Pa(p1, p2) o a= True(X) o a’
   >-- arw[GSYM o_assoc] >>
   qspecl_then ["π1(2,2) o Pa(p1,p2) o a","π2(2,2) o Pa(p1,p2) o a"] assume_tac CONJ_def >>
   fs[Pa_distr,pi12_of_Pa] >> fs[True2TRUE])) >>
 strip_tac >> arw[] >> irule fun_ext >> strip_tac  >>
 rw[o_assoc,Pa_distr,True2TRUE] >> rw[CONJ_def])
(form_goal
“!X p1:X ->2 p2:X->2. 
 CONJ o Pa(p1,p2) = True(X) <=> p1 = True(X) & p2 = True(X)”)



val Diag_ismono = proved_th $
e0
(strip_tac >> qspecl_then ["A","A"] assume_tac pi2_def >>
 drule diag_is_mono >> fs[GSYM Diag_def,pa2Pa])
(form_goal
“!A. ismono(Diag(A))”)

val Eq_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM Eq_def] >>
 assume_tac TRUE_def >> drule char_diag >>
 qspecl_then ["X","X"] assume_tac pi2_def >>
 first_x_assum drule >> fs[Char_def,pa2Pa,Diag_def] >>
 dimp_tac (* 2 *) >> strip_tac (* 2 *) >--
 (irule fun_ext >> strip_tac >> arw[True2TRUE,o_assoc,Pa_distr]) >>
 irule fun_ext >> strip_tac >>
 first_x_assum (irule o iffLR) >>
 qspecl_then ["X","A","f","g","1","a"] assume_tac $
 GSYM Pa_distr >> arw[GSYM o_assoc,True2TRUE] )
(form_goal
“!X A f:A->X g:A->X. 
f = g <=> Eq(X) o Pa(f,g) = True(A)”)

val Sing_ex = proved_th $
e0
(strip_tac >> qexists_tac "Tp(Eq(X))" >> rw[])
(form_goal
“!X. ?sX:X-> Exp(X,2). Tp(Eq(X)) = sX”)

val Sing_def = Sing_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "Sing" ["X"]
                       |> C mp (trueI []) |> gen_all

val pi31_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac "π1(A,B * C)" >> rw[])
(form_goal
 “!A B C. ?pi31: A * B * C ->A. π1(A,B * C) = pi31”)

val pi31_def = pi31_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "π31" ["A","B","C"]
                       |> C mp (trueI []) |> gen_all

val pi32_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac "π1(B,C) o π2(A,B * C)" >> rw[])
(form_goal
 “!A B C. ?pi32: A * B * C ->B.π1(B,C) o π2(A,B * C) = pi32”)

val pi32_def = pi32_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "π32" ["A","B","C"]
                       |> C mp (trueI []) |> gen_all

val pi33_ex = proved_th $
e0
(rpt strip_tac >> qexists_tac "π2(B,C) o π2(A,B * C)" >> rw[])
(form_goal
 “!A B C. ?pi33: A * B * C ->C.π2(B,C) o π2(A,B * C) = pi33”)

val pi33_def = pi33_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "π33" ["A","B","C"]
                       |> C mp (trueI []) |> gen_all

fun qex_tac tq = qexists_tac $ q2str tq

val Insert_ex = proved_th $
e0
(strip_tac >> qex_tac
 ‘Tp(DISJ o 
    Pa(Eq(X) o Pa(π31(X,X,Exp(X,2)),π32(X,X,Exp(X,2))),
       Ev(X,2) o Pa(π31(X,X,Exp(X,2)),π33(X,X,Exp(X,2)))))’
 >> rw[])
(form_goal
 “!X.?Ins: X * Exp(X,2) -> Exp(X,2). 
 Tp(DISJ o 
    Pa(Eq(X) o Pa(π31(X,X,Exp(X,2)),π32(X,X,Exp(X,2))),
       Ev(X,2) o Pa(π31(X,X,Exp(X,2)),π33(X,X,Exp(X,2))))) = Ins ”)


val Insert_def = 
    Insert_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Insert" ["X"]
              |> C mp (trueI []) |> gen_all

val Ins_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Insert(X) o Pa(x,s0)’ >> rw[])
(form_goal
“!A X x:A->X s0:A->Exp(X,2).?f. Insert(X) o Pa(x,s0) = f”)

val Ev_of_Tp = proved_th $
e0
(rpt strip_tac >>
 assume_tac (aspec [rastt "f:A * X ->B",rastt "Tp(f:A * X ->B)"] Tp_def) >> fs[])
(form_goal
 “!A B X f:A * X ->B. 
  Ev(A,B) o Pa(π1(A,X), Tp(f) o π2(A,X)) = f”)

val to_Pr_components = proved_th $
e0
(rpt strip_tac >> assume_tac $ spec_all pi2_def >>
 drule to_p_components >> fs[pa2Pa])
(form_goal
 “!A B X f: X -> A * B. Pa(π1(A,B) o f, π2(A,B) o f) = f”)

val to_Pr_eq = proved_th $
e0
()
(form_goal
 “A B X f:X-> A * B g:X -> A * B.
  π1(A,B) o f = π1(A,B) o g & π2(A,B) o f = π2(A,B) o g ==>
 f = g”)

val Ev_of_Tp_el = proved_th $
e0
(rpt strip_tac >>
 assume_tac Ev_of_Tp >> 
 qby_tac ‘Ev(A, B) o Pa(a, Tp(f) o x) = 
 Ev(A, B) o Pa(π1(A, X), Tp(f) o π2(A, X)) o Pa(a,x)’
 assume_tac (aspec [rastt "f:A * X ->B",rastt "Tp(f:A * X ->B)"] Tp_def) >> fs[])
(form_goal
 “!A B X f:A * X ->B P a:P->A x: P ->X. 
  Ev(A,B) o Pa(a, Tp(f) o x) = f o Pa(a,x)”)


val Ins_def = 
    Ins_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Ins" ["x","s0"]
           |> C mp (trueI []) |> gen_all

val Ins_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM Ins_def,GSYM Insert_def,Ev_of_Tp])
(form_goal
 “!X x0:1->X s0:1->Exp(X,2).
  !x:1->X. Ev(X,2) o Pa(x,Ins(x0,s0)) = TRUE <=> 
  (x = x0 | Ev(X,2) o Pa(x,s0) = TRUE)”)


(*use abbreved long map instead?

if so, may have equalities Po4(A,B,C,D) = Po(A,Po(B,Po(C,D)))

How can I allow writing multiple product and do not get it messed up?
*)

val Pr3_ex = proved_th $
e0
cheat
(form_goal
“!A B C. ?ABC pA:ABC->A pB:ABC->B pC:ABC->C.
 !X f:X->A g:X->B h:X->C. ?fgh:X->ABC. 
 !fgh':X->ABC. pA o fgh' = f & pB o fgh' = g & pC o fgh' = h <=> fgh' = fgh”)


val Po3_def = Pr3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Po3" ["A","B","C"]
              |> C mp (trueI []) |> gen_all

val Pr1_def = Po3_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pr1" ["A","B","C"]
              |> C mp (trueI []) |> gen_all

val Pr2_def = Pr1_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pr2" ["A","B","C"]
              |> C mp (trueI []) |> gen_all

val Pr3_def = Pr2_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pr3" ["A","B","C"]
              |> C mp (trueI []) |> gen_all

val Pa3_def = Pr3_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa3" ["f","g","h"]
              |> C mp (trueI []) |> gen_all


val Pr4_ex = proved_th $
e0
cheat
(form_goal
“!A B C D.?ABCD pA:ABCD->A pB:ABCD->B pC:ABCD->C pD:ABCD->D.
 !X f:X->A g:X->B h:X->C k:X->D. ?fghk:X->ABCD. 
 !fghk':X->ABCD. pA o fghk' = f & pB o fghk' = g & 
                 pC o fghk' = h & pD o fghk' = k <=> 
                 fghk' = fghk”)

val Po4_def = Pr4_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Po4" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val Pi1_def = Po4_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Π1" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val Pi2_def = Pi1_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Π2" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val Pi3_def = Pi2_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Π3" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val Pi4_def = Pi3_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Π4" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val Pa4_def = Pi4_def |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa4" ["f","g","h","k"]
              |> C mp (trueI []) |> gen_all


(*TODO: using 2 * 2 * 2 and pr3 as example to see how does triple product work for triple conj

and subscript... usual number takes to much space
*)

(*AQ: how to set up abbrevs as Pow(X) = Exp(X,2), this is equality on object*)

val fst_conjunct = 
rastt $ q2str 
‘Ev(Exp(X,2),2) o Pa(Π2(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),Π4(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)) )’


val Insert_ex' = proved_th $
e0
cheat
(form_goal
“!(x0 : A -> X)  (s0 : A -> Exp(X, 2)).
        ?s1:A-> Exp(X,2).
          !(x : A -> X).
            Ev(X, 2) o Pa(x, s1) = True(A) <=>
            x = x0 | Ev(X, 2) o Pa(x, s0) = True(A)”)

val Insert_def = 
    Insert_ex' |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Insert" ["x0","s0"]
              |> C mp (trueI []) |> gen_all

val snd_conjunct = 
rastt $ q2str
‘Eq(Exp(X,2)) o Pa(Π3(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),
 Insert(Π1(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),
        Π2(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2))))’

(*tool of write Pa ... as 
something like π_2,4 of 4 objects
*)

val trd_conjunct = 
rastt $ q2str
‘NEG o Ev(X,2) o Pa(Π1(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),Π2(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)))’

fun mk_o a1 a2 = mk_fun "o" [a1,a2]

fun Pa f g = mk_fun "Pa" [f,g]

val from4_pred0 = 
mk_o CONJ $
 Pa trd_conjunct (mk_o CONJ (Pa fst_conjunct snd_conjunct))

(*prove there exists a iso from prod to p4,may turn it into function symbol, but can we avoid it and just take p4 to be the desired product?*)


val Bridge3_ex  = proved_th $
e0
cheat
(form_goal
“!X.?f:X * (Exp(X,2) * Exp(Exp(X,2),2)) ->
    Po3(X,Exp(X,2),Exp(Exp(X,2),2)).
 isiso(f)”)

val Bridge3_def = 
Bridge3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Bridge3" ["X"]
              |> C mp (trueI []) |> gen_all


val Bridge4_ex  = proved_th $
e0
cheat
(form_goal
“!X.?f:X * (Exp(X,2) * (Exp(X,2) * Exp(Exp(X,2),2))) ->
    Po4(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)).
 isiso(f)”)

val Bridge4_def = 
Bridge4_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Bridge4" ["X"]
              |> C mp (trueI []) |> gen_all

val from4_pred0 = 
mk_o CONJ $
 Pa trd_conjunct (mk_o CONJ (Pa fst_conjunct snd_conjunct))

(*AQ: it is already too ugly*)

val from4_pred = 
mk_o from4_pred0 (rastt "Bridge4(X)")

(*sort of it is 

X * Exp(X, 2) * Exp(X, 2) * Exp(Exp(X, 2), 2) -> 2:*)

fun Tp f = mk_fun "Tp" [f]

fun Ex X = mk_fun "Ex" [X]

val Ex_x_from4_pred = 
 mk_o (Ex (mk_ob "X")) (Tp from4_pred)
 
val Ex_s0_Ex_x_from4_pred = 
mk_o (rastt "Ex(Exp(X,2))") (Tp Ex_x_from4_pred)

val required_map2 = Tp Ex_s0_Ex_x_from4_pred

val Empty_ex = proved_th $
e0
cheat
(form_goal
“!X.?ept:1->Exp(X,2). Tp(False(X) o π1(X,1))= ept”)

val Empty_def = 
    Empty_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Empty" ["X"]
             |> C mp (trueI []) |> gen_all

val required_map1 =
Tp (rastt $ q2str
‘Eq(Exp(X,2)) o Pa(id(Exp(X,2)),Empty(X) o To1(Exp(X,2))) o 
 π1(Exp(X,2),1)’)

fun Nind x0 t = mk_fun "Nind" [x0,t]

val card0 = Nind required_map1 required_map2

fun Ev e f = mk_fun "Ev" [e,f]

val hasCard =
mk_o (rastt "Ev(Exp(X,2),2)") 
(Pa (rastt "π1(Exp(X,2),N)")
 (mk_o card0 (rastt "π2(Exp(X,2),N)")))

(*has sort Exp(X, 2) * N -> 2: sort*)

(*Recall 
 it = Empty(X): term
> sort_of it;
val it = 1 -> Exp(X, 2): sort
*)

val contain_empty = 
mk_o (rastt "Ev(Exp(X,2),2)") $
Pa
(rastt "Empty(X) o To1(Exp(Exp(X,2),2))")
(rastt "id(Exp(Exp(X,2),2))")


val longpred_ant = rastt "Ev(Exp(X,2),2)"
(*mk_o (rastt "Ev(Exp(X,2),2)")
(Pa (rastt "Pr2(X,Exp(X,2),Exp(Exp(X,2),2))")
 (rastt "Pr3(X,Exp(X,2),Exp(Exp(X,2),2))"))
*)

val longpred_conc = 
rastt $ q2str
‘All(X) o Tp(Ev(Exp(X,2),2) o 
 Pa(Insert(Pr1(X,Exp(X,2),Exp(Exp(X,2),2)),
           Pr2(X,Exp(X,2),Exp(Exp(X,2),2))),
Pr3(X,Exp(X,2),Exp(Exp(X,2),2))) o Bridge3(X))’

val longpred = 
mk_o (rastt "All(Exp(X,2))") $ Tp (mk_o IMP (Pa longpred_ant longpred_conc))

val bigset = Tp $
mk_o longpred (rastt "π1(Exp(Exp(X, 2), 2),1)")
(*bigset is the thing to be taken biginter*)

val BIGINTER_ex = proved_th $
e0
cheat
(form_goal
“!X.?biX. ?reorder.
 Tp (All(Exp(X,2)) o Tp(IMP o Pa
 (Ev(Exp(X,2),2) o 
  Pa(Pr2(X,Exp(X,2),Exp(Exp(X,2),2)),
     Pr3(X,Exp(X,2),Exp(Exp(X,2),2))),
  Ev(X,2) o 
  Pa(Pr1(X,Exp(X,2),Exp(Exp(X,2),2)),
     Pr2(X,Exp(X,2),Exp(Exp(X,2),2)))) o Bridge3(X) o 
  reorder:Exp(X, 2) * X * Exp(Exp(X, 2), 2) -> 
  X * Exp(X, 2) * Exp(Exp(X, 2), 2))) = biX ”)

val BIGINTER_def = 
BIGINTER_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "BIGINTER" ["X"] 
            |> C mp (trueI []) |> gen_all

val finites = 
mk_o (rastt "BIGINTER(Exp(X,2))") bigset

val isFinite = 
mk_o (mk_o (rastt "Ev(Exp(X,2),2)") 
(Pa (rastt "π1(Exp(X,2),1)") (mk_o finites (rastt "π2(Exp(X,2),1)")))) (rastt "Pa(id(Exp(X,2)),To1(Exp(X,2)))")


(*AQ list:

1.SLOW thms. Thm5_mono Thm6_g_ev_lemma pb_reorder
char_diag equality_ind double_ind triple_ind 
cancel_sub_pred iff_ex

Po3(A,B,C) = A * B * C 

(A * (B * C))

π2(B,C) o π2(A, B * C)  = 

π3(A,B,C)



! A B C. ? ABC pA pB pC. 

pred :X -> 2. 

mono a: A >--> X.  char(a) = pred


ex 2 fsym 

“!X pred:X->2. ?A a:A->X. Char(a) = pred”




2.tools of writing 3,4ary products, without having equality of objects. tools like π_2,4, to take the 2th and 4th component of a product and send it to a binary predicate.

(and have notfigured out the way of doing subscripts)

better to have such thing for definition of group, otherwise very nested projection will be required, see the current definition.

3.ex2fsym cannot form things like taking the mono corresponding the char map. Allow partial application in some sense? see wCard

4. tokenizer function ugly, cannot have something like scan ident, because otherwise it will think "*\ )\ (\" is 
one symbol.  

5.write !x.1-> Grouptype as wf formula, where Grouptype is as discussed before, without have equality Grouptype = G * ...

Po(A,B,C)

val Grouptype = mk_Po G ...

ex 2 fsym 

G * ... = Grouptype(G)

"!x:1->Grouptype(X). " x : 1-> G * G ...



Similarly. when the second argument of Exp is 2, say, Exp X 2, write Pow(X)

6.treatment of Reorder map? 


A * C * B -> A * B -> 2


Pa(π1, π2)


7.current version of ex2fsym cannot produce To1,except for as this above.




8.How to allow writing 1,2,3,4,5, instead of SUC SUC SUC...
express "group of order 6"

parse 1 = BIT .....
parse 2 = BIT ....


parse n = 
case n of 0 => BIT ...
 SUC n0 => BIT ...





*)

val BIGINTER0 = rastt $ q2str
‘IMP o Pa
 (Ev(Exp(X,2),2) o 
  Pa(Pr2(X,Exp(X,2),Exp(Exp(X,2),2)),
     Pr3(X,Exp(X,2),Exp(Exp(X,2),2))),
  Ev(X,2) o 
  Pa(Pr1(X,Exp(X,2),Exp(Exp(X,2),2)),
     Pr2(X,Exp(X,2),Exp(Exp(X,2),2)))) o Bridge3(X) o 
  reorder:Exp(X, 2) * X * Exp(Exp(X, 2), 2) -> 
  X * Exp(X, 2) * Exp(Exp(X, 2), 2)’

val BIGINTER = Tp 
(mk_o (rastt "All(Exp(X,2))") (Tp BIGINTER0))

(*wChar 
val ofChar_ex = proved_th $
e0
cheat
(form_goal
“!X c:X->2.?A a:A->X. ismono(a) & Char(a) = c”)
*)

(*cannot define set of char, since need to define its domain first*)



(*QA: the reorder map...*)




(*choice function cannot choose the
!A B.
        ?efs (p1 : efs# -> A#)  (p2 : efs# -> Exp(A#, B#))
        (ev : efs# -> B#). isexp(p1#, p2#, ev#): thm

to be A * (B ^ A)
 *)


(*
Exq(X) : 2 ^ X -> 2

!P: X * Y -> 2. tp(P): Y -> 2^X -> Exq(X)

!y. ?x. P o <x,y> = true <=> 
 Exq o tp(P) o y = true


*)


(*

eg pb_ex

it should work for 

!X Z (f : X# -> Z#)  Y (g : Y# -> Z#).
        ?P (p : P# -> X#)  (q : P# -> Y#). ispb(f#, g#, p#, q#): thm

if only need to work as above, then easy, but in practice also want it wo work for 

!X Z Y (f : X# -> Z#) (g : Y# -> Z#).
        ?P (p : P# -> X#)  (q : P# -> Y#). ispb(f#, g#, p#, q#): thm

X Z Y (f : X# -> Z#) (g : Y# -> Z#)

 [(f : X# -> Z#) (g : Y# -> Z#)]

[f':X0 -> Z0 g':Y0 -> Z0]


π1

or
!X Z (f : X# -> Z#) (g : Y# -> Z#).
        ?P (p : P# -> X#)  (q : P# -> Y#). ispb(f#, g#, p#, q#): thm

or

!Z (f : X# -> Z#)  Y (g : Y# -> Z#).
        ?P (p : P# -> X#)  (q : P# -> Y#). ispb(f#, g#, p#, q#): thm
...

val sspec tl th = 
    let val (b,qvs) = strip_forall (concl th)
        val qars = List.filter is_ar_ss qvs

*)







val coPosym_def = ex2fsym "+" ["A","B"] (iffRL $ eqT_intro $ spec_all copr_ex)
                          |> C mp (trueI []) |> gen_all

val tau1_def = ex2fsym "τ1" ["A","B"] (iffRL $ eqT_intro $ spec_all coPosym_def)
                        |> C mp (trueI []) |> gen_all

val tau2_def = ex2fsym "τ2" ["A","B"] (iffRL $ eqT_intro $ spec_all tau1_def)
                        |> C mp (trueI []) |> gen_all

(*maybe nice to have a tool that realise which component, and just assign maps to components, how can I do this?*)



fun check_wffv fvs = 
    case fvs of 
        [] => true
      | h :: t => if ill_formed_fv h then
                      raise ERR ("ill-formed free variable",[snd h],[var h],[])
                  else check_wffv t

fun wffv_ok f = check_wffv (HOLset.listItems (fvf f))
  

fun new_ax f = 
    let val _ = wffv_ok f orelse
                raise ERR ("formula contains ill-formed free variable(s)",[],[],[])
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm essps [] f
    end

val ADD_ex = proved_th $
e0
cheat
(form_goal
“?ADD: N * N ->N. 
  ADD o Pa(id(N), ZERO o To1(N)) = id(N) & 
  ADD o Pa(π1(N,N), s o π2(N,N)) = 
  s o π2(N * N,N) o Pa(id(N * N),ADD)”)

val ADD_def = ex2fsym "ADD" [] (iffRL $ eqT_intro $ spec_all ADD_ex)
                        |> C mp (trueI []) |> gen_all


val pred_subset_ex = proved_th $
e0
cheat
(form_goal
“!X pred:X->2.?A ss:A ->X.
 (!x:1->X. pred o x = TRUE <=> ?x0:1->A. x = ss o x0)”)

val ZRel_subset_ex = 
    pred_subset_ex |> allE $ rastt "(N * N) * (N * N)"
                   |> allE $ rastt $ q2str
‘Eq(N) o Pa(ADD o 
     Pa(π1(N,N) o π1(N * N,N * N),
        π2(N,N) o π2(N * N,N * N)),
     ADD o 
     Pa(π2(N,N) o π1(N * N,N * N), 
        π1(N,N) o π2(N * N,N * N)))’

val ZRel_subset_def = ex2fsym "ZRel" [] (iffRL $ eqT_intro $ spec_all ZRel_subset_ex)
                        |> C mp (trueI []) |> gen_all

val ZRel_inc_def = 
ex2fsym "ZRinc" [] (iffRL $ eqT_intro $ spec_all ZRel_subset_def)
                        |> C mp (trueI []) |> gen_all

val intZ_ex = 
    coeq_ex |> allE $ rastt "ZRel" 
            |> allE $ rastt "N * N"
            |> allE $ rastt "π1(N * N, N * N) o ZRinc"
            |> allE $ rastt "π2(N * N, N * N) o ZRinc"

val intZ_def = ex2fsym "intZ" [] (iffRL $ eqT_intro $ spec_all intZ_ex)
                        |> C mp (trueI []) |> gen_all

val toZ_def = ex2fsym "toZ" [] (iffRL $ eqT_intro $ spec_all intZ_def)
                        |> C mp (trueI []) |> gen_all

fun Po A B = mk_fun "*" [A,B]

val _ = new_pred "isGrp" 
        [("G",ob_sort),("e",ar_sort one (mk_ob "G")),
         ("m",ar_sort (Po (mk_ob "G") (mk_ob "G")) 
                      (mk_ob "G")),
         ("i",ar_sort (mk_ob "G") (mk_ob "G"))]

(*

Exp(G,e,m,i,n,a) = a

2^G * G * (G^ (G * G)) * (G^ G)

type of groups

Exp(g:1->group type,n,a:group member) = a

Exp(G,e,m,i,z,a) = a

Exp(G,e,m,i,SUC n,a) = m o PROD(a,Exp(G,e,m,i,n,a) )

*)

val orefl_th = 
    let val f = “A == A”
    in mk_thm (fvf f) [] f
    end

val Grps_ex = proved_th $
e0
(strip_tac >> qexists_tac "Exp(G,2) * G * Exp(G * G,G) * Exp(G,G)" >> once_rw[orefl_th])
(form_goal
“!G. ?Grps. Exp(G,2) * G * Exp(G * G,G) * Exp(G,G) == Grps”)

val Grp_def = 
    ex2fsym "Grp" ["G"] (iffRL $ eqT_intro $ spec_all Grps_ex)
            |> C mp (trueI []) |> gen_all


(*TODO: bug Exp(G,2) * G * Exp(G * G,G) * Exp(G,G) = Grps is 
parsable*)



val isGrp_def = new_ax
“!G e m i.isGrp(G,e,m,i) <=> 
 m o Pa (m o π1(G * G,G),id(G) o π2(G * G,G)) = 
 m o Pa (id(G) o π1(G,G * G),m o π2(G,G * G)) o 
 Pa(π1(G,G) o π1(G * G,G),
      Pa(π1(G,G) o π1(G * G,G),π2(G * G,G))) &
 m o Pa(id(G),e o To1(G)) = id(G) & 
 m o Pa(e o To1(G),id(G)) = id(G) &
 m o Pa(id(G),i) = id(G) &
 m o Pa(i,id(G)) = id(G)”

val _ = new_pred "isAb" [("G",ob_sort),("e",ar_sort one (mk_ob "G")),
         ("m",ar_sort (Po (mk_ob "G") (mk_ob "G")) 
                      (mk_ob "G")),
         ("i",ar_sort (mk_ob "G") (mk_ob "G"))]

val _ = new_fun "swap" (ar_sort (Po (mk_ob "X") (mk_ob "X")) (Po (mk_ob "X") (mk_ob "X")),[("X",ob_sort)])


val isAb_def = new_ax
“!G e m i. isAb(G,e,m,i) <=> isGrp(G,e,m,i) &
 m = m o swap(G)”


val Add_ex = proved_th $
e0
cheat
(form_goal
“!n1:1->N n2:1->N. ?a. a = ADD o Pa(n1,n2)”)

val Add_def = 
    ex2fsym "Add" ["n1","n2"] (iffRL $ eqT_intro $ spec_all Add_ex)
            |> C mp (trueI []) |> gen_all

(*

!G. ?n. .... 

ex2fsym

FINITE({}) & 
!X. FINITE X ==> FINITE (X U {x}) 

2^X --> 1 + 1

ss = {} | ? ss0. FINITE ss0 /\ 

take the set of s

BIGINTER { s | s SUBSET 2^X /\ {} IN s /\ !e. a IN s ==> a UNION {e} IN s } (SUBSET of 2^X)

{ s | ({},0) IN s /\ !e a m. (a,m) IN s /\ e NOTIN a ==> (a UNION {e}, m + 1) IN s}

val _ = new_pred "Card" [X,s:A->X,("n",1->N)]

for every set X, take the empty subset of it.

card(s, SUC n) <=> ?e s0. s = s0 UNION {e} /\ card (s0, n) /\ e NOTIN s0

N  * 2 ^ X -> 2 

N -> 2 ^ (2 ^ X)

new_ax 
“Card(X,EMPTY(X),0) &
 !ss.Card(X,ss,n) & 
 ”




*)

(*Exp (G,e,m,i,int:1->Z,a:1->G) need a group to define,so take so many parameters, can hide some of them or other way to make it better? defined as

prove



!G e m i. isGrp(G,e,m,i) ==>
 ?EXP: N * G ->G. 
 EXP o PROD(z,g) = g & 
 EXP o PROD(SUC o n, g) = m o PROD(g,EXP o PROD(n,g))

and get fun sym

Exp(G,e,m,i,n,a) = a

2^G * G * (G^ (G * G)) * (G^ G)

type of groups

Exp(g:1->group type,n,a:group member) = a

Exp(G,e,m,i,z,a) = a

Exp(G,e,m,i,SUC n,a) = m o PROD(a,Exp(G,e,m,i,n,a) )

using UMP of N, define map N -> G ^ G and transpose to get EXP

parsing B^A as Exp A B? just treat it specially?
*)



(*enable the user to define infix, why is it tricky for parsing? *)



fun fl_diff fl1 fl2 = 
    case (fl1,fl2) of
        (h1::t1,_) => 
        if List.exists (fn f => eq_form(f,h1)) fl2 then fl_diff t1 fl2
        else h1 :: (fl_diff t1 fl2)
      | ([],_) => []



fun is_ar t = 
    case view_sort (sort_of t) of 
        vo => false | _ => true

fun is_ar_ss (n,s) = is_ar (var (n,s))


fun aspec tl th = 
    let val (b,vs) = strip_forall $ concl th
        val ars = List.filter is_ar_ss vs
        val env = match_tl essps (List.map var ars) tl emptyvd
        val tl' = List.map (inst_term env) (List.map var vs)
    in specl tl' th
    end



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
