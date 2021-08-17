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
 
val coeq_eqn = coeqind_def |> strip_all_and_imp
                    |> conjE2 |> iffRL |> strip_all_and_imp
                    |> rewr_rule [assume (rapf "x0 = coeqind(ce:B->cE, f:A->B, g, x:B->X)")] |> disch (rapf "x0 = coeqind(ce:B->cE, f:A->B, g, x:B->X)")
                    |> gen_all 
                    |> allE (rastt "coeqind(ce:B->cE, f:A->B, g, x:B->X)") 
                    |> C mp $ refl (rastt "coeqind(ce:B->cE, f:A->B, g, x:B->X)")
                    |> disch_all''
 





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



val ev_eq_eq = proved_th $
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
 qby_tac ‘copa(i1,i2,x1,x2) o i1 = x1 &copa(i1,i2,x1,x2) o i2 = x2’
 (*by_tac (rapf "copa(i1:1->oneone,i2:1->oneone,x1:1->X,x2) o i1 = x1 &copa(i1,i2,x1,x2) o i2 = x2")*) >-- (drule i12_of_copa >> arw_tac[]) >>
 pop_assum (assume_tac o GSYM) >> 
 rev_full_simp_tac[] >> (*suffices_tac (rapf "x1:1->X = x2") *)
 qsuff_tac ‘x1 = x2’
 >-- (arw_tac[]) >>
 qpick_x_assum ‘~x1 = x2’ (K all_tac)
 (*pick_x_assum (rapf "~x1:1->X = x2") (K all_tac)*) >> once_arw_tac[] >> rw_tac[] >>
 rw_tac[])
(rapg "!oneone i1:1 -> oneone i2:1 -> oneone. iscopr(i1,i2) ==> ~i1 = i2")

(*∀A B x. ¬(x∶one → (A + B) ∧ (∃x0 x0'. x0∶one → A ∧ x0'∶one → B ∧
                             i1 A B ∘ x0 = x ∧
                             i2 A B ∘ x0' = x))
*)

(* TODO:  i1_ne_i2|> spec_all |> undisch|> eqF_intro |> iffLR |> disch_all|> gen_all |> irule_canon
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
(*AQ: why is pb proof so slow*)
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

(*TODO: match_mp_bug  e o a1 = e o a2 ==> a1 = a2 ismono_property h is double bind to a1 and a2 because ismono_property is not in correct order!!!!!*)

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
 (*drule ismono_property >> *))
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
 suffices_tac (rapf "x1:1->X = x2") 
 >-- (arw_tac[] (*>> first_x_assum accept_tac*)) >>
 assume_tac const0_def >> drule from0_exists >> 
 first_assum (specl_then [one] strip_assume_tac) >> 
 suffices_tac (rapf "x1 o f':0->1 o f:1->0 = (x2:1->X) o f' o f") 
 >-- (assume_tac (one_to_one_id |> allE (rastt "f':0->1 o f:1->0")) >>
      arw_tac[idR]) >>
 suffices_tac (rapf "x1 o f':0->1 = (x2:1->X) o f'")
 >-- (strip_tac >> arw_tac[] >> arw_tac[GSYM o_assoc]) >>
 match_mp_tac from0_unique >> rw_tac[const0_def])
(rapg "~?f:1->0.T")

(*∀A. A≅ zero ⇒ ¬(∃x. x∶ one → A)*)

val iso_zero_no_mem = proved_th $
e0
(rw_tac[areiso_def] >> repeat strip_tac >> ccontra_tac 
 >> pop_assum strip_assume_tac >> 
 suffices_tac (rapf "?f:1->0.T")
 >-- (strip_tac >> contr_tac (zero_no_mem |> eqF_intro |> iffLR |> undisch)) >>
 exists_tac (rastt "(f:A->0) o (f':1->A)") >> rw_tac[])
(rapg "!A. areiso(A,0) ==> ~?f:1->A.T")

(*∀A B f. is_epi f /\ f∶ A → B ==> (∀b. b∶ one → B ⇒ ∃b0. b0∶ one → A ∧ f o b0 = b)*)


val no_epi_from_iso_zero = contrapos (no_epi_from_zero |> spec_all |> undisch) |> neg_neg_elim |> rewr_rule [GSYM iso_zero_is_zero] |> contrapos|> disch_all |> gen_all


(*maybe TODO:This one is messy, should consistently use one of the predicates*) 

val is_epi_surj = proved_th $
e0
(repeat strip_tac >>
 by_tac (rapf "~areiso(B,0)")
 >-- (by_tac (rapf "?(f : 1 -> B). T")
      >-- (exists_tac (rastt "b:1->B") >> rw_tac[]) >>
      ccontra_tac >> assume_tac (allE (rastt "B") iso_zero_no_mem) 
      >> last_assum drule >> full_simp_tac[]) >>
 by_tac (rapf "~areiso(A,0)")
 >-- (match_mp_tac (irule_canon no_epi_from_iso_zero) >> exists_tac (rastt "B") >>
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
(rapg "!oneone i1:1->oneone i2:1->oneone. iscopr(i1,i2) ==> ~copa(i1,i2,i1,i2) = copa(i1,i2,i2,i1)") 


(*∃X e1 e2. e1∶ X → X ∧ e2∶ X → X ∧ e1 ≠ e2*)

val distinct_endo_exists = proved_th $
e0
(assume_tac distinct_endo_2 >> x_choosel_then ["oneone","i1","i2"] assume_tac (copr_ex|> allE one |> allE one) >> first_x_assum drule >> 
exists_tac (rastt "oneone") >> 
exists_tac (rastt "copa(i1:1->oneone, i2:1->oneone, i1, i2)") >>
exists_tac (rastt "copa(i1:1->oneone, i2:1->oneone, i2, i1)") >>
first_x_assum accept_tac)
(rapg "?X e1:X->X e2. ~e1 = e2")

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
 >-- (match_mp_tac (irule_canon to_p_eq) >> exists_tac (rastt "X") >>
      exists_tac (rastt "X2Y") >> exists_tac' (rastt "p1:efs->X") >> 
      exists_tac' (rastt "p2:efs->X2Y") >> arw_tac[] >> repeat strip_tac (* 2 *) 
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
(rapg "!X Y X2Y efs ev p1 p2. isexp(p1:efs ->X,p2:efs->X2Y,ev:efs -> Y) ==> !X1 pX:X1->X pone:X1->1. ispr(pX,pone) ==>!x:1->X f:X->Y.ev o pa(p1,p2,x,tp (p1,p2,ev,pX,pone,f o pX)) = f o x")

(*last_x_assum (first_assum o mp_then Any mp_tac) rev_drule 
use mp_then, but a better style is to use spec first.

or jusr write a rev_drule FREEZE_THEN
*)
(*is_mono a ∧ a∶ A → X ∧ x∶ one → X ∧
 ¬(∃x0. x0∶ one → A ∧ a o x0 = x) ⇒ is_mono (copa a x)*)

(*TODO: a drule such that if !x.~ P(x) in assumption, then know p(a) is false,isnt it rw_canon?*)

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
          match_mp_tac (irule_canon ismono_property) >>
          exists_tac' (rastt "X") >> exists_tac' (rastt "a:A->X") >>
          drule i1_of_copa >>
          by_tac (rapf "a = copa(iA:A->A1,ione:1->A1,a:A->X, x:1->X) o iA")
          >-- arw_tac[] >> 
          once_arw_tac[] >> rw_tac[o_assoc] >> arw_tac[] >> 
          rw_tac[GSYM o_assoc] >> 
          pop_assum (K all_tac) >> pop_assum (K all_tac) >> 
          once_arw_tac[] >> rw_tac[]) >>
      assume_tac (specl (List.map readt ["1","id(1)","x0':1->1"]) to1_unique) >>
      suffices_tac (rapf "?x0:1->A. (a:A->X) o x0 = x") 
      >-- (disch_tac >> first_assum opposite_tac) >> 
      exists_tac' (rastt "x0:1->A") >>
      by_tac (rapf "copa(iA,ione,a,x) o ione o (x0':1->1) = copa(iA:A->A1,ione:1->A1,a:A->X,x:1->X) o iA o (x0:1->A)") 
      >-- (arw_tac[] >> arw_tac[GSYM o_assoc]) >>
      pop_assum mp_tac >> rw_tac[GSYM o_assoc] >> drule i12_of_copa >> 
      arw_tac[idR] >> strip_tac >> arw_tac[]) >> 
first_assum 
          (specl_then [rastt "(g:X'->A1) o (a':1->X')"] strip_assume_tac)
>-- (assume_tac (specl (List.map readt ["1","id(1)","x0:1->1"]) to1_unique) >>
     suffices_tac (rapf "?x0:1->A. (a:A->X) o x0 = x") 
     >-- (disch_tac >> first_assum opposite_tac) >> 
     exists_tac' (rastt "x0':1->A") >> 
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
 >-- (exists_tac' (rastt "g:Y->X") >> exists_tac' (rastt "f:X->Y") >>
      arw_tac[]) >>
(exists_tac' (rastt "g:X->Y") >> exists_tac' (rastt "f:Y->X") >>
 arw_tac[]))
(rapg "areiso(X,Y) <=> areiso(Y,X)")

(*∀X Y Z f g. is_iso f ∧ is_iso g ∧ f∶ X → Y ∧ g∶ Y → Z ⇒
            is_iso (g o f)*)

val iso_o_iso = proved_th $
e0
(rw[isiso_def] >> repeat strip_tac >> 
 exists_tac' (rastt "(f':Y->X) o (f'':Z-> Y)") >> 
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

(*TODO: AQ match_mp_tac iso_trans--solved, ir_canon does this*)
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

(*TODO: gen_all in to_zero_zero |> strip_all_and_imp  does not do the correct thing -- solved, fixed the soundness issue.*)

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
      by_tac (rapf "g o b o h1 o h2 = (g:A->Y) o (b o h1:X->Y) o h2:Y->X")
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
           exists_tac' (rastt "xb':1->Y") >> rw[]) >>
      drule from_iso_zero_eq  >> 
      pick_x_assum (rapf "areiso(Y, 0)") (assume_tac o (rewr_rule[areiso_def]))>>
      pick_x_assum (rapf "areiso(X, 0)") (assume_tac o (rewr_rule[areiso_def]))>>
      pop_assum mp_tac >> pop_assum mp_tac >> repeat strip_tac >>
      exists_tac' (rastt "(g:0->Y) o (f':X->0)") >>
      first_x_assum (specl_then (List.map rastt ["A","(b:Y->A) o (g:0->Y) o (f':X->0)","a:X->A"]) assume_tac) >>
      arw_tac[]) >> 
 full_simp_tac[iso_zero_is_zero] >> drule mono_non_zero_post_inv >>
 first_x_assum drule >> pop_assum strip_assume_tac >> 
 exists_tac' (rastt "(g:A->Y) o (a:X->A)") >> 
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
 >-- (match_mp_tac (irule_canon prop_2_half2) >> arw_tac[] >> 
      repeat strip_tac >> 
      first_x_assum (specl_then [rastt "xb:1->X"] assume_tac) >> 
      pop_assum strip_assume_tac >> exists_tac' (rastt "y:1->Y") >>
      full_simp_tac[]) >> 
 by_tac (rapf "?h2:Y->X. (a:X->A) o h2 = b") 
 >-- (match_mp_tac (irule_canon prop_2_half2) >> arw_tac[] >> 
      repeat strip_tac >>
      first_x_assum (specl_then [rastt "xb:1->Y"] assume_tac) >>
      pop_assum strip_assume_tac >> exists_tac' (readt "x':1->X") >>
      full_simp_tac[]) >>
 pop_assum_list (map_every strip_assume_tac) >> 
 exists_tac' (rastt "h1:X->Y") >> exists_tac' (rastt "h2:Y->X") >>
 arw[] >> match_mp_tac (irule_canon inc_inc_iso_as_subobj) >>
 exists_tac' (rastt "A") >> exists_tac' (rastt "a:X->A") >> exists_tac' (rastt "b:Y->A") >> arw[])
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
      exists_tac' (rastt "f0x:B->A") >> 
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

exists_tac' (rastt "f0x:B->A")  bug! does not complain here, but complain later in validation check!
*)

val epi_has_section = proved_th $
e0
(repeat strip_tac >> cases_on (rapf "areiso(B,0)")
 >-- (drule iso_zero_zero >> 
      first_assum (specl_then [rastt "B"] strip_assume_tac) >> 
      first_x_assum (specl_then [rastt "A"] strip_assume_tac) >>
      exists_tac' (rastt "f0x':B->A") >> 
      first_assum (specl_then [rastt "(e:A->B) o (f0x':B->A)"] assume_tac) >>
      first_x_assum (specl_then [rastt "id(B)"] assume_tac) >>
      remove_asm_tac (rapf "!f0x0: B -> A. f0x0 = f0x'") >>
      arw_tac[]) >>
 match_mp_tac (irule_canon epi_pre_inv) >> full_simp_tac[iso_zero_is_zero])
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
 suffices_tac (rapf "ce o f = ce:B->cE o (g:A->B)")
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
exists_tac' (rastt "eqind(e:E->A,f:A->B,g,h:X->A)") >>
drule eq_eqn >> first_x_assum drule >> arw[])
(rapg "iseq(e:E->A,f:A->B,g) ==> ((?h0: X-> E.e o h0 = h) <=> f o h = g o h)")


val fac_through_coeq_iff = proved_th $
e0
(strip_tac >> dimp_tac >> strip_tac 
 >-- (drule fac_through_coeq' >> first_x_assum drule >> arw[]) >> 
exists_tac' (rastt "coeqind(ce:B->cE,f:A->B,g,h:B->X)") >>
drule coeq_eqn >> first_x_assum drule >> arw[])
(rapg "iscoeq(ce:B->cE,f:A->B,g) ==> ((?h0: cE->X.h0 o ce = h) <=> h o f = h o g)")

 
(*∀B f g. f∶ N → B ∧ g∶ one → B ⇒
          (f o z = g  ⇔ ⟨id N,f⟩ o z = ⟨z,g⟩)*)

(*?A B (p1 : NB -> A#)  (p2 : NB -> B). p2 o pa(pN, pB, id(N), f) o z =
               p2 o pa(pN, pB, z, g) & ispr(p1, p2) &
               p1 o pa(pN, pB, id(N), f) o z = p1 o pa(pN, pB, z, g)

TODO: ppbug*)


val Thm1_case1_comm_condition_left = proved_th $
e0
(repeat strip_tac >> dimp_tac >> strip_tac
 >-- (drule to_p_eq >> first_x_assum match_mp_tac >> 
      drule p12_of_pa >> arw_tac[GSYM o_assoc,idL]) >>
 drule p2_of_pa >>
 first_assum (specl_then (List.map rastt ["N","id(N)","f:N->B"])
 (assume_tac o GSYM)) >>
 first_assum (specl_then (List.map rastt ["1","z","g:1->B"])
 (assume_tac o GSYM)) >> once_arw_tac[] >> rw_tac[o_assoc] >>
 once_arw_tac[] >> first_assum (accept_tac o GSYM)
 )
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B g:1->B.f o z = g <=> (pa(pN,pB,id(N),f) o z = pa(pN,pB,z,g))")


(*∀B f h. f∶ N → B ∧ h∶ N×B → B ⇒
        (h o ⟨id N,f⟩ = f o s ⇔ ⟨s o p1 N B, h⟩ o ⟨id N, f⟩ = ⟨id N, f⟩ o s)
cannot use different choice of products for two N* B, because of the h.
*)
val once_arw = once_arw_tac

val Thm1_case1_comm_condition_right = proved_th $
e0
(repeat strip_tac >> dimp_tac >> strip_tac
 >-- (drule to_p_eq >> first_x_assum match_mp_tac >> 
     drule p12_of_pa >> arw[GSYM o_assoc] >> arw[o_assoc,idL,idR]) >>
 drule p2_of_pa >> first_assum (specl_then (List.map rastt ["NB","s o pN:NB->N","h:NB->B"]) (assume_tac o GSYM)) >> 
first_x_assum (specl_then (List.map rastt ["N","id(N)","f:N->B"]) (assume_tac o GSYM)) >> pop_assum mp_tac >> once_arw_tac[] >> rw_tac[o_assoc] >>
strip_tac >> drule p2_of_pa >> once_arw[] >> rw[o_assoc])
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B h:NB->B. h o pa(pN,pB,id(N),f) = f o s <=> pa(pN,pB,s o pN,h) o pa(pN,pB,id(N),f) = pa(pN,pB,id(N),f) o s")



val Thm1_case1_comm_condition_right' = proved_th $
e0
(repeat strip_tac >> dimp_tac >> strip_tac
 >-- (rev_drule to_p_eq >> first_x_assum match_mp_tac >> 
     rev_drule p12_of_pa >> arw[GSYM o_assoc] >> arw[o_assoc,idL,idR] >>
     drule p1_of_pa >> arw[idR]) >>
 rev_drule p2_of_pa >> first_assum (specl_then (List.map rastt ["NB'","s o pN':NB'->N","h:NB'->B"]) (assume_tac o GSYM)) >> once_arw[] >> 
 rw[o_assoc] >> once_arw[] >> once_arw[]>> 
first_x_assum (specl_then (List.map rastt ["N","id(N)","f:N->B"]) assume_tac) >>
rw[GSYM o_assoc] >> once_arw[] >> rw[])
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !NB' pN':NB'->N pB':NB'->B. ispr(pN',pB') ==> !f:N->B h:NB'->B. h o pa(pN',pB',id(N),f) = f o s <=> pa(pN,pB,s o pN',h) o pa(pN',pB',id(N),f) = pa(pN,pB,id(N),f) o s")


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

TODO: rw does not do anything to this *)

val Thm1_case1_comm_condition_right'' = 
dimpI
(Thm1_case1_comm_condition_right |> strip_all_and_imp |> dimpl2r 
|> undisch |> prove_hyp (sym (assume (rapf "f o s = h o pa(pN:NB->N, pB:NB->B, id(N), f:N->B)"))) |> disch (rapf "f o s = h o pa(pN:NB->N, pB:NB->B, id(N), f:N->B)")) 
(Thm1_case1_comm_condition_right |> strip_all_and_imp |> dimpr2l 
|> undisch |> sym |> disch (rapf "pa(pN, pB, (s o pN), h:NB->B) o pa(pN, pB, id(N), f) = pa(pN:NB->N, pB:NB->B, id(N), f:N->B) o s"))|> gen_all |> disch_all
|> gen_all



val Thm1_case1_comm_condition = proved_th $
e0
(repeat strip_tac >> drule Thm1_case1_comm_condition_left >>
 first_x_assum (specl_then (List.map rastt ["f:N->B","g:1->B"]) assume_tac) >>
 arw[] >> rw_tac[] >> drule Thm1_case1_comm_condition_right'' >>
 first_x_assum (specl_then (List.map rastt ["f:N->B","h:NB->B"]) assume_tac) >>
 arw[])
(rapg "!B NB pN:NB->N pB:NB->B.ispr(pN,pB) ==> !f:N->B h:NB->B g:1->B. f o z = g & f o s = h o pa(pN,pB,id(N),f) <=> pa(pN,pB,id(N),f) o z = pa(pN,pB,z,g) & pa(pN,pB,s o pN,h) o pa(pN,pB,id(N),f) = pa(pN,pB,id(N),f) o s")


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

val longf' = rastt "Nind(pa(pN:NB->N,pB:NB->B,z,g:1->B),pa(pN,pB,s o pN,h:NB->B))" 

val longf = mk_fun "o" [rastt "pB:NB->B",longf']

val Thm1_case_1 = proved_th $
e0
(repeat strip_tac >> 
 abbrev_tac (rapf "Nind(pa(pN:NB->N,pB:NB->B,z,g:1->B),pa(pN,pB,s o pN,h:NB->B)) = f'") >> 
 by_tac (rapf "(pN: NB->N) o (f':N->NB) = id(N)")
 >-- (match_mp_tac (GSYM comm_with_s_id) >> pop_assum (assume_tac o GSYM) >>
      assume_tac
      (Neqn_zs |> specl (List.map rastt ["NB","pa(pN:NB->N, pB:NB->B, s o pN, h:NB->B)","pa(pN:NB->N, pB:NB->B, z, g:1->B)"])) >>
      pop_assum strip_assume_tac >> rw_tac[o_assoc] >> 
      arw[] >> drule p1_of_pa >> arw[GSYM o_assoc]) >>
 abbrev_tac (rapf "(pB:NB->B) o (f':N->NB) = f") >>
 exists_tac' (rastt "f:N->B") >> 
 by_tac (rapf "f' = pa(pN:NB->N,pB:NB->B,id(N),f:N->B)")
 >-- (drule to_p_eq >> first_x_assum match_mp_tac >>
      drule p12_of_pa >> arw[]) >>
 by_tac (rapf "(f:N->B) o z = g & f o s = h o pa(pN:NB->N,pB:NB->B,id(N),f)")
 >-- (suffices_tac (mk_conj (mk_eq (mk_fun "o" [longf,z]) (rastt "g:1->B")) 
                 (mk_eq (mk_fun "o" [longf,s]) 
                        (mk_fun "o" [rastt "h:NB->B",mk_fun "pa" ((List.map rastt ["pN:NB->N","pB:NB->B","id(N)"]) @ [longf])])))
      >-- (once_arw[] >> once_arw[] >> disch_tac >> 
          first_x_assum accept_tac) >>
      assume_tac
      (Neqn_zs |> specl (List.map rastt ["NB","pa(pN:NB->N, pB:NB->B, s o pN, h:NB->B)","pa(pN:NB->N, pB:NB->B, z, g:1->B)"])) >>
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
(rapg "!NB pN:NB->N B pB:NB->B. ispr(pN,pB) ==> !g:1->B h:NB->B. ?f:N->B.!f0. (f0 o z = g & f0 o s = h o pa(pN,pB,id(N),f0)) <=> f0 = f")



(*∀A B f g. g∶ A → B ∧ f∶ A×N → B ⇒
          (tp f o z = tp (g o (p1 A one)) ⇔
           f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one))*)



fun split_assum f th = 
    if fmem f (ant th) then
        case view_form f of (vConn("&",[f1,f2])) => 
                  th |> disch f |> (C mp) (conjI (assume f1) (assume f2))
                | _ =>  raise ERR ("split_assum.not a conjunction: ",[],[],[f])
    else raise ERR ("split_assum.formula not in assumption list",[],[],[f])

fun split_assum' th = 
    let fun f _ f0 = if is_conj f0 then SOME f0 else NONE
    in
        case first_opt f (ant th) of
            NONE => raise simple_fail "split_assum'.no conjunction"
          | SOME cj0 => split_assum cj0 th
    end


val parallel_p_one_side_split = 
 parallel_p_one_side |> strip_all_and_imp
                     |> split_assum' |> split_assum' |> disch_all'' |> gen_all

val f0 = rastt "(f:AN->B) o pa(pA:AN->A, pN:AN->N, pA':A1->A, z o (pone:A1->1))"
val f0' = rastt "ev o pa(p1:efs->A,p2:efs->A2B,pA':A1->A,tp(p1,p2,ev:efs->B,pA:AN->A,pN:AN->N,f:AN -> B) o z o pone:A1->1)"



fun pexistsl_tac l = map_every (exists_tac') (List.map rastt l)

fun pspecl_then l ttac = specl_then (List.map rastt l) ttac

fun pspecl l th = specl (List.map rastt l) th

val Thm1_comm_eq_left = proved_th $
 e0
(repeat strip_tac >> drule exp_ispr >>
 by_tac (rapf "ispr(pA':A1->A, pone:A1->1) & ispr(pA:AN->A, pN:AN->N) & ispr(p1:efs->A, p2:efs->A2B)") >-- arw[] >>
 drule parallel_p_one_side >> 
 first_x_assum (specl_then (List.map rastt ["z","tp(p1:efs->A,p2:efs->A2B,ev:efs->B,pA:AN->A,pN:AN->N,f:AN->B)"]) assume_tac) >> 
 dimp_tac >> strip_tac 
 >-- (by_tac (mk_eq f0 f0') 
      >-- (once_arw[]  >> 
      drule ev_of_tp >> 
      first_x_assum 
       (specl_then ([rastt "AN"]) assume_tac) >> 
      first_x_assum drule >>
      first_x_assum 
       (specl_then (List.map rastt ["f:AN->B"]) (assume_tac o GSYM)) >>
      pop_assum (assume_tac o (fn th => EQ_fsym "o" [th,refl (rastt "pa(pA:AN->A, pN:AN->N, pA':A1->A, z o pone)")])) >>
      once_arw[] >> rw[o_assoc]) >>
      once_arw[] >> rw[GSYM o_assoc] >> once_arw[] >>
      drule ev_of_tp >>
      first_x_assum 
       (specl_then ([rastt "A1"]) assume_tac) >>
      first_x_assum drule >> 
      first_x_assum 
       (specl_then ([rastt "(g:A->B) o (pA':A1->A)"]) accept_tac)
      (*turn ev o pa(p1, p2, pA', (tp(p1, p2, ev, pA, pN, f) o z) o pone)
        into ev o pa(p1, p2, pA', tp(p1, p2, ev, pA', pone, (g o pA')) o pone)
        by assumption then into non-tp*)) >>
 match_mp_tac (irule_canon ev_eq_eq) >>
 pexistsl_tac ["A","A1","B","efs","ev:efs->B","p1:efs->A",
               "pA':A1->A","p2:efs->A2B","pone:A1->1"] >>
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
(rapg "!A AN pA:AN->A pN:AN->N. ispr(pA,pN) ==> !A2B B efs p1:efs->A p2:efs->A2B ev:efs->B. isexp(p1,p2,ev) ==> !A1 pA':A1->A pone:A1->1. ispr(pA',pone) ==> !g:A->B f:AN->B.tp(p1,p2,ev,pA,pN,f) o z = tp(p1,p2,ev,pA',pone,g o pA') <=> f o pa(pA,pN,pA',z o pone) = g o pA'")




fun sym_tac (G,fl,f) = 
    case view_form f of
        vPred("=",[t1,t2]) => 
        ([(G,fl,mk_eq t2 t1)], sing sym)
      | _ => raise ERR ("sym_tac.not an equation",[],[],[f])

fun readfq [QUOTE s] = rapf s

structure Parse = struct val Term=readfq end


val Thm1_comm_eq_right_lemma_short = proved_th $
 e0
(repeat strip_tac >> sym_tac >> match_mp_tac (irule_canon is_tp) >> arw[] >>
 (*split the pa(p1, p2, pA, (tp(p1, p2, ev, pA, pN, f) o s) o pN)*) 
 drule exp_ispr >>
 by_tac 
 “ispr(pA, pN) & ispr(pA:AN->A, pN:AN->N) & ispr(p1:AA2B->A, p2:AA2B->A2B)” >> 
 arw[] >> drule parallel_p_one_side >> 
 first_x_assum (pspecl_then ["s","tp(p1:AA2B->A,p2:AA2B->A2B,ev:AA2B->B,pA:AN->A,pN:AN->N,f:AN->B)"] assume_tac) >>
 arw[o_assoc] >> drule ev_of_tp >> first_x_assum rev_drule >>
 arw[GSYM o_assoc])
(rapg "!A B A2B AA2B p1:AA2B->A p2:AA2B->A2B ev:AA2B->B. isexp(p1,p2,ev) ==> !AN pA:AN->A pN:AN->N. ispr(pA,pN) ==> !f:AN->B.tp(p1,p2,ev,pA,pN,f o pa(pA,pN,pA,s o pN)) = tp(p1,p2,ev,pA,pN,f) o s")

fun form_goal f = new_goal (fvf f,[]:form list,f)

(*(pick_x_assum “ispr(Ap:AP->P, aP:AP->A)” mp_tac) if the input not in the asumption list, then HOL error instead of pick x assum err TODO*)

val Thm1_comm_eq_right_lemma_long = proved_th $ 
e0 
(repeat strip_tac >> pop_assum (assume_tac o sym) >> arw[] >>
 sym_tac >> match_mp_tac (irule_canon is_tp) >> arw[] >>
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
 match_mp_tac (irule_canon to_p_eq) >> 
 pexistsl_tac ["A","A2B","p1 : AA2B ->A","p2 : AA2B -> A2B"] >>
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
 h o pa(pAN,pB,id(AN),f) = f o pa(pA,pN,pA,s o pN) <=>
 tp(p1,p2,ev,Ap,aP,h o l) o pa(Na2b,nA2B,id(N),tp(p1,p2,ev,pA,pN,f)) = 
 tp(p1,p2,ev,pA,pN,f) o s”
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
   f o pa(pA, pN, pA', z o pone) = g o pA' & 
   h o pa(pAN,pB,id(AN),f) = f o pa(pA,pN,pA,s o pN) <=>
(tp(p1, p2, ev, pA, pN, f) o z =
tp(p1, p2, ev, pA', pone, g o pA') &
(!l. l = pa(pAN,pB,pa(pA,pN,Ap,Na2b o aP),ev o pa(p1,p2,Ap,nA2B o aP)) ==>
 tp(p1,p2,ev,Ap,aP,h o l) o pa(Na2b,nA2B,id(N),tp(p1,p2,ev,pA,pN,f)) = 
 tp(p1,p2,ev,pA,pN,f) o s))”)

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
 >-- (sym_tac >> match_mp_tac (irule_canon is_tp) >> once_arw[] >> rw[]) >>
 strip_tac >> dimp_tac >> strip_tac (* 2 *) 
 >-- (once_arw[] >> match_mp_tac (gen_all tp_eq) >>
      pexistsl_tac ["A","A2B","pA:AN->A","N","pN:AN->N",
                    "AA2B","ev:AA2B->B","p1:AA2B->A","p2:AA2B->A2B"] >>
      once_arw[] >> rw[] >> first_x_assum drule  >>
      pick_xnth_assum 10 (assume_tac o GSYM) >>
      once_arw[] >> strip_tac >-- first_x_assum accept_tac
      >-- first_x_assum (accept_tac o GSYM)) >>
 suffices_tac
 “tp(p1:AA2B->A, p2:AA2B->A2B, ev:AA2B->B, pA:AN->A, pN:AN->N, f':AN->B) o z = tp(p1, p2, ev, pA':A1->A, pone:A1->1, (g:A->B) o pA') & 
  tp(p1, p2, ev, pA, pN, f') o s = 
  tp(p1, p2, ev, Ap:AP->A, aP:AP->P, ((h:ANB->B) o (l:AP->ANB))) o pa(Na2b, nA2B, id(N), tp(p1, p2, ev, pA, pN, f'))”
 >-- (strip_tac >> arw[]) >>
 once_arw[] >> sym_tac >> match_mp_tac (irule_canon is_tp) >>
 once_arw[] >> once_arw[] >> rw[]
 (*
 >-- (strip_tac >> once_arw[] >> rw[] >> repeat strip_tac  >>
     by_tac “l' = l:AP->ANB” >-- (once_arw[](* >> rw[]*))  >>
     pick_xnth_assum 15 mp_tac >> pop_assum mp_tac >> 
     pop_assum_list (map_every (K all_tac)) >>
     repeat strip_tac >> rev_full_simp_tac[] ) 
 >-- cheat >-- cheat
 >>
 once_arw[] >> sym_tac >> match_mp_tac (irule_canon is_tp) >>
 once_arw[] >> once_arw[] >> rw[] *))
(form_goal
 “!A AN pA:AN->A pN:AN->N.
  ispr(pA,pN) ==> 
  !ANB B pAN:ANB->AN pB:ANB-> B. 
  ispr(pAN,pB) ==>
  !A1 pA':A1 -> A pone:A1 -> 1. ispr(pA', pone) ==> 
  !g:A->B h:ANB->B.
  ?f:AN->B. !f'. (f' o pa(pA,pN,pA',z o pone) = g o pA' &
            h o pa(pAN,pB,id(AN),f') = f' o pa(pA,pN,pA,s o pN)) <=> f' = f”)

(*∃p. p∶ N → N ∧ p o z = z ∧ p o s = id N*)

val pred_exists = proved_th $
e0
(x_choosel_then ["NN","p1","p2"] assume_tac (pr_ex |> pspecl ["N","N"]) >>
 drule Thm1_case_1 >> 
 first_x_assum (pspecl_then ["z","p1:NN->N"] assume_tac) >>
 first_x_assum (x_choose_then "p" assume_tac) >> 
 pexistsl_tac ["p:N->N"] >>
 first_x_assum (pspecl_then ["p:N->N"] assume_tac) >>
 drule p1_of_pa >> full_simp_tac[])
(form_goal “?p:N->N. p o z = z & p o s = id(N)”)

(*∀n. n∶ one → N ⇒ (s o n) ≠ z*)

(*TODO, may AQ, ~!X (e1 : X# -> X#)  (e1 : X# -> X#). ~~e1# = e1#: thm elim the double neg*)

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
 by_tac “s o z = z”
 >-- (by_tac “p o s o n = (p:N->N) o z” 
      >-- arw[] >>
      pop_assum mp_tac >> rw[GSYM o_assoc]>> arw[idL] >> 
      strip_tac >> full_simp_tac[]) >>
 suffices_tac “e1 = id(X) & e1'= id(X)”
 >-- (strip_tac >> arw[]) >> strip_tac >> match_mp_tac fun_ext >>
 strip_tac >> rw[idL]
 >-- (strip_assume_tac 
     (Neqn_zs |> pspecl ["X","e1:X->X","a:1->X"] |> GSYM) >>
     once_arw[] >> rw[GSYM o_assoc] >>
     suffices_tac “(Nind(a, e1) o s)  o z = Nind(a:1->X, e1:X->X) o z”
     >-- (strip_tac >> pick_xnth_assum 5 mp_tac >> rev_full_simp_tac[]) >>
     rw[o_assoc] >> once_arw[] >> rw[]
     ) >>
strip_assume_tac 
 (Neqn_zs |> pspecl ["X","e1':X->X","a:1->X"] |> GSYM) >>
     once_arw[] >> rw[GSYM o_assoc] >>
     suffices_tac “(Nind(a, e1') o s)  o z = Nind(a:1->X, e1':X->X) o z”
     >-- (strip_tac >> pick_xnth_assum 5 mp_tac >> rev_full_simp_tac[]) >>
     rw[o_assoc] >> once_arw[] >> rw[]
 )
(form_goal “!n:1->N. ~ s o n = z”)

(*is_mono s*)

val Thm2_2 = proved_th $
e0
(match_mp_tac post_inv_mono >> strip_assume_tac pred_exists >>
 pexistsl_tac ["p:N->N"] >> arw[])
(form_goal “ismono(s)”)

(*∀A a s' z'. a∶ A → N ∧ is_mono a ∧ s'∶ A → A ∧ z'∶ one → A ∧
            a o s' = s o a ∧ a o z' = z ⇒ A ≅ N*)

val rpt = repeat  

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
  !s':A->A z':1->A. (a o s' = s o a & a o z' = z ==> areiso(A,N))”)

(*∀A a. a∶ A → N ∧ is_mono a ∧ (∀n. is_mem n a N ⇒ is_mem (s ∘ n) a N) ⇒
        ∃t. t∶ A → A ∧ a o t = s o a*)

val ind_fac = proved_th $
 e0
(rpt strip_tac >> 
 strip_assume_tac (pb_exists |> pspecl ["A","N","s o a:A->N","A","a:A->N"]) >>
 drule pb_equality >>
 suffices_tac “isiso(p:P->A)”
 >-- (rw[isiso_def] >> strip_tac >> pexistsl_tac ["(q:P->A) o (f':A->P)"] >>
      pick_xnth_assum 4 (assume_tac o GSYM) >> arw[GSYM o_assoc] >>
      arw[o_assoc,idR]) >>
 match_mp_tac mono_epi_is_iso >> strip_tac
 >-- (drule pb_mono_mono >> first_x_assum drule >> first_x_assum accept_tac) >>
 match_mp_tac surj_is_epi >> strip_tac >> 
 by_tac “ismem(s o (a:A->N) o (b:1->A),a)”
 >-- (first_x_assum match_mp_tac >> arw[ismem_def] >>
      pexistsl_tac ["b:1->A"] >> rw[]) >>
 full_simp_tac[ismem_def] >> pop_assum (assume_tac o GSYM) >> 
 rev_drule (ispb_def_alt' |> iffLR) >> 
 pop_assum strip_assume_tac >> full_simp_tac[GSYM o_assoc] >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 pexistsl_tac ["a':1->P"] >> arw[])
(form_goal “!A a:A->N. ismono(a) ==> (!n:1->N. ismem(n,a) ==> ismem(s o n,a)) ==>
 ?t:A->A. a o t = s o a”)

(*Theorem Thm2_3:        
∀A a. is_subset a N ∧ (∀n. is_mem n a N ⇒ is_mem (s o n) a N) ∧
    is_mem z a A ⇒ dom a ≅ N
Proof
rw[] >> irule Thm2_3_alt >> fs[is_subset_def] >>
‘a∶ dom a → N’ by metis_tac[hom_def] >>
qabbrev_tac ‘A = dom a’ >>
drule ind_factorization >> fs[is_mem_def] >> metis_tac[]
QED*)

val Thm2_3 = proved_th $
e0
(repeat strip_tac >> match_mp_tac (irule_canon Thm2_3_alt) >> 
 drule ind_fac >> first_x_assum drule >> pop_assum strip_assume_tac >>
 full_simp_tac[ismem_def] >> 
 pexistsl_tac ["a:A->N","t:A->A","x0:1->A"] >> arw[])
(form_goal “!A a:A->N. (ismono(a) & (!n:1->N. ismem(n,a) ==> ismem(s o n,a)) & ismem(z,a)) ==>
           areiso(A,N)”)

(*MaybeTODO: machinary of prove isN from areiso(A,0)*)
(*?C P PQ Q (pC : ANB -> C#)  (pP : PQ -> P)  (pPQ : ANB -> PQ)
               (pQ : PQ -> Q). pC o l o
                 pa(Ap, aP, pA,
                  pa(Na2b, nA2B, id(N), tp(p1, p2, ev, pA, pN, f)) o pN) =
               pC o pa(pAN, pB, id(AN), f) & ispr(pPQ, pC) & ispr(pP, pQ) &
               pP o pPQ o l o
                 pa(Ap, aP, pA,
                  pa(Na2b, nA2B, id(N), tp(p1

TODO: huge ppbug!*)

val coeq_of_equal_post_inv = proved_th $
e0
(rpt strip_tac >> 
 drule coeqind_def >> pop_assum strip_assume_tac >>
 by_tac “id(B) o f = id(B) o f:A->B” >-- rw[] >> first_x_assum drule >>
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
 suffices_tac “k'' o (k' o i1) o q' o t = (k'':R'->BB) o (k' o (i2:B->BB)) o q' o t:1->I0” 
 >-- (rw[GSYM o_assoc] >> once_arw[] >> rw[idL]) >>
 by_tac “k'' o (k' o i1) o q' o t = (k'':R'->BB) o ((k' o i1:B->BB) o q') o (t:1->I0) & 
         k'' o (k' o i2) o q' o t = (k'':R'->BB) o ((k' o i2:B->BB) o q') o (t:1->I0)”
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
      match_mp_tac to_zero_zero >> pexistsl_tac ["I0","(h:I'->I0) o q:A->I'"] >>
      arw[]) >>
 strip_tac  (* 2 *)
 >-- (suffices_tac “ismono((q':I0->B) o h:I'->I0)” 
      >-- (strip_tac >> drule o_mono_imp_mono >> first_x_assum accept_tac) >>
      by_tac “?t.(q:A->I') o t = id(I')”
      >-- (match_mp_tac (irule_canon epi_non_zero_pre_inv) >>
           fs[iso_zero_is_zero]) >>
      pop_assum strip_assume_tac >>
      match_mp_tac ismono_applied >> rpt strip_tac >>
      by_tac
     “?w. (k:R->AA) o w = pa(p1:AA->A,p2:AA->A,(t:I'->A) o (h':X->I'), t o g)”
      >-- (drule
           (fac_through_eq_iff |> undisch|> disch_all'' |> gen_all |> iffRL) >>
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
           (fac_through_coeq_iff |> undisch|> disch_all'' |> gen_all |> iffRL) >>
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
 arw[] >> match_mp_tac (irule_canon mono_o_iso_mono) >> arw[])
(form_goal “!A B f:A->B. ?X m:X->B e:A->X. isepi(e) & ismono(m) & f = m o e”)


val irule = match_mp_tac o irule_canon

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
      >-- (irule to_p_eq >> pexistsl_tac ["X","X2two","p1:P->X","p2:P->X2two"]>>
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
 >-- (irule to_p_eq >> pexistsl_tac ["X","J","pX:XJ->X","pJ:XJ->J"] >>
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

(*TODO: pull exists
?A. (?(f : 1 -> A#). T) & areiso(A#, 0)
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

(*AQ list*)
(*
AQ0:set backup stuff! Do we need GOALSTACK and GOALTREE? I only have goalstack but not goaltree.sml.


AQ1: example:
(rapg "!X x:1->X Y f:X->Y ev X2Y efs p1 p2. isexp(p1:efs ->X,p2:efs->X2Y,ev:efs -> Y) ==> !X1 pX:X1->X pone:X1->1. ispr(pX,pone) ==> ev o pa(p1,p2,x,tp (p1,p2,ev,pX,pone,f o pX)) = f o x")

if after strip, have some free variables whose dom/cod is bound, then raise error. in type checking in parsing.


rapg "!a.ismono(a) & ismono(a)"

should I introduce a constaint so it never happens?

AQ2: parser: how to use fixity of "~" aApp ~? with the ast approach, infix and ~ are treated by app and ainfix, always need (~(...) & P(a))

AQ3: the occurence of B(0) in error message has nothing to do with the dest_all stuff, so even if I edit dest of quant it will happen, but edit dest to replace variables may need renaming, and so cause pain in definition of the rules and tactics.

AQ4. pick_assum / pick_xnth_assum okay (like it anyway...)? would like qpat assum, how basically does it work? (have not make attempt to look at its code though, any key thing to know about it? guess it is parsing & matching, but how far does the parsing go/ how to parse the partial formulas like a = _, another special parser other than pwc?)  how would we allow qpick assum? cannot think of a higher order function for it.

first_x_assume with (fn => which can match the given formula which is obtaibed by parsing in cont, or use _ )

AQ5. possible to use quotation for both usual parser and pwc, seems like HOL only has one parser, and the usual parse has the ct empty. but the current parser very different from the old one, nothing to do with unification. show the treatment of bounded variables.

AQ6. pp bug, missing many #, and ugly printted context, anything obvious for improvement?

AQ7. talked about "do not allow more free variables on RHS", but if the variables are in the context and it is once arw then it is okay, say once arw using GSYM p12_of_pa. discussed before for things like “?x:A->B <=>T” maybe give the conv access to the cont. should the restriction on rw be "no free var outside the cont" in conv, instead of no more fv on RHS? or how else should we once rw with GSYM p12_of_pa?


g:A->B
 ispr(p1#, p2#)

P(f)
------
f (f# = p1# o pa(p1#, p2#, f#, g#) |> )= f' 



AQ8. show the uex stuff, do not have ?! and just use ? to test now, any obvious improvement?

AQ9. Jim replyed and prefers having equality on objects.

*)

(*TODO: parser bug rapg "!i1:A->AB i2:B->AB. iscopr(i1,i2) ==> !x:1->AB. (?x0:1->A. i1 o x0 = x) | (?x0:1->B. i2 o x0 = x)" need () around  (?x0:1->B. i2 o x0 = x)*)

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

(*
val Thm5_existences = proved_th $
e0
(rpt strip_tac)
(form_goal 
“!A X. 
 ?A1 pA:A1->A pone:A1->1. ispr(pA,pone) &
 ?two i1:1->two i2:1->two. iscopr(i1,i2) &
 ?AA2 p1:AA2 -> A A2 p2:AA2 -> A2 ev:AA2 -> two. isexp(p1,p2,ev) &
 ?XX2 p1':XX2->X X2 p2':XX2->X2 ev':XX2->two. isexp(p1',p2',ev') &
 ?AX2 Ax2:AX2->A aX2:AX2->X2.ispr(Ax2,aX2)”)
*)


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
     pexistsl_tac ["X","X2","p1':XX2->X","p2':XX2->X2"] >>
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
          pexistsl_tac ["X","X2","p1':XX2->X","p2':XX2->X2"] >>
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
pexistsl_tac ["X","X2","p1':XX2->X","p2':XX2->X2"] >> once_arw[] >>
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

(*TODO: AQ: should I edit the once arw so it rw a refl into T? to avoid once_arw[] >> rw[] 

but sometimes once_arw gives t = t & x = x but arw gives something weird*)

(*TODO: rpt strip can create variables whose name clashes with existing variables*)

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
     pexistsl_tac ["X","X2","p1':XX2->X","p2':XX2->X2"] >> once_arw[] >>
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
 >-- (irule to_p_eq >> pexistsl_tac ["X","L","pX:XL->X","pL:XL->L"] >>
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
 irule to_p_eq >> qexistsl_tac ["A","A","p1","p2"] >> 
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
(rpt strip_tac >> drule (fac_through_eq_iff |> undisch |> disch_all''
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


(*Theorem char_thm:
∀a A X.
    is_mono a ∧ a∶ A → X ⇒
         char a∶ X → one + one ∧
         ∀x.
             x∶one → X ⇒
             ((∃x0. x0∶one → A ∧ a ∘ x0 = x) ⇔ char a ∘ x = i2 one one)
Proof
strip_tac >> strip_tac >> strip_tac >> strip_tac >>
fs[hom_def] >> metis_tac[char_def,hom_def]
QED*)

(*TODO: if in exists, feed "copa(i1,i2,i2:1->two o to1(A,1),i1:1->two o to1(A',1)) o f':X->AA'", is wrong ,but get wrong error message*)

(*TODO, if input of f' o x is f o x, which is wrong , the error message is err find, not the q parsing*)

val char_exists = proved_th $
   e0
(rpt strip_tac >> drule Thm5 >> pop_assum strip_assume_tac >>
 qspecl_then ["A","A'"] 
 (x_choosel_then ["AA'","iA","iA'"] assume_tac) copr_ex >>
 first_x_assum drule >> fs[isiso_def] >>
 exists_tac' (rastt "copa(iA:A->AA',iA':A'->AA',i2:1->two o to1(A,1),i1:1->two o to1(A',1)) o f':X->AA'") >> strip_tac >> dimp_tac >> strip_tac(* 2 *)
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
(rpt strip_tac >> irule to_p_eq >> qexistsl_tac ["A","1","pA","pone"] >>
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
(rpt strip_tac >> irule to_p_eq >> qexistsl_tac ["A","Y","Ay","aY"] >>
 rw[GSYM o_assoc] >> drule p12_of_pa >> once_arw[] >>
 rw[o_assoc] >> rev_drule p12_of_pa >> once_arw[] >> rw[idR])
(form_goal 
“!A X AX Ax:AX->A aX:AX->X.ispr(Ax,aX) ==>
 !Y AY Ay:AY->A aY:AY->Y. ispr(Ay,aY) ==>
 !f:X->A g:X->Y. pa(Ay,aY,Ax,g o aX) o pa(Ax,aX,f,id(X)) = pa(Ay,aY,f,g)”)

(*do not understand why do not response if use qby*)

val compose_partial_ev = proved_th $
e0
(rpt strip_tac >> 
 by_tac (rapf "pa(pA,pone,id(A),to1(A,1)) o x = pa(pA:A1->A,pone:A1->1,x:1->A,id(1))") >-- (rev_drule compose_with_id_to1 >> once_arw[] >> rw[]) >>
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
qexistsl_tac ["A","X2Y","Ax2y","aX2Y"] >> once_arw[] >>
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
qexistsl_tac ["A","1","pA","pone"] >> arw[] >> once_rw[one_to_one_id] >>
rw[])
(form_goal
“!A A1 pA:A1->A pone:A1->1. ispr(pA,pone) ==> 
 !a:1->A1.?a0:1->A. a = pa(pA,pone,a0,id(1))”)

(*WHY do we not have once fs in HOL?*)

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

(*
val char_exists' = 

char_exists |> strip_all_and_imp |> conj_all_assum
|> disch_all |> gen_all *)



(*irule_canon char_exists is wrong*)

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
(*qby_tac ‘!x:1->AR2. (?x0:1->M. m o x0 = x) <=> phi o x = i2’
example of qby does not response.*)
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
      qexistsl_tac ["R","R2","p1'","p2'"] >> 
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
>-- (irule to_p_eq >> qexistsl_tac ["A","R2","Ar2","aR2"] >>
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
parallel_p_one_side_three |> strip_all_and_imp |> split_assum' |>
split_assum' |> split_assum' |> gen_all |> disch_first |> gen_all
 |> disch_nth 1 |> gen_all |> disch_first |> gen_all
 |> disch_last |> gen_all

val Thm6_g_ev_lemma = proved_th $
e0
(rpt strip_tac >> irule ev_eq_eq >>
 qexistsl_tac ["R","R1","two","RR2","ev'","p1'","pR","p2'","pone'"] >>
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
 qexistsl_tac ["A","A2","p1","p2"] >> 
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
      strip_tac >> dimp_tac >> rw[]) >>
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
 qexistsl_tac ["A","A1","two","AA2","ev","p1","pA","p2","pone"] >> 
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


(*TODO: let rw be able to solve f <=>f*)
val compose_with_g_eq_equiv = proved_th $
e0
(rpt strip_tac >>
 assume_tac (Thm6_page29_means_just_that |> strip_all_and_imp |> allI ("a'",mk_ar_sort one (mk_ob "A"))) >>
 irule equiv_to_same_element >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >> strip_tac >> rw[] >>
 dimp_tac >> rw[])
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
 qexistsl_tac ["A","AA","cE","ce","e","f0","f1","pA1","pA2"] >>
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
(rpt strip_tac  >> last_x_assum mp_tac >> rw[ispb_def] >> arw[] >> 
 strip_tac >>
 first_x_assum (qspecl_then ["A","u","v"] assume_tac)  >>
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
  (drule pb_fac_exists' >> (*TODO:irule bug,should use irule*)
  first_x_assum (qspecl_then ["1","a o x","id(1)"] assume_tac) >>
  rev_drule char_def >> first_x_assum drule >>
  (*TODO: once have pull exists test here*)
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

