(*char property*)


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
(form_goal “!X f:1->X. ismono(f)”);


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
 !A u v. f o u = g o v ==> ?a:A->Pb. p o a = u & q o a = v”);

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
    ?h1 h2.pb1 o h1 = a & a o h2 = pb1 & h1 o h2 = id(Pb) & h2 o h1 = id(A)”);

val char_square = proved_th $
e0
(rpt strip_tac >> irule fun_ext >> rpt strip_tac >> 
 drule char_def >> first_x_assum drule >> 
 first_x_assum (qspecl_then ["a o a'"] assume_tac) >> rw[o_assoc] >>
 once_rw[one_to_one_id] >> rw[idR] >>
 pop_assum (assume_tac o GSYM) >>
 arw[] >> qexistsl_tac ["a'"] >> rw[])
(form_goal
“!two i1 i2.iscopr(i1:1->two,i2:1->two) ==>!A X a:A->X. ismono(a) ==> char(i1,i2,a) o a = i2 o to1(A,1)”);

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
“ismono(a:A->X) ==> iscopr(i1:1->two,i2) ==> ispb(char(i1,i2,a),i2,a,to1(A,1))”);

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
 !c:X->two. ispb(c,i2,a,to1(A,1)) ==> c = char(i1,i2,a)”);

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
 char(i1,i2,a) = char(i1,i2,b)”);

(* !NN (Nn : NN# -> N)  (nN : NN# -> N). ispr(Nn#, nN#) ==>
                 ?NE (ne : NE# -> NN#). ismono(ne) &
                   !Sum (iEQ : N -> Sum#)
                     (iNE : NE# -> Sum#). iscopr(iEQ#, iNE#) ==>
                     isiso(copa(iEQ#, iNE#, pa(Nn#, nN#, id(N), id(N)), ne))]

ppbug , see ne has no #*)



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

(*
val isexp_th = proved_th $
e0
(form_goal
“!A B A2B efs p1:efs->A p2:efs-> A2B ev:efs -> B.
 isexp(p1,p2,ev) <=> 
 ispr(p1,p2) & 
 !X AX p1':AX->A p2':AX->X.ispr(p1',p2') ==>
 !f:AX->B.?h0:X-> A2B. !h. ev o pa(p1,p2,p1',h o p2') = f <=> h = h0”)
*)

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


val Diag_ex = proved_th $
e0
(strip_tac >> qexists_tac "Pa(id(X),id(X))" >> rw[])
(form_goal
“!X.?dX:X->X * X. Pa(id(X),id(X)) = dX”)

val Diag_def = Diag_ex |> spec_all |> eqT_intro
                       |> iffRL |> ex2fsym "Diag" ["X"]
                       |> C mp (trueI []) |> gen_all


(*AQ: should abbrevation like this True_ex use the same schemata as well?*)




val Eq_ex = proved_th $
e0
(strip_tac >> qexists_tac "Char(Diag(X))" >> rw[])
(form_goal “!X.?eqX:X * X -> 2. Char(Diag(X)) = eqX”)


val Eq_def = Eq_ex |> spec_all |> eqT_intro
                   |> iffRL |> ex2fsym "Eq" ["X"]
                   |> C mp (trueI []) |> gen_all


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

val Pa_distr = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["A","B"] assume_tac pi2_def >>
 drule distr_to_pa' >> fs[pa2Pa])
(form_goal
“!A B X a1:X ->A a2:X->B X0 x:X0->X. Pa(a1,a2) o x = 
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
“!X x:1->X. True(X) o x = TRUE”);



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
 (?a:A->P. p o a = u & q o a = v) <=> f o u = g o v”);

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
 (?a:1->P. p0 o a = u) <=> f o u = g”);

(*
fun readf f = (fvf f,[]:form list,f) *)


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
 !X f0:A->X g0:B->X. isiso(copa(iA,iB,f0,g0)) ==> iscopr(f0,g0)”);

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
  Aa o aa = aA o aa”);


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
(form_goal “iscopr(ZERO,SUC)”);


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
“!n:1->N. ~(n = ZERO) <=> ?n0:1->N. n = SUC o n0”);


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
 !a1:1->A a2:1->A. char(i1,i2,pa(Aa,aA,id(A),id(A))) o pa(Aa,aA,a1,a2) = i2 <=> a1 = a2”);


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
 (pred o ZERO = i2 & (!n:1->N. pred o n = i2 ==> pred o SUC o n = i2))”);


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
 (pred o ZERO = i2 & (!n:1->N. pred o n = i2 ==> pred o SUC o n = i2))”);


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
 f o pa(Xn,xN,x,SUC o n0) = g o pa(Yn,yN,y,SUC o n0)”);


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
 !pred.pred = i2 o to1(XY,1) <=> !x:1->X y:1->Y. pred o pa(Xy,xY,x,y) = i2”);


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
 qspecl_then ["X","X","A","f","g","1","a"] assume_tac $
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
 drule $ GSYM to_p_components
 (*if no GSYM here, then fs loops, why?*) >> fs[pa2Pa])
(form_goal
 “!A B X f: X -> A * B. Pa(π1(A,B) o f, π2(A,B) o f) = f”)

val to_Pr_eq = proved_th $
e0
(rpt strip_tac >> assume_tac $ aspec [rastt "π1(A,B) o g:X -> A * B",rastt "π2(A,B) o g:X -> A * B",rastt "f: X -> A * B"] Pa_def >> rfs[] >> rw[to_Pr_components])
(form_goal
 “!A B X f:X-> A * B g:X -> A * B.
  π1(A,B) o f = π1(A,B) o g & π2(A,B) o f = π2(A,B) o g ==>
 f = g”)

val Ev_of_Tp_el = proved_th $
e0
(rpt strip_tac >>
 assume_tac Ev_of_Tp >> 
 first_x_assum (qspecl_then ["A","B","X","f"] assume_tac) >>
 qby_tac 
 ‘Pa(a, Tp(f) o x) = Pa(π1(A, X), Tp(f) o π2(A, X)) o Pa(a,x)’ >--
 (irule to_Pr_eq >> rw[pi12_of_Pa] >> 
  rw[pi12_of_Pa,GSYM o_assoc] >> rw[o_assoc,pi12_of_Pa]) >>
 arw[GSYM o_assoc])
(form_goal
 “!A B X f:A * X ->B P a:P->A x: P ->X. 
  Ev(A,B) o Pa(a, Tp(f) o x) = f o Pa(a,x)”)


val Ev_of_Tp_el' = proved_th $
e0
(rpt strip_tac >> 
 qby_tac ‘Tp(f) = Tp(f) o id(P)’ >-- rw[idR] >>
 once_arw[] >> rw[Ev_of_Tp_el])
(form_goal
“!A B P f:A * P -> B  a:P -> A.
Ev(A, B) o Pa(a, Tp(f)) = f o Pa(a, id(P))”);


val pi31_of_Pa =
    proved_th $
              e0
              (rpt strip_tac >> rw[GSYM pi31_def,pi1_of_Pa] )
              (form_goal
                   “!A B C X a:X-> A bc: X-> B * C. π31(A,B,C) o Pa(a, bc) = a”)


val pi32_of_Pa = proved_th $
e0
(rpt strip_tac >> rw[GSYM pi32_def,o_assoc,pi12_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. π32(A,B,C) o Pa(a, Pa(b,c)) = b”)


val pi33_of_Pa = proved_th $
e0
(rpt strip_tac >> rw[GSYM pi33_def,o_assoc,pi2_of_Pa] )
(form_goal
“!A B C X a:X-> A b: X-> B c: X-> C. π33(A,B,C) o Pa(a, Pa(b,c)) = c”)


val True1TRUE = proved_th $
e0
(rw[GSYM True_def] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal “True(1) = TRUE”)

fun qex_tac tq = qexists_tac $ q2str tq



val Pa3_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Pa(f,Pa(g,h))’ >> rw[])
(form_goal
 “!A B C X f:X->A g:X ->B h:X->C. ?Pa3.
 Pa(f,Pa(g,h)) = Pa3 
”)


val Pa3_def = Pa3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa3" ["f","g","h"]
              |> C mp (trueI []) |> gen_all

val Pa4_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Pa(f,Pa(g,Pa(h,j)))’ >> rw[])
(form_goal
 “!A B C D X f:X->A g:X ->B h:X->C j:X->D. ?Pa4.
 Pa(f,Pa(g,Pa(h,j))) = Pa4
”)

val Pa4_def = Pa4_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Pa4" ["f","g","h","j"]
              |> C mp (trueI []) |> gen_all

val pi41_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘π1(A, B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?pi41. π1(A,B * C * D) = pi41”)

val pi41_def = pi41_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "π41" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all

val pi42_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘π1(B, C * D) o π2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?pi42. π1(B, C * D) o π2(A,B * C * D) = pi42”)


val pi42_def = pi42_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "π42" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val pi43_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘π1(C,D) o π2(B, C * D) o π2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?pi43. π1(C,D) o π2(B, C * D) o π2(A,B * C * D) = pi43”)


val pi43_def = pi43_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "π43" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val pi44_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘π2(C,D) o π2(B, C * D) o π2(A,B * C * D)’ >> rw[])
(form_goal 
 “!A B C D. ?pi44. π2(C,D) o π2(B, C * D) o π2(A,B * C * D) = pi44”)


val pi44_def = pi44_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "π44" ["A","B","C","D"]
              |> C mp (trueI []) |> gen_all


val pi31_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM pi31_def,pi1_of_Pa])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. π31(A,B,C) o Pa3(f,g,h) = f”)



val pi32_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM pi32_def,pi12_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. π32(A,B,C) o Pa3(f,g,h) = g”)


val pi33_of_Pa3 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa3_def,GSYM pi33_def,pi2_of_Pa,o_assoc])
(form_goal
“!A B C X f:X->A g:X->B h:X->C. π33(A,B,C) o Pa3(f,g,h) = h”)

fun mk_o a1 a2 = mk_fun "o" [a1,a2]

fun Pa f g = mk_fun "Pa" [f,g]


val Rssoc3_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Pa3(π1(A,B) o π1(A * B,C),π2(A,B) o π1(A * B,C),π2(A * B,C))’ >> rw[])
(form_goal
 “!A B C. ?asc3:(A * B) * C -> A * B * C. 
  Pa3(π1(A,B) o π1(A * B,C),π2(A,B) o π1(A * B,C),π2(A * B,C)) = asc3”)

val Rssoc3_def = 
    Rssoc3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Rssoc3" ["A","B","C"]
              |> C mp (trueI []) |> gen_all


val Lssoc3_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Pa(Pa(π31(A,B,C),π32(A,B,C)),π33(A,B,C))’ >> rw[])
(form_goal
 “!A B C. ?asc3:A * B * C -> (A * B) * C. 
  Pa(Pa(π31(A,B,C),π32(A,B,C)),π33(A,B,C)) = asc3”)

val Lssoc3_def = 
    Lssoc3_ex |> spec_all |> eqT_intro
              |> iffRL |> ex2fsym "Lssoc3" ["A","B","C"]
              |> C mp (trueI []) |> gen_all

(*TODO: 
π1(A, B * C) o fgh = f &
             (π1(B, C) o π2(A, B * C)) o fgh = g &
             (π2(B, C) o π2(A, B * C)) o fgh = h <=>
             π1(A, B * C) o fgh = f & π2(A, B * C) o fgh = Pa(g, h)

autommatic innto 

             (π1(B, C) o π2(A, B * C)) o fgh = g &
             (π2(B, C) o π2(A, B * C)) o fgh = h <=>
            π2(A, B * C) o fgh = Pa(g, h)

*)

(*A & B <=> A & C <=> B <=> C

  1.fA & fB <=> fA & fC
   2.fB
   3.fA
   ----------------------------------------------------------------------
   fC

TODO: should be able to use tactic to do this, 

but how to enable formula variables?


*)




val Pa3_property = proved_th$
e0
(rpt strip_tac >>  rw[GSYM Pa3_def,GSYM pi31_def,GSYM pi32_def,GSYM pi33_def] >> once_rw[GSYM Pa_def] >>
 dimp_tac >> strip_tac (* 2 *) >--
 (arw[] >> once_rw[GSYM Pa_def] >> fs[o_assoc]) >>
 arw[o_assoc,pi12_of_Pa]
)
(form_goal
“!A B C X f:X->A g:X->B h:X->C fgh. 
 π31(A,B,C) o fgh = f & π32(A,B,C) o fgh = g & 
 π33(A,B,C) o fgh = h <=> fgh = Pa3(f,g,h)”)




val to_Pr3_components = proved_th $
e0
(rpt strip_tac >> sym_tac >> irule $ iffLR Pa3_property >>
 rw[])
(form_goal
 “!A B C X f:X->A * B * C. 
  Pa3(π31(A,B,C) o f,π32(A,B,C) o f,π33(A,B,C) o f) = f”)


val to_Pr3_eq = proved_th $
e0
(rpt strip_tac >> once_rw[GSYM to_Pr3_components]>>
 irule $ iffLR Pa3_property >> rw[to_Pr3_components] >>
 arw[])
(form_goal
 “!A B C X f:X->A * B * C g:X->A * B * C. 
  π31(A,B,C) o f = π31(A,B,C) o g & 
  π32(A,B,C) o f = π32(A,B,C) o g & 
  π33(A,B,C) o f = π33(A,B,C) o g ==> f = g”)


val RLssoc3_iso = proved_th $
e0
(rpt strip_tac (* 2 *) >--
 (irule to_Pr3_eq >>
  rw[GSYM Rssoc3_def,GSYM o_assoc,pi33_of_Pa3,pi31_of_Pa3,pi32_of_Pa3,idR] >> 
 rw[o_assoc,GSYM Lssoc3_def,pi12_of_Pa]) >>
 irule to_Pr_eq >> rw[GSYM o_assoc,GSYM Lssoc3_def,pi12_of_Pa,idR] >> strip_tac (* 2 *) >--
 rw[GSYM Rssoc3_def,pi33_of_Pa3] >>
 irule to_Pr_eq >> 
 rw[GSYM o_assoc,pi12_of_Pa,GSYM Rssoc3_def,pi31_of_Pa3,
    pi32_of_Pa3] 
 
 )
(form_goal
 “!A B C. Rssoc3(A,B,C) o Lssoc3(A,B,C) = id(A * B * C) &
  Lssoc3(A,B,C) o Rssoc3(A,B,C) = id((A * B) * C)”)

fun Tp f = mk_fun "Tp" [f]

fun Ex X = mk_fun "Ex" [X]


val Empty_ex = proved_th $
e0
(strip_tac >> qex_tac ‘Tp(False(X) o π1(X,1))’ >> rw[])
(form_goal
“!X.?ept:1->Exp(X,2). Tp(False(X) o π1(X,1))= ept”)


val Empty_def = 
    Empty_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Empty" ["X"]
             |> C mp (trueI []) |> gen_all


val False2FALSE = proved_th $
e0
(rw[GSYM False_def,o_assoc] >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal
 “!X x:1->X. False(X) o x = FALSE”)

val Empty_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM Empty_def,Ev_of_Tp_el'] >>
 rw[o_assoc,pi1_of_Pa,idR,False2FALSE])
(form_goal
“!X x:1->X. Ev(X,2) o Pa(x,Empty(X)) = FALSE”)



fun Po A B = mk_fun "*" [A,B]



val Tp1_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Tp(f o π1(A,1))’ >> rw[])
(form_goal
 “!A B f:A->B. ?tpf:1->Exp(A,B).Tp(f o π1(A,1)) = tpf”)

val Tp1_def = Tp1_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "Tp1" ["f"] 
                     |> C mp (trueI []) |> gen_all


fun Tp1 f = mk_fun "Tp1" [f] 

val Tp0_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Ev(X,Y) o Pa(id(X),f o To1(X))’ >>
 rw[])
(form_goal
 “!X Y f:1->Exp(X,Y).?tp0:X->Y. Ev(X,Y) o Pa(id(X),f o To1(X)) = tp0”)

val Tp0_def = 
    Tp0_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Tp0" ["f"] 
           |> C mp (trueI []) |> gen_all


val is_Tp = proved_th $
e0
(rpt strip_tac >> rw[GSYM Tp_def] >> arw[])
(form_goal
 “!A B X f: A * X ->B h: X -> Exp(A,B). Ev(A,B) o Pa(π1(A,X) ,h o π2(A,X)) = f ==> h = Tp(f)”)

val To1_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM To1_def] >>
 assume_tac const1_def >> drule to1_def >> once_arw[])
(form_goal
 “!X f:X->1. f = To1(X)”)

val Tp1_Tp0_inv = proved_th $
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 sym_tac >> irule is_Tp >> rw[o_assoc,Pa_distr,idL] >>
 once_rw[To1_property] >> rw[]
 )
(form_goal
 “!X Y f:1-> Exp(X,Y). Tp1(Tp0(f)) = f”)


val Tp0_Tp1_inv = proved_th $
e0
(rpt strip_tac >> rw[GSYM Tp1_def,GSYM Tp0_def] >>
 rw[Ev_of_Tp_el,o_assoc,pi1_of_Pa,idR](* >>
 sym_tac >> irule is_Tp >> rw[o_assoc,Pa_distr,idL] >>
 once_rw[To1_property] >> rw[]*)
 )
(form_goal
 “!X Y f:X->Y. Tp0(Tp1(f)) = f”)

val Ev_of_el = proved_th $
e0
(rpt strip_tac >>
 qby_tac 
 ‘f = Tp1(Tp0(f))’ >-- rw[Tp1_Tp0_inv] >> once_arw[] >>
 rw[GSYM Tp1_def,Ev_of_Tp_el'] >> rw[Tp1_def,Tp1_Tp0_inv] >>
 rw[o_assoc,pi1_of_Pa,idR])
(form_goal
 “!A B f:1->Exp(A,B) a:1->A.
  Ev(A,B) o Pa(a,f) = Tp0(f) o a”)


val Ev_of_Tp1_el = proved_th $
e0
(rw[Ev_of_el,Tp0_Tp1_inv])
(form_goal
 “!A B f:A -> B a:1->A.
  Ev(A,B) o Pa(a,Tp1(f)) = f o a”)

fun Exp A B = mk_fun "Exp" [A,B]






val Swap_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Pa(π2(A,B),π1(A,B))’ >> rw[])
(form_goal
 “!A B. ?swap:A * B ->B * A. Pa(π2(A,B),π1(A,B)) = swap”)

val Swap_def = 
    Swap_ex |> spec_all |> eqT_intro
               |> iffRL |> ex2fsym "Swap" ["A","B"] 
               |> C mp (trueI []) |> gen_all


val Swap_property = proved_th $
e0
(rw[GSYM Swap_def,pi12_of_Pa])
(form_goal
 “!A B. π1(B,A) o Swap(A,B) = π2(A,B) & π2(B,A) o Swap(A,B) = π1(A,B)”)


val Swap_Swap_id = proved_th $
e0
(rpt strip_tac >> irule to_Pr_eq >> rw[GSYM Swap_def,idR] >>
 rw[Pa_distr,pi12_of_Pa])
(form_goal
 “!A B. Swap(B,A) o Swap(A,B) = id(A * B)”)

val N_equality = proved_th $
e0
(rpt strip_tac >> 
 qspecl_then ["X","x0:1->X","t","Nind(x0,t)"] assume_tac
 constN_def >> fs[])
(form_goal
“!X x0:1->X t. Nind(x0,t) o ZERO = x0 &
  Nind(x0,t) o SUC = t o Nind(x0,t)”)



val pi41_of_Pa4 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM pi41_def,pi12_of_Pa])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 π41(A,B,C,D) o Pa4(f,g,h,k) = f”);

val pi42_of_Pa4 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM pi42_def,pi12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 π42(A,B,C,D) o Pa4(f,g,h,k) = g”);


val pi43_of_Pa4 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM pi43_def,pi12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 π43(A,B,C,D) o Pa4(f,g,h,k) = h”);


val pi44_of_Pa4 = proved_th $
e0
(rpt strip_tac >> rw[GSYM Pa4_def,GSYM pi44_def,pi12_of_Pa,o_assoc])
(form_goal
“!A B C D X f:X->A g:X->B h:X->C k:X->D.
 π44(A,B,C,D) o Pa4(f,g,h,k) = k”);

val TRUE2FALSE = proved_th $
e0
(assume_tac TRUE_def >> drule i1_xor_i2 >> arw[])
(form_goal
“!f. ~(f = TRUE) <=> f = FALSE”);



val Mem_ex = proved_th $
e0
(strip_tac >> qex_tac ‘Ev(X,2)’ >> rw[])
(form_goal
 “!X. ?mem. Ev(X,2) = mem”)

val Mem_def = Mem_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Mem" ["X"]
             |> C mp (trueI []) |> gen_all




val Swap_Pa = proved_th $
e0
(rw[GSYM Swap_def,Pa_distr] >> rpt strip_tac >>
 irule to_Pr_eq >> rw[pi12_of_Pa])
(form_goal
“!A B X f:X->A g:X->B. Swap(A,B) o Pa(f,g) = Pa(g,f)”)

val NOT_IN_Empty = proved_th $
e0
(rpt strip_tac >> rw[GSYM Mem_def,GSYM Empty_def,Ev_of_Tp_el',o_assoc] >> once_rw[one_to_one_id] >> rw[idR,False2FALSE]>>
 rw[TRUE2FALSE])
(form_goal
“!X x:1->X. ~(Mem(X) o Pa(x,Empty(X)) = TRUE)”)




val Tp0_INJ = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac >-- 
 (once_rw[GSYM Tp1_Tp0_inv] >> arw[]) >> arw[])
(form_goal
 “!A B f:1->Exp(A,B) g:1->Exp(A,B).
  Tp0(f) = Tp0(g) <=> f = g”)

val MEMBER_NOT_Empty= proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (contra_tac >> fs[NOT_IN_Empty]) >>
 qby_tac ‘~(Tp0(s0) = Tp0(Empty(X)))’ >-- 
 arw[Tp0_INJ] >> 
 drule $ contrapos $ spec_all fun_ext >> 
 fs[GSYM Empty_def,Tp1_def,Tp0_Tp1_inv,False2FALSE] >>
 fs[gen_all $ forall_exists ("a",ar_sort (mk_ob "A") (mk_ob "B"))] >> qex_tac ‘a’ >> rw[GSYM Mem_def] >>
 fs[GSYM Tp0_def,o_assoc,idL,Pa_distr] >> 
 pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR,GSYM TRUE2FALSE])
(form_goal
“!X s0:1->Exp(X,2). (?x.(Mem(X) o Pa(x,s0) = TRUE)) <=>
 ~(s0 = Empty(X))”)

val FALSE_ne_TRUE = proved_th $
e0
(irule i1_ne_i2 >> rw[TRUE_def])
(form_goal
“~(FALSE = TRUE)”)

val TRUE_ne_FALSE = GSYM FALSE_ne_TRUE

val pred_ext = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (cases_on “p1:1->2 = TRUE” >-- fs[] >>
 fs[TRUE2FALSE] >> fs[GSYM TRUE_ne_FALSE] >>
 fs[TRUE2FALSE]) >>
 arw[])
(form_goal
“!p1 p2. (p1 = TRUE <=> p2 = TRUE) <=> p1 = p2”)

val fun_ext_iff = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) >-- 
 (drule fun_ext >> arw[]) >>
 rpt strip_tac >> arw[])
(form_goal
“!A B f:A->B g. (!a:1->A. f o a = g o a) <=> f = g”)



val IP_el = proved_th $
e0
(assume_tac $ GSYM ind_principle >> assume_tac TRUE_def >>
 first_x_assum drule >> fs[] >> rpt strip_tac >> 
 fconv_tac 
 (rand_fconv no_conv (rewr_fconv (GSYM $ spec_all fun_ext_iff))) >>
 rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idR]) 
(form_goal
 “!P:N->2. (!n. P o n = TRUE) <=>
  P o ZERO = TRUE &
  (!n. P o n = TRUE ==> P o SUC o n = TRUE)”)
(*!!!!!!!!! qex*)

fun Po A B = mk_fun "*" [A,B]


val o_assoc_middle = proved_th $
e0
(rpt strip_tac >> rw[o_assoc])
(form_goal 
“!A B f:A->B C g:B->C D h:C->D E i:D->E. 
 i o h o g o f = i o (h o g) o f”)


val exists_forall0 = 
exists_forall ("x",mk_ar_sort (mk_ob "A") (mk_ob "B"))

fun Nind x0 t = mk_fun "Nind" [x0,t]

fun Ev e f = mk_fun "Ev" [e,f]
(*inv_suc_eq s_eq_iff_eq p_z_cases PRE_eq_0*)


fun pi1 A B = mk_fun "π1" [A,B]

fun pi2 A B = mk_fun "π2" [A,B]
