
val Thm1 = proved_th $ val (ct,asl,w) = cg $
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
 >-- (strip_tac) )
(form_goal
 “!A AN pA:AN->A pN:AN->N.
  ispr(pA,pN) ==> 
  !ANB B pAN:ANB->AN pB:ANB-> B. 
  ispr(pAN,pB) ==>
  !A1 pA':A1 -> A pone:A1 -> 1. ispr(pA', pone) ==> 
  !g:A->B h:ANB->B.
  ?f:AN->B. !f'. (f' o pa(pA,pN,pA',z o pone) = g o pA' &
            h o pa(pAN,pB,id(AN),f') = f' o pa(pA,pN,pA,s o pN)) <=> f' = f”)










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


(*
val pb_fac_exists' = proved_th $ val (ct,asl,w) = cg $
e0
(rpt strip_tac  >> last_x_assum mp_tac >> rw[ispb_def] >> arw[]  )
(form_goal “!X Z f:X->Z Y g:Y->Z Pb p:Pb->X q:Pb->Y.ispb(f:X->Z,g:Y->Z,p,q) ==> 
 !A u v. f o u = g o v ==> ?a:A->Pb. p o a = u & q o a = v”)


dest_forall0 u0;
val it =
   ("!", "A", ob,
    !(u : B(1) -> X)
      (v : B(2) -> Y). ?(a : B(3) -> Pb). !(a' : B(4) -> Pb). p o a' = u &
          q o a' = v <=> a' = a): string * string * sort * form

*)

e0
(rpt strip_tac  >> last_x_assum mp_tac >> rw[ispb_def] >> arw[] >>
 strip_tac )
(form_goal “!X Z f:X->Z Y g:Y->Z Pb p:Pb->X q:Pb->Y.ispb(f:X->Z,g:Y->Z,p,q) ==> 
 !A u v. f o u = g o v ==> ?a:A->Pb. p o a = u & q o a = v”)


val pb_fac_exists' = proved_th $ 
e0
(rpt strip_tac  >> last_x_assum mp_tac >> rw[ispb_def] >> arw[] >> 
 strip_tac >>
 first_x_assum (qspecl_then ["A","u","v"] assume_tac)  >>
 pop_assum strip_assume_tac >> qexistsl_tac ["a"] >> 
 first_x_assum (qspecl_then ["a"] assume_tac) >> arw[])
(form_goal “!X Z f:X->Z Y g:Y->Z Pb p:Pb->X q:Pb->Y.ispb(f:X->Z,g:Y->Z,p,q) ==> 
 !A u v. f o u = g o v ==> ?a:A->Pb. p o a = u & q o a = v”)

val f = rapf "f:X->Z o u:A->X = g:Y->Z o v:"
val th = form
basic_fconv

e0
(strip_tac >> once_arw[])
(form_goal “a = b ==>!a. a = c”)

val th0 =assume “x:C->B = y”
(“!x:C->B.x = pa(p1,p2,f,g)” |> once_depth_fconv (rewr_conv th0) all_fconv)

val zero_no_mem = proved_th $
e0
(ccontra_tac >> pop_assum strip_assume_tac >> 
 strip_assume_tac ax8 >> suffices_tac (rapf "x1:1->X = x2") 
 >-- arw_tac[] )
(rapg "~?f:1->0.T")

val iso_to_same = proved_th $
e0
(strip_tac >> by_tac (rapf "areiso(A,Y)")
 >-- (once_rw_tac[iso_symm] >> arw_tac[]) >>
 match_mp_tac (ir_canon iso_trans))
(rapg "areiso(X,A) & areiso(Y,A) ==> areiso(X,Y)")

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
>-- (by_tac (rapf " to1(A, 1) o (x0:1->A) = to1(B, 1) o x0'") 
    >-- once_rw_tac[to1_unique])
 (*
>-- ((*by_tac (rapf " to1(A, 1) o (x0:1->A) = to1(B, 1) o x0'") TODO: do not understand why cannot use rw to1_unique to solve this by*)
      assume_tac (specl (List.map rastt ["1","id(1)","to1(A, 1) o (x0:1->A)"]) to1_unique) >>  assume_tac (specl (List.map rastt ["1","id(1)","to1(B, 1) o (x0':1->B)"]) to1_unique)>>
  arw_tac[] >> rw_tac[idR]) >>
suffices_tac (rapf "copa(i1:A->AB, i2:B->AB, ((one1:1->oneone) o to1(A, 1)), ((one2:1->oneone) o to1(B, 1))) o i1 o (x0:1->A) = copa(i1, i2, (one1 o to1(A, 1)), (one2 o to1(B, 1))) o i2 o x0'") 
>-- (rw_tac[GSYM o_assoc] >> arw_tac[]) >>
arw_tac[] *)
)
(rapg "!A B AB i1:A->AB i2:B->AB. iscopr(i1,i2) ==> !x0:1->A x0':1->B.~i1 o x0 = i2 o x0'")

e0
(rw_tac[iscoeq_def] >> repeat strip_tac >> exists_tac (rastt "x:B->X") >> 
 strip_tac >> rw[idR])
(rapg "iscoeq(id(B),f:A->B,f:A->B)")

val to1_unique0 = specl [rastt "X",rastt "f:X->1"] eq_to1 |> GSYM 
                       |> trans (specl [rastt "X",rastt "g:X->1"] eq_to1) 
                       |> allI ("f",mk_ar_sort (mk_ob "X") one)
                       |> gen_all



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
 dimp_tac >> strip_tac >> arw_tac[] >> pop_assum_list (map_every strip_assume_tac) )
(rapg "!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y. ispb(f, g, p, q) <=> f o p = g o q & !A u : A -> X v : A -> Y. f o u = g o v ==> ?a : A -> P. p o a = u & q o a = v & !a1 : A -> P a2:A->P. p o a1 = u & q o a1 = v& p o a2 = u & q o a2 = v ==> a1 = a2")




f:A->B
A,B
------
P(A)


f:A->B
B
------
!A.P(A)

val f0 = rapf "!a. a = b"

val thm0 = assume (rapf "a = b")

fun forall_fconv fc' f' = 
    case view_form f' of
        (vQ("!",n,s,b)) => 
        forall_iff (n,s) $ fc' (subst_bound (mk_var n s) b)
      | _ => raise ERR ("forall_fconv.not an all",[],[],[f'])


e0
(rpt strip_tac >> irule prop_2_corollary_as_subobj >> arw[]>>
 drule pb_mono_mono >> 
 qspecl_then ["two","i2"] assume_tac dom_1_mono >>
 first_x_assum drule >> arw[] >>
 rpt strip_tac (* 2 *) >-- 
 (by_tac 
   (rapf "?y:1->Pb. pb1:Pb->X o y = a:A->X o x:1->A & pb2:Pb->1 o y = id(1)") >--
  (irule pb_fac_exists' ) 
  ) )
(form_goal
“!A X a.ismono(a:A->X) ==> 
 !two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !Pb pb1 pb2. ispb(char(i1,i2,a),i2,pb1,pb2) ==> 
    ?h1 h2.pb1 o h1 = a & a o h2 = pb1 & h1 o h2 = id(Pb) & h2 o h1 = id(A)”)


e
(strip_tac >> rw[]) ( new_goalstack (fvf f,[],f))
(form_goal “(!A B a:A->B.~ismono(a)) ==> ismono(b:A->B)”)

rapf' "~!X e1 : X -> X  e2 : X -> X. ~~e1 = e2" basic_fconv

