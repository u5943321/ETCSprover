
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

todo list:

(*(pick_x_assum “ispr(Ap:AP->P, aP:AP->A)” mp_tac) if the input not in the asumption list, then HOL error instead of pick x assum err TODO*)

(*?C P PQ Q (pC : ANB -> C#)  (pP : PQ -> P)  (pPQ : ANB -> PQ)
               (pQ : PQ -> Q). pC o l o
                 pa(Ap, aP, pA,
                  pa(Na2b, nA2B, id(N), tp(p1, p2, ev, pA, pN, f)) o pN) =
               pC o pa(pAN, pB, id(AN), f) & ispr(pPQ, pC) & ispr(pP, pQ) &
               pP o pPQ o l o
                 pa(Ap, aP, pA,
                  pa(Na2b, nA2B, id(N), tp(p1

TO-DO: huge ppbug!*)


(*TODO: if in exists, feed "copa(i1,i2,i2:1->two o to1(A,1),i1:1->two o to1(A',1)) o f':X->AA'", is wrong ,but get wrong error message*)

(*TODO, if input of f' o x is f o x, which is wrong , the error message is err find, not the q parsing*)



(*TODO: irule bug!
qsuff_tac ‘m o e o r' =
               pa(Ar2, aR2, x, tp(p1', p2', ev', pR, pone', psi o pR))’
     >-- (strip_tac >> first_x_assum drule >> 
         first_x_assum (qspecl_then ["two","i1","i2"] assume_tac) >>
         first_x_assum drule >> first_x_assum accept_tac)

exception find! and need qspecl, drule directly does not work, means that it does not find copr i1 i2 in assum
*)

(*for bar_exists, too many paramaters and I just want to use existence.*)

(*TODO: if give wrong input here then wrong err message:
(x_choosel_then ["AA","pA1","pA2"] assume_tac) pr_ex >>
pexistsl_tac ["tp(p1:AA2->A,p2:AA2->A2,ev:AA2->two,pA1:AA->A,pA2:AA->A,char(i1,i2,pa(pA1,pA2,id(A),id(A))))"]

match_term.unexpected term constructor
*)



AQ: view_form (rapf "?(p1 : NN -> N)  (p2 : NN -> N). ispr(p1, p2)"); reason  to discard view_form stuff?

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

(*TO-DO:
(?(x0 : 1 -> LT). (ne o ltne) o x0# = x)
             <=>
             ?(x0 : 1 -> LT). (le o ltle) o x0# = x
so where is the problem..
?
*)

val th0 = read_axiom "ne o ltne = le o ltle"
e0
(assume_tac (th0) >> arw[])
(form_goal
“(?(x0 : 1 -> LT). (ne o ltne) o x0 = x)
             <=>
             ?(x0 : 1 -> LT). (le o ltle) o x0 = x”)

(*TODO: why slow?

if instead of the first_x_assum irule, use  (*qsuff_tac ‘!n0:1->N. ~char(i1, i2, lt) o pa(Nn, nN, n0, z) = i2’ *) then no output and stuck there.

in  suffices_tac “isiso(q:Q->N)”, can use irule o_epi_imp_epi, but give the wrong thing.
*)


(*TODO: a version of GSYM top-down*)


(*TODO: a tool su we can only inst the arrows once the sorts are correct, to avoid one by one for pb_ex*)



(*TODO: should eliminate the x0:

~(?(x0 : 1 -> 1). pa(Tt, tT, p1, p2) = pa(Tt, tT, i2, i1))

AQ: tactic for this? can have a rw thm that 

(?f:A->A. P(a) <=> Q(a)) <=> P(a) <=> Q(a), if f is not mentioned in P and Q
*)



val Thm6_lemma_3 = proved_th $ val (ct,asl,w) = cg $
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


!i:A->B. (!X f:A->X. ?f0:B->X. f = f0 o i) ==>
!X. (!f:A->X. P(f)) <=> (!f0:B->X. P(f0 o i))

!j:B->A. (!X f:X->A. ?f0:X->B. f = i o f0) ==>
(?f:A->X. P(f)) <=> (?f0:B->X. P(i o f0))


(*
have !X ?f:X->1. !f':X->1. f' = f

i:1->A. j:A->1. i o j = id(A) j o i = id(1)

want !X ?f:X->A. !f':X->A. f' = f

strip: X :Ob |- ?f:X->A. !f':X->A. f' = f

have for the isomorphism i:1->A, have 
!f:X->A. ?f0:X->1. f = i o f0.

therefore, 

!j:B->A. (!X f:X->A. ?f0:X->B. f = i o f0) ==>
(?f:A->X. P(f)) <=> (?f0:B->X. P(i o f0))

applies, can rw the goal into:

X:Ob |- ?f0:X->1.!f':X->A. f' = j o f0


then rw the goal into:

X:Ob |- ?f0:X->1.!f0':X->1. j o f0' = j o f0.

have by assumption:

X:Ob |- ?f:X->1. !f':X->1. f' = f.

strip assum and put in assumption get the goal into

X:Ob f:X->1 !f':X->1. f' = f |- ?f0:X->1.!f0':X->1. j o f0' = j o f0.

qexists with the f0 to be f, the goal becomes:

X:Ob f:X->1 f0:X->1 f0':X->1. (!f':X->1. f' = f) |- j o f0' = j o f0.

rw with assumption and solve.



*)

(*
AQ deserve to have tools qspec which only need to plug arrow terms?/ drule w/ cont? or such thing are of bad style?
*)




(a + b) * c
AQ1:
and other pp formating stuff.


 rapf "~(p o sub o pa(Nn, nN, n0, n) = z & ~n0 = s o n)"

make 

 "~p o sub o pa(Nn, nN, n0, n) = z & ~n0 = s o n"

the not on the outmost is for the whole, the whole is not a conjunction!

AQ2: deserve to have tools qspec which only need to plug arrow terms?/ drule w/ cont? or such thing are of bad style? what is good style? Does there exists anyvalue to force the user to write the proof in good style? is "good style" means that the proof is readable without runing it?

pick_xnth_assum 

good style means need minor change after changing things.


!A B f:A->B C D g:C->D
--------
qspecl_then ["f:A->B","g:C->D"]

spec 


AQ3:hope for get induction along isos? seems that our system has no particularadvantage of doing this.

AQ4:
 should not allow this to happen?


 mk_forall "x" (mk_ar_sort one N) $ mk_eq
 (rastt 
 "pa(Tt:TT->two, tT:TT->two, char(i1:1->two, i2:1->two, le), (char(i1, i2, p0:P->N) o Nn)) o pa(Nn, nN, x, n:1->N)")
 (rastt 
 "pa(Tt:TT->two,tT:TT->two, char(i1:1->two, i2:1->two, le) o pa(Nn, nN, x:1->N, n:1->N),p0 o n)")
second p0 is of different type of the first one, it is two->N

not a problem

maybe add warning!

AQ5:should induction be made automatic, and can do rpt induct_tac, as in HOL?


AQ6:trick for capture error message, at least  should not have HOL error anywehre. some times error message comfusing

if give wrong input here then wrong err message:
(x_choosel_then ["AA","pA1","pA2"] assume_tac) pr_ex >>
pexistsl_tac ["tp(p1:AA2->A,p2:AA2->A2,ev:AA2->two,pA1:AA->A,pA2:AA->A,char(i1,i2,pa(pA1,pA2,id(A),id(A))))"]

match_term.unexpected term constructor 

catch an reraise exception

AQ7:comprehension: have already get 2 examples of constructing subsets by predicates, seems a bit routine, therefore, should we mkake attempt to automatic on this?

if work on this, may can test list object exists.

list objects induct_tac 

finite set type is a quotient of lists.

appending two lists is taking the union of two finite sets.

AQ8:have goals like this:

qby_tac ‘q0 o a' = u & p0 o a' = v <=> p0 o a' = v & q0 o a' = u’

may need conv_tac land_conv with conj_comm. is there an

AQ9:pb_reorder very slow, find may proofs about pb are slow.


val pb_exists''' = proved_th $ (*val (ct,asl,w) = cg $*)
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
(rapg "!X Z f:X->Z Y g:Y->Z.?P p0:P->X q. ispb(f,g,p0,q)")


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
 (*TODO: AQ: how to automatic on this?
may have conv tac with land conv, but how shu=ould my land conv be look like, <=> is not an operator, so it may looks like:

fun land_conv "<=>" fc f = dimp_iff ...
    land_conv "&" fc f = conj_iff ...

tland_conv & fland_conv eq_fsym for tland.

*)
 qby_tac ‘q0 o a' = u & p0 o a' = v <=> p0 o a' = v & q0 o a' = u’ >--
 (dimp_tac >> disch_tac >> arw[] >>
  fs[]) >>
 arw[]
)
(form_goal
“!X Z f:X->Z Y g:Y->Z P p0:P->X q0:P->Y.ispb(f,g,p0,q0) ==>
 ispb(g,f,q0,p0)”)


TODO: pp goals just like pp thms (avoid add newlines if possible. )

TODO: ppbug:  ev o pa(p1, p2, p1, (tp(p1, p2, ev, p1, p2, (neg o ev)) o p2)) o





val nt_def = const2_def |> eqT_intro |> iffRL 
                       |> ex2fsym "nt" [] |> C mp (trueI [])

val t_def = nt_def |> eqT_intro |> iffRL 
                    |> ex2fsym "t" [] |> C mp (trueI [])

val t = mk_fun "t" []

val Chi_ex = proved_th $
e0
(rpt strip_tac >> assume_tac t_def >>
 drule char_def >> first_x_assum drule >>
 qexists_tac "char(nt,t,a)" >> arw[])
(form_goal
“!A X a:A->X. ismono(a) ==>
 ?chi.!x:1->X.(?x0:1->A.a o x0 = x) <=> 
  (chi o x = t)”)

val two = mk_fun "2" []

val _ = new_fun "Chi" (mk_ar_sort (mk_ob "X") two,[("a",mk_ar_sort (mk_ob "A") (mk_ob "X"))])

val Chi_def = read_axiom
"!A X a:A->X. ismono(a) ==>!x:1->X.(?x0:1->A.a o x0 = x) <=> (Chi(a) o x = t)"

fun dest_o t = 
    case (view_term t) of
        vFun("o",s,[t1,t2]) => (t1,t2)
      | _ => raise ERR ("not a composition: ",[],[t],[])

fun is_el t = 
    case (view_sort (sort_of t)) of
        va(d,c) => if eq_term(d,one) then true else false
      | _ => false

fun is_chi t = 
    case view_term t of
        vFun("chi",s,tl) => true
      | _ => false

fun chi_eqn f = 
    let val (l,r) = dest_eq f 
        val _ = eq_term(r,t) orelse
                raise ERR ("RHS is not t",[sort_of r],[r],[])
        val (a1,a2) = dest_o l
        val _ = is_el a2 orelse 
                raise ERR ("pred not applied to an element",[sort_of a2],[a2],[])
    in is_chi t
    end

AQ: should I write like this?

AQ: while proving the iff between the built predicate and the 

fun chi_of_chi_eqn f = 
    let val (l,r) = dest_eq f
    in fst (dest_o l)
    end

val twotwo_def = pr_ex |> allE two |> allE two |> eqT_intro
                      |> iffRL |> ex2fsym "twotwo" [] |> C mp (trueI [])


val two1_def = twotwo_def |> eqT_intro
              |> iffRL |> ex2fsym "two1" [] |> C mp (trueI [])

val two2_def = two1_def |> eqT_intro
              |> iffRL |> ex2fsym "two2" [] |> C mp (trueI [])

val two1 = mk_fun "two1" []
val two2 = mk_fun "two2" []

val cj_ex = proved_th $
e0
(cheat)
(form_goal
“?cj. !p1 p2.cj o pa(two1,two2,p1,p2) = t <=> 
 p1 = t & p2 = t”)

val cj_def = cj_ex |> eqT_intro
             |> iffRL |> ex2fsym "cj" [] |> C mp (trueI [])

val cj = mk_fun "cj" []


val dj_ex = proved_th $
e0
(cheat)
(form_goal
“?dj. !p1 p2.dj o pa(two1,two2,p1,p2) = t <=> 
 p1 = t | p2 = t”)

val dj_def = dj_ex |> eqT_intro
             |> iffRL |> ex2fsym "dj" [] |> C mp (trueI [])

val dj = mk_fun "dj" []



val ip_ex = proved_th $
e0
(cheat)
(form_goal
“?ip. !p1 p2.ip o pa(two1,two2,p1,p2) = t <=> 
 p1 = t ==> p2 = t”)

val ip_def = ip_ex |> eqT_intro
             |> iffRL |> ex2fsym "ip" [] |> C mp (trueI [])

val ip = mk_fun "ip" []


val dimp_ex = proved_th $
e0
(cheat)
(form_goal
“?dimp. !p1 p2.dimp o pa(two1,two2,p1,p2) = t <=> 
 (p1 = t <=> p2 = t)”)

val dimp_def = dimp_ex |> eqT_intro
             |> iffRL |> ex2fsym "dimp" [] |> C mp (trueI [])

val dimp = mk_fun "dimp" []

val _ = new_fun "Chi" (mk_ar_sort (mk_ob "X") two,[("a",mk_ar_sort (mk_ob "A") (mk_ob "X"))])

val Chi_def = read_axiom
"!A X a:A->X. ismono(a) ==>!x:1->X.(?x0:1->A.a o x0 = x) <=> (Chi(a) o x = t)"

fun is_pred_ar a = 
    eq_term(snd $ dest_ar (sort_of a),two)



fun extract_pred f = 
    let val (l,r) = dest_eq f 
        val _ = eq_term(r,t) orelse
                raise ERR ("RHS is not t",[sort_of r],[r],[])
        val (a1,a2) = dest_o l
        val _ = is_el a2 orelse 
                raise ERR ("pred not applied to an element",[sort_of a2],[a2],[])
        val _ = is_pred_ar a1 orelse 
                raise ERR ("not an application of a pred",[sort_of a1],[a1],[])
    in a1
    end

val _ = new_fun "pr1" (mk_ar_sort (mk_ob "A") (mk_ob "B"),[("A",ob),("B",ob)]



fun mk_pa p1 p2 a1 a2 = mk_fun "pa" [p1,p2,a1,a2] 



val U_ex = proved_th $
e0
cheat
(form_goal
“!X.?U : exp(X,2)  -> 2.
 !Y.!pxy : X * Y -> 2 y:1->Y.
  Uq o tp(pxy) o y = t <=>
 !x : 1 -> X. pxy o pa(x,y) = t”)


fun split_input longp x = 
(*dj o pa(two1,two2,p1 o <m,n>,p2 o <n,m>) = 
  dj o pa(two1,two2,p1 o <nN,Nn>, p2) o <n,m>
conj o <dj o pa(two1,two2,p1 o <m,n>,p2 o <n,m>),
        imp o pa(two1,two2,p3 o <m,n>,p4 o <n,m>)>

takes a map 1->2 and an element x, and split it so it is an application of a pred on the pair (x,y), where y may br a tuple itself
*)

input : !m n. char(lt) o (m,n) = t | char(le) o (n,m) = t
output: (pred, |- !m. (pred o m = t <=> !n. char(lt) o (m,n) = t | char(le) o (n,m) = t))

fun pred_of f = 
    case (view_form f) of
        vPred(_,_) =>
        (fst $ dest_eq f,frefl f)
      | vConn("&",[f1,f2]) =>
        let val (p1,th1) = pred_of f1
            val (p2,th2) = pred_of f2
        in (mk_o cj (mk_pa two1 two2 p1 p2),cj_def |> allE p1 |> allE p2 |> GSYM)
        end
      | vConn("|",[f1,f2]) =>
        let val (p1,th1) = pred_of f1
            val (p2,th2) = pred_of f2
        in (mk_o dj (mk_pa two1 two2 p1 p2),dj_def |> allE p1 |> allE p2 |> GSYM)
        end
      | vConn("==>",[f1,f2]) =>
        let val (p1,th1) = pred_of f1
            val (p2,th2) = pred_of f2
        in (mk_o ip (mk_pa two1 two2 p1 p2),ip_def |> allE p1 |> allE p2 |> GSYM)
        end
      | vConn("<=>",[f1,f2]) =>
        let val (p1,th1) = pred_of f1
            val (p2,th2) = pred_of f2
        in (mk_o dimp (mk_pa two1 two2 p1 p2),dimp_def |> allE p1 |> allE p2 |> GSYM)
        end
      | vQ("!",x,s0,b) =>
        let val (p0,th0) = pred_of b 
            val X = snd $ dest_ar s0
            val (x,y,pxy) = split_input (x,s0) p0
            val p = mk_o (Uq X) $ mk_o (tp pxy) y
        in (p,U_ex |> allE pxy |> allE y)
        end


pxn:XN->2 o <x:1->X,n:1->N,y:1->Y>  = (pxn o <x o to1(N,1),id(N)>):N->2 o n:1->N

exp(x,n)
N * N -> N

prove

0 < n^n

lt o exp 

le o <n + 3,m> = t

(le o <s o s o s,m o to1(N)>) o n

f = f' o n 

g = g' o n



f o g = f' o n:1->N o g' o n

<n:1->N,x:1->X> 

P o Q

UNBETA_CONV;


fun f 

(*pred_of f will output a pred such that

pred_of ``p1:X->2 o x:1->X = t <=> p2:Y->2 o y:1->Y = t``;
val it =
   (dimp o pa(two1, two2, p1 o x, p2 o y),
    {(X : ob), (Y : ob), (p1 : X -> 2), (p2 : Y -> 2), (x : 1 -> X),
     (y : 1 -> Y)}, 
    |- (p1 o x = t <=> p2 o y = t) <=>
       dimp o pa(two1, two2, p1 o x, p2 o y) = t): term * thm

output (dimp o pa(two1, two2, p1 o Nn, p2 o nN)) o 
pa(n,m) 

and (dimp o pa(two1, two2, p1 o Nn, p2 o nN)) o 
pa(n,m) <=> p1(n) <=> 
 *)


(*take a formula f which corresponds a predicate about a variable n:1->N., return a pred such that for every argument n:1->N, pred o n = t <=> .../

firstly, collect the only free variable m:1->N. to induct on.

if f is char(even) o n = i2, then pred is just char(even) since
!n. char(even) o n = i2 <=> char(even) o n = i2

if f is !n. char(lt) o pa(m,n) = i2 | char(le) o pa(n,m) 
return a pred such that 
!m (!n. char(lt) o pa(m,n) = i2 | char(le) o pa(n,m)) <=>
 pred o m

case f of 
Quant("!",n,s,f0) => 
let val (pred0,th) = pred_of f0 
Uq o tp(p1:N * Omega^N,p2,)

 *)


quick questions : () pp, slow pb.

(*induct_tac procedure:
want to prove by induction that
!m n. char(lt) o (m,n) = t | char(le) o (n,m) = t

should I have lt(m,n) instead? but anyway during the procedure it will be unwinded into the "= t"-form.

Step 1:

prove that 
“!m. (!n. char(lt) o (m,n) = t | char(le) o (n,m) = t)
 <=> pred o m = t” for some pred, where the pred is constructed from the pred_of (!n. char(lt) o (m,n) = t | char(le) o (n,m) = t)

Step 2: 
rw the goal with the thm produced in Step 1, in the example, the goal:
!m n. char(lt) o (m,n) = t | char(le) o (n,m) = t
is rw into:

!m. pred o m = t.

Step 3 (*not only for induction which does not involve othere variables, but the ones with other variables can just be turned into the one which does not consider x as an argument, but a constant.

for instance, “pred:X * N -> 2 o <x,n>” can be turned into 
pred o <x o to1(N), id(N)> o n

any reference to HOL about normalisation in this flavor?

rw the goal according to ind_principle_elements, so the goal, in this example, becomes:

pred o z = t & (!m0. pred o m0 = t ==> pred o suc o m0 = t)

Step 4: by the theorem produced in Step 1, with opposite direction, which is:
“!m. pred o m = t <=> (!n. char(lt) o (m,n) = t | char(le) o (n,m) = t)”
rw the goal back into:

(!n.char(lt) o <z,n> = t) &
(!m0. (!n.char(lt) o <m0,n> = t | char(le) o <m0,n> = t) ==>
 (!n.char(lt) o <s o m0,n> = t | char(le) o <s o m0,n> = t) )

automatically strip or not?

if rpt induct_tac, then in the first conjunct, the induction is for n, the second one is for m0.

*): 

induct_conv first, and fconv_tac with it.

*)



fun induct_tac (ct,asl,w) = 
    let val ((n,s),f) = dest_forall w
        val (p0,th0) = pred_of f
        val th = allI (n,s) th0
        (*th is of form !n. f (n) <=> pred o n = t*)
    in rw_tac[th] >> 

val _ = new_fun "*"(mk_ob_sort,[("A",mk_ob_sort), ("B",mk_ob_sort)])

fun fxty i = 
    case i of 
       "<=>" => 100
      | "==>" => 200
      | "|" => 300
      | "&" => 400
      | "=" => 450
      | "o" => 455
      | ":" => 460 (*900*)
      | "->" => 470 (*900*)
      | "+" => 500
      | "*" => 600
      | "^" => 700
      | "~" => 900
      | _ => ~1

form_goal
“!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y. ispb(f, g, p, q) <=> f o p = g o q & !A u : A -> X v : A -> Y. f o u = g o v ==> ?a : A -> P. p o a = u & q o a = v & !a1 : A -> P a2:A->P. p o a1 = u & q o a1 = v& p o a2 = u & q o a2 = v ==> a1 = a2”

parse_ast $ lex "!X Z f:X -> Z Y g : Y -> Z  P p : P -> X q : P -> Y.\
      \ ispb(f, g, p, q) <=> \
      \  f o p = g o q & \
      \  !A u : A -> X v : A -> Y. \
      \        ?a : A -> P. p o a = u & q o a = v & !a1 : A -> P a2:A->P. p o a1 = u & q o a1 = v& p o a2 = u & q o a2 = v ==>
 a1 = a2"

rapf "!X P p : P -> X A u : A -> X a1 : A -> P. p o a1 = u"

parse_ast $ lex
 "!X P p : P -> X A u : A -> X a1 : A -> P. p o a1 = u"

rapf
 "!a1 : A -> P. p0 o a1 = u"



P ->X A ->P


 parse_ast $ lex "(f0x:0->X) o f:A->0";
val it =
   (aInfix
     (aInfix
       (aInfix
         (aInfix (aInfix (aId "f0x", ":", aId "0"), "->", aId "X"), "o",
          aId "f"), ":", aId "A"), "->", aId "0"), []): ast * token list

if use the prec 900 instead, need to write f: (A * B) ->X. 

f:A * B->X is not parsable


val ax_2el = read_axiom "?X x1: 1 -> X x2: 1 -> X. ~(x1 = x2)"

need () around (x1 = x2), desired effect?

cannot write (rastt "f':0->1 o f:1->0")


if rapf "ce o f = ce:B->cE o (g:A->B)"

# Exception-
   TER
     ("match_term.match_sort.cannot match ob with ar: ",
      [ar (Var ("B", ob), Var ("C", ob)), ob],
      [Var ("f", ar (Var ("B", ob), Var ("C", ob))), Var ("cE", ob)]) raised

need
rapf "ce o f = (ce:B->cE) o g:A->B"

previously, can write "s o pN':NB'->N", now cannot

previously can write “!n:1->N. ~ s o n = z”

now cannot

“a:bool /\ P (c:β ->γ o b:α ->β)”

works in HOL. but not in mine,

tired of fixing it, want to do it as HOL.

TODO: ppbug:  ev o pa(p1, p2, p1, (tp(p1, p2, ev, p1, p2, (neg o ev)) o p2))

``A = A``;
val it = A = A: form
> dest_eq it;
val it = (A, A): term * term
> fst it;
val it = A: term
> sort_of it;
val it = ob: sort



rastt " pa(p1, p2, p1, (tp(p1, p2, ev, p1, p2, (neg o ev)) o p2))";
val it = pa(p1, p2, p1, tp(p1, p2, ev, p1, p2, (neg o ev)) o p2): term
> rastt " tp(p1, p2, ev, p1, p2, (neg o ev))";
val it = tp(p1, p2, ev, p1, p2, neg o ev): term
similar a qexists tac such that deal with:

 ?A' AX (p1' : AX# -> A'#)  (p2' : AX# -> 1)  B' efs' (ev' : efs'# -> B'#)
             (p1' : efs'# -> A'#)  (p2' : efs'# -> A2B).
               ev'# o
                 pa(p1'#, p2'#, p1'#, (tp(p1, p2, ev, pA, pN, f) o z) o p2'#) =
                 ev'# o
                 pa(p1'#, p2'#, p1'#, tp(p1, p2, ev, pA', pone, (g o pA')) o
                  p2'#) & isexp(p1'#, p2'#, ev'#) & ispr(p1'#, p2'#)

Thm1_comm_eq_left is above


ev_eq_eq in the proof of f0g_eq_f1g

Thm6_first_sentence in Thm6
