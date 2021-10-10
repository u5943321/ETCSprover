
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
