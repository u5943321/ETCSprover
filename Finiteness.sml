
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



val Ins_def = 
    Ins_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Ins" ["x","s0"]
           |> C mp (trueI []) |> gen_all


val Ins_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM Ins_def,GSYM Insert_def,Ev_of_Tp] >> rw[Ev_of_Tp_el,Pa_distr,o_assoc,DISJ_def,pi31_def] >> rw[pi31_of_Pa,pi32_of_Pa] >> 
(qspecl_then ["X","1","x","x0"] mp_tac) $ GSYM Eq_property >> once_rw[True1TRUE] >> 
 strip_tac >> arw[] >> rw[pi33_of_Pa]
)
(form_goal
 “!X x0:1->X s0:1->Exp(X,2).
  !x:1->X. Ev(X,2) o Pa(x,Ins(x0,s0)) = TRUE <=> 
  (x = x0 | Ev(X,2) o Pa(x,s0) = TRUE)”);


val fst_conjunct = 
rastt $ q2str 
‘Ev(Exp(X,2),2) o Pa(π42(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),π44(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)) )’


val snd_conjunct = 
rastt $ q2str
‘Eq(Exp(X,2)) o Pa(π43(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),
 Ins(π41(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),
     π42(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2))))’



val trd_conjunct = 
rastt $ q2str
‘NEG o Ev(X,2) o Pa(π41(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),π42(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)))’



val from4_pred0 = 
mk_o CONJ $
 Pa trd_conjunct (mk_o CONJ (Pa fst_conjunct snd_conjunct))



val Ex_x_from4_pred = 
 mk_o (Ex (mk_ob "X")) (Tp from4_pred0)
 
val Ex_s0_Ex_x_from4_pred = 
mk_o (rastt "Ex(Exp(X,2))") (Tp Ex_x_from4_pred)

val required_map2 = Tp Ex_s0_Ex_x_from4_pred


val map2_ex = proved_th $
e0
(exists_tac required_map2 >> rw[])
(form_goal
$ mk_exists "m2" (sort_of required_map2)
(mk_eq required_map2 (rastt "m2:Exp(Exp(X, 2), 2) -> Exp(Exp(X, 2), 2)")) 
)


val map2_def = 
    map2_ex |> eqT_intro
            |> iffRL |> ex2fsym "map2" ["X"]
            |> C mp (trueI []) |> gen_all


val required_map1 =
Tp (rastt $ q2str
‘Eq(Exp(X,2)) o Pa(id(Exp(X,2)),Empty(X) o To1(Exp(X,2))) o 
 π1(Exp(X,2),1)’)

val map1_ex = proved_th $
e0
(exists_tac required_map1 >> rw[])
(form_goal
$ mk_exists "m1" (sort_of required_map1)
(mk_eq required_map1 (rastt "m1:1 -> Exp(Exp(X, 2), 2)")) 
)


val map1_def = 
    map1_ex |> eqT_intro
            |> iffRL |> ex2fsym "map1" ["X"]
            |> C mp (trueI []) |> gen_all



val card0 = Nind (rastt "map1(X)") (rastt "map2(X)")


val hasCard =
mk_o (rastt "Ev(Exp(X,2),2)") 
(Pa (rastt "π1(Exp(X,2),N)")
 (mk_o card0 (rastt "π2(Exp(X,2),N)")))



val contain_empty = 
mk_o (rastt "Mem(Exp(X,2))") $
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
 Pa(Ins(π31(X,Exp(X,2),Exp(Exp(X,2),2)),
           π32(X,Exp(X,2),Exp(Exp(X,2),2))),
π33(X,Exp(X,2),Exp(Exp(X,2),2))))’

val longpred0 = 
mk_o (rastt "All(Exp(X,2))") $ Tp (mk_o IMP (Pa longpred_ant longpred_conc))

val longpred = 
mk_o CONJ (Pa contain_empty longpred0)

val bigset = Tp1 longpred



val BIGINTER_ex = proved_th $
e0
(*?(biX : Exp(Exp(X#, 2), 2) -> Exp(X#, 2))*)
(strip_tac >> qex_tac ‘Tp (All(Exp(X,2)) o Tp(IMP o Pa
 (Ev(Exp(X,2),2) o 
  Pa(π31(Exp(X,2),X,Exp(Exp(X,2),2)),
     π33(Exp(X,2),X,Exp(Exp(X,2),2))),
  Ev(X,2) o 
  Pa(π32(Exp(X,2),X,Exp(Exp(X,2),2)),
     π31(Exp(X,2),X,Exp(Exp(X,2),2))))  ))’ >> rw[])
(form_goal
“!X.?biX.
 Tp (All(Exp(X,2)) o Tp(IMP o Pa
 (Ev(Exp(X,2),2) o 
  Pa(π31(Exp(X,2),X,Exp(Exp(X,2),2)),
     π33(Exp(X,2),X,Exp(Exp(X,2),2))),
  Ev(X,2) o 
  Pa(π32(Exp(X,2),X,Exp(Exp(X,2),2)),
     π31(Exp(X,2),X,Exp(Exp(X,2),2))))  )) = biX ”)


val BIGINTER_def = 
BIGINTER_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "BIGINTER" ["X"] 
            |> C mp (trueI []) |> gen_all

val BIGINTER_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM BIGINTER_def] >>
 rw[Ev_of_Tp_el] >> rw[o_assoc,All_def] >> 
 rw[Pa_distr,IMP_def] >>
 rw[o_assoc,Pa_distr,pi33_of_Pa,pi31_of_Pa,pi32_of_Pa])
(form_goal
 “!X ss:1->Exp(Exp(X,2),2) x:1->X.
  Ev(X,2) o Pa(x,BIGINTER(X) o ss) = TRUE <=> 
  !s0:1-> Exp(X,2). Ev(Exp(X,2),2) o Pa(s0,ss) = TRUE ==>
   Ev(X,2) o Pa(x,s0) = TRUE”)


val finites = 
mk_o (rastt "BIGINTER(Exp(X,2))") bigset

val isFinite_subset = 
mk_o (mk_o (rastt "Ev(Exp(X,2),2)") 
(Pa (rastt "π1(Exp(X,2),1)") (mk_o finites (rastt "π2(Exp(X,2),1)")))) (rastt "Pa(id(Exp(X,2)),To1(Exp(X,2)))")

(*fun Exp A B = mk_fun "Exp" [A,B]*)

val isFinite_ex = proved_th $
e0
(strip_tac >> 
 exists_tac isFinite_subset >> rw[])
(form_goal $
mk_forall "X" ob_sort
 (mk_exists "f" (ar_sort (Exp (mk_ob "X") two) two)
  (mk_eq isFinite_subset (rastt "f:Exp(X,2) -> 2")))
);

val isFinite_def = 
isFinite_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "isFinite" ["X"] 
            |> C mp (trueI []) |> gen_all;




val isFinite_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM isFinite_def] >>
rw[o_assoc,Pa_distr,idL,pi1_of_Pa] >>
rw[BIGINTER_property] >> 
rw[pi2_of_Pa] >> rw[GSYM Tp1_def] >>
rw[Ev_of_Tp_el] >> rw[o_assoc,CONJ_def,Pa_distr] >>
rw[pi1_of_Pa,idL] >> rw[All_def] >>
rw[o_assoc,Pa_distr] >> rw[IMP_def] >>
rw[All_def] >> rw[o_assoc,Pa_distr] >>
rw[Pa3_def] >> rw[pi32_of_Pa3,pi33_of_Pa3] >>
rw[GSYM Ins_def] >> rw[Pa_distr,o_assoc] >>
rw[pi31_of_Pa3,pi32_of_Pa3] >>
rw[GSYM Mem_def] >> once_rw[one_to_one_id] >> rw[idR]
)
(form_goal
“!X a:1->Exp(X,2). isFinite(X) o a = TRUE <=>
!P: 1-> Exp(Exp(X,2),2). 
 Ev(Exp(X,2),2) o Pa(Empty(X),P) = TRUE &
 (!s0:1-> Exp(X,2). Ev(Exp(X,2),2) o Pa(s0,P) = TRUE ==>
   !e:1->X.Ev(Exp(X,2),2) o Pa(Ins(e,s0),P) = TRUE) ==>
 Ev(Exp(X,2),2) o Pa(a,P) = TRUE
 ”);



val isFinite_property1 =proved_th $
e0
(rw[isFinite_property] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (first_x_assum (qspecl_then ["Tp1(P)"] assume_tac) >>
  fs[GSYM Tp1_def,Ev_of_Tp_el',o_assoc,pi1_of_Pa] >>
  first_x_assum irule >> arw[]) >>
 rw[Ev_of_el] >> first_x_assum irule >>
 fs[Ev_of_el]
 )
(form_goal 
 “!X a:1->Exp(X,2). isFinite(X) o a = TRUE <=> !P:Exp(X,2) ->2.
 P o Empty(X) = TRUE &
 (!s0:1-> Exp(X,2). 
  P o s0 = TRUE ==> !e:1->X.P o Ins(e,s0) = TRUE) ==>
 P o a = TRUE
 ”)



val hasCard_ex = proved_th $
e0
(strip_tac >> 
 exists_tac hasCard >> rw[])
(form_goal $
mk_forall "X" ob_sort
 (mk_exists "f" (ar_sort (Po (Exp (mk_ob "X") two) N) two)
  (mk_eq hasCard (rastt "f:Exp(X,2) * N -> 2")))
)


val hasCard_def = 
hasCard_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "hasCard" ["X"] 
            |> C mp (trueI []) |> gen_all

val _ = new_pred "FINITE" [("X",ob_sort)]

val FINITE_def = new_ax 
“!X. FINITE(X) <=> isFinite(X) o Tp1(True(X)) =TRUE”


val isFinite_Empty = proved_th $
e0
(strip_tac >> rw[isFinite_property1] >> rpt strip_tac)
(form_goal
 “!X. isFinite(X) o Empty(X) = TRUE”)


val isFinite_Insert = proved_th $
e0
(rw[isFinite_property1] >> rpt strip_tac >>
 qsuff_tac 
 ‘All(X) o Tp(P o Insert(X)) o a = TRUE’ >--
 (rw[All_def,o_assoc,Ins_def] >> strip_tac >> arw[]) >>
 rw[GSYM o_assoc] >> first_x_assum irule >>
 strip_tac >-- 
 (rw[All_def,o_assoc,Ins_def] >> strip_tac >> strip_tac >>
  strip_tac >> first_x_assum irule >> arw[]) >>
 rw[All_def,o_assoc,Ins_def] >> first_x_assum irule >> arw[]
 )
(form_goal
 “!X a:1-> Exp(X,2). isFinite(X) o a = TRUE ==>
  !x:1->X. isFinite(X) o Ins(x,a) = TRUE”)



val hasCard_property = proved_th $
e0
(strip_tac >> rw[GSYM hasCard_def] >> strip_tac >--
  (rw[o_assoc,Pa_distr,pi12_of_Pa] >>
  rw[N_equality] >> rw[GSYM map1_def] >>
  rw[Ev_of_Tp_el'] >> rw[o_assoc,Pa_distr,pi12_of_Pa,idL] >>
  once_rw[one_to_one_id] >> rw[idR] >> 
  once_rw[GSYM True1TRUE] >> rw[GSYM Eq_property]) >>
 strip_tac >> strip_tac >>
 rw[o_assoc,Pa_distr,pi12_of_Pa] >>
 once_rw[GSYM o_assoc] >> rw[N_equality] >>
 once_rw[GSYM map2_def] >>
 rw[o_assoc,Pa_distr] >> rw[Ev_of_Tp_el] >>
 rw[o_assoc] >> rw[Ex_def] >> rw[o_assoc] >> rw[Ex_def] >>
 (*if use rw, then too slow*)
 once_rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[CONJ_def] >> once_rw[o_assoc] >>
 once_rw[Pa_distr] >> once_rw[CONJ_def] >>
 once_rw[map2_def] >>
 rw[o_assoc,NEG_def] >>
 once_rw[Pa_distr] >> once_rw[Pa4_def] >> 
 once_rw[pi42_of_Pa4] >> once_rw[pi41_of_Pa4] >>
 once_rw[pi43_of_Pa4] >> once_rw[pi44_of_Pa4] >>
 rw[GSYM Ins_def] >> rw[o_assoc] >> once_rw[Pa_distr] >>
 once_rw[pi42_of_Pa4] >> once_rw[pi41_of_Pa4] >>
 once_rw[GSYM True1TRUE] >>
 once_rw[GSYM Eq_property] >> once_rw[True1TRUE] >>
 once_rw[GSYM Mem_def] >> rpt strip_tac >>
 qexistsl_tac ["s0","x"] >> 
 once_arw[] >> fs[TRUE2FALSE]
 )
(form_goal
“!X. hasCard(X) o Pa(Empty(X),ZERO) = TRUE &
 !s0 n. hasCard(X) o Pa(s0,n) = TRUE ==>
 !x:1->X. ~ (Mem(X) o Pa(x,s0) = TRUE) ==>
 hasCard(X) o Pa(Ins(x,s0),SUC o n) = TRUE”);



val ABSORPTION_RWT = proved_th $
e0
(rpt strip_tac >> rw[GSYM Mem_def] >>
 once_rw[GSYM Tp0_INJ] >> dimp_tac >> strip_tac (* 2 *) >-- 
 (irule fun_ext >> strip_tac >> 
 rw[GSYM Tp0_def,o_assoc,Pa_distr,idL] >> 
 once_rw[one_to_one_id] >> rw[idR] >>
 once_rw[GSYM pred_ext] >> rw[Ins_property] >>
 dimp_tac >> strip_tac (* 2 *) 
 >-- fs[] >> arw[]) >>
 pop_assum mp_tac >>  
 rw[GSYM Tp0_def,o_assoc,Pa_distr,idL] >> 
 once_rw[GSYM fun_ext_iff] >> once_rw[one_to_one_id] >>
 rw[idR] >> once_rw[GSYM pred_ext] >> rw[] >>
 rw[Pa_distr,o_assoc] >> once_rw[one_to_one_id] >>
 rw[idL,idR] >> rw[Ins_property] >> rpt strip_tac >>
 first_x_assum (qspecl_then ["x"] assume_tac) >>
 fs[])
(form_goal
“!X x:1->X s0:1->Exp(X,2). (Mem(X) o Pa(x,s0) = TRUE) <=>
 Ins(x,s0) = s0”);


val isFinite_hasCard0 = proved_th $
e0
(rpt strip_tac >> fs[isFinite_property1] >>
 first_x_assum irule >> rw[o_assoc,Ex_def] >>
 rw[Swap_Pa] >> assume_tac hasCard_property >>
 rpt strip_tac (* 2 *) >--
 (cases_on “s0 = Empty(X)” (* 2 *) >--
  (qex_tac ‘SUC o ZERO’ >> 
   first_x_assum (qspecl_then ["X"] strip_assume_tac) >>
   first_x_assum irule >> arw[NOT_IN_Empty]) >>
  cases_on “Mem(X) o Pa(e,s0) = TRUE” (* 2 *) >--
  (fs[ABSORPTION_RWT] (*fs bug here, so does arw[]*) >> qex_tac ‘x’ >> arw[]) >>
  first_x_assum (qspecl_then ["X"] strip_assume_tac) >>
  first_x_assum rev_drule >> first_x_assum drule >>
  qex_tac ‘SUC o x’ >> arw[]) >>
 first_x_assum (qspecl_then ["X"] strip_assume_tac) >>
 qex_tac ‘ZERO’ >> arw[])
(form_goal
 “!X a:1->Exp(X,2).isFinite(X) o a = TRUE ==>
   (Ex(N) o Tp(hasCard(X) o Swap(N,Exp(X,2)))) o a = TRUE”)

val isFinite_hasCard = proved_th $
e0
(rpt strip_tac >> drule isFinite_hasCard0 >>
 fs[o_assoc,Ex_def,Swap_Pa] >> qex_tac ‘x’ >> arw[]) 
(form_goal
 “!X a:X->2.isFinite(X) o Tp1(a) = TRUE ==>
  ?n. hasCard(X) o Pa(Tp1(a),n) = TRUE”)



val FINITE_hasCard = proved_th $
e0
(rpt strip_tac >> irule isFinite_hasCard >>
 fs[GSYM FINITE_def])
(form_goal
 “!X. FINITE(X) ==> ?n:1->N. hasCard(X) o Pa(Tp1(True(X)),n) = TRUE”)
 
val Card_def = 
    FINITE_hasCard |> spec_all |> ex2fsym "Card" ["X"] 
                   |> gen_all
