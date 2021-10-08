
fun pi1 A B = mk_fun "π1" [A,B]

fun pi2 A B = mk_fun "π2" [A,B]

val N_Pr_N = proved_th $
e0
(rw[pi2_def])
(form_goal
“ispr(π1(N,N),π2(N,N))”)


val NN_Pr_N = proved_th $
e0
(rw[pi2_def])
(form_goal
“ispr(π1(N * N,N),π2(N * N,N))”)



val SUB_def = minus_ex |> specl [Po N N,pi1 N N,pi2 N N] |> C mp N_Pr_N
                       |> specl [Po (Po N N) N,pi1 (Po N N) N,pi2 (Po N N) N] |> C mp NN_Pr_N
                       |> specl [N,rastt "id(N)",rastt "to1(N,1)"]
                       |> C mp (allE N pr_with_one)
                       |> eqT_intro |> iffRL |> ex2fsym "SUB" []
                       |> C mp (trueI []) |> rewr_rule[To1_def]

val SUB = mk_fun "SUB" []

val LEQo_def = pb_ex |> specl [Po N N,N,SUB] |> specl [rastt "1",ZERO] 
                   |> eqT_intro |> iffRL |> ex2fsym "LEQo" []
                   |> C mp (trueI [])

val LEQo = mk_fun "LEQo" []

val LEQ_def = LEQo_def |> eqT_intro |> iffRL |> ex2fsym "LEQ" []
                    |> C mp (trueI [])

val LEQ = mk_fun "LEQ" []

val LEQ_pb = proved_th $
e0
(strip_assume_tac LEQ_def >>
 assume_tac (to1_unique |> specl [LEQo]) >>
 first_x_assum (qspecl_then ["To1(LEQo)","q"] assume_tac) >> 
 fs[])
(form_goal “ispb(SUB,ZERO,LEQ,To1(LEQo))”)

val NEQo_def = ne_ex |> specl [Po N N,pi1 N N,pi2 N N] |> C mp N_Pr_N
                   |> eqT_intro |> iffRL 
                   |> ex2fsym "NEQo" []
                   |> C mp (trueI [])

val NEQ_def = NEQo_def |> eqT_intro |> iffRL |> ex2fsym "NEQ" []
                    |> C mp (trueI [])

val NEQ = mk_fun "NEQ" []

val NEQo = mk_fun "NEQo" []


val LESSo_def = pb_ex |> specl [LEQo,Po N N,LEQ]
                      |> specl [NEQo,NEQ] 
                      |> eqT_intro |> iffRL 
                      |> ex2fsym "LESSo" []
                      |> C mp (trueI [])

val LESS2LEQ_def = LESSo_def |> eqT_intro |> iffRL |> ex2fsym "LESS2LEQ" []
                      |> C mp (trueI [])


val LESS2NEQ_def = LESS2LEQ_def |> eqT_intro |> iffRL |> ex2fsym "LESS2NEQ" []
                      |> C mp (trueI [])



val LESS_mono = proved_th $
e0
(irule o_mono_mono >>
 by_tac “ismono(NEQ)” >-- 
 accept_tac (conjE1 NEQ_def) >>
 assume_tac LESS2NEQ_def >> arw[] >> 
 strip_assume_tac LEQ_def >>
 by_tac “ismono(ZERO)”
 >-- (qspecl_then ["N","ZERO"] accept_tac dom_1_mono) >>
 drule pb_mono_mono >> first_x_assum drule >> 
 qby_tac ‘ispb(NEQ,LEQ, LESS2NEQ, LESS2LEQ)’ 
 >-- (rev_drule pb_reorder >> first_x_assum accept_tac)>>
 drule pb_mono_mono >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal “ismono(NEQ o LESS2NEQ)”)


val LESS_def0 = proved_th $
e0
(qexistsl_tac ["NEQ o LESS2NEQ"]>> rw[])
(form_goal “?LESS. LESS = NEQ o LESS2NEQ”)

val LESS_def = LESS_def0 |> eqT_intro |> iffRL
                     |> ex2fsym "LESS" []
                     |> C mp (trueI [])


val NEQ_property = proved_th $
e0
(rpt strip_tac >> assume_tac NEQ_def >>
 pop_assum strip_assume_tac >>
 qspecl_then ["N","NEQo"] (x_choosel_then ["W","iN","iNEQo"] assume_tac) copr_ex >>
 first_x_assum drule >>
 drule iso_copr_copr >> first_x_assum drule >>
 drule copr_disjoint >>
 by_tac
 “(?nnb : 1 -> NEQo. NEQ o nnb = nn:1->N * N) <=> (?nnb : 1 -> NEQo. nn:1->N * N= NEQ o nnb)” 
 (*TODO: the by above is stupid step*)>--
 (dimp_tac >> strip_tac >> qexists_tac "nnb" >> arw[]) >>
 (*TODO AQ: how to avoid this trivial steps?*)
 arw[] >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >>
 assume_tac N_Pr_N >> drule fac_diag_eq_iff >>
 first_x_assum (qspecl_then ["nn"] assume_tac) >>
 arw[])
(form_goal 
 “!nn:1->N * N.(?nnb:1->NEQo. NEQ o nnb = nn) <=> ~
 (π1(N,N) o nn = π2(N,N) o nn)”)




(*TODO: use char to define pred LESS,after removing all LE and LT etc*)


(*sub_z_iff_le*)
val SUB_EQ_00 = proved_th $
e0
(rw[GSYM pa2Pa] >> rpt strip_tac >> 
 assume_tac LEQ_def >> pop_assum strip_assume_tac >>
 drule $ iffLR ispb_def >> 
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then ["1","pa(π1(N,N),π2(N,N),n1,n2)","id(1)"] assume_tac) >> fs[idR] >> dimp_tac >> strip_tac (* 2 *)
 >-- (arw[GSYM o_assoc] >> rw[o_assoc] >>
      once_rw[one_to_one_id] >> rw[idR]) >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 qexists_tac "a" >>
 first_x_assum (qspecl_then ["a"] assume_tac) >> fs[])
(form_goal 
“!n1:1->N n2:1->N.
 (?le0:1->LEQo. Pa(n1,n2) = LEQ o le0) <=>
 SUB o Pa(n1,n2) = ZERO”)

(*sub_zero_id*)
val SUB_0_cj2 = proved_th $
e0
(strip_tac >> assume_tac SUB_def >>
 pop_assum strip_assume_tac >> 
 by_tac “SUB o pa(π1(N,N), π2(N,N), id(N), ZERO o To1(N)) o n:1->N = id(N) o n” >-- (rw[GSYM o_assoc] >> arw[]) >>
 fs[idL] >> 
 by_tac “pa(π1(N,N), π2(N,N), id(N), ZERO o To1(N)) o n:1->N = pa(π1(N,N), π2(N,N), n, ZERO)” >-- 
 (assume_tac N_Pr_N >> drule to_p_eq >> 
  first_x_assum irule >> 
  drule p12_of_pa >> arw[GSYM o_assoc] >>
  rw[o_assoc] >> once_rw[one_to_one_id] >>
  rw[idL,idR]) >>
 fs[pa2Pa])
(form_goal 
“!n:1->N. SUB o Pa(n,ZERO) = n”)

(*le_z*)
val LESS_EQ_00 = proved_th $
e0
(rpt strip_tac >> assume_tac SUB_EQ_00 >>
 first_x_assum (qspecl_then ["n0","ZERO"] assume_tac) >>
 by_tac “?(le0 : 1 -> LEQo). Pa(n0, ZERO) = LEQ o le0”
 >-- (qexists_tac "a" >> arw[]) >>
 fs[] >> 
 assume_tac SUB_0_cj2 >> fs[]
 )
(form_goal
“!n0:1->N a:1->LEQo. Pa(n0,ZERO) = LEQ o a ==>
 n0 = ZERO”)

(*lt_le*)
val LESS_IMP_LESS_OR_EQ0 = proved_th $
e0
(rpt strip_tac >> assume_tac LESS_def >>
 assume_tac LESS2NEQ_def >> drule $ iffLR ispb_def >>
 pop_assum strip_assume_tac >> fs[] >>
 pick_x_assum “LEQ o LESS2LEQ = NEQ o LESS2NEQ” (assume_tac o GSYM) >>
 fs[] >> 
 qexists_tac "LESS2LEQ o lt0" >> rw[o_assoc])
(form_goal 
“
 !n1:1->N n2:1->N. 
 (?lt0: 1->LESSo. Pa(n1,n2) = LESS o lt0) ==>
 (?le0: 1->LEQo. Pa(n1,n2) = LEQ o le0) ”)


(*lt_ne0*)
val LESS_NOT_EQ00 = proved_th $
e0
(rpt strip_tac >> assume_tac LESS_def >>
 assume_tac LESS2NEQ_def >> drule $ iffLR ispb_def >>
 pop_assum strip_assume_tac >> fs[] >>
 qexists_tac "LESS2NEQ o lt0" >> rw[o_assoc])
(form_goal 
“
 !n1:1->N n2:1->N. 
 (?lt0: 1->LESSo. Pa(n1,n2) = LESS o lt0) ==>
 (?ne0: 1->NEQo. Pa(n1,n2) = NEQ o ne0)”)

(*lt_ne*)
val LESS_NOT_EQ0 = proved_th $
e0
(strip_tac >> strip_tac >> disch_tac >>
 assume_tac LESS_NOT_EQ00 >> first_x_assum drule >>
 assume_tac NEQ_property >> pop_assum mp_tac >>
 pop_assum (assume_tac o GSYM) >> strip_tac >> 
 pop_assum (assume_tac o iffLR) >> first_x_assum drule >>
 pop_assum mp_tac >> assume_tac N_Pr_N >> 
 arw[pi12_of_Pa])
(form_goal 
“
 !n1:1->N n2:1->N. 
 (?lt0: 1->LESSo. Pa(n1,n2) = LESS o lt0) ==>
 ~(n1 = n2)”)


(*le_ne_lt*)
val LEQ_NEQ_LESS = proved_th $ 
e0
(
 rpt strip_tac >>
 assume_tac LESS_def >> assume_tac LESS2NEQ_def >>
 drule $ iffLR ispb_def >> pop_assum strip_assume_tac >>
 assume_tac NEQ_property >>
 first_x_assum (qspecl_then ["Pa(n1,n2)"] assume_tac)>>
 assume_tac N_Pr_N >> fs[pi12_of_Pa] >>
 pop_assum (K all_tac) >>
 pick_x_assum 
“(?nnb : 1 -> NEQo. NEQ o nnb = Pa(n1:1->N, n2)) <=> ~(n1 = n2)” (assume_tac o GSYM) >> fs[] >>
 first_x_assum (qspecl_then ["1","le0","nnb"] assume_tac) >>
 rfs[] >> qexists_tac "a" >> 
 first_x_assum (qspecl_then ["a"] assume_tac) >> fs[] >>
 arw[o_assoc])
(form_goal 
“
 !n1:1->N n2:1->N.
 ((?le0: 1->LEQo. Pa(n1,n2) = LEQ o le0) & ~(n1 = n2))
 ==> (?lt0: 1->LESSo. Pa(n1,n2) = LESS o lt0)”)


(*lt_iff_le_ne*)
val LESS_iff_LEQ_NEQ = proved_th $
e0
(rpt strip_tac >> dimp_tac >> disch_tac (* 2 *)
 >-- (assume_tac LESS_NOT_EQ0 >> first_x_assum drule >>
      assume_tac LESS_IMP_LESS_OR_EQ0 >> first_x_assum drule >> arw[]) >>
 assume_tac LEQ_NEQ_LESS >> first_x_assum drule >> arw[])
(form_goal 
“
 !n1:1->N n2:1->N.
 (?lt0: 1->LESSo. Pa(n1,n2) = LESS o lt0) <=> 
 ((?le0: 1->LEQo. Pa(n1,n2) = LEQ o le0) & ~(n1 = n2))”)

(*clt_iff_le_ne*)
val CLESS_iff_LEQ_NEQ = proved_th $
e0
(rpt strip_tac >>
 assume_tac LESS_iff_LEQ_NEQ >> pop_assum (assume_tac o GSYM) >>
 arw[] >> 
 assume_tac LESS_mono >>
 assume_tac $ GSYM LESS_def >> fs[] >>
 drule char_def >> assume_tac TRUE_def >> 
 first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 fs[Char_def] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[]) >>
 qexists_tac "lt0" >> arw[])
(form_goal 
“!n1:1->N n2:1->N.
 (Char(LESS) o Pa(n1, n2) = TRUE) <=> 
 ((?le0: 1->LEQo. Pa(n1,n2) = LEQ o le0) & ~(n1 = n2))”)

(*not_lt_z *)
val not_LESS_ZERO = proved_th $
e0
(rpt strip_tac >>
 ccontra_tac >>
 by_tac “Char(LESS) o Pa(n0, ZERO) = TRUE <=> (?a:1->LEQo.Pa(n0,ZERO) = LEQ o a) & ~(n0:1->N = ZERO)” 
 >-- rw[CLESS_iff_LEQ_NEQ] >> fs[] >>
 drule LESS_EQ_00 >> fs[]  
 )
(form_goal 
“!n0:1->N. ~(Char(LESS) o Pa(n0,ZERO) = TRUE)”)

(*sub_def'*)
val SUB_def' = proved_th $
e0
(assume_tac SUB_def >> fs[pi12_of_Pa,pa2Pa])
(form_goal 
“SUB o Pa(id(N), ZERO o To1(N)) = id(N) &
 PRE o SUB = SUB o Pa(π1(N,N), SUC o π2(N,N))”)

(*ind_one_component*)
val INDUCT_one_component = proved_th $
e0
(rpt strip_tac >> assume_tac N_Pr_N >> drule equality_ind >>
 first_x_assum drule >> 
 fs[pa2Pa])
(form_goal
“!f:N * N->N g:N * N->N.
 !n0.(!n.f o Pa(n0,n) = g o Pa(n0,n)) <=>
 f o Pa(n0,ZERO) = g o Pa(n0,ZERO) & 
 !n:1->N. f o Pa(n0,n) = g o Pa(n0,n) ==> 
 f o Pa(n0,SUC o n) = g o Pa(n0,SUC o n)”)



(*add_ex*)
val ADD_ex = proved_th $
e0
(assume_tac N_Pr_N >> assume_tac NN_Pr_N >>
 assume_tac pr_with_one >>
 first_x_assum (qspecl_then ["N"] assume_tac) >>
 rev_drule Thm1 >> first_x_assum drule >> first_x_assum drule >>
 first_x_assum (qspecl_then ["id(N)","SUC o π2(N * N,N)"] assume_tac) >>
 pop_assum strip_assume_tac  >>
 first_x_assum (qspecl_then ["f"] assume_tac) >> fs[] >>
 qexists_tac "f" >> fs[o_assoc,idL,pa2Pa,To1_def])
(form_goal 
“?Add:N * N->N.Add o Pa(id(N),ZERO o To1(N)) = id(N) & 
 Add o Pa(π1(N,N),SUC o π2(N,N)) = SUC o π2(N * N,N) o Pa(id(N * N),Add)”)

(*add_def0*)
val ADD_def0 = ADD_ex |> eqT_intro |> iffRL |> ex2fsym "ADD" []
                      |> C mp (trueI [])


val ADD = mk_fun "ADD" [] 


(*add_def*)
val ADD_def = proved_th $
e0
(assume_tac ADD_def0 >> assume_tac NN_Pr_N >> 
 fs[pi12_of_Pa])
(form_goal
“ADD o Pa(id(N),ZERO o To1(N)) = id(N) & 
 ADD o Pa(π1(N,N),SUC o π2(N,N)) = SUC o ADD”)

(*add_elements*)
val ADD_el = proved_th $
e0
(rpt strip_tac >> assume_tac ADD_def (* 2 *)
 >-- (by_tac “ADD o Pa(id(N), ZERO o To1(N)) o n:1->N = id(N) o n”
      >-- arw[GSYM o_assoc] >>
      assume_tac N_Pr_N >> 
      fs[Pa_distr] >>
      pick_x_assum “ADD o Pa(id(N) o n:1->N, (ZERO o To1(N)) o n) = 
      id(N) o n” mp_tac >>
      rw[o_assoc] >> once_rw[one_to_one_id] >> rw[idL,idR]) >>
 by_tac “ADD o Pa(π1(N,N), SUC o π2(N,N)) o Pa(n, n0:1->N) = SUC o ADD o Pa(n, n0)” >-- arw[GSYM o_assoc] >>
 fs[o_assoc,pi12_of_Pa,Pa_distr])
(form_goal 
“!n:1->N. ADD o Pa(n,ZERO) = n &
 !n0:1->N. ADD o Pa(n, SUC o n0) = SUC o ADD o Pa(n,n0)”)


(*sub_elements*)
val SUB_el = proved_th $
e0
(strip_assume_tac SUB_def' >> rpt strip_tac >--
 (by_tac 
 “SUB o Pa(id(N), ZERO o To1(N)) o n:1->N = id(N) o n”
 >-- arw[GSYM o_assoc] >> fs[Pa_distr,idL,o_assoc] >>
(* assume_tac nN_def >> drule distr_to_pa >> fs[idL] >> *)
 pop_assum mp_tac >> once_rw[one_to_one_id] >> rw[idR]) >>
 by_tac 
 “PRE o SUB o Pa(n:1->N, n0) = 
  SUB o Pa(π1(N,N), SUC o π2(N,N)) o Pa(n, n0)”
 >-- arw[GSYM o_assoc] >> fs[o_assoc,Pa_distr,pi12_of_Pa])
(form_goal
“!n:1->N. SUB o Pa(n,ZERO) = n & 
 !n0.SUB o Pa(n,SUC o n0) = PRE o SUB o Pa(n,n0)”)


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
 SUB o Pa(SUC o m, SUC o n) = SUB o Pa(m,n)”) 


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

(*le_mono*)
val LEQ_mono = proved_th $
e0
(assume_tac LEQ_def >> pop_assum strip_assume_tac >>
 drule pb_mono_mono >> first_x_assum irule >>
 accept_tac z_mono)
(form_goal “ismono(LEQ)”)



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

