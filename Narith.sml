
fun pi1 A B = mk_fun "π1" [A,B]

fun pi2 A B = mk_fun "π2" [A,B]

val N_Pr_N = proved_th $
e0
(rw[pi2_def])
(form_goal
“ispr(π1(N,N),π2(N,N))”);


val NN_Pr_N = proved_th $
e0
(rw[pi2_def])
(form_goal
“ispr(π1(N * N,N),π2(N * N,N))”);



val SUB_def = minus_ex |> specl [Po N N,pi1 N N,pi2 N N] |> C mp N_Pr_N
                       |> specl [Po (Po N N) N,pi1 (Po N N) N,pi2 (Po N N) N] |> C mp NN_Pr_N
                       |> specl [N,rastt "id(N)",rastt "to1(N,1)"]
                       |> C mp (allE N pr_with_one)
                       |> eqT_intro |> iffRL |> ex2fsym "SUB" []
                       |> C mp (trueI []) |> rewr_rule[To1_def];

val SUB = mk_fun "SUB" [];

val LEQo_def = pb_ex |> specl [Po N N,N,SUB] |> specl [rastt "1",ZERO] 
                   |> eqT_intro |> iffRL |> ex2fsym "LEQo" []
                   |> C mp (trueI []);

val LEQo = mk_fun "LEQo" [];

val LEQ_def = LEQo_def |> eqT_intro |> iffRL |> ex2fsym "LEQ" []
                    |> C mp (trueI []);

val LEQ = mk_fun "LEQ" [];

val LEQ_pb = proved_th $
e0
(strip_assume_tac LEQ_def >>
 assume_tac (to1_unique |> specl [LEQo]) >>
 first_x_assum (qspecl_then ["To1(LEQo)","q"] assume_tac) >> 
 fs[])
(form_goal “ispb(SUB,ZERO,LEQ,To1(LEQo))”);

val NEQo_def = ne_ex |> specl [Po N N,pi1 N N,pi2 N N] |> C mp N_Pr_N
                   |> eqT_intro |> iffRL 
                   |> ex2fsym "NEQo" []
                   |> C mp (trueI []);

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
                     |> C mp (trueI []);


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
 (π1(N,N) o nn = π2(N,N) o nn)”);




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
 SUB o Pa(n1,n2) = ZERO”);

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
“!n:1->N. SUB o Pa(n,ZERO) = n”);

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
 n0 = ZERO”);

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
 (?le0: 1->LEQo. Pa(n1,n2) = LEQ o le0) ”);


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
 (?ne0: 1->NEQo. Pa(n1,n2) = NEQ o ne0)”);

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
 ~(n1 = n2)”);


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
 ==> (?lt0: 1->LESSo. Pa(n1,n2) = LESS o lt0)”);


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
 ((?le0: 1->LEQo. Pa(n1,n2) = LEQ o le0) & ~(n1 = n2))”);

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
 ((?le0: 1->LEQo. Pa(n1,n2) = LEQ o le0) & ~(n1 = n2))”);

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
“!n0:1->N. ~(Char(LESS) o Pa(n0,ZERO) = TRUE)”);

(*sub_def'*)
val SUB_def' = proved_th $
e0
(assume_tac SUB_def >> fs[pi12_of_Pa,pa2Pa])
(form_goal 
“SUB o Pa(id(N), ZERO o To1(N)) = id(N) &
 PRE o SUB = SUB o Pa(π1(N,N), SUC o π2(N,N))”);

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
 f o Pa(n0,SUC o n) = g o Pa(n0,SUC o n)”);



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
 Add o Pa(π1(N,N),SUC o π2(N,N)) = SUC o π2(N * N,N) o Pa(id(N * N),Add)”);

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
 ADD o Pa(π1(N,N),SUC o π2(N,N)) = SUC o ADD”);

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
 !n0:1->N. ADD o Pa(n, SUC o n0) = SUC o ADD o Pa(n,n0)”);


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

(*sub_mono_eq*)
val SUB_MONO_EQ = proved_th $
e0
(assume_tac N_Pr_N >>
 drule ind_gen_principle >>
 assume_tac TRUE_def >> first_assum drule >>
 drule char_diag >> first_assum drule >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 last_x_assum drule >>
 fs[Char_def,pa2Pa] >> 
 suffices_tac
 “Char(Pa(id(N), id(N))) o 
  Pa(SUB o Pa(SUC o π1(N,N), SUC o π2(N,N)), SUB) = TRUE o To1(N * N)” >-- (rpt strip_tac >>
 drule $ iffRL fun_ext_iff >>
 first_assum (qspecl_then ["Pa(m,n)"] assume_tac) >>
 fs[o_assoc,Pa_distr,pi12_of_Pa] >>
 once_rw[one_to_one_id] >> rw[idR]) >> 
 fs[Pa_distr,o_assoc,To1_def,pi12_of_Pa] >>
 assume_tac SUB_el >>
 rpt strip_tac (* 2 *) >--
 (arw[] >> rw[GSYM o_assoc,PRE_def,idL] >>
 pop_assum (K all_tac) >> pop_assum (K all_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[]) >>
 fs[Pa_distr,pi12_of_Pa] >>
 pick_xnth_assum 4 (assume_tac o GSYM) >> fs[] >>
 qsuff_tac
 ‘PRE o SUB o Pa(SUC o x, n) = SUB o Pa(x,n)’ 
 >-- (strip_tac >> arw[]) >>
 qby_tac 
 ‘PRE o SUB o Pa(SUC o x, n) = SUB o Pa(SUC o x, SUC o n)’
 >-- (pop_assum mp_tac  >> pop_assum mp_tac >> arw[]) >>
 arw[]
 )
(form_goal 
“!m:1->N n:1->N. 
 SUB o Pa(SUC o m, SUC o n) = SUB o Pa(m,n)”) 

(*add_sub0*)
val ADD_SUB0 = proved_th $
e0
(rw[INDUCT_one_component] >> 
 rw[o_assoc,Pa_distr,pi12_of_Pa] >>
 rw[ADD_el,SUB_MONO_EQ] >> rw[SUB_el])
(form_goal 
“!a:1->N. (!c:1->N. (SUB o Pa(ADD,π2(N,N))) o Pa(a,c) = π1(N,N) o Pa(a,c))”)

(*add_sub*)
val ADD_SUB = proved_th $
e0
(assume_tac ADD_SUB0 >> fs[o_assoc,Pa_distr,pi12_of_Pa])
(form_goal 
“!a:1->N c:1->N. SUB o Pa(ADD o Pa(a,c),c) = a”)



(*add_z_n0*)
val ADD_ZERO_n0 = proved_th $
e0
(rw[ind_N_element,o_assoc,Pa_distr,idL] >> 
 once_rw[one_to_one_id] >> rw[idR] >>
 rw[ADD_el] >> rpt strip_tac >> arw[])
(form_goal
“!n:1->N. (ADD o Pa(ZERO o To1(N),id(N))) o n = id(N) o n”)

(*add_z_n*)
val ADD_ZERO_n = proved_th $
e0
(assume_tac ADD_ZERO_n0 >> fs[Pa_distr,idL,o_assoc] >>
 pop_assum mp_tac >> once_rw[one_to_one_id] >>
 rw[idR])
(form_goal
“!n:1->N. ADD o Pa(ZERO,n) = n”)

(*add_clauses1*)
val ADD_CLAUSES1 =  ADD_ZERO_n

(*sub_equal_0*)
val SUB_equal_0 = proved_th $
e0
(strip_tac >> assume_tac ADD_SUB >>
  first_x_assum (qspecl_then ["ZERO","n"] assume_tac) >>
  fs[ADD_ZERO_n])
(form_goal 
“!n. SUB o Pa(n,n) = ZERO”)

(*n_sub_n_z*)
val n_SUB_n_z = SUB_equal_0

(*le_mono*)
val LEQ_mono = proved_th $
e0
(assume_tac LEQ_def >> pop_assum strip_assume_tac >>
 drule pb_mono_mono >> first_x_assum irule >>
 accept_tac z_mono)
(form_goal “ismono(LEQ)”)


(*le_refl*)
val LEQ_refl = proved_th $
e0
(rpt strip_tac >> assume_tac LEQ_mono >>
 drule char_def >> 
 assume_tac TRUE_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 fs[Char_def] >> 
 arw[] >> strip_assume_tac LEQ_def >> 
 drule pb_fac_iff_1 >>  arw[] >>
 assume_tac n_SUB_n_z >>
 arw[]
 )
(form_goal 
“!x:1->N. Char(LEQ) o Pa(x, x) = TRUE”)

(*le_z_z*)
val LEQ_ZERO_ZERO = proved_th $
e0
(rpt strip_tac >> assume_tac LEQ_mono >>
 drule char_def >> assume_tac TRUE_def >> 
 first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >>
 last_x_assum mp_tac >> fs[Char_def] >>
 disch_tac >> strip_assume_tac LEQ_def >>
 drule pb_fac_iff_1 >> fs[] >>
 assume_tac SUB_0_cj2 >> fs[])
(form_goal 
“!n0:1->N. Char(LEQ) o Pa(n0, ZERO) = TRUE ==> n0 = ZERO”)


(*le_cases*)
val LEQ_cases = proved_th $
e0
(rpt strip_tac >> cases_on “n0 = n:1->N” (* 2 *)
 >-- arw[] >>
 assume_tac CLESS_iff_LEQ_NEQ >> 
 arw[] >> assume_tac LEQ_mono >> drule char_def >>
 assume_tac TRUE_def >>
 first_x_assum drule >> 
 fs[Char_def] >> pop_assum (assume_tac o GSYM) >>
 fs[] >> qexists_tac "x0" >> arw[])
(form_goal
 “!n0:1->N n:1->N. Char(LEQ) o Pa(n0, n) = TRUE ==> 
  Char(LESS) o  Pa(n0, n) = TRUE | n0 = n”)

(*sub_s*)
val SUB_SUC = proved_th $
e0
(rpt strip_tac >> assume_tac SUB_def' >>
 by_tac
 “PRE o SUB o Pa(a:1->N, b:1->N) = 
  SUB o Pa(π1(N,N), SUC o π2(N,N)) o Pa(a, b)”
 >-- arw[GSYM o_assoc] >>
 fs[o_assoc,Pa_distr,pi12_of_Pa])
(form_goal
“!a:1->N b:1->N. SUB o Pa(a,SUC o b) = 
 PRE o SUB o Pa(a,b)”)

(*double_ind*)
val double_IND = proved_th $
e0
(rpt strip_tac >> 
 assume_tac TRUE_def >> drule ind_principle_elements >>
 rw[GSYM All_def,GSYM o_assoc] >> arw[] >>
 qsuff_tac
 ‘(!n : 1 -> N.
   (All(N) o Tp(pred)) o n = TRUE ==>
   (All(N) o Tp(pred)) o SUC o n = TRUE) <=>
  (!n : 1 -> N.
    (All(N) o Tp(pred)) o n = TRUE ==>
    pred o Pa(ZERO, SUC o n) = TRUE &
    !m : 1 -> N.
     pred o Pa(m, SUC o n) = TRUE ==>
     pred o Pa(SUC o m, SUC o n) = TRUE)’
 >-- (strip_tac >> arw[]) >> 
 qsuff_tac
 ‘!n:1->N. 
  (All(N) o Tp(pred)) o n = TRUE ==>
    ((All(N) o Tp(pred)) o SUC o n = TRUE <=>
      pred o Pa(ZERO, SUC o n) = TRUE &
      !m : 1 -> N.
      pred o Pa(m, SUC o n) = TRUE ==>
      pred o Pa(SUC o m, SUC o n) = TRUE)’ 
 >-- (strip_tac >> dimp_tac >> strip_tac >> strip_tac >> 
      strip_tac >-- (last_x_assum drule >> 
                    first_x_assum drule >> fs[]) >>
      first_x_assum drule >> first_x_assum drule >> fs[]) >>
 rpt strip_tac >> 
 first_x_assum (qspecl_then ["pred o Pa(id(N),SUC o n o To1(N))"] assume_tac) >>
 fs[o_assoc,Pa_distr] >> pop_assum mp_tac >>
 once_rw[one_to_one_id] >> rw[idL,idR] >>
 rw[All_def])
(form_goal
“!pred:N * N-> 2.(!n m:1->N. pred o Pa(m,n) = TRUE) <=>
 (!m.pred o Pa(m,ZERO) = TRUE) &
 (!n.(!m.pred o Pa(m,n) = TRUE) 
   ==>
   pred o Pa(ZERO,SUC o n) = TRUE & 
   (!m.pred o Pa(m,SUC o n) = TRUE ==> pred o Pa(SUC o m, SUC o n) = TRUE))”)


val All_Pr = proved_th $
e0
(cheat)
(form_goal
 “!X Y Z pxyz: (X * Y) * Z -> 2 z0:1->Z. All(X * Y) o Tp(pxyz) o z0 = TRUE <=> !x:1->X y:1->Y.pxyz o Pa(Pa(x,y),z0) = TRUE”)


val All_Pr' = proved_th $
e0
(cheat)
(form_goal
 “!X Y Z pxyz: (X * Y) * Z -> 2 z0:1->Z. All(X * Y) o Tp(pxyz) o z0 = TRUE <=> !y:1->Y x:1->X.pxyz o Pa(Pa(x,y),z0) = TRUE”)

val triple_IND = proved_th $
e0
(rpt strip_tac >> assume_tac TRUE_def >> 
 drule ind_principle_elements >> 
 qby_tac 
 ‘(!a:1->N m:1-> N n:1->N.
   pred o Pa(Pa(n, m), a) = TRUE) <=> 
  (!a:1->N. All(N * N) o Tp(pred) o a = TRUE)’ >--
 (rw[All_def] >> dimp_tac >> rpt strip_tac (* 2 *) >--
  (first_x_assum (qspecl_then ["a","π2(N,N) o x","π1(N,N) o x"] assume_tac) >> fs[to_Pr_components]) >> arw[]) >>
 arw[GSYM o_assoc] >> 
rw[o_assoc,All_Pr'] >> 
qsuff_tac
‘!a:1->N.(!m:1->N n:1->N.pred o Pa(Pa(n,m),a) = TRUE) ==>
 ((All(N * N) o Tp(pred)) o SUC o a = TRUE <=>
  (!n:1->N.pred o Pa(Pa(n,ZERO),SUC o a) = TRUE) & 
  !m:1->N. 
  (!n:1->N. pred o Pa(Pa(n,m),SUC o a) = TRUE) ==>
   pred o Pa(Pa(ZERO,SUC o m),SUC o a) = TRUE &
   !n:1->N. pred o Pa(Pa(n,SUC o m),SUC o a) = TRUE ==>
            pred o Pa(Pa(SUC o n,SUC o m),SUC o a) = TRUE)’
>-- (rw[GSYM All_Pr'] >> strip_tac >>
    dimp_tac >> strip_tac (* 2 *) >--
    (arw[] >> strip_tac >> strip_tac >> 
     first_x_assum drule >>
     pop_assum mp_tac >> first_x_assum drule >> 
     fs[GSYM o_assoc]) >>
    arw[] >> strip_tac >> strip_tac >>
    first_x_assum drule >> first_x_assum drule >>
    fs[o_assoc]) >>
rpt strip_tac >> arw[o_assoc] >> 
assume_tac double_IND >>
first_x_assum (qspecl_then ["pred o Pa(id(N * N),(SUC o a) o To1(N * N))"] assume_tac) >>
rw[All_Pr'] >> pop_assum mp_tac >>
rw[o_assoc] >> once_rw[Pa_distr] >>
rw[o_assoc] >> once_rw[one_to_one_id] >> 
once_rw[idL] >> once_rw[idR] >> rw[])
(form_goal
 “!pred:(N * N) * N-> 2. 
  (!a:1->N m n. pred o Pa(Pa(n,m),a) = TRUE) <=>
   (!m:1->N n. pred o Pa(Pa(n,m),ZERO) = TRUE) &
   (!a:1->N. 
     (!m:1->N n. pred o Pa(Pa(n,m),a) = TRUE)==>
     (!n.pred o Pa(Pa(n,ZERO),SUC o a) = TRUE) & 
     (!m.(!n.pred o Pa(Pa(n,m),SUC o a) = TRUE) ==>
         pred o Pa(Pa(ZERO,SUC o m),SUC o a) = TRUE &
         (!n. pred o Pa(Pa(n,SUC o m),SUC o a) = TRUE              ==> 
              pred o Pa(Pa(SUC o n,SUC o m),SUC o a) = TRUE)))”)

(*le_sub*)
val LEQ_SUB = proved_th $
e0
(rpt strip_tac >> assume_tac LEQ_def >>
 pop_assum strip_assume_tac >> assume_tac LEQ_mono >>
 drule char_def >> assume_tac TRUE_def >> 
 first_x_assum drule >>
 pop_assum (assume_tac o GSYM) >>
 once_arw[] >> 
 drule pb_fac_iff_1 >> arw[] >> fs[Char_def])
(form_goal
“(!m:1->N n. Char(LEQ) o Pa(m,n) = TRUE <=>
 SUB o Pa(m,n) = ZERO)”)

(*TODO automatic rw A ==> B ==>C <=> A & B ==>C*)
val CANCEL_SUB_pred = proved_th $
e0
(rpt strip_tac >> 
 qexists_tac
 $ q2str
 ‘IMP o 
  Pa(CONJ o 
    Pa(Char(LEQ) o Pa(π2(N * N,N),π1(N,N) o π1(N * N,N)),
       Char(LEQ) o Pa(π2(N * N,N),π2(N,N) o π1(N * N,N))),
     IFF o 
    Pa(Eq(N) o 
       Pa(SUB o Pa(π1(N,N) o π1(N * N,N),π2(N * N,N)), 
          SUB o Pa(π2(N,N) o π1(N * N,N),π2(N * N,N))),
       Eq(N) o 
       Pa(π1(N,N) o π1(N * N,N),π2(N,N) o π1(N * N,N))))’ >>
 rpt strip_tac >>
 rw[o_assoc,Pa_distr,IMP_def] >>
 rw[pi12_of_Pa] >>
 rw[CONJ_def] >> rw[IFF_def] >> 
 rw[GSYM True1TRUE] >> rw[GSYM Eq_property] >>
 dimp_tac >> rpt strip_tac >> fs[])
(form_goal
“?pred:(N * N) * N-> 2. 
!a:1->N m n.(Char(LEQ) o Pa(a,n) = TRUE ==>
     Char(LEQ) o Pa(a,m) = TRUE ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a) <=> n = m)) <=>
 pred o Pa(Pa(n,m),a) = TRUE”)


(*cancel_sub00*)
val CANCEL_SUB00 = proved_th $
e0
(strip_assume_tac CANCEL_SUB_pred >> arw[] >>
rw[triple_IND] >> pop_assum (assume_tac o GSYM) >> arw[] >>
strip_tac (* 2 *) >-- rw[SUB_0_cj2] >>
strip_tac >> strip_tac >> strip_tac (* 2 *) >--
rw[LEQ_SUB,SUB_0_cj2,Thm2_1] >>
strip_tac >> strip_tac >> strip_tac (* 2 *) >--
rw[LEQ_SUB,SUB_0_cj2,Thm2_1] >>
rpt strip_tac >> rw[SUB_MONO_EQ,inv_suc_eq] >>
first_x_assum irule >> fs[SUB_MONO_EQ,LEQ_SUB]
)
(form_goal 
“!a m n. Char(LEQ) o Pa(a,n) = TRUE ==>
 Char(LEQ) o Pa(a,m) = TRUE ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a)  <=> n = m)”)

(*cancel_sub00'*)
val CANCEL_SUB00' = proved_th $
e0
(rpt strip_tac >> rev_drule CANCEL_SUB00 >>
 first_x_assum drule >> arw[]
 )
(form_goal 
“!a n. Char(LEQ) o Pa(a,n) = TRUE ==>
 !m. Char(LEQ) o Pa(a,m) = TRUE ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a)  <=> n = m)”)

(*sub_0*)
val SUB_0 = proved_th $
e0
(suffices_tac
 “!n:1->N. (SUB o Pa(ZERO o To1(N), id(N))) o n = ZERO o To1(N) o n” >--
 (rpt strip_tac >> 
 pop_assum mp_tac >> rw[o_assoc,Pa_distr] >>
 once_rw[one_to_one_id] >> rw[idL,idR] >> rpt strip_tac >>
 arw[]) >>
 rw[GSYM o_assoc] >> rw[ind_N_element] >>
 assume_tac SUB_el >> rw[o_assoc,Pa_distr] >>
 once_rw[one_to_one_id] >> rw[idL,idR] >> arw[] >>
 rpt strip_tac >> arw[PRE_def])
(form_goal 
“!n:1->N. SUB o Pa(ZERO,n) = ZERO”)

(*zero_less_eq*)
val ZERO_LESS_EQ = proved_th $ 
e0
(rw[LEQ_SUB,SUB_0])
(form_goal
 “!x. Char(LEQ) o Pa(ZERO, x) = TRUE”)

(*less_eq_mono*)
val LESS_EQ_MONO = proved_th $
e0
(rw[SUB_MONO_EQ,LEQ_SUB])
(form_goal
 “(!m n.Char(LEQ) o Pa(SUC o m, SUC o n) = TRUE <=>
        Char(LEQ) o Pa(m, n) = TRUE)”)


(*lt_char_LT*)
val LESS_Char_LESSo = proved_th $
e0
(rpt strip_tac >> assume_tac $ GSYM LESS_def >>
 assume_tac LESS_mono >> rfs[] >> drule char_def >>
 assume_tac TRUE_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 fs[Char_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[]) >>
 qexists_tac "x0" >> arw[])
(form_goal
“!x:1->N * N. (?(x0 : 1 -> LESSo). x = LESS o x0) <=>
  Char(LESS) o x = TRUE”)

(*le_char_LE*)
val LEQ_Char_LEQo = proved_th $
e0
(rpt strip_tac >> strip_assume_tac LEQ_def >>
 assume_tac LEQ_mono >> drule char_def >>
 assume_tac TRUE_def >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 fs[Char_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[]) >>
 qexists_tac "x0" >> arw[])
(form_goal
“!x:1->N * N. (?(x0 : 1 -> LEQo). x = LEQ o x0) <=>
   Char(LEQ) o x = TRUE”)

(*less_0*)
val LESS_0 = proved_th $
e0
(rpt strip_tac >> 
 rw[GSYM LESS_Char_LESSo] >> 
 rw[LESS_iff_LEQ_NEQ] >> 
 rw[GSYM Thm2_1] >> 
 rw[LEQ_Char_LEQo] >> rw[ZERO_LESS_EQ]
 )
(form_goal
 “!n. Char(LESS) o Pa(ZERO, SUC o n) = TRUE”)

(*less_mono_eq*)
val LESS_MONO_EQ = proved_th $
e0
(assume_tac LESS_mono >>
 (*assume_tac LESS_def >> *)drule char_def >>
 assume_tac TRUE_def >> first_x_assum drule >>
 fs[Char_def] >> fs[GSYM LESS_def] >>
 rw[GSYM LESS_Char_LESSo] >>
 rw[LESS_iff_LEQ_NEQ] >> 
 rw[inv_suc_eq] >> assume_tac LEQ_Char_LEQo >>
 arw[LESS_EQ_MONO])
(form_goal
 “(!m n.Char(LESS) o Pa(SUC o m, SUC o n) = TRUE <=>
        Char(LESS) o Pa(m, n) = TRUE)”)

(*less_cases_pred*)
val LESS_cases_pred = proved_th $
e0
(rpt strip_tac >>
 qexists_tac $ q2str
 ‘DISJ o 
  Pa(Char(LESS),Char(LEQ) o Pa(π2(N,N),π1(N,N)))’ >>
 rw[o_assoc,Pa_distr,DISJ_def,pi12_of_Pa])
(form_goal
“ ?pred:N * N-> 2.
  (!m n. (Char(LESS) o Pa(m,n) = TRUE | 
         Char(LEQ) o Pa(n,m) = TRUE) <=> 
         pred o Pa(m,n) = TRUE)”)

(*less_cases*)
val LESS_cases = proved_th $
e0
(strip_assume_tac LESS_cases_pred >> arw[] >>
 qsuff_tac
 ‘!n:1->N m:1->N. pred o Pa(m,n) = TRUE’
 >-- (strip_tac >> arw[]) >>
 rw[double_IND] >> pop_assum (assume_tac o GSYM) >>
 arw[] >> 
 strip_tac (* 2 *) >-- rw[ZERO_LESS_EQ] >>
 strip_tac >> strip_tac >> strip_tac (* 2 *) >-- 
 rw[LESS_0] >>
 arw[LESS_MONO_EQ,LESS_EQ_MONO]
)
(form_goal
 “!m n.Char(LESS) o Pa(m,n) = TRUE |
       Char(LEQ) o Pa(n,m) = TRUE”)

(*less_eq_cases*)
val LESS_EQ_cases = proved_th $
e0
(rpt strip_tac >> assume_tac LESS_cases >>
 cases_on “Char(LEQ) o Pa(m:1->N, n) = TRUE” (* 2 *)
 >-- arw[] >>
 fs[] >> 
 first_x_assum (qspecl_then ["n","m"] assume_tac) >>
 fs[] >>
 assume_tac LESS_iff_LEQ_NEQ >> 
 assume_tac LEQ_mono >>
 drule char_def >> assume_tac TRUE_def >>
 first_x_assum drule >> fs[Char_def] >> 
 first_x_assum (qspecl_then ["n","m"] assume_tac) >>
 pick_xnth_assum 5 (assume_tac o GSYM) >>
 arw[] >>
 assume_tac LESS_mono >> drule char_def >>
 first_x_assum drule >> assume_tac (GSYM LESS_def) >>
 fs[] >>
 first_x_assum (qspecl_then ["Pa(n,m)"] assume_tac) >>
 rfs[Char_def] >>
 by_tac 
 “?lt0:1->LESSo. Pa(n,m) = LESS o lt0”
 >-- (qexists_tac "x0" >> arw[]) >>
 rfs[] >> qexists_tac "le0" >> rw[]
 )
(form_goal
 “!m n.Char(LEQ) o Pa(m,n) = TRUE |
       Char(LEQ) o Pa(n,m) = TRUE”)

(*cancel_sub0*)
val CANCEL_SUB0 = proved_th $
e0
(rpt strip_tac >> 
 assume_tac TRUE_def >>
 assume_tac CANCEL_SUB00 >> assume_tac LESS_EQ_cases >>
 first_x_assum irule >> fs[GSYM LEQ_SUB] >>
 first_assum (qspecl_then ["n","a"] assume_tac) >>
 first_x_assum (qspecl_then ["m","a"] assume_tac) >>
 fs[]
 )
(form_goal 
“!a n m. ~(SUB o Pa(n,a) = ZERO) & ~(SUB o Pa(m,a) = ZERO) ==>
 (SUB o Pa(n,a) = SUB o Pa(m,a)  <=> n = m)”)

(*equality_NN_ind*)
val equality_NN_IND = proved_th $
e0
(rpt strip_tac >> assume_tac N_Pr_N >>
 drule equality_ind >> first_x_assum drule >>
 fs[pa2Pa,pi12_of_Pa])
(form_goal
“!f:N* N->N g:N * N->N.
 !m:1->N.(!n.f o Pa(m,n) = g o Pa(m,n)) <=>
 f o Pa(m,ZERO) = g o Pa(m,ZERO) & 
 !n0:1->N. f o Pa(m,n0) = g o Pa(m,n0) ==> 
 f o Pa(m,SUC o n0) = g o Pa(m,SUC o n0)”)

(*add_suc0*)
val ADD_SUC0 = proved_th $
e0
(rw[equality_NN_IND] >>
 fs[pi12_of_Pa,Pa_distr,o_assoc,idL,ADD_el] >>
 rpt strip_tac >> arw[])
(form_goal
“!n m:1->N.(ADD o Pa(SUC o π1(N,N),id(N) o π2(N,N))) o Pa(n,m) = (SUC o ADD) o Pa(n,m)”)


(*add_suc*)
val ADD_SUC = proved_th $
e0
(assume_tac ADD_SUC0 >> fs[idL,o_assoc,Pa_distr,pi12_of_Pa])
(form_goal 
“!n:1->N m:1->N. ADD o Pa(SUC o n,m) = SUC o ADD o Pa(n,m)”)

(*add_sym0*)
val ADD_SYM0 = proved_th $
e0
(rw[equality_NN_IND] >> rw[ADD_el,Pa_distr,o_assoc,pi12_of_Pa,ADD_ZERO_n,ADD_SUC] >> rpt strip_tac >> arw[])
(form_goal “!m:1->N. (!n. ADD o Pa(m,n) = 
   (ADD o Pa(π2(N,N),π1(N,N))) o Pa(m,n))”)

(*add_sym*)
val ADD_SYM = proved_th $
e0
(assume_tac ADD_SYM0 >> fs[Pa_distr,pi12_of_Pa,o_assoc])
(form_goal 
“!m:1->N n:1->N. ADD o Pa(m,n) = ADD o Pa(n,m)”)

(*suc_sub*)
val SUC_SUB = proved_th $
e0
(assume_tac ADD_SUB >> strip_tac >>
 first_x_assum (qspecl_then ["SUC o ZERO","n"] assume_tac) >>
 qsuff_tac
 ‘ADD o Pa(SUC o ZERO,n) = SUC o n’
 >-- (strip_tac >> fs[]) >>
 once_rw[ADD_SYM] >> rw[ADD_el])
(form_goal
 “!n:1->N. SUB o Pa(SUC o n,n) = SUC o ZERO”)

(*sub_diff_1*)
val SUB_DIFF_1 = proved_th $
e0
(rpt strip_tac >> dimp_tac >--
 (strip_tac >> irule $ iffLR CANCEL_SUB0 >> qexists_tac "b" >>
 assume_tac SUC_SUB >> once_arw[] >> arw[Thm2_1]) >>
 rpt strip_tac >> arw[SUC_SUB])
(form_goal 
“!a:1->N b. SUB o Pa(a,b) = SUC o ZERO <=> a = SUC o b”)


(*sub_s_z_cases*)
val SUB_SUC_ZERO_cases = proved_th $
e0
(rpt strip_tac >> assume_tac SUB_SUC >> fs[] >>
 by_tac “SUB o Pa(a, b) = ZERO | 
         SUB o Pa(a, b) = SUC o ZERO”
 >-- (drule $ iffLR p_z_cases >> arw[])>>
 pop_assum strip_assume_tac >-- arw[] >>
 disj1_tac >>
 fs[SUB_DIFF_1] 
 )
(form_goal 
“!a:1->N b:1->N. SUB o Pa(a,SUC o b) = ZERO ==>
 a = SUC o b | SUB o Pa(a,b) = ZERO”)


(*le_cases_iff*)
val LEQ_cases_iff = proved_th $
e0
(rpt strip_tac >> cases_on “n0 = n:1->N” (* 2 *)
 >-- (arw[] >> rw[LEQ_refl]) >>
 assume_tac CLESS_iff_LEQ_NEQ >> arw[] >> 
 assume_tac LEQ_mono >> drule char_def >>
 assume_tac TRUE_def >> first_x_assum drule >>
 fs[Char_def] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac "x0" >> arw[])  >>
 qexists_tac "le0" >> arw[])
(form_goal “!n0:1->N n:1->N. Char(LEQ) o Pa(n0, n) = TRUE <=> Char(LESS) o  Pa(n0, n) = TRUE | n0 = n”)


(*sub_eq_0*)
val SUB_EQ_0 = proved_th $
e0
(rpt strip_tac >> assume_tac LEQ_def >>
 pop_assum strip_assume_tac >>
 drule $ iffLR ispb_def >> pop_assum strip_assume_tac >>
 assume_tac LEQ_mono >> drule char_def >>
 assume_tac TRUE_def >> first_x_assum drule >>
 fs[Char_def] >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >> once_arw[] >>
 drule pb_fac_iff_1 >> 
 pop_assum (assume_tac o GSYM) >> once_arw[] >> arw[])
(form_goal
“(!m:1->N n:1->N. SUB o Pa(m,n) = ZERO <=> Char(LEQ) o Pa(m,n) = TRUE)”);

(*lt_succ_le*)
val LESS_SUC_LEQ = proved_th $
e0
(rpt strip_tac >> 
 assume_tac CLESS_iff_LEQ_NEQ >> arw[] >>
 pop_assum (K all_tac) >> assume_tac LEQ_mono >>
 drule char_def >> assume_tac TRUE_def >>
 first_x_assum drule >> fs[Char_def] >>
 assume_tac LEQ_cases_iff >> 
 first_x_assum 
  (qspecl_then ["Pa(n0, SUC o n)"] assume_tac) >>
 by_tac 
 “(?le0 : 1 -> LEQo. Pa(n0:1->N, SUC o n:1->N) = LEQ o le0) <=> 
  (?x0 : 1 -> LEQo. LEQ o x0 = Pa(n0, SUC o n))”
 >-- (dimp_tac >> strip_tac
      >-- (qexists_tac "le0" >> arw[]) >>
      qexists_tac "x0" >> arw[]) >> arw[] >> 
 pop_assum (K all_tac) >>
 pop_assum mp_tac >>
 pop_assum (assume_tac o GSYM) >> once_arw[] >>
 strip_tac >> assume_tac (GSYM SUB_EQ_0) >>
 arw[] >>
 assume_tac SUB_el >> arw[] >> 
 cases_on “SUB o Pa(n0:1->N,n) = ZERO” (* 2 *) >--
 (arw[] >> assume_tac PRE_def >> arw[] >>
  assume_tac (GSYM SUB_DIFF_1) >> once_arw[] >>
  pop_assum (K all_tac) >> ccontra_tac >> fs[Thm2_1]) >>
 arw[] >> ccontra_tac >> pop_assum strip_assume_tac >>
 pop_assum mp_tac >>
 assume_tac (GSYM SUB_DIFF_1) >> 
 once_arw[] >> once_arw[] >> rw[] >>
 pop_assum (K all_tac) >>
 assume_tac PRE_eq_0 >> fs[])
(form_goal “!n0:1->N n:1->N. Char(LESS) o Pa(n0, SUC o n) = TRUE  <=> Char(LEQ) o Pa(n0, n) = TRUE”)



(*strong_ind_lemma*)
val strong_IND_lemma = proved_th $ 
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
      rev_drule char_def >>
      assume_tac TRUE_def >> first_x_assum drule >>
      fs[Char_def] >> 
      last_x_assum (qspecl_then ["x"] assume_tac) >>
      first_assum (assume_tac o iffLR) >>
      first_x_assum irule >> 
      by_tac “?(nb : 1 -> Q). x = q:Q->N o nb”
      >-- (qexistsl_tac ["xb"] >> arw[]) >>
      arw[] >> assume_tac LEQ_refl >> arw[]) >>
irule Thm2_3' >> arw[] >>
rw[ismem_def] >> arw[] >> strip_tac (* 2 *) >--
(suffices_tac “?(x0 : 1 -> Q). ZERO = q o x0”
 >-- (strip_tac >> qexistsl_tac ["x0"] >> arw[]) >>
 arw[] >> rpt strip_tac >> first_x_assum irule >>
 drule LEQ_ZERO_ZERO >> arw[] >>
 suffices_tac 
 “!n0:1->N. ~(Char(LESS) o Pa(n0,ZERO) = TRUE)”
 >-- (strip_tac >> arw[]) >>
 rw[not_LESS_ZERO]) >>
 rpt strip_tac >> 
 suffices_tac “?(x0 : 1 -> Q). SUC o n = q:Q->N o x0”
 >-- (strip_tac >> qexistsl_tac ["x0'"] >> arw[]) >>
 arw[] >> pop_assum mp_tac >> pop_assum mp_tac >>
 pop_assum (qspecl_then ["n"] assume_tac) >> 
 rpt strip_tac >> assume_tac LEQ_cases >>
 first_x_assum drule >> 
 first_x_assum strip_assume_tac (* 2 *) >-- 
 (by_tac “?nb:1->Q. n = q:Q->N o nb”
  >-- (qexists_tac "x0" >> sym_tac >> 
       first_x_assum accept_tac) >>
  pop_assum mp_tac >> arw[] >> strip_tac >> 
  first_x_assum irule >>
  assume_tac (GSYM LESS_SUC_LEQ) >> once_arw[] >>
  first_x_assum accept_tac) >> 
first_x_assum irule >> 
by_tac “?nb:1->Q. n = q:Q->N o nb”
>-- (qexists_tac "x0" >> sym_tac >> 
    first_x_assum accept_tac) >>
first_assum (assume_tac o iffLR) >>
first_x_assum drule >> once_arw[] >> rpt strip_tac >>
first_x_assum irule >> fs[LESS_SUC_LEQ])
(form_goal 
“!P p0:P->N. ismono(p0) ==>
 !Q q:Q->N. 
  (ismono(q) & !n:1->N. (?nb:1->Q. n = q o nb) <=> 
            (!n0:1->N. Char(LEQ) o Pa(n0,n) = TRUE
==> Char(p0) o n0 = TRUE))
 ==>
 (!n:1->N. 
  (!n0:1->N. 
    Char(LESS) o Pa(n0,n) = TRUE ==> Char(p0) o n0 = TRUE) ==> Char(p0) o n = TRUE) ==> isiso(p0)”)


val Q_Ex = proved_th $
e0
(rpt strip_tac >> 
 abbrev_tac 
  “IMP o Pa(Char(LEQ),Char(p0:P->N) o π1(N,N)) = lep0” >>
 abbrev_tac
  “All(N) o Tp(lep0:N * N ->2) = cq” >>
 qspecl_then ["N","2","cq","1","TRUE"] (x_choosel_then ["Q","q","Qto1"] assume_tac) pb_ex >>
 qexistsl_tac ["Q","q"] >>
 by_tac “ismono(q:Q->N)”
 >-- (drule pb_mono_mono >> first_x_assum irule >>
     qspecl_then ["2","TRUE"] accept_tac dom_1_mono) >>
 arw[] >> strip_tac >>
 by_tac “(?nb:1->Q. n:1->N = q o nb) <=> cq:N->2 o n = TRUE”
 >-- (drule pb_fac_iff_1 >> pop_assum (assume_tac o GSYM) >> arw[] >>
      dimp_tac >> strip_tac >-- (qexists_tac "nb" >> arw[]) >>
      qexists_tac "a" >> arw[]) >>
 arw[] >> 
 qpick_x_assum ‘All(N) o Tp(lep0) = cq’ (assume_tac o GSYM)>>
 once_arw[] >> rw[o_assoc] >> rw[All_def] >>
 qpick_x_assum
 ‘IMP o Pa(Char(LEQ), Char(p0) o π1(N, N)) = lep0’
 (assume_tac o GSYM) >> once_arw[] >>
 rw[Pa_distr,o_assoc,IMP_def,pi1_of_Pa]
)
(form_goal 
“!P p0:P->N. ismono(p0) ==>
 ?Q q:Q->N. 
  ismono(q) & !n:1->N. (?nb:1->Q. n = q o nb) <=> 
            (!n0:1->N. Char(LEQ) o Pa(n0,n) = TRUE
==> Char(p0) o n0 = TRUE)”)

val strong_IND = proved_th $
e0
(rpt strip_tac >> drule strong_IND_lemma >>
 drule Q_Ex >>
 pop_assum (x_choosel_then ["Q","q"] assume_tac) >>
 first_x_assum drule >> first_x_assum drule >>
 first_x_assum accept_tac)
(form_goal 
“!P p0:P->N. ismono(p0) ==>
 (!n:1->N. 
  (!n0:1->N. 
    Char(LESS) o Pa(n0,n) = TRUE ==> Char(p0) o n0 = TRUE) ==> Char(p0) o n = TRUE) ==> isiso(p0)”)





val coPosym_def = ex2fsym "+" ["A","B"] (iffRL $ eqT_intro $ spec_all copr_ex)
                          |> C mp (trueI []) |> gen_all

val tau1_def = ex2fsym "τ1" ["A","B"] (iffRL $ eqT_intro $ spec_all coPosym_def)
                        |> C mp (trueI []) |> gen_all

val tau2_def = ex2fsym "τ2" ["A","B"] (iffRL $ eqT_intro $ spec_all tau1_def)
                        |> C mp (trueI []) |> gen_all


val E1q_ex = proved_th $
e0
(cheat)
(form_goal
“!two i1:1->two i2:1->two. iscopr(i1,i2) ==>
 !X eps ps p1:eps->X p2:eps ->ps ev:eps->two.isexp(p1,p2,ev) ==>
 ?Exq:ps -> two. 
 !Y XY Xy:XY->X xY:XY->Y. ispr(Xy,xY) ==>
 !pxy:XY->two y:1->Y. 
 (Exq o tp(p1,p2,ev,Xy,xY,pxy) o y = i2  <=> 
  ?x:1->X. pxy o pa(Xy,xY,x,y) = i2 & 
  !x0:1->X. pxy o pa(Xy,xY,x0,y) = i2 ==> x0 = x)”)


val E1_ex = proved_th $
e0
(cheat)
(form_goal
“!X.?E1. !Y pxy:X * Y -> 2 y:1-> Y. E1 o Tp(pxy) o y = TRUE <=>
 ?x:1->X. pxy o Pa(x,y) = TRUE & 
 !x0:1->X. pxy o Pa(x0,y) = TRUE ==> x0 = x”)

val E1_def =  E1_ex |> spec_all |> eqT_intro
                      |> iffRL |> ex2fsym "E1" ["X"] |> C mp (trueI []) |> gen_all

val LO_ex = proved_th $
e0
(strip_tac >>
 abbrev_tac
 “”
 (*abbrev_tac
 “IFF o 
  Pa(Eq(A + 1) o 
     Pa(Ev(N,A + 1) o Pa(π31(N,N,Exp(N,A + 1)),
                         π33(N,N,Exp(N,A + 1))),
        τ2(A,1) o To1(N * N * Exp(N,A + 1))),
     Char(LESS) o Pa(π32(N,N,Exp(N,A + 1)),
                     π31(N,N,Exp(N,A + 1)))) = pred0” >>
 abbrev_tac
 “Ex(N) o Tp(All(N) o Tp(pred0:N * N * Exp(N,A + 1) -> 2)) = pred” >>
 qspecl_then ["Exp(N,A + 1)","2","pred","1","TRUE"] (x_choosel_then ["LA","inc","LA1"] assume_tac) pb_ex >>
 qex_tac ‘LA’ >> drule pb_fac_iff_1 >>
 qby_tac
 ‘pred o Tp1(τ2(A,1) o To1(N)) = TRUE’ >-- cheat >>
 qby_tac 
 ‘?oA:1->LA. inc o  oA = Tp1(τ2(A,1) o To1(N))’ >-- cheat >>
 pop_assum strip_assume_tac >>
 qex_tac ‘oA’ >> *)
 
 )
(form_goal
 “!A. ?LA oA:1->LA sA:A * LA -> LA. 
      !B b:1->B t: A * B ->B. 
      ?f:LA->B. 
       f o oA = b & 
       t o Pa(π1(A,LA),f o π2(A,LA)) = f o sA & 
      (!f':LA->B.
       f' o oA = b & 
       t o Pa(π1(A,LA),f' o π2(A,LA)) = f' o sA ==> f' = f)”)
