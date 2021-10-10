

type ThmDataBase = (string,thm)Binarymap.dict 

val ThmDB0: ThmDataBase = Binarymap.mkDict String.compare

val ThmDB = ref ThmDB0

fun store_thm (thname,th) = 
    ThmDB := Binarymap.insert(!ThmDB,thname,th)

fun find_th0 str thl = 
    case thl of [] => []
              | (nthm as (thname,th)) :: t =>  
                if isSubstring str thname then
                    nthm :: (find_th str t)
                else find_th str t

fun find_th str = 
    find_th0 str (Binarymap.listItems (!ThmDB))
      
fun prove_store (n,g0) = 
    let 
        val th = proved_th g0
        val _ = store_thm(n,th)
    in
        th 
    end


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


(*
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
*)


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

(*

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

*)

val lt_def0 = proved_th $
e0
(qexistsl_tac ["ne o ltne"]>> rw[])
(form_goal “?lt. lt = ne o ltne”)

val lt_def = lt_def0 |> eqT_intro |> iffRL
                     |> ex2fsym "lt" []
                     |> C mp (trueI [])


(*
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
*)

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

(*
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
*)

(*
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
 
*)

(*
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
*)


(*
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
*)

(*
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
*)

(*
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
*)

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

(*
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
*)

(*
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
*)


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
(*
val inv_suc_eq = proved_th $
e0
(assume_tac Thm2_2 >> drule ismono_property >>
 rpt strip_tac >> dimp_tac >> strip_tac >--
 (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal 
“!m n:1->N. SUC o m = SUC o n <=> m = n”)
*)

(*
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
*)

(*
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

*)


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


(*
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

*)

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

(*
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
*)

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




(*
val PRE_eq_0 = proved_th $
e0
(strip_tac >> assume_tac PRE_def >> cases_on “n = ZERO” >> arw[] >>
 dimp_tac >> strip_tac (* 2 *) >--
 (assume_tac z_xor_s >> first_x_assum (qspecl_then ["n"] assume_tac) >>
 rfs[] >> fs[GSYM o_assoc,idL] >> rfs[idL] >> arw[] >> arw[GSYM o_assoc,idL]) >>
 arw[GSYM o_assoc,idL])
(form_goal
“!n:1->N. PRE o n = ZERO <=> (n = ZERO | n = SUC o ZERO)”)
*)


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
 strip_tac  >> assume_tac (GSYM sub_eq_0) >>
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





(*
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
*)





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

(*
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

*)

(*
val o_assoc_middle = proved_th $
e0
(rpt strip_tac >> rw[o_assoc])
(form_goal 
“!A B f:A->B C g:B->C D h:C->D E i:D->E. 
 i o h o g o f = i o (h o g) o f”)


val exists_forall0 = 
exists_forall ("x",mk_ar_sort (mk_ob "A") (mk_ob "B"))


*)

(*
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
*)



(*
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
*)


(*
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
*)


(*
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
*)


(*
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
*)

(*
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
“!X x:1->X. True(X) o x = TRUE”)
*)


(*
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
*)

(*

val Diag_ismono = proved_th $
e0
(strip_tac >> qspecl_then ["A","A"] assume_tac pi2_def >>
 drule diag_is_mono >> fs[GSYM Diag_def,pa2Pa])
(form_goal
“!A. ismono(Diag(A))”)
*)

(*
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

*)


(*
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
*)

(*
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
*)


(*
val Ins_def = 
    Ins_ex |> spec_all |> eqT_intro
           |> iffRL |> ex2fsym "Ins" ["x","s0"]
           |> C mp (trueI []) |> gen_all
*)

(*

val True1TRUE = proved_th $
e0
(rw[GSYM True_def] >> once_rw[one_to_one_id] >> rw[idR])
(form_goal “True(1) = TRUE”)
*)


(*fs with True1TRUE causes loop*)


(*
val Ins_property = proved_th $
e0
(rpt strip_tac >> rw[GSYM Ins_def,GSYM Insert_def,Ev_of_Tp] >> rw[Ev_of_Tp_el,Pa_distr,o_assoc,DISJ_def,pi31_def] >> rw[pi31_of_Pa,pi32_of_Pa] >> 
(qspecl_then ["X","1","x","x0"] mp_tac) $ GSYM Eq_property >> once_rw[True1TRUE] >> 
 strip_tac >> arw[] >> rw[pi33_of_Pa]
)
(form_goal
 “!X x0:1->X s0:1->Exp(X,2).
  !x:1->X. Ev(X,2) o Pa(x,Ins(x0,s0)) = TRUE <=> 
  (x = x0 | Ev(X,2) o Pa(x,s0) = TRUE)”)
*)

(*use abbreved long map instead?

if so, may have equalities Po4(A,B,C,D) = Po(A,Po(B,Po(C,D)))

How can I allow writing multiple product and do not get it messed up?
*)

(*
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

*)

(*
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

*)

(*
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
*)


(*TODO: using 2 * 2 * 2 and pr3 as example to see how does triple product work for triple conj

and subscript... usual number takes to much space
*)

(*AQ: how to set up abbrevs as Pow(X) = Exp(X,2), this is equality on object*)


(*
val fst_conjunct = 
rastt $ q2str 
‘Ev(Exp(X,2),2) o Pa(π42(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),π44(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)) )’
*)


(*
val Ins_property_gen = proved_th $
e0
()
(form_goal
 “!X A x0:A->X s0:A -> Exp(X,2) x:A -> ”)
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
*)

(*
val snd_conjunct = 
rastt $ q2str
‘Eq(Exp(X,2)) o Pa(π43(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),
 Ins(π41(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),
     π42(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2))))’

(*tool of write Pa ... as 
something like π_2,4 of 4 objects
*)

val trd_conjunct = 
rastt $ q2str
‘NEG o Ev(X,2) o Pa(π41(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)),π42(X,Exp(X,2),Exp(X,2),Exp(Exp(X,2),2)))’
*)


(*
fun mk_o a1 a2 = mk_fun "o" [a1,a2]

fun Pa f g = mk_fun "Pa" [f,g]
*)

(*
val from4_pred0 = 
mk_o CONJ $
 Pa trd_conjunct (mk_o CONJ (Pa fst_conjunct snd_conjunct))
*)

(*prove there exists a iso from prod to p4,may turn it into function symbol, but can we avoid it and just take p4 to be the desired product?*)

(*
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
*)

(*
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
*)

(*
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
*)

(*
val from4_pred0 = 
mk_o CONJ $
 Pa trd_conjunct (mk_o CONJ (Pa fst_conjunct snd_conjunct))
*)


(*AQ: it is already too ugly*)
(*
val from4_pred = 
mk_o from4_pred0 (rastt "Bridge4(X)")

*)


(*sort of it is 

X * Exp(X, 2) * Exp(X, 2) * Exp(Exp(X, 2), 2) -> 2:*)

(*
fun Tp f = mk_fun "Tp" [f]

fun Ex X = mk_fun "Ex" [X]

*)


(*
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

*)


(*
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
*)

(*
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

*)

(*fun Nind x0 t = mk_fun "Nind" [x0,t]*)

(*
val card0 = Nind required_map1 required_map2
*)

(*val card0 = Nind (rastt "map1(X)") (rastt "map2(X)")*)

(*fun Ev e f = mk_fun "Ev" [e,f]*)

(*
val hasCard =
mk_o (rastt "Ev(Exp(X,2),2)") 
(Pa (rastt "π1(Exp(X,2),N)")
 (mk_o card0 (rastt "π2(Exp(X,2),N)")))
*)

(*has sort Exp(X, 2) * N -> 2: sort*)

(*Recall 
 it = Empty(X): term
> sort_of it;
val it = 1 -> Exp(X, 2): sort
*)

(*
val Mem_ex = proved_th $
e0
(strip_tac >> qex_tac ‘Ev(X,2)’ >> rw[])
(form_goal
 “!X. ?mem. Ev(X,2) = mem”)

val Mem_def = Mem_ex |> spec_all |> eqT_intro
             |> iffRL |> ex2fsym "Mem" ["X"]
             |> C mp (trueI []) |> gen_all
*)

(*Mem(X) is a predicate that takes an element and a subset of X, gives if x is in s*)


(*
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

*)


(*
val Tp1_ex = proved_th $
e0
(rpt strip_tac >> qex_tac ‘Tp(f o π1(A,1))’ >> rw[])
(form_goal
 “!A B f:A->B. ?tpf:1->Exp(A,B).Tp(f o π1(A,1)) = tpf”)

val Tp1_def = Tp1_ex |> spec_all |> eqT_intro
                     |> iffRL |> ex2fsym "Tp1" ["f"] 
                     |> C mp (trueI []) |> gen_all


fun Tp1 f = mk_fun "Tp1" [f] 
*)


(*
val bigset = Tp1 longpred
$
mk_o longpred (rastt "π1(Exp(Exp(X, 2), 2),1)")*)

(*bigset is the thing to be taken biginter*)




(*
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

*)


(*
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
)

val isFinite_def = 
isFinite_ex |> spec_all |> eqT_intro
            |> iffRL |> ex2fsym "isFinite" ["X"] 
            |> C mp (trueI []) |> gen_all
*)

(*
fun Po A B = mk_fun "*" [A,B]

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
*)

(*
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
 ”)

*)


(*
(!(s0 : 1 -> Exp(Exp(X, 2), 2)).
                 Mem(Exp(X, 2)) o
                   Pa(Empty(X) o To1(Exp(Exp(X, 2), 2)) o s0#, s0#) = TRUE &
                 (!(x : 1 -> Exp(X, 2)).
                     Ev(Exp(X, 2), 2) o Pa(x#, s0#) = TRUE ==>
                     !(x' : 1 -> X).
                       Ev(Exp(X, 2), 2) o Pa(Insert(X) o Pa(x'#, x#), s0#) =
                         TRUE) ==> Ev(Exp(X, 2), 2) o Pa(a, s0#) = TRUE) <=>
             !(P : Exp(X, 2) -> 2).
               Ev(Exp(X, 2), 2) o Pa(Empty(X), Tp(P# o π1(Exp(X, 2), 1))) =
                 TRUE &
               (!(s0 : 1 -> Exp(X, 2)).
                   Ev(Exp(X, 2), 2) o Pa(s0#, Tp(P# o π1(Exp(X, 2), 1))) =
                     TRUE ==>
                   !(e : 1 -> X).
                     Ev(Exp(X, 2), 2) o
                       Pa(Insert(X) o Pa(e#, s0#), Tp(P# o π1(Exp(X, 2), 1))) =
                       TRUE) ==>
               Ev(Exp(X, 2), 2) o Pa(a, Tp(P# o π1(Exp(X, 2), 1))) = TRUE
*)

(*
val isFinite_property1 =proved_th $
e0
(rw[isFinite_property] >> cheat)
(form_goal “!a:1->Exp(X,2). isFinite(X) o a = TRUE <=> !P:Exp(X,2) ->2.
 Ev(Exp(X,2),2) o Pa(Empty(X),Tp1(P)) = TRUE &
 (!s0:1-> Exp(X,2). Ev(Exp(X,2),2) o Pa(s0,Tp1(P)) = TRUE ==>
   !e:1->X.Ev(Exp(X,2),2) o Pa(Ins(e,s0),Tp1(P)) = TRUE) ==>
 Ev(Exp(X,2),2) o Pa(a,Tp1(P)) = TRUE
 ”)

*)

(*
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
*)

(*
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

*)

(*
 ∀s. FINITE s ⇔ ∀P. P ∅ ∧ (∀s. P s ⇒ ∀e. P (e INSERT s)) ⇒ P s

pred_setTheory.FINITE_DEF (DEFINITION)
--------------------------------------
⊢ ∀s. FINITE s ⇔ ∀P. P ∅ ∧ (∀s. P s ⇒ ∀e. P (e INSERT s)) ⇒ P s 

*)





(*
AQ ... 
1.enable "find" stuff 
Binarymap (string , thm) dict

2.superscript does not work Π¹
3.tokenizer.
4.abbrev as parsing and pp, hence no need of object equality.

0xB9

rastt "Π⁴" 0x

Or substitution of object equality?

 Exp(X,2) as Pow(X), that is, when the parser see Pow(X), it should parse it into Exp(X,2). 

5.rw into local constant

6.Do you agree that we need list object for the bit1 bit2 stuff.  can I find a proof of that?

?N->L(N^N).  

7.
“a = _” is parsable, but is it a bad thing to let it parsable everywhere? want the _ reserved for matching forever, do not want the user to use it as a variable name.


8. strip_split, why HOL does not do this way?
*)


(*
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
*)


(*
val isFinite_Insert0 = proved_th $
e0
(rpt strip_tac >> rw[isFinite_property1] >>
 rw[Ins_def] >> dimp_tac >> rpt strip_tac (* 2 *) >--
 ()
 )
(form_goal
 “!X x:1->X a:1->Exp(X,2). isFinite(X) o Insert(X) o Pa(x,a) = TRUE <=> isFinite(X) o a = TRUE”)

val isFinite_Insert = proved_th $
e0
(rpt strip_tac >> irule fun_ext >> 
 rw[o_assoc]
 once_rw[GSYM to_Pr_components] >> rw[pi2_of_Pa] >>
 )
(form_goal
 “!X a. isFinite(X) o Insert(X) = isFinite(X) o π2(X,Exp(X,2))”)
*)


(*
val isFinite_property = proved_th $
e0
(cheat)
(form_goal
 “!X. isFinite(X) o Empty(X) = TRUE &
  !s0:1-> Exp(X,2). isFinite(X) o s0 = TRUE ==>
  !x:1->X.isFinite(X) o Ins(x,s0) = TRUE”)



val isFinite_gen_property = proved_th $
e0
(cheat)
(form_goal
 “!X. isFinite(X) o Empty(X) = TRUE &
  !A s0:A-> Exp(X,2). isFinite(X) o s0 = True(A) ==>
  !x:A->X.isFinite(X) o Ins(x,s0) = True(A)”)
*)

(*
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
*)

(*Po4(A,B,C,D)  A * B * C * D

Exp(X,2) |-> Pow(X)

G * ... Grouptype(G)


(*  *) () [] {} <>
 <f,g>

<> 

*)


(*
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
*)

(*
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
*)


(*
val set_el_ext = proved_th $
e0
()
(form_goal)
*)


(*
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

*)


(*
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
*)

(* TODO: fs bug,
produce this:
 X ,   
   (a : 1 -> Exp(X, 2)), (e : 1 -> X), (s0 : 1 -> Exp(X, 2)), (x : 1 -> N)
   1.!X.
               hasCard(X#) o Pa(Empty(X#), ZERO) = TRUE &
               !(s0 : 1 -> Exp(X#, 2))  (n : 1 -> N).
                 hasCard(X#) o Pa(s0#, n#) = TRUE ==>
                 !(x : 1 -> X#).
                   ~Ins(x#, s0#) = s0# ==>
                   hasCard(X#) o Pa(Ins(x#, s0#), SUC o n#) = TRUE
   2.hasCard(X) o Pa(s0, x) = TRUE
   3.~s0 = Empty(X)
   4.Ins(e, s0) = s0
   ----------------------------------------------------------------------
   ?(x : 1 -> N). hasCard(X) o Pa(Ins(e, s0), x#) = TRUE

*)

(*
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
*)


(*up to here*)


val LO_ex = proved_th $
e0
(cheat)
(form_goal
 “!A. ?LA oA:1->LA sA:A * LA -> LA. 
      !B b:1->B t: A * B ->B. 
      ?f:LA->B. 
       f o oA = b & 
       t o Pa(π1(A,LA),f o π2(A,LA)) = f o sA & 
      (!f':LA->B.
       f' o oA = b & 
       t o Pa(π1(A,LA),f' o π2(A,LA)) = f' o sA ==> f' = f)”)


(*
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

*)

(*TODO: rw: ~(A & B) <=> A ==> ~ B & B ==> ~A*)

val WOP = proved_th $
e0
(rpt strip_tac >> 
 ccontra_tac >>
 qby_tac 
 ‘!l:1->N. P o l = TRUE ==>
  ?n:1->N. P o n = TRUE & ~(Char(LEQ) o Pa(l,n) = TRUE)’ 
 >-- (fs[exists_forall0] >>
     fs[NEG_CONJ2IMP_NEG])>>
 qsuff_tac 
 ‘!n:1->N. (All(N) o Tp(IMP o Pa(Char(LEQ),NEG o P o π1(N,N)))) o n = TRUE’ >-- 
 (rw[o_assoc,All_def,Pa_distr,IMP_def,pi1_of_Pa,NEG_def] >>
 ccontra_tac >>
 qsuff_tac 
 ‘P = False(N)’ >-- fs[] >>
 irule fun_ext >> rw[False2FALSE] >> strip_tac >>
 first_x_assum irule >> 
 qex_tac ‘a’ >> rw[LEQ_refl]) >>
 rw[IP_el,o_assoc,All_def,Pa_distr,IMP_def,pi1_of_Pa,
    NEG_def,GSYM TRUE2FALSE] >> rpt strip_tac (* 2 *) >--
 (qby_tac ‘x = ZERO’ >--
  (drule LEQ_ZERO_ZERO >> arw[]) >> arw[] >>
 ccontra_tac >> first_x_assum drule >>
 pop_assum strip_assume_tac >> fs[ZERO_LESS_EQ]
 (*~Le o Pa(ZERO, n) = TRUE is false*)) >> 
 cases_on “Char(LEQ) o Pa(x:1->N,n:1->N) = TRUE” >--
 (first_x_assum drule >> arw[]) >>
 qby_tac ‘x = SUC o n’ >-- 
 (drule LEQ_cases >> fs[LESS_SUC_LEQ]
  (*TODO: lemma x <= n ^ + /\ x ~<= n <=> x = n+*)) >>
 arw[] >> ccontra_tac >>
 first_x_assum drule >> pop_assum strip_assume_tac >>
 (*~Le o Pa(SUC o n, n') = TRUE 
  use ~(n + 1 <= n') <=> n' < n + 1 <=> n' <= n*) 
 qby_tac ‘Char(LEQ) o Pa(n',n) = TRUE’ >-- 
 (rw[GSYM LESS_SUC_LEQ] >> assume_tac LESS_cases >>
 first_x_assum (qspecl_then ["n'","SUC o n"] assume_tac) >>
 fs[]) >>
 first_x_assum drule >> fs[]
 )
(form_goal
 “!P:N->2. ~(P = False(N)) ==> 
  ?l:1->N. P o l = TRUE &
  !n:1->N. P o n = TRUE ==>
  Char(LEQ) o Pa(l,n) = TRUE”)



 “(~?n. P n /\ !m. (m<n) ==> ~P m) ==> (!n m. (m<n) ==> ~P m)”)
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






(*maybe nice to have a tool that realise which component, and just assign maps to components, how can I do this?*)



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

(*fun Po A B = mk_fun "*" [A,B]*)

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


(*
val f0 = “!a. (ismono(a) & ismono(b)) & ismono(c) & (?a.ismono(x)) ==> ismono(h)”

val th = mk_thm (fvf f0) [] f0

rewr_rule [pe_ob_clauses,pe_ar_clauses,CONJ_ASSOC,CONJ_IMP_IMP] th
*)

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
