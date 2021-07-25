
(*

Q1: is it better to add {elimvars = false, droptrues = false, strip = false} to current version?

why it is record type, not a triple? not complaining, just confused record/pairs should be used for what.

which ones are the necessary ones to control?  Just worry about that if I will need it if I need more versions of simplifiers later.

and what is "drop" doing? why we need it.

do not bother with mk_require

Q2. critical difference between REWR_CONV and SIMP_CONV? Should the normalisation function of simp and fs be the same? (TODO tomorrow:try find it)
 Do we actually need all the top_sweep depth redepth conv/fconv? had some of them previously, but never used, is there anywhere that it is better to use that things?

top_depth_conv

Q3. why do we need mk_require tac? (TODO tomorrow:try understand it)

Q4. what is this drop function doing, do not understand this.

Q5. pp, can I have pp.sml for basic functions such as gravities, and open pp in term.sml form.sml and write pp functions there? which part of pp function should be put into sig?


Q6. proofmanager stuff, things does not work e.g. M-h g, complains. should we have both gstk and gtree?

fun initial_proofs() = PRFS[];

what is the () here? 

fun backup ()

why take () as an argument.


Q7. does not have the effect of setting up goal with M-h g

quite messed up, ask this first.

ppgstk 


Q8. Okay to have 

datatype proposition = POSED of abbrev.goal
                       | PROVED of logic.thm * abbrev.goal
    datatype gstk = GSTK of {prop  : proposition,
                             stack : tac_result list}

in goalstack.sig? 

okay


once I add val ppgstk: gstk -> ('a, unit) t to sig since it is needed for proofmanager, why complain abou the t? formerly not and get complained several times recently.

goalstack.sig:15: error: Type constructor (t) has not been declared
Found near val ppgstk : gstk -> ('a, unit) t

fixed by open smpp, add it to master.ml?


Q9. fun first tacl =
    case tacl of
        [] => raise simple_fail "no tactic"
      | h :: t => h Orelse (first t)
 does not work, why?

Tactical.sml uses ORELSE in comment, but not in the code.

Know that SML is not lazy evaluation (Larry's rw paper), but the definition of ORELSE should apply the tactic on the goal.


Q10. Not get replied if should avoid eq on objects, but think anyway is not needed, so will just do eq on arrows because anyway equality on objects are induced by eq on arrows.


P(A)

P(f:A->X) 

A \cong B 

P(f':B->X)

drule for iso, like this? If it is obviously wrong then I will give up, if it is just too early to say if it is wrong or not I will just keep trying and may write a draft function.

If A \cong B, with f: B ~~> A the iso, then for every formula P, contains A or not, let P[f] denote the formula which:



--all occurrence of A is replaced by B.
--all arrow with domain A is composed with f
  a:A->X |-> a o f: B -> X
--all arrow with codomain A is precomposed with f ^ -1
  a: X->A |-> f ^ -1 o a: X ->B

construct a function prove P[f] from P, an induction.
!f: A ->B. P(f)

A \cong C. i: C -> A

P(f o i)

!f': C ->B. P(f')





 


isprod(p1,p2)

A <-p1- AB -p2-> B

AB \cong C

isprod (p1',p2') <== isprod(p1,p2)

issubset f: X ->A is a subset of A, if f is a mono

issubset(f,A) 



Q11. Get goalstack.sml worked, but tried too much things that I am not sure which makes it work. Why is there ?.term.term? Have saw ?.form.form also, what to do to avoid all that?


*)



(*

1.   !x. P x /\ Q x ==> R x

  2.   Q a

-- - -- >

  1.   ..
  2.   ..
  3.   P a ==> R a


first_x_assum (first_x_assum strip_assume_tac o MATCH_MP_at (Pos )
*)



val compose_assoc_4_3_left = proved_th $
e0
(rw_tac[o_assoc])
(rapg "(f4 o f3 o f2) o f1 = f4 o f3 o f2 o f1")

val compose_assoc_4_2_left = proved_th $ 
e0
(rw_tac[o_assoc])
(rapg "(f4 o f3) o f2 o f1 = f4 o f3 o f2 o f1")

val compose_assoc_4_2_middle = proved_th $
e0
(rw_tac[o_assoc])
(rapg "f4 o (f3 o f2) o f1 = f4 o f3 o f2 o f1")

val compose_assoc_4_2_middle_SYM = proved_th $
e0
(rw_tac[o_assoc])
(rapg "f4 o f3 o f2 o f1 = f4 o (f3 o f2) o f1")
           
val compose_assoc_4_2_left_SYM = proved_th $
e0
(rw_tac[o_assoc])
(rapg "f4 o f3 o f2 o f1 = (f4 o f3) o f2 o f1")


val compose_assoc_4_3_2_left = proved_th $
e0
(rw_tac[o_assoc])
(rapg "(f4 o f3 o f2) o f1 = (f4 o f3) o f2 o f1")        


val compose_assoc_4_2_left_middle = proved_th $
e0
(rw_tac[o_assoc])
(rapg "(f4 o f3) o f2 o f1 = f4 o (f3 o f2) o f1")



val compose_assoc_4_2_left_left = proved_th $
e0
(rw_tac[o_assoc])
(rapg "((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1")

val o_bracket_left = proved_th $
e0
(rw_tac[o_assoc])
(rapg "f o b o a = g o d o c ==> (f o b) o a = (g o d) o c")

val o_bracket_right = proved_th $
e0
(rw_tac[o_assoc])
(rapg "(f o b) o a = (g o d) o c ==> f o b o a = g o d o c")

val compose_assoc_5_2_left1_left = proved_th $
e0
(rw_tac[o_assoc])
(rapg "f5 o (f4 o f3) o f2 o f1 = (f5 o f4) o f3 o f2 o f1")


val compose_assoc_6_3_2_left_middle = proved_th $
e0
(rw_tac[o_assoc]) 
(rapg "(f6 o f5 o f4) o f3 o f2 o f1 = f6 o f5 o (f4 o f3) o f2 o f1")
                
val compose_assoc_6_left_left_left_right2 = proved_th $
e0
(rw_tac[o_assoc])
(rapg "(((f6 o f5 o f4) o f3) o f2) o f1 = f6 o f5 o f4 o (f3 o f2) o f1")

                
val compose_assoc_5_4_left = proved_th $
e0
(rw_tac[o_assoc])
(rapg "f5 o f4 o f3 o f2 o f1 = (f5 o f4 o f3 o f2) o f1")


val compose_assoc_5_4_left_SYM = proved_th $
e0
(rw_tac[o_assoc])
(rapg "(f5 o f4 o f3 o f2) o f1 = f5 o f4 o f3 o f2 o f1")


val compose_assoc_5_2_left = proved_th $
e0
(rw_tac[o_assoc])
(rapg "(f5 o f4) o f3 o f2 o f1 = f5 o f4 o f3 o f2 o f1")



val compose_assoc_5_2_left_SYM = proved_th $
e0
(rw_tac[o_assoc])
(rapg "f5 o f4 o f3 o f2 o f1 = (f5 o f4) o f3 o f2 o f1")
                         
val ax1_5_applied = 
    ax1_5 |> spec_all |> conjE2 |> iffRL |> strip_all_and_imp |>
          rewr_rule[assume (rapf "x0 = eqinduce(f:A->B, g, h:X->A)")] |>
          disch_all |> allI (dest_var $ rastt "x0:X->eqo(f,g:A->B)")



local
   val imp_th = gen_all (el 5 (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))
in

val i1_i2_disjoint = mk_fth (rapf "!X.!t.~ (i1(X,X) o (t:1->X) = i2(X,X) o t)")


fun contrapos impth =
      let
         val (ant, conseq) = dest_imp (concl impth)
         val notb = mk_neg conseq
      in
         disch notb
           (dimp_mp_l2r 
                  (disch ant (mp (assume notb |> eqF_intro |> dimpl2r) (mp impth (assume ant)))) (F_imp2 ant))
      end
      handle e => raise wrap_err "contrapos." e

i1_i2_disjoint |> specl (List.map readt ["X"])eqF_intro 

(*aq: subst
  lookup_pred (!psyms) "T";
val it = NONE: (string * sort) list option
> new_pred "T";
val it = fn: (string * sort) list -> unit
> new_pred "T" [];
val it = (): unit
>  lookup_pred (!psyms) "T";
val it = SOME []: (string * sort) list option
> val hol_mode_time0 = 3.599: Time.time
> # Exception- ERR ("subst_f.mk_pred.psym not found", [], [], []) raised

 *)

qabbrev_tac ‘k' = coeqa (i1 B B ∘ f) (i2 B B ∘ f)’ >>
qabbrev_tac ‘I0 = eqo (k' ∘ i1 B B) (k' ∘ i2 B B)’ >>
qabbrev_tac ‘R' = coeqo ((i1 B B) o f) ((i2 B B) o f)’ >>
qabbrev_tac ‘q' = eqa (k' o i1 B B) (k' o i2 B B)’ >>

val cg = current_goal o current_tac_result


(*TODO: parser bug:
rapg "!h:coeqo(f,g) -> X. f = g ==> ?h':coeqo(g,g) -> X.T"
 Exception-
   TER
     ("match_sort.cannot match ob with ar: ",
      [ar (Var ("A", ob), Var ("B", ob)), ob], []) raised

*)


(*


> val hol_mode_time0 = 3.128: Time.time
> # val it =
   (A : ob),
   (B : ob),
   (X : ob),
   (f : A -> B),
   (g : A -> B),
   (h : coeqo(f, g) -> X)
   f = g
   |-
   ?(h' : coeqo(g, g) -> X). T: thm
> # # # # # 
*** Time taken: 0.002s
> val th = it;
val th =
   (A : ob),
   (B : ob),
   (X : ob),
   (f : A -> B),
   (g : A -> B),
   (h : coeqo(f, g) -> X)
   f = g
   |-
   ?(h' : coeqo(g, g) -> X). T: thm
> temp;
val it =
   (HOLset{("A", ob), ("B", ob), ("X", ob), ("g", A -> B),
           ("h", coeqo(tv0, g) -> X), ("tv0", A -> B)}, [tv0 = g],
    ?(h' : coeqo(g, g) -> X). T): (string * sort) set * form list * form
> val hol_mode_time0 = 3.135: Time.time
> # Exception-
   ERR
     ("not a templete, error in assumption list... ", [], [],
      [Pred ("=", [f, g]), Pred ("=", [tv0, g])]) raised
> # # # # # 
*** Time taken: 0.002s
> val (c0,asl0,w0) = temp;
val asl0 = [tv0 = g]: form list
val c0 =
   HOLset{("A", ob), ("B", ob), ("X", ob), ("g", A -> B),
          ("h", coeqo(tv0, g) -> X), ("tv0", A -> B)}: (string * sort) set
val w0 = ?(h' : coeqo(g, g) -> X). T: form
> val hol_mode_time0 = 3.144: Time.time
> > > > # # poly: : error: Value or constructor (ct0) has not been declared
Found near var $ List.hd $ HOLset.listItems $ HOLset.difference (ct0, ...)
Static Errors
> val (ct0,asl0,w0) = temp;
val asl0 = [tv0 = g]: form list
val ct0 =
   HOLset{("A", ob), ("B", ob), ("X", ob), ("g", A -> B),
          ("h", coeqo(tv0, g) -> X), ("tv0", A -> B)}: (string * sort) set
val w0 = ?(h' : coeqo(g, g) -> X). T: form
> val hol_mode_time0 = 3.152: Time.time
> > > > # # val tv = h: term
> # # # # # 
*** Time taken: 0.011s
> val hol_mode_time0 = 3.164: Time.time
> # val it =
   HOLset{("A", ob), ("B", ob), ("X", ob), ("f", A -> B), ("g", A -> B),
          ("h", coeqo(f, g) -> X)}: (string * sort) set
> # # # # # 
*** Time taken: 0.002s
> val hol_mode_time0 = 3.167: Time.time
> # val it =
   HOLset{("A", ob), ("B", ob), ("X", ob), ("g", A -> B),
          ("h", coeqo(tv0, g) -> X), ("tv0", A -> B)}: (string * sort) set
> # # # # # 
*** Time taken: 0.003s
> val hol_mode_time0 = 3.172: Time.time
> > # val it = HOLset{("h", coeqo(tv0, g) -> X), ("tv0", A -> B)}:

may take the intersection to get the tv0
*)

e0
(strip_tac >> strip_tac >> subst_tac (assume (rapf "f:A->B = g")) >> 
 exists_tac (rastt "h : coeqo(g:A->B, g) -> X") >> rw_tac[])
(rapg "!h:coeqo(f:A->B,g) -> X. f = g ==> ?h':coeqo(g,g) -> X.T")

e0
(repeat strip_tac)
(rapg "!h:coeqo(f:A->B,g) -> X. f = g ==> ?h':coeqo(g,g) -> X.T")

val g0 = cg $
e0 
(strip_tac >> match_mp_tac (contrapos (spec_all ax6) |> neg_neg_elim) >>
 ccontra_tac >> pop_assum $ x_choose_tac "t" >> 
 abbrev_tac (rapf "coeqa(i1(B,B) o f:A->B, i2(B,B) o f) = k'") >>
 subst1_tac (assume (rapf "coeqa(i1(B,B) o f:A->B, i2(B,B) o f) = k'")) >>
 rev_full_simp_tac[] >>
 by_tac (rapf "?f'.f = f':A->B") >-- cheat >>
 pop_assum strip_assume_tac >>
 full_simp_tac[] >> 
 
)
(rapg "areiso(A,0) ==> areiso(eqo(coeqa(i1(B,B) o f:A->B, i2(B,B) o f) o i1(B,B),coeqa(i1(B,B) o f, i2(B,B) o f) o i2(B,B)),0)")   

val i1_i2_disjoint' = 
i1_i2_disjoint |> specl [rastt "eqo((ca: (B + B) -> coeqo(c1:A-> (B + B),c2:A->(B + B))) o i1(B, B), ca o i2(B, B))",
rastt "t:1->eqo((ca: (B + B) -> coeqo(c1:A->(B + B),c2:A ->(B + B))) o i1(B, B), ca o i2(B, B))"] |> eqF_intro |> dimpl2r

rastt "ca: (B + B) -> coeqo(c1:A-> (B + B),c2)"

i1_i2_disjoint |> spec_all |> eqF_intro |> dimpl2r |> gen_all

val coeq_of_equal = mk_fth (rapf "?ki. ki o (coeqa(f,f)) = id(B)")
val from_iso_zero_eq = mk_fth (rapf "areiso(A,0) ==>!f:A->B g.f = g")

val (ct,asl,w) = cg $
e0 
(strip_tac >> match_mp_tac (contrapos (spec_all ax6) |> neg_neg_elim) >>
 ccontra_tac >> pop_assum $ x_choose_tac "t" >>
 abbrev_tac (rapf "(i1(B, B) o f:A->B) = c1") >>
 abbrev_tac (rapf "(i2(B, B) o f:A->B) = c2") >>
 subst1_tac (assume (rapf "(i1(B, B) o f:A->B) = c1")) >>
 subst1_tac (assume (rapf "(i2(B, B) o f:A->B) = c2")) >>
 full_simp_tac[] >>
 abbrev_tac (rapf "coeqa(c1:A->(B + B), c2) = k'") >>
 subst1_tac (assume (rapf "coeqa(c1:A->(B + B), c2) = k'")) >>
 abbrev_tac (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i1(B,B) = c3") >>
 abbrev_tac (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i2(B,B) = c4") >>
 subst1_tac (assume (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i1(B,B) = c3")) >>
 subst1_tac (assume (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i2(B,B) = c4")) >> 
 abbrev_tac (rapf "eqa(c3:B -> coeqo(c1:A -> (B + B),c2:A -> (B + B)),c4) = q'")>>
 match_mp_tac (i1_i2_disjoint |> spec_all |> eqF_intro |> dimpl2r |> gen_all) >>
 exists_tac (rastt "B") >>
 exists_tac (rastt "(q':eqo(c3,c4:B -> coeqo(c1,c2:A -> (B + B))) -> B) o (t:1->eqo(c3,c4:B->coeqo(c1,c2)))") >>
 by_tac (rapf "k' o i1(B,B) o q' = (k':(B+B)->coeqo(c1:A->(B+B),c2:A->(B+B))) o i2(B,B) o q':eqo(c3:B->coeqo(c1,c2),c4:B->coeqo(c1,c2)) -> B") >--
 (pick_x_assum (rapf "eqa(c3:B -> coeqo(c1: A -> (B + B), c2), c4) = q'") (assume_tac o GSYM) >>
 rw_tac[GSYM o_assoc] >> arw_tac[ax1_5 |> spec_all |> conjE1]) >>
 rw_tac[GSYM o_assoc] >>
 suffices_tac (rapf "i1(B, B) o q':eqo(c3:B -> coeqo(c1:A->(B+B),c2),c4)->B = i2(B,B) o q'") >-- 
 (strip_tac >> arw_tac[]) >>
 assume_tac (from_iso_zero_eq |> allI ("B",mk_ob_sort) |> allE (rastt "B+B")|> undisch |> specl [rastt"c1:A->(B+B)",rastt"c2:A->(B+B)"]) >--
 subst1_tac (assume (rapf "c1:A ->(B+B) = c2"))
 
)
(rapg "areiso(A,0) ==> areiso(eqo(coeqa(i1(B,B) o f:A->B, i2(B,B) o f) o i1(B,B),coeqa(i1(B,B) o f, i2(B,B) o f) o i2(B,B)),0)")  



x_choose_then "ki" assume_tac (coeq_of_equal |> gen_all |> allE (rastt "A") |>
allE (rastt "B+B") |> allE (rastt "c2:A->(B+B)"))



val (ct,asl,w) = cg $
e0 
(strip_tac >> (*match_mp_tac (contrapos (spec_all ax6) |> neg_neg_elim) >>
 ccontra_tac >> pop_assum $ x_choose_tac "t" >>*)
 abbrev_tac (rapf "(i1(B, B) o f:A->B) = c1") >>
 abbrev_tac (rapf "(i2(B, B) o f:A->B) = c2") >>
 assume_tac (from_iso_zero_eq |> allI ("B",mk_ob_sort) |> allE (rastt "B+B")|> undisch |> specl [rastt"c1:A->(B+B)",rastt"c2:A->(B+B)"]) >> 
 full_simp_tac[] >> 
 pop_assum (K all_tac) >> 
 match_mp_tac (contrapos (spec_all ax6) |> neg_neg_elim) >>
 ccontra_tac >> pop_assum $ x_choose_tac "t" >>
 x_choose_then "ki" assume_tac
 (coeq_of_equal |> gen_all |> allE (rastt "A") |>
                allE (rastt "B+B") |> allE (rastt "c2:A->(B+B)")) >> (*>>
 abbrev_tac (rapf "coeqa(c2:A->(B + B), c2) = k'") >>
 subst1_tac (assume (rapf "coeqa(c2:A->(B + B), c2) = k'")) if do so, then complain*)
 last_x_assum subst1_tac (*>>
 remove_asm_tac (rapf "i1(B, B) o f:A->B = c2") >>
(*AQ: if do not do remove asm, use last_x_assume, then will subst other eqn and complain as in existsE, do not know why*)
 first_x_assum subst1_tac >>
 abbrev_tac (rapf "coeqa(c2:A->(B + B), c2) = k'") >>
 subst1_tac (assume (rapf "coeqa(c2:A->(B + B), c2) = k'"))*)

 
(*
 subst1_tac (assume (rapf "(i1(B, B) o f:A->B) = c1")) >>
 subst1_tac (assume (rapf "(i2(B, B) o f:A->B) = c2")) >>
 full_simp_tac[] >>
 abbrev_tac (rapf "coeqa(c1:A->(B + B), c2) = k'") >>
 subst1_tac (assume (rapf "coeqa(c1:A->(B + B), c2) = k'")) >>
 abbrev_tac (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i1(B,B) = c3") >>
 abbrev_tac (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i2(B,B) = c4") >>
 subst1_tac (assume (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i1(B,B) = c3")) >>
 subst1_tac (assume (rapf "(k':(B + B)->coeqo(c1:A -> (B + B),c2:A -> (B + B))) o i2(B,B) = c4")) >> 
 abbrev_tac (rapf "eqa(c3:B -> coeqo(c1:A -> (B + B),c2:A -> (B + B)),c4) = q'")>>
 match_mp_tac (i1_i2_disjoint |> spec_all |> eqF_intro |> dimpl2r |> gen_all) >>
 exists_tac (rastt "B") >>
 exists_tac (rastt "(q':eqo(c3,c4:B -> coeqo(c1,c2:A -> (B + B))) -> B) o (t:1->eqo(c3,c4:B->coeqo(c1,c2)))") >>
 by_tac (rapf "k' o i1(B,B) o q' = (k':(B+B)->coeqo(c1:A->(B+B),c2:A->(B+B))) o i2(B,B) o q':eqo(c3:B->coeqo(c1,c2),c4:B->coeqo(c1,c2)) -> B") >--
 (pick_x_assum (rapf "eqa(c3:B -> coeqo(c1: A -> (B + B), c2), c4) = q'") (assume_tac o GSYM) >>
 rw_tac[GSYM o_assoc] >> arw_tac[ax1_5 |> spec_all |> conjE1]) >>
 rw_tac[GSYM o_assoc] >>
 suffices_tac (rapf "i1(B, B) o q':eqo(c3:B -> coeqo(c1:A->(B+B),c2),c4)->B = i2(B,B) o q'") >-- 
 (strip_tac >> arw_tac[]) >>
 assume_tac (from_iso_zero_eq |> allI ("B",mk_ob_sort) |> allE (rastt "B+B")|> undisch |> specl [rastt"c1:A->(B+B)",rastt"c2:A->(B+B)"]) >--
 subst1_tac (assume (rapf "c1:A ->(B+B) = c2")) *)
 
)
(rapg "areiso(A,0) ==> areiso(eqo(coeqa(i1(B,B) o f:A->B, i2(B,B) o f) o i1(B,B),coeqa(i1(B,B) o f, i2(B,B) o f) o i2(B,B)),0)")  






val (ct,asl,w) = cg $
e0 
(strip_tac >> 
 by_tac (rapf "i1(B, B) o f:A->B = i2(B, B) o f:A->B") 
 >-- (match_mp_tac from_iso_zero_eq >> arw_tac[]) >>
 first_x_assum subst1_tac
 (*match_mp_tac (contrapos (spec_all ax6) |> neg_neg_elim) >>
 ccontra_tac >> pop_assum $ x_choose_tac "t" >>*)
 (*abbrev_tac (rapf "(i1(B, B) o f:A->B) = c1") >>
 abbrev_tac (rapf "(i2(B, B) o f:A->B) = c2") >>
 assume_tac (from_iso_zero_eq |> allI ("B",mk_ob_sort) |> allE (rastt "B+B")|> undisch |> specl [rastt"c1:A->(B+B)",rastt"c2:A->(B+B)"]) >> 
 full_simp_tac[] >> 
 pop_assum (K all_tac) >> 
 match_mp_tac (contrapos (spec_all ax6) |> neg_neg_elim) >>
 ccontra_tac >> pop_assum $ x_choose_tac "t" >>
 x_choose_then "ki" assume_tac
 (coeq_of_equal |> gen_all |> allE (rastt "A") |>
                allE (rastt "B+B") |> allE (rastt "c2:A->(B+B)"))*)
)
(rapg "areiso(A,0) ==> areiso(eqo(coeqa(i1(B,B) o f:A->B, i2(B,B) o f) o i1(B,B),coeqa(i1(B,B) o f, i2(B,B) o f) o i2(B,B)),0)")  



ax1_5 |> spec_all |> conjE1


Theorem Thm3_A_zero_I_zero:
∀A B f h. f∶ A → B ∧ A≅ zero ⇒ 
          (eqo ((coeqa (i1 B B o f) (i2 B B o f)) o (i1 B B))
                  ((coeqa (i1 B B o f) (i2 B B o f)) o (i2 B B))) ≅ zero



Theorem eq_fac:
∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶X → A ∧ f ∘ h = g ∘ h ⇒
             eqa f g ∘ (eq_induce f g h)
