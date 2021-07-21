
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
          disch_all |> allI (dest_var $ rastt "x0:X->eqo(f:A->B,g:A->B)")

         

Theorem eq_fac:
∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶X → A ∧ f ∘ h = g ∘ h ⇒
             eqa f g ∘ (eq_induce f g h)
