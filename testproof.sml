structure Parse = struct val Term=readfq end

fun readfq [QUOTE s] = readf s

val ax1_5_applied = prove 
“ALL A.ALL B.ALL g. ALL f.ALL X.ALL h.(f: A ->B) o (h:X -> A) = g o h ==> (eqa(f, g) o eqinduce(f, g, h)) = h”
(repeat stp_tac >> drule
                 (conjE2 (specl ax1_5
                      (List.map readt 
                                ["A","B","f:A -> B","g:A -> B","X",
                                 "eqinduce(f:A -> B, g: A -> B, h:X -> A)",
                                 "h: X ->A"])
                     )) >> assum_list rw_tac >> T_INTRO_TAC)

val ax1_5_applied = 
    gen_all
        (disch “(f: A -> B) o (h: X -> A) = g o h”
          (dimp_mp_r2l 
               (iff_trans
                    (inst_thm (mk_inst [(("x0",
                                          ar
                                              (Var ("X", ob),
                                               Fun
                                                   ("eqo", ob,
                                                    [Var ("f", ar (Var ("A", ob), Var ("B", ob))),
                                                     Var ("g", ar (Var ("A", ob), Var ("B", ob)))]))),
                                         readt "eqinduce(f:A -> B,g,h:X -> A)")] []) (undisch (conjE2 (spec_all ax1_5))))
                    (equivT (refl (readt "eqinduce(f:A -> B,g,h:X -> A)"))))
               (trueI [])))

val compose_assoc_5_4_left = gen_all
(prove (rapf "(f5 o f4 o f3 o f2 o f1) = (f5 o (f4 o (f3 o f2))) o f1")
 (rw_tac [spec_all o_assoc]))

val compose_assoc_5_4_left' = gen_all
(prove (rapf "(f5 o f4 o f3 o f2 o f1) = (f5 o (f4 o (f3 o f2))) o f1")
 (rw_tac [o_assoc]))

val compose_assoc_5_4_left_SYM = gen_all
(prove (readf "(f5 o f4 o f3 o f2) o f1 = f5 o f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))

val compose_assoc_5_4_left_SYM' = gen_all
(prove (rapf "(f5 o f4 o f3 o f2) o f1 = f5 o f4 o f3 o f2 o f1")
 (rw_tac [o_assoc]))

val compose_assoc_5_2_left = gen_all
(prove (readf "(f5 o f4) o f3 o f2 o f1 = f5 o f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))

val compose_assoc_5_2_left' = gen_all
(prove (rapf "(f5 o f4) o f3 o f2 o f1 = f5 o f4 o f3 o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_4_3_left = gen_all
(prove (readf "(f4 o f3 o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_3_left' = gen_all
(prove (rapf "(f4 o f3 o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_5_2_left_SYM = gen_all
(prove (readf "f5 o f4 o f3 o f2 o f1 = (f5 o f4) o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_5_2_left_SYM' = gen_all
(prove (rapf"f5 o f4 o f3 o f2 o f1 = (f5 o f4) o f3 o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_4_2_left = gen_all
(prove (readf "(f4 o f3) o f2 o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))

val compose_assoc_4_2_left' = gen_all
(prove (rapf "(f4 o f3) o f2 o f1 = f4 o f3 o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_4_2_middle = gen_all
(prove (readf "f4 o (f3 o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_middle' = gen_all
(prove (rapf "f4 o (f3 o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [o_assoc]))

val compose_assoc_4_2_middle_SYM = gen_all
(prove (readf "f4 o f3 o f2 o f1 = f4 o (f3 o f2) o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_middle_SYM' = gen_all
(prove (rapf "f4 o f3 o f2 o f1 = f4 o (f3 o f2) o f1")
 (rw_tac [o_assoc]))


val compose_assoc_4_2_left_SYM = gen_all
(prove (readf "f4 o f3 o f2 o f1 = (f4 o f3) o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_left_SYM' = gen_all
(prove (rapf "f4 o f3 o f2 o f1 = (f4 o f3) o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_4_2_left_middle = gen_all
(prove (readf "(f4 o f3) o f2 o f1 = f4 o (f3 o f2) o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))



val compose_assoc_4_2_left_middle' = gen_all
(prove (rapf "(f4 o f3) o f2 o f1 = f4 o (f3 o f2) o f1")
 (rw_tac [o_assoc]))

val compose_assoc_4_2_left_left = gen_all
(prove (readf "((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_left_left' = gen_all
(prove (rapf "((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_4_2_left_left = gen_all
(prove (readf "((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_left_left' = gen_all
(prove (rapf "((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_5_2_left1_left = gen_all
(prove (readf "f5 o (f4 o f3) o f2 o f1 = (f5 o f4) o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_5_2_left1_left' = gen_all
(prove (rapf "f5 o (f4 o f3) o f2 o f1 = (f5 o f4) o f3 o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_6_3_2_left_middle = gen_all
(prove (readf "(f6 o f5 o f4) o f3 o f2 o f1 = f6 o f5 o (f4 o f3) o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_6_3_2_left_middle' = gen_all
(prove (rapf "(f6 o f5 o f4) o f3 o f2 o f1 = f6 o f5 o (f4 o f3) o f2 o f1")
 (rw_tac [o_assoc]))


val compose_assoc_6_left_left_left_right2 = gen_all
(prove (readf "(((f6 o f5 o f4) o f3) o f2) o f1 = f6 o f5 o f4 o (f3 o f2) o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_6_left_left_left_right2' = gen_all
(prove (rapf "(((f6 o f5 o f4) o f3) o f2) o f1 = f6 o f5 o f4 o (f3 o f2) o f1")
 (rw_tac [o_assoc]))


(*' version is with the new rw*)

(*rw_tac can prove all these examples in one proof!*)

(*Q1: why does assum list loop!*)

(*TODO: Change rw_tac into without spec!*)


(*
 rewr_conv (assume (readf "a = b")) (readt "x");
Exception- ERR "current term not alloed to be instantiated" raised
> rw_tac [assume f] (fvf (readf "u = v"),[],readf "u = v");
poly: : error: Value or constructor (f) has not been declared Found near [assume f]
Static Errors
> val f = readt "x = y";
Exception- ERROR "Extra characters in formula" raised
> val f = readf "x = y";
val f = x = y: form
> rw_tac [assume f] (fvf (readf "u = v"),[],readf "u = v");
val it = ([(HOLset{("u", ob), ("v", ob)}, [], u = v)], fn):
   goal list * validation
> rw_tac [assume f] (fvf f,[],f);
val it = ([(HOLset{("x", ob), ("y", ob)}, [], y = y)], fn):
   goal list * validation


*)
val o_bracket_left = proved_th
                         (expandf 
                              ((repeat gen_tac) >> rw_tac[spec_all o_assoc] >>
                                                stp_tac >> 
                                                accept_tac (assume (readf "((f:Z->A) o ((b:Y->Z) o (a:X ->Y)))=((g:Z ->A) o ((d:Y -> Z) o c))"))) 
                              (read_goal "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.f o b o a = g o d o c ==> (f o b) o a = (g o d) o c"))


val o_bracket_left0 =
                         (expandf 
                              ((repeat stp_tac) >> arw_tac[spec_all o_assoc])
                              (read_goal "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.f o b o a = g o d o c ==> (f o b) o a = (g o d) o c"))



val o_bracket_left0 =
                         (expandf 
                              ((repeat stp_tac) >> rw_tac[spec_all o_assoc] >> assum_list rw_tac)
                              (read_goal "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.f o b o a = g o d o c ==> (f o b) o a = (g o d) o c"))

(*
RULE_ASSUM_TAC for making change of assumptions
*)



(*should be proved if rw with o_assoc and assum list, but will loop if we actually do this*)

(*∀X Y Z A a b c d f g.
 f o b o a = g o d o c ∧ a∶ X → Y ∧ c∶ X → Y ∧ b∶ Y → Z ∧ d∶ Y → Z ∧
 f∶ Z → A ∧ g∶ Z → A ⇒ (f o b) o a = (g o d) o c*)


(*Q2: rw the assumptions, not with the assumptions... *)

val o_bracket_right = proved_th
                         (expandf 
                              ((repeat gen_tac) >> rw_tac[spec_all o_assoc] >>
                                                stp_tac >>
accept_tac (assume (readf "((f:Z->A) o ((b:Y->Z) o (a:X ->Y)))=((g:Z ->A) o ((d:Y -> Z) o c))"))) 
                              (read_goal "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.(f o b) o a = (g o d) o c ==> f o b o a = g o d o c"))


(*∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶X → A ∧ f ∘ h = g ∘ h ⇒
             eqa f g ∘ (eq_induce f g h) = h*)

val eq_fac = proved_th 
(expandf (repeat stp_tac >> drule (spec_all ax1_5_applied) >> 
accept_tac (assume (readf "eqa(f:A -> B,g) o eqinduce(f,g,h:X -> A) = h"))) 
(read_goal "ALL A.ALL B.ALL f:A -> B. ALL g:A -> B.ALL X. ALL h: X -> A. f o h = g o h ==>eqa(f,g) o eqinduce(f,g,h) = h"))

(*Q3: unique exists!*)

(*put it into the kernel and let the parser parse it/ a rule for it, turing it into a definition/
only up to isomorphism for objects?

 *)

(*Q4: thing I need to do instead of T_INTRO_TAC?*)

val ax1_6_applied = prove 
(readf "ALL A.ALL B.ALL g. ALL f.ALL X.ALL h. (h:B -> X) o (f: A ->B) = h o g ==> coeqinduce(f, g, h) o coeqa(f, g) = h")
(repeat stp_tac >> drule
                 (conjE2 (specl ax1_6
                      (List.map readt 
                                ["A","B","f:A -> B","g:A -> B","X",
                                 "coeqinduce(f:A -> B, g: A -> B, h:B -> X)",
                                 "h: B ->X"])
                     )) >> assum_list rw_tac >> T_INTRO_TAC)
 

val coeq_fac = proved_th 
(expandf (repeat stp_tac >> drule (spec_all ax1_6_applied) >> 
accept_tac (assume (readf "coeqinduce(f,g,h:B -> X) o coeqa(f:A -> B,g) = h"))) 
(read_goal "ALL A.ALL B.ALL f:A -> B. ALL g:A -> B.ALL X. ALL h: B -> X. h o f = h o g ==> coeqinduce(f,g,h) o coeqa(f,g) = h"))


(*should I do a normalisation on th list to turn a = b into a = b <=> T in fconv0?
TODO: SOMe normalisation precedure, but not "a = b <=> T"
*)

(*
val aeqb =
(expandf (repeat stp_tac >> rw_tac[] >> )
(read_goal "ALL A. ALL B. A = B ==> A = B"))
*)

val ax_exp0 =  
    gen_all 
        (dimp_mp_r2l
             (specl ax_exp 
                    [mk_ob "A",mk_ob "B",mk_ob "X",
                     Var("g",mk_ar_sort (po (mk_ob "A") (mk_ob "X")) (mk_ob "B")),readt "tp(g: A * X -> B)"])
             (refl (readt "tp(g: A * X -> B)")))



(*∀A B X f. f∶A × X → B ⇒ ev A B ∘ ⟨p1 A X, tp f ∘ p2 A X⟩ = f*)

(*VALID tac apply the tactic to the goal, and  
pretend the goal is theorem
*)




(*Q5: current setting the tactics may throw in other things
PROVED!(A : ob),
   (B : ob),
   (X : ob),
   (f : (A * X) -> B)
   tp(f) = tp(f)
   |-
   (ev(A, B) o pa(p1(A, X), (tp(f) o p2(A, X)))) = f




A : ob),
   (B : ob),
   (X : ob),
   (f : (A * X) -> B)
   |-
   (ev(A, B) o pa(p1(A, X), (tp(f) o p2(A, X)))) = f


if use assume_tac with (assume "this equation")

it is ture that is adds assumption, but in that case it shoud complain about the extra assumption, instead claiming that the goal is proved.
*)



val ev_of_tp = proved_th
(expandf (assume_tac (refl (readt "tp(f:A * X -> B)")) >> 
         drule (dimpr2l (spec_all ax_exp)) >>
         accept_tac (assume (readf "ev(A,B) o pa(p1(A,X),tp(f) o p2(A,X)) = f")))
(read_goal "ev(A,B) o pa(p1(A,X),tp(f) o p2(A,X)) = f"))
 

(*

validity check works
(e (assume_tac (assume (readf "tp(f:A * X -> B) = tp(f)")) >> 
         drule (dimpr2l (spec_all ax_exp)) >>
         accept_tac (assume (readf "ev(A,B) o pa(p1(A,X),tp(f) o p2(A,X)) = f")))
(read_goal "ev(A,B) o pa(p1(A,X),tp(f) o p2(A,X)) = f"))
*) 

(*(tp f = tp g ⇔ f = g)*)

(*should I have (fVar f <=> fVar f') <=> (fVar f ==> fVar f' & fVar f' ==> fVar f)*)


(*TO-DO: reverse the order of pp of gstk done*)

val tp_eq = proved_th
                (expandf (dimp_tac >> stp_tac >> arw_tac[] >> 
                                   fconv_tac (pred_fconv (rewr_conv (GSYM ev_of_tp))) >> 
                                   arw_tac[])
                         (rpg "tp (f) = tp (g) <=> f = g"))

val tp_eq = proved_th
 (expandf (dimp_tac >> stp_tac >> arw_tac[] >> 
                    once_rw_tac[(GSYM ev_of_tp)] >> arw_tac[])
          (rpg "tp (f) = tp (g) <=> f = g"))



(*
(rw_tac [assume (readf "(f: B * A -> C) = g")])

but should not loop if I give it f = g without assumption, 
(fvf (rapf "f: B * A -> C = g"),[]:form list,rapf "tp(f:B * A -> C) = tp(g)")
*)
(* TODO:
∀A B X f h. f∶ A × X → B ∧ h∶ X → exp A B ∧
            (ev A B) o ⟨p1 A X, h o (p2 A X)⟩ = f ⇒
            h = tp f *)


(*
(A : ob),
   (B : ob),
   (X : ob),
   (f : A * X -> B),
   (h : X -> exp(A, B))
   
   ----------------------------------------------------------------------
   h = tp(f) ==> h = tp(f)
test rule assum here

maybe add (equivT o conjE1 o dimpE) (frefl (fVar "f"))
*)

val is_tp = proved_th(
e (rw_tac[spec_all ax_exp] >> rw_tac[(equivT o conjE1 o dimpE) (frefl (fVar "f"))])
(rapg "ev(A,B) o < p1(A,X), h o p2(A,X)> = f ==> h = tp(f)"))


val is_tp = proved_th(
expandf (rw_tac[spec_all ax_exp,(equivT o conjE1 o dimpE) (frefl (fVar "f"))])
(rapg "ev(A,B) o < p1(A,X), h o p2(A,X)> = f ==> h = tp(f)"))

val ev_eq_eq = 
    gen_all
        (disch 
             (readf "ev(A,B) o pa(p1(A, X), tp(g) o p2(A, X)) = ev(A,B) o pa(p1(A, X), tp(f) o p2(A, X))")
             (trans
                  (trans
                       (GSYM
                            (specl ax_exp0
                                   (List.map readt ["A","B","X","g:A * X -> B","tp(g: A * X -> B)"])))
                       (assume (readf "ev(A,B) o pa(p1(A, X), tp(g) o p2(A, X)) = ev(A,B) o pa(p1(A, X), tp(f) o p2(A, X))")))

                  (specl ax_exp0
                         (List.map readt ["A","B","X","f:A * X -> B","tp(f: A * X -> B)"]))))



val to_p_components = 
    gen_all
        (GSYM
             (dimp_mp_l2r 
                  (conjI 
                       (refl (readt "p1(A,B) o (fg: X -> A * B)"))
                       (refl (readt "p2(A,B) o (fg: X -> A * B)")))
                  (specl ax_pr (List.map readt ["A","B","X","fg: X -> A * B",
                                                "p1(A,B) o (fg: X -> A * B)",
                                                "p2(A,B) o (fg: X -> A * B)"]))))



val to_p_eq = 
gen_all
(
disch (readf "p2(A,B) o (g : X -> A * B) = p2(A,B) o (f : X -> A * B)")

(disch (readf "p1(A,B) o (g : X -> A * B) = p1(A,B) o (f : X -> A * B)")

(trans
(trans
(GSYM
     (specl to_p_components
            (List.map readt 
                      ["A","B","X","(g: X -> A * B)"])))

(EQ_fsym "pa" (* (sort_of (readt "(f : X -> A * B)")) *)
[(assume (readf "p1(A,B) o (g : X -> A * B) = p1(A,B) o (f : X -> A * B)")),
 (assume (readf "p2(A,B) o (g : X -> A * B) = p2(A,B) o (f : X -> A * B)"))]))


(specl to_p_components
            (List.map readt 
                      ["A","B","X","(f: X -> A * B)"]))))
)


val from_cop_components = 
    gen_all
        (GSYM
             (dimp_mp_l2r 
                  (conjI 
                       (refl (readt "(fg: A+B ->X) o i1(A,B)"))
                       (refl (readt "(fg: A+B ->X) o i2(A,B)")))
                  (specl ax_copr (List.map readt ["A","B","X","fg: A+B ->X",
                                                "(fg: A+B ->X) o i1(A,B)",
                                                "(fg: A+B ->X) o i2(A,B)"]))))


val i1_ne_i2 = 
existsE ("X",ob)
ax8
(
existsE ("x1",sort_of (readt "x1: 1 -> X"))
(assume (readf "EXISTS x1.EXISTS x2:1-> X. ~x1 = x2"))
(
existsE ("x2",sort_of (readt "x2: 1 -> X"))
(assume (readf "EXISTS x2:1-> X. ~x1 = x2"))

(negI
(negE
(trans
(trans
(sym (conjE1
    (dimp_mp_r2l
    (specl ax_copr 
          (List.map readt ["1","1","X","copa(x1:1 -> X,x2:1 -> X)",
                           "x1:1 -> X","x2:1 -> X"]))
    (refl (readt "copa(x1:1 -> X,x2:1 -> X)"))))
)

(EQ_fsym "o" (* (sort_of (readt "x:1 -> X")) *)
    [refl (readt "copa(x1:1 -> X,x2:1 -> X)"),assume (readf "i1(1,1) = i2(1,1)")]))

(conjE2
    (dimp_mp_r2l
    (specl ax_copr 
          (List.map readt ["1","1","X","copa(x1:1 -> X,x2:1 -> X)",
                           "x1:1 -> X","x2:1 -> X"]))
    (refl (readt "copa(x1:1 -> X,x2:1 -> X)"))))
)

   (assume (readf "~x1:1 -> X = x2: 1 -> X"))
)

 (readf "i1(1,1) = i2(1,1)") 
)
)
)

val to1_unique = gen_all
(trans
(spec_all ax_tml)
(sym (specl ax_tml (List.map readt ["X","tx1:X -> 1"]))))

val from0_unique = gen_all
(trans
(spec_all ax_inl)
(sym (specl ax_inl (List.map readt ["X","ix1: 0 -> X"]))))


val i1_of_copa = gen_all
(conjE1
(
dimp_mp_r2l 
(
specl ax_copr
(List.map readt ["A","B","X","copa(f: A -> X,g:B -> X)","f: A -> X","g:B -> X"])
)
(refl (readt "copa(f: A -> X,g:B -> X)"))
)
)

val i2_of_copa = gen_all
(conjE2
(
dimp_mp_r2l 
(
specl ax_copr
(List.map readt ["A","B","X","copa(f: A -> X,g:B -> X)","f: A -> X","g:B -> X"])
)
(refl (readt "copa(f: A -> X,g:B -> X)"))
)
)

val id1_to1 = 
    specl to1_unique (List.map readt ["1","to1(1)","id(1)"])

val tx1_id1 = 
    gen_all
        (specl to1_unique
               (List.map readt ["1","tx:1 -> 1","id(1)"]))


(*EQ_refl produces ill-formed:
 # # # # # val it =
   (A : ob),
   (B : ob),
   (x1 : 1() -> A)
   
   ----------------------------------------------------------
   1() i1 1() o to1(A) copa 1() i2 1() o to1(B) o A i2 B o x1 = 1() i2 1() o
     to1(B) o x1: thm
*)

(*how to add "()" only when needed but not everywhere?*)

val prop_5_lemma = 
let 

    val eq1 = 
EQ_fsym "o" (*sort_of (readt "f: 1 -> 1 + 1")*)
[refl 
     (readt "copa(i1(1,1) o to1(A),i2(1,1) o to1(B))"),
trans
(sym
(conjE1 (
assume 
(readf "x = i1(A,B) o (x0:1 -> A) & x = i2(A,B) o (x1:1 -> B)")
))
)

(conjE2 (
assume 
(readf "x = i1(A,B) o (x0:1 -> A) & x = i2(A,B) o (x1:1 -> B)")
))]




    val t1 = 
readt "(copa(i1(1,1) o to1(A), i2(1,1) o to1(B)) o i1(A,B)) o (x0:1 -> A)"
    val t1eqLeq = top_depth_conv (rewr_conv (spec_all o_assoc)) t1
    val eq1' = 
        EQ_fsym "o" (*sort_of (readt "f: 1 -> 1 + 1")*)
                [specl i1_of_copa
                       (List.map readt 
                                 ["A","B","1+1","i1(1,1) o (to1(A))","i2(1,1) o (to1(B))"])
,
  refl (readt "x0: 1 -> A")]
    val Leq1' = trans (sym t1eqLeq) eq1'
    val o2i1 = 
        let val t0 = readt "i1(1,1) o to1(A) o x0"
            val R_Leq1'eqt0 = 
                top_depth_conv (rewr_conv (spec_all o_assoc)) 
                               (#2 (dest_eq(concl Leq1')))
            val t0eqi1 = trans
                (EQ_fsym "o" (*sort_of (readt "f: 1 -> 1 + 1")*)
                    [(refl (readt "i1(1,1)")),
                    (specl tx1_id1 [readt "to1(A) o x0:1 -> A"])])
                (specl idR 
                       (List.map readt
                                 ["1","1+1","i1(1,1)"]))
        in trans R_Leq1'eqt0 t0eqi1
        end
    val Leqi1 = trans Leq1' o2i1






    val t2 = 
readt "(copa(i1(1,1) o to1(A), i2(1,1) o to1(B)) o i2(A,B)) o (x1:1 -> B)"
    val t2eqReq = top_depth_conv (rewr_conv (spec_all o_assoc)) t2
    val eq2' = 
        EQ_fsym "o" (*sort_of (readt "f: 1 -> 1 + 1")*)
                [specl i2_of_copa
                       (List.map readt 
                                 ["A","B","1+1","i1(1,1) o (to1(A))","i2(1,1) o (to1(B))"])
,
  refl (readt "x1: 1 -> B")]
    val Req2' = trans (sym t2eqReq) eq2'
    val o2i2 = 
        let val t0 = readt "i2(1,1) o to1(B) o x1"
            val R_Req2'eqt0 = 
                top_depth_conv (rewr_conv (spec_all o_assoc)) 
                               (#2 (dest_eq(concl Req2')))
            val t0eqi2 = trans
                (EQ_fsym "o" (*sort_of (readt "f: 1 -> 1 + 1")*)
                    [(refl (readt "i2(1,1)")),
                    (specl tx1_id1 [readt "to1(B) o x1:1 -> B"])])
                (specl idR 
                       (List.map readt
                                 ["1","1+1","i2(1,1)"]))
        in trans R_Req2'eqt0 t0eqi2
        end
    val Reqi2 = trans Req2' o2i2


    val i1eqi2 = trans (trans (sym Leqi1) eq1) Reqi2
    val contra = negE i1eqi2 i1_ne_i2
in
gen_all
(
negI 

(
existsE ("x1",sort_of (readt "x1 : 1-> B"))

(assume 
     (readf "EXISTS x1.EXISTS x0.x = i1(A,B) o (x0:1 -> A) & x = i2(A,B) o (x1:1 -> B)"))

(existsE ("x0",sort_of (readt "x0 : 1-> A"))
(assume 
(readf "EXISTS x0.x = i1(A,B) o (x0:1 -> A) & x = i2(A,B) o (x1:1 -> B)"))
contra)
)

(readf "EXISTS x1.EXISTS x0.x = i1(A,B) o (x0:1 -> A) & x = i2(A,B) o (x1:1 -> B)")
)
end



(*∀f g X A B. f∶ (A+ B) → X ∧ g∶ (A + B) → X ⇒
            (f o (i1 A B) = g o (i1 A B) ∧ f o (i2 A B) = g o (i2 A B) ⇔ f = g)*)

(*suggesions on 
(A : ob),
   (B : ob),
   (C : ob),
   (f : A + B -> C),
   (g : A + B -> C)
   
   ----------------------------------------------------------------------
   f = copa(g o i1(A, B), g o i2(A, B)) <=> f = g

?

*)

(*
e
(rw_tac[spec_all ax_copr,refl (readt "(fg:A + B -> C) o i1(A,B)"),
        refl (readt "(fg:A + B -> C) o i2(A,B)")])
(rapg "copa(fg o i1(A,B), fg o i2(A,B)) = fg")
loops

maybe add changed_conv
)

*)


(*
TODO: how to deal with this?
(A : ob),
   (B : ob),
   (C : ob),
   (fg : A + B -> C)
   fg o i1(A, B) = fg o i1(A, B) & fg o i2(A, B) = fg o i2(A, B) <=> fg =
       copa(fg o i1(A, B), fg o i2(A, B))
   ----------------------------------------------------------------------
   copa(fg o i1(A, B), fg o i2(A, B)) = fg
*)

(*
val from_cop_components = proved_th(
e
(assume_tac (specl ax_copr (List.map readt ["A","B","C","fg: A+B->C","(fg:A + B -> C) o i1(A,B)","(fg:A + B -> C) o i2(A,B)"])))
(rapg "copa(fg o i1(A,B), fg o i2(A,B)) = fg")

)
*)



val from_cop_components = 
    gen_all
        (GSYM
             (dimp_mp_l2r 
                  (conjI 
                       (refl (readt "(fg: A+B ->X) o i1(A,B)"))
                       (refl (readt "(fg: A+B ->X) o i2(A,B)")))
                  (specl ax_copr
                         (List.map readt ["A","B","X","fg: A+B ->X",
                                                "(fg:A+B->X) o i1(A,B)",
                                                "(fg:A+B->X) o i2(A,B)"]))))


(*TODO:need once_rw_tac[spec_all from_cop_components] >> once_rw_tac[]! otherwise get g = g remains *)

val from_cop_eq = proved_th
(
e (rw_tac[spec_all ax_copr] >> dimp_tac >> stp_tac >> arw_tac[]
         >> rw_tac [spec_all from_cop_components])
         (*fconv_tac (sub_fconv (rewr_conv (GSYM from_cop_components)) no_fconv) ) *)
      (*   >> once_rw_tac [GSYM from_cop_components] *)
         
(rapg "f o i1(A,B) = g o i1(A,B) & f o i2(A,B) = g o i2(A,B) <=> f = g")

)


(*!X t. t∶ one → X ==> i1 X X o t <> i2 X X o t*)
(*need ( ) after the ~*)

(*parser bug (rapg "~ (i1(X,X) o (t:1->X) = i2(X,X) o t)")*)

(*
 # val it =
   (A : ob),
   (B : ob)
   
   |-
   ALL (x : 1 -> A + B).
       ~EXISTS (x1 : 1 -> B).
         EXISTS (x0 : 1 -> A). x = i1(A, B) o x0 & x = i2(A, B) o x1: thm


should complain in that case

*)


(*e says:
ERR
     "formula has the wrong formEXISTSx0.((X i2 X) o t) = ((X i1 X) o t)&((X i2 X) o t) = ((X i2 X) o t)"

but expandf does not?
*)


(*TODO : rapf bug!
 val f1 = rapf "~(EXISTS x1 : 1 -> X. EXISTS x0 : 1 -> X. i2(X, X) o t = i1(X, X) o x0 & i2(X, X) o (t:1->X) = i2(X, X) o x1)";
Exception- UNIFY "occurs check(pt):pv X : psv  0 ptu  0" raised

*)

val i1_i2_disjoint = 
let val f = rapf "EXISTS (x1 : 1 -> X). EXISTS (x0 : 1 -> X).i2(X, X) o t = i1(X, X) o x0 & i2(X, X) o t = i2(X, X) o x1"
in

proved_th(
e
(contra_tac >> 
 assume_tac 
(specl prop_5_lemma (List.map readt ["X","X","i2(X, X) o (t:1->X)"])) >> 
 by_tac (readf "EXISTS x1: 1 -> X. EXISTS x0 : 1 -> X. i2(X, X) o t = i1(X, X) o x0 & i2(X, X) o t = i2(X, X) o x1")
 >-- wexists_tac (readt "t:1-> X") >-- wexists_tac (readt "t:1-> X")  
 >-- arw_tac[] 
 >> assume_tac (negE (assume f) (assume (mk_neg f))) >> accept_tac (falseE [FALSE,f,mk_neg f] FALSE
)
)
(rpg "~ (i1(X,X) o (t:1->X) = i2(X,X) o t)")
)
end


(*contradiction between forall and exists, TODO: derive such a thm*)
(*
expandf 
(stp_tac >> wexists_tac (readt "c:A->B") >>
         wexists_tac (readt "d:C->D") >> arw_tac[] >> accept_tac (assume (readf "P(c:A -> B,d:C -> D)")))
(rapg "P(c:A -> B,d:C -> D) ==>EXISTS a:A -> B. EXISTS b:C -> D. P(a,b)")


val ft = readf "P(c:A -> B,d:C -> D)" 
val th = thm (fvf ft,[],ft)
val (n,s) = ("b",sort_of (readt "b:C->D"))
val t = (readt "d:C->D") 
existsI th (n,s) (readt "d:C->D") ()

val f = readf "EXISTS b:C -> D. P(c:A->B,b)";


for debugging
*)


(*TODO: turn off the pp and then the whole thing still works...*)
(*po A one ≅ A po_with_one*)

val p1_of_pa = gen_all
(conjE1 (dimp_mp_r2l 
     (specl ax_pr (List.map readt ["A","B","X","pa(f:X->A,g:X -> B)","f:X->A","g:X->B"])) (refl (readt "pa(f:X->A,g:X -> B)"))))


val p2_of_pa = gen_all
(conjE2 (dimp_mp_r2l 
     (specl ax_pr (List.map readt ["A","B","X","pa(f:X->A,g:X -> B)","f:X->A","g:X->B"])) (refl (readt "pa(f:X->A,g:X -> B)"))))

(*
fun rapfq [QUOTE s] = rapf s 
    rapfq ‘a=b’

rapf "a = b"

*)

(*rapf bug, TODO: rapf "p2(A, B) o g:X->A * B = p2(A, B) o f" not an infix operator*)
val to_p_eq' =
    let val h1 = rapf "p2(A, B) o (g:X->A * B) = p2(A, B) o f"
        val h2 = rapf "p1(A, B) o (g:X->A * B) = p1(A, B) o f"
        val a = assume (mk_conj h1 h2)
        val a1 = conjE1 a 
        val a2 = conjE2 a
        val th0 = mp (mp (spec_all to_p_eq) a1) a2
    in gen_all (disch (mk_conj h1 h2) th0)
    end


val po_with_one = proved_th(
e
(rw_tac[spec_all areiso_def] >> wexists_tac (readt "p1(A,1)") >>
 wexists_tac (readt "pa(id(A),to1(A))") >> conj_tac >> 
 rw_tac[spec_all p1_of_pa] >> match_mp_tac to_p_eq' >> conj_tac >>
 rw_tac[spec_all idR]
 >-- by_tac (rapf "p2(A, 1) o pa(id(A), to1(A)) o p1(A, 1)=(p2(A, 1) o pa(id(A), to1(A))) o p1(A, 1)") 
 >-- rw_tac[spec_all o_assoc] >-- arw_tac[spec_all p2_of_pa](*
 >-- rw_tac[spec_all to1_unique] TODO: if do so, then loops *)
 >-- accept_tac (specl to1_unique (List.map readt ["A * 1","to1(A) o p1(A, 1)","p2(A, 1)"]))
 >> by_tac (rapf "p1(A, 1) o pa(id(A), to1(A)) o p1(A, 1)=(p1(A, 1) o pa(id(A), to1(A))) o p1(A, 1)")
 >> rw_tac[spec_all o_assoc] >> arw_tac[spec_all p1_of_pa] >>
 rw_tac[spec_all idL]
)
(rapg "areiso(A * 1,A)")
)

(*
∀A B C D P Q f g i j. f∶ A → C ∧ g∶ B → D ∧ i∶ C → P ∧ j∶ D → Q ⇒
                      ⟨i o p1 C D,j o p2 C D⟩ o ⟨f o p1 A B, g o p2 A B⟩ =
                      ⟨i o f o p1 A B, j o g o p2 A B⟩
*)

val parallel_p_compose = proved_th(
e
(match_mp_tac to_p_eq' >> conj_tac
 >-- by_tac 
     (readf "p2(F, E) o pa((i o p1(C, D)),(j o p2(C, D))) o pa(f o p1(A, B), g o p2(A, B)) = (p2(F, E) o pa((i o p1(C, D)), (j o p2(C, D)))) o pa(f o p1(A, B), g o p2(A, B))")
 >-- rw_tac[spec_all o_assoc]
 >-- arw_tac[spec_all p2_of_pa]
 >-- by_tac 
 (readf "((j:D->E) o p2(C, D)) o pa(f o p1(A, B), g o p2(A, B)) = j o p2(C, D) o pa(f o p1(A, B), g o p2(A, B))")
 >-- rw_tac[spec_all o_assoc] (*solve the added formula added*)
 >-- arw_tac[spec_all p2_of_pa] (*solve first goal*)
 >> (*maybe same as the whole block before*)
by_tac 
     (readf "p1(F, E) o pa((i o p1(C, D)),(j o p2(C, D))) o pa(f o p1(A, B), g o p2(A, B)) = (p1(F, E) o pa((i o p1(C, D)), (j o p2(C, D)))) o pa(f o p1(A, B), g o p2(A, B))")
 >-- rw_tac[spec_all o_assoc]
 >-- arw_tac[spec_all p1_of_pa]
 >-- by_tac 
 (readf "((i:C->F) o p1(C, D)) o pa(f o p1(A, B), g o p2(A, B)) = i o p1(C, D) o pa(f o p1(A, B), g o p2(A, B))")
 >-- rw_tac[spec_all o_assoc] (*solve the added formula added*)
 >-- arw_tac[spec_all p1_of_pa] (*solve first goal*)
)
(rapg "<i o p1(C,D),j o p2(C,D)> o <f o p1(A,B), g o p2(A,B)> =<i o f o p1(A,B), j o g o p2(A,B)>")
)

(*
Theorem parallel_p_one_side:
∀A B C D f g.f∶ B → C ∧ g∶ C→ D ⇒
             ⟨p1 A B,g o f o p2 A B⟩ =
             ⟨p1 A C, g o p2 A C⟩ o ⟨p1 A B, f o p2 A B⟩

*)

val parallel_p_one_side = proved_th(
e
(match_mp_tac to_p_eq' >> conj_tac >> rw_tac[spec_all p1_of_pa,spec_all p2_of_pa] >> once_rw_tac[GSYM o_assoc] >>  rw_tac[spec_all p1_of_pa,spec_all p2_of_pa] 
  >> rw_tac[spec_all o_assoc,spec_all p2_of_pa] )
(rapg "<p1(A,B),g o f o p2(A,B)> = <p1(A,C), g o p2(A,C)> o <p1(A,B),f o p2(A,B)>")
)

(*∀A B C D f g.f∶ B → C ∧ g∶ C→ D ⇒
             ⟨p1 A B,(g o f) o p2 A B⟩ =
             ⟨p1 A C, g o p2 A C⟩ o ⟨p1 A B, f o p2 A B⟩*)

(*TODO: may need to be simpler? rewr_conv on it and then accept tac?*)

val parallel_p_one_side' = proved_th(
e 
(rw_tac[spec_all o_assoc] >> accept_tac parallel_p_one_side)
(rapg "<p1(A,B),(g o f) o p2(A,B)> = <p1(A,C), g o p2(A,C)> o <p1(A,B),f o p2(A,B)>")
)
(*
Theorem parallel_p_one_side_three:
∀A B C D E f g h.
         f∶B → C ∧ g∶C → D /\ h ∶ D → E ⇒
         ⟨p1 A B,(h o g ∘ f) ∘ p2 A B⟩ =
         ⟨p1 A D, h ∘ p2 A D⟩ o ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩
*)

(*maybe TODO:

(A : ob),
   (B : ob),
   (C : ob),
   (D : ob),
   (E : ob),
   (f : B -> C),
   (g : C -> D),
   (h : D -> E)
   
   ----------------------------------------------------------------------
   p1(A, B) = (p1(A, D) o pa(p1(A, C), g o p2(A, C))) o
     pa(p1(A, B), f o p2(A, B))

once_rw_tac[GSYM o_assoc,spec_all p1_of_pa]

does not use p1_of_pa at all
*)

val parallel_p_one_side_three = proved_th(
e
(match_mp_tac to_p_eq' >> conj_tac >> rw_tac[spec_all p1_of_pa,spec_all p2_of_pa] >> once_rw_tac[GSYM o_assoc]>> rw_tac[spec_all p1_of_pa,spec_all p2_of_pa]
>-- by_tac (rapf "(h o p2(A, D)) o pa(p1(A, C), (g o p2(A, C))) o pa(p1(A, B), f o p2(A, B)) = h o (p2(A, D) o pa(p1(A, C), (g o p2(A, C)))) o pa(p1(A, B), f o p2(A, B))")
>-- rw_tac[spec_all o_assoc]
>-- (arw_tac[spec_all p2_of_pa] >> rw_tac[spec_all o_assoc,spec_all p2_of_pa])>>
once_rw_tac[GSYM o_assoc] >> rw_tac[spec_all p1_of_pa]
)
(rapg "<p1(A,B),(h o g o f) o p2(A,B)> =<p1(A,D),h o p2(A,D)> o <p1(A,C),g o p2(A,C)> o <p1(A,B),f o p2(A,B)>")
)

(*
iterated_p_eq:
∀X A B C f g. f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ⇒
              (f = g ⇔
              (p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
              (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
              (p2 (A×B) C) o f = (p2 (A×B) C) o g)
*)

(*TODO: where is the procedure of splitting the assumptions done?*)
(*TODO: really want split conjunction rw_tac for dealing with 
 (A : ob),
   (B : ob),
   (C : ob),
   (D : ob),
   (f : D -> (A * B) * C),
   (g : D -> (A * B) * C)
   p1(A, B) o p1((A * B), C) o f = p1(A, B) o p1((A * B), C) o g &
       p2(A, B) o p1((A * B), C) o f = p2(A, B) o p1((A * B), C) o g &
         p2((A * B), C) o f = p2((A * B), C) o g
   ----------------------------------------------------------------------
   p2((A * B), C) o f = p2((A * B), C) o g

*)

val iterated_p_eq = proved_th(
e
(dimp_tac >> repeat stp_tac >> arw_tac[] >> 
match_mp_tac to_p_eq' >> conj_tac
>-- accept_tac
(conjE2 (conjE2 (assume 
                     (rapf "p1(A,B) o p1 (A * B,C) o f = p1(A,B) o p1(A * B,C) o g & p2(A,B) o p1(A*B,C) o f = p2(A,B) o p1(A*B,C) o g& p2(A*B,C) o f =p2(A*B,C) o g")
        ))
)
>> match_mp_tac to_p_eq' >> conj_tac (* 2 *)
>-- accept_tac
(conjE1 (conjE2 (assume 
                     (rapf "p1(A,B) o p1 (A * B,C) o f = p1(A,B) o p1(A * B,C) o g & p2(A,B) o p1(A*B,C) o f = p2(A,B) o p1(A*B,C) o g& p2(A*B,C) o f =p2(A*B,C) o g")
        ))
)
>-- accept_tac
(conjE1 (assume 
                     (rapf "p1(A,B) o p1 (A * B,C) o f = p1(A,B) o p1(A * B,C) o g & p2(A,B) o p1(A*B,C) o f = p2(A,B) o p1(A*B,C) o g& p2(A*B,C) o f =p2(A*B,C) o g")
        ))
)
(rapg 
"f = g <=> p1(A,B) o p1 (A * B,C) o f = p1(A,B) o p1(A * B,C) o g & p2(A,B) o p1(A*B,C) o f = p2(A,B) o p1(A*B,C) o g& p2(A*B,C) o f =p2(A*B,C) o g")
)


val iterated_p_eq_applied = (conjE2 o dimpE) iterated_p_eq

(*
Theorem N_ind_z_s_id:
id N = N_ind z s
*)

(*TODO: maybe serious problem: rw_tac[spec_all idL,spec_all idR] does not solve


   ----------------------------------------------------------------------
   id(N) o z = z & id(N) o s = s o id(N) 
and even do not solve them individually
*)

val N_ind_z_s_id = proved_th
(
e 
(match_mp_tac
 (dimpl2r (specl ax_N (List.map readt ["N","z","id(N)","s"]))) >>
 conj_tac
 >-- accept_tac (specl idL (List.map readt ["1","N","z"]))
 >> accept_tac (trans (specl idL (List.map readt ["N","N","s"])) 
                      (sym (specl idR (List.map readt ["N","N","s"]))))
 
)
(rapg "id(N) = Nind(z,s)")
)
 

(*
trans  ((c1) (readt "id(N) o s")) ((arg_conv c1)(readt " s"));
Exception- ERR "equalities do not match(id(N) o s) = s s = s" raised
> (c1) (readt "id(N) o s");
val it =
   
   
   |-
   id(N) o s = s: thm
>  (arg_conv c1)(readt " s");
val it =
   
   
   |-
   s = s: thm
> val th1 = (c1) (readt "id(N) o s");
val th1 =
   
   
   |-
   id(N) o s = s: thm
> val th2 = (arg_conv c1)(readt " s");
val th2 =
*)
(*
val N_ind_z_s_id = proved_th
(
e 
(match_mp_tac
 (dimpl2r (specl ax_N (List.map readt ["N","z","id(N)","s"]))) >> conj_tac >>
 rw_tac[idL,idR] >> rw_tac[idL](*
 >-- accept_tac (specl idL (List.map readt ["1","N","z"]))
 >> accept_tac (trans (specl idL (List.map readt ["N","N","s"])) 
                      (sym (specl idR (List.map readt ["N","N","s"]))))
 *)
)
(rapg "id(N) = Nind(z,s)")
)
*)
(*
 basic_fconv (rewr_conv (spec_all idL)) no_fconv (readf "id(A) o f = f");
val it =
   ( 6 : ob),
   (A : ob),
   (f :  6 -> A)
   
   |-
   id(A) o f = f <=> T(): thm
> basic_fconv (rewr_conv (spec_all idL)) no_fconv (readf "id(N) o z = z");
val it =
   
   
   |-
   id(N) o z = z <=> id(N) o z = z: thm
> basic_fconv (rewr_conv (spec_all idL)) no_fconv (readf "id(N) o f = f");
val it =
   ( 5 : ob),
   (f :  5 -> N)
   
   |-
   id(N) o f = f <=> T(): thm

something wrong with the constants

*)

(*
Theorem comm_with_s_id:
∀f. f∶ N → N ∧ f o z = z ∧ f o s = s o f ⇒ f = id N
*)

(*TODO: if without gen_all, will display as: current 
Exception- ERR "current term not alloed to be instantiated" raised


f o z = z & f o s = s o f
   ----------------------------------------------------------------------
   f o z = z & f o s = s o f


if rw can split the assumptions in assumption list, then should solve the goal
*)

val comm_with_s_id = proved_th(
expandf 
(stp_tac >> rw_tac[N_ind_z_s_id] >>
match_mp_tac (gen_all (dimpl2r (spec_all ax3))) >>
accept_tac (assume (rapf "f o z = z & f o s = s o f"))
 )
(rapg "f o z = z & f o s = s o f ==> f = id(N)")
)

(*
to_p_eq_one_side:
∀A B f g. f∶ A → B ∧ g∶ A → B ∧ ⟨id A,f⟩ = ⟨id A,g⟩ ⇒ f = g

*)

(*TODO: test rule_assum_tac on this*)

val to_p_eq_one_side = proved_th(
e
(stp_tac >>
by_tac (rapf "p2(A,B) o <id(A),f> = p2(A,B) o <id(A),g>")
>-- arw_tac[] 
>> (*return to the main goal*)
rule_assum_tac (
let val fc = basic_fconv (rewr_conv (spec_all p2_of_pa)) no_fconv
in (fn th => dimp_mp_l2r th (fc (concl th)))
end
) >>
accept_tac (assume (rapf "f:A -> B = g"))
)
(rapg "<id(A),f> = <id(A),g> ==> f = g")
)


(*
Definition is_inc_def:
is_inc a b A ⇔ is_subset a A ∧ is_subset b A ∧ ∃h. h∶(dom a) → (dom b) ∧ b o h = a
End

*)
val psyms0 = insert_psym "isinc";

val isinc_def = define_pred(rapf "ALL A.ALL A0.ALL a:A0 ->A.ALL A1. ALL b:A1 ->A. isinc(a,b,A) <=> EXISTS h. b o h = a")

(*is_mono_thm:
∀A B m. m∶ A → B ⇒
        (is_mono m ⇔
        (∀X f g. f∶ X → A ∧ g∶ X → A ∧ m o f = m o g ⇒ f = g))*)

val is_mono_thm = (gen_all o dimpl2r o spec_all) ismono_def


(*
is_mono_applied:
∀A B m. m∶ A → B ∧
        (∀X f g. f∶ X → A ∧ g∶ X → A ∧ m o f = m o g ⇒ f = g) ⇒
        is_mono m

TO-DO: check the applied works for match_mp_tac (done)
*)
val is_mono_applied = (gen_all o dimpr2l o spec_all) ismono_def

(*
is_mono_property:
∀A B m. is_mono m ∧ m∶ A → B ⇒
(∀X f g. f∶ X → A ∧ g∶ X → A ∧ m o f = m o g ⇒ f = g)

same as is_mono_thm here

Definition is_mono_def:   
  is_mono f ⇔
  ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = dom f ∧ cod g2 = dom f ∧
          f o g1 = f o g2 ⇒ g1 = g2

maybe not useful thms here, we need them before, not sure if useful here.
*)

(*
Theorem post_inv_mono:
∀A B m i. m∶ A → B ∧ i∶ B → A ∧ (i o m) = id A ⇒ is_mono m
*)


(*TODO:rapf bug:
rapf "((i:B->A) o m:A-> B) o h = (i o m) o g"
 Exception- ERR "not an infix operator" raised


*)

(* TODO:
 arw_tac[] >-- rw_tac[spec_all idL] works, whereas 
arw_tac[spec_all idL] seems loops, but can be interuptted

 m o g = m o h, i o m = id(A)
   ----------------------------------------------------------------------
   h = g ==> h = g


should be automatically solved
*)

val post_inv_mono = proved_th(
e
(stp_tac >> match_mp_tac is_mono_applied >> repeat stp_tac >>
suffices_tac (rapf "((i:B->A) o (m:A-> B)) o (h:X-> A) = (i o m) o g") 
(*solving the suffices*)
>-- arw_tac[] >-- rw_tac[spec_all idL] >-- stp_tac >-- 
accept_tac (assume (rapf "h:X->A = g"))
>> (*done with suffices*)
rw_tac[spec_all o_assoc] >> arw_tac[]
)
(rapg "i o m = id(A) ==> ismono(m)")
)

(*

previous is_epi_def uses dom/cod stuff, now is_epi_thm can just be def

Theorem is_epi_thm:
∀e A B. e∶ A → B ⇒
       (is_epi e ⇔ (∀X f g. f∶ B → X ∧ g∶ B → X ∧ f o e = g o e ⇒ f = g))

*)

val psyms0 = insert_psym "isepi";

(*
TODO: define_pred does not update the dict for type-inference, so does ismono
# val it = isepi(f): form
> fvf it;
val it = HOLset{("f", ob)}: (string * sort) set
*)
 
val isepi_def = define_pred (readf "ALL A. ALL B. ALL e: A -> B. isepi(e) <=> ALL X.ALL f:B -> X. ALL g. f o e = g o e  ==> f = g")

val is_epi_thm = (gen_all o dimpl2r o spec_all) isepi_def

val is_epi_applied = (gen_all o dimpr2l o spec_all) isepi_def

(*have already checked that thm and applied look the same for mono and epi*)

(*
pre_inv_epi:
∀A B e i. e∶ A → B ∧ i∶ B → A ∧ e o i = id B ⇒ is_epi e
*)

val post_inv_mono = proved_th(
e
(stp_tac >> match_mp_tac is_mono_applied >> repeat stp_tac >>
suffices_tac (rapf "((i:B->A) o (m:A-> B)) o (h:X-> A) = (i o m) o g") 
(*solving the suffices*)
>-- arw_tac[] >-- rw_tac[spec_all idL] >-- stp_tac >-- 
accept_tac (assume (rapf "h:X->A = g"))
>> (*done with suffices*)
rw_tac[spec_all o_assoc] >> arw_tac[]
)
(rapg "i o m = id(A) ==> ismono(m)")
)

(*TODO: need check! the arw works here and does not work for that of mono
how to do it better than once_rw_tac[GSYM o_assoc] >> arw_tac[]? once arw_tac?
*)

val pre_inv_epi = proved_th(
e
(stp_tac >> match_mp_tac is_epi_applied >> repeat stp_tac >>
 suffices_tac (rapf "(f:B->X) o (e:A->B) o (i:B->A) = g o e o i") 
 >-- arw_tac[spec_all idR] 
 >-- stp_tac >-- accept_tac (assume (rapf "f:B -> X = g")) >>
 once_rw_tac[GSYM o_assoc] >> arw_tac[]
 )
(rapg "e o i = id(B) ==> isepi(e)")
)

(*

Definition is_pb_def:
is_pb P p q f g <=> cod f = cod g /\ p∶ P → dom f ∧ q∶ P → dom g /\
                      f o p = g o q ∧
                      (∀A u v. u∶ A → dom f ∧ v∶ A → dom g ∧ f o u = g o v ⇒
                      ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)
*)

val psyms0 = insert_psym "ispb"

(*TODO: remove () and check it works*)
val is_pb_def = define_pred (rapf 
"ALL X. ALL Z. ALL f: X -> Z. ALL Y. ALL g:Y -> Z. ALL P. ALL p:P-> X. ALL q:P->Y. ispb(P,p,q,f,g) <=> f o p = g o q & (ALL A. ALL u: A -> X. ALL v: A -> Y. f o u = g o v ==> EXISTS a:A -> P. (p o a = u & q o a = v & ALL b:A -> P. (p o b = u & q o b = v) ==> a = b))"
)

(*
eq_equlity:
∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ f ∘ eqa f g = g ∘ eqa f g
*)

val eq_equality = (conjE1 o spec_all) ax_eq'

val coeq_equality = (conjE1 o spec_all) ax_coeq'

(*
coeq_of_equal:
!f A B. f∶ A → B ==> ?ki. ki∶ coeqo f f → B /\ ki o (coeqa f f) = id B
*)

(*already checked that type inference works for coeqinduce*)

val coeq_of_equal = proved_th(
e
(wexists_tac (readt "coeqinduce(f:A-> B,f,id(B))") >> 
match_mp_tac ax1_6_applied >> rw_tac[]
)
(rapg "EXISTS ki. ki o (coeqa(f,f)) = id(B)")
)

(*
eqa_is_mono:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_mono (eqa f g)
*)
(*
TODO: 
(rapf "h = eqinduce (f1:A-> B,f2,eqa(f1,f2) o g:X -> eqo(f1,f2))") 

not an infix operator error
*)

(*if use arw for 
(A : ob),
   (B : ob),
   (X : ob),
   (f1 : A -> B),
   (f2 : A -> B),
   (g : X -> eqo(f1, f2)),
   (h : X -> eqo(f1, f2))
   h = eqinduce(f1, f2, eqa(f1, f2) o g), g =
     eqinduce(f1, f2, eqa(f1, f2) o g), eqa(f1, f2) o g = eqa(f1, f2) o h
   ----------------------------------------------------------------------
   h = g

then loop, not surprise

and once_arw leaves this:

 eqinduce(f1, f2, eqa(f1, f2) o g) = eqinduce(f1, f2, eqa(f1, f2) o g)
*)

(*TODO:AQ want match_mp_tac to work for 
f o h = g o h ==>
                     eqa(f, g) o x0 = h ==> x0 = eqinduce(f, g, h): thm
*)




val is_eqinduce = (gen_all o disch_all o 
                   (conj_assum
                        (rapf "(f:A-> B) o (h:X-> A) = g o h")
                        (rapf "eqa(f:A->B, g) o (x0:X->eqo(f,g)) = h:X->A")) o 
                   undisch o dimpl2r o undisch o conjE2 o spec_all) ax1_5

val is_coeqinduce = (gen_all o disch_all o 
                   (conj_assum
                        (rapf "(h:B-> X) o (f:A-> B) = h o g")
                        (rapf "(x0:coeqo(f,g) -> X) o coeqa(f:A->B, g) = h:B->X")) o 
                   undisch o dimpl2r o undisch o conjE2 o spec_all) ax1_6

(*The above two thms can be strengthen by moving ALL inwards*)

val eqa_is_mono = proved_th(
e
(match_mp_tac is_mono_applied >> repeat stp_tac >> 
 suffices_tac
 (rapf "h = eqinduce (f1:A-> B,f2,eqa(f1,f2) o (g:X -> eqo(f1,f2)))") 
 >-- suffices_tac
 (rapf "g = eqinduce (f1:A-> B,f2,eqa(f1,f2) o (g:X -> eqo(f1,f2)))") 
 >-- repeat stp_tac >-- once_arw_tac[] 
 >-- accept_tac (refl (readt "eqinduce(f1:A->B, f2, eqa(f1, f2) o (g:X->eqo(f1,f2)))"))
(*two goals remaining*)
 >> (match_mp_tac is_eqinduce >> rw_tac[] >> once_rw_tac[GSYM o_assoc] >>
     rw_tac[eq_equality])
(*only one *)
>> arw_tac[]
)
(rapg "ismono(eqa(f1,f2))")
)

(*coeqa_is_epi:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_epi (coeqa f g)*)

val coeqa_is_epi = proved_th(
e
(match_mp_tac is_epi_applied >> repeat stp_tac >> 
 suffices_tac
 (rapf "f = coeqinduce (f1:A-> B,f2, (g:coeqo(f1, f2) -> X) o coeqa(f1,f2))") 
 >-- suffices_tac
 (rapf "g = coeqinduce (f1:A-> B,f2, (g:coeqo(f1, f2) -> X) o coeqa(f1,f2))") 
 >-- repeat stp_tac >-- once_arw_tac[] 
 >-- accept_tac (refl (readt "coeqinduce(f1:A->B, f2, (g:coeqo(f1, f2) -> X) o coeqa(f1, f2))"))
(*two goals remaining*)
 >> (match_mp_tac is_coeqinduce >> rw_tac[spec_all o_assoc] >>
     rw_tac[coeq_equality])
(*only one *)
>> arw_tac[]
)
(rapg "isepi(coeqa(f1,f2))")
)


(*
THEOREM pb_exists:
∀X Y Z f g. f∶ X → Z ∧ g∶ Y → Z ⇒ ∃P p q. p∶ P → X ∧ q∶ P → Y ∧ f o p = g o q ∧
            (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
             ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)
*)


(*TODO: type inference for ispb does not work
 (f : ob),
   (g : ob)
   
   ----------------------------------------------------------------------
   EXISTS P. EXISTS p. EXISTS q. ispb(P, p, q, f, g)
*)


(*TODO:AQ maybe have an abbrev_tac... better have the Q stuff
OR just use let val... in ?

may have a long composition, the point is adding a new symbol to represent the thing, but not add any variable

*)

(*
TODO:

(once_rw_tac[GSYM o_assoc] >> rw_tac[GSYM eq_equality])

does but once_rw_tac[GSYM o_assoc,GSYM eq_equality] does not work for:

(X : ob),
   (Y : ob),
   (Z : ob),
   (f : X -> Z),
   (g : Y -> Z)
   
   ----------------------------------------------------------------------
   (f o p1(X, Y)) o eqa(f o p1(X, Y), g o p2(X, Y)) = (g o p2(X, Y)) o
     eqa(f o p1(X, Y), g o p2(X, Y))

*)


(*
TODO: pp: assumption list ugly indented like:

  (f o p1(X, Y)) o pa(u, v) = (g o p2(X, Y)) o
     pa(u, v),
     f o u = g o
     v,
     f o p1(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y)) = g o p2(X, Y) o
     eqa(f o p1(X, Y), g o p2(X, Y))

Have new lines though.

(f o p1(X, Y)) o pa(u, v) = (g o p2(X, Y)) o
     pa(u, v),
     f o u = g o
     v,
     f o p1(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y)) = g o p2(X, Y) o
     eqa(f o p1(X, Y), g o p2(X, Y))

newly added assumption appears in the top, need reverse. 
*)


(*TODO:
up to 
 ----------------------------------------------------------------------
   (p1(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y))) o
       eqinduce(f o p1(X, Y), g o p2(X, Y), pa(u, v)) = u &
       (p2(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y))) o
         eqinduce(f o p1(X, Y), g o p2(X, Y), pa(u, v)) = v &
         ALL (b : A -> eqo(f o p1(X, Y), g o p2(X, Y))).
           (p1(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y))) o b = u & (p2(X, Y) o
               eqa(f o p1(X, Y), g o p2(X, Y))) o b = v ==>
             eqinduce(f o p1(X, Y), g o p2(X, Y), pa(u, v)) = b
, if can put ax1_5' into assumption and drule with it, then will be nice.
*)

(*parser bug
rapf "P(a) & P(b) ==> ALL s.Q(s) & Q(c)";
Exception- ERR "err in parsing bound variable" raised
*)


(* 

A /\ B ==>C 


A ==> B ==> C

A ==> !x. B x ==> C x

--pull ! x. out !x. A ==> B x ==> C x
--rw with A /\ Bx ==> Cx. 

!x. ! y.  P(x,y) ==> Q(z)

!x. P(x) /\ !y.P(y) ==>Q(z)

TODO: fill the gap from match_mp_tac

*)



(*TODO: AQ

Change GSYM to apply anywhere in a formula once_depth_conv

goal is:

eqinduce(f o p1(X, Y), g o p2(X, Y), pa(u, v)) = b

want to apply match_mp on ... ==> x0 = eqinduce ...

need a tactic which applies a rule on the goal, is it fconv_tac?

test the strip_assume_tac here

in the proof below :
 once_arw_tac[GSYM o_assoc] >> arw_tac[] works, but once_arw_tac itself does not 
*)

val pb_exists = proved_th(
e
(repeat stp_tac >> 
 wexists_tac (readt "eqo ((f:X->Z)o p1(X,Y),g o p2(X,Y))") >>
 wexists_tac (readt "p1(X,Y) o eqa ((f:X->Z) o p1(X,Y),g o p2(X,Y))") >>
 wexists_tac (readt "p2(X,Y) o eqa ((f:X->Z) o p1(X,Y),g o p2(X,Y))") >>
 rw_tac[spec_all is_pb_def] >>
 by_tac 
 (rapf "(f:X->Z) o p1(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y)) = g o p2(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y))") 
 >-- (once_rw_tac[GSYM o_assoc] >> rw_tac[GSYM eq_equality])
 >> arw_tac[] >> repeat stp_tac >> 
 by_tac
 (rapf "((f:X->Z) o p1(X,Y)) o <u:A->X,v:A->Y> = (g o p2(X,Y)) o <u,v>")
(*for solving by tac*)
 >-- (arw_tac[spec_all p1_of_pa,spec_all p2_of_pa,spec_all o_assoc])
 >> wexists_tac (readt "eqinduce ((f:X->Z) o p1(X,Y),g o p2(X,Y), pa(u:A->X,v:A->Y))")
 >> by_tac (rapf "eqa((f:X->Z) o p1(X, Y), g o p2(X, Y)) o eqinduce(f o p1(X,Y), g o p2(X, Y), pa(u:A->X, v:A-> Y)) = <u,v>")
(*solving the by tac*)
 >-- (match_mp_tac ax1_5_applied >> 
     arw_tac[spec_all o_assoc,spec_all p1_of_pa,spec_all p2_of_pa])
 >> arw_tac[spec_all o_assoc] 
 >> rw_tac[spec_all p1_of_pa,spec_all p2_of_pa]
(*uniqueness, last subgoal*)
 >> repeat stp_tac >> 
 suffices_tac
 (rapf "b = eqinduce((f:X->Z) o p1(X, Y), g o p2(X, Y), pa(u:A->X, v:A->Y))")
 >-- (stp_tac >> accept_tac (sym(assume(rapf "b=eqinduce((f:X->Z) o p1(X, Y), g o p2(X, Y), pa(u:A->X, v:A->Y))"))))
 (*proved the suffices*)
 >> match_mp_tac is_eqinduce >> arw_tac[spec_all o_assoc,spec_all p1_of_pa,spec_all p2_of_pa] >>
 match_mp_tac to_p_eq' >> rw_tac[spec_all p1_of_pa,spec_all p2_of_pa] >>
 by_tac (readf "(p1(X, Y) o eqa((f:X->Z) o p1(X, Y), g o p2(X, Y))) o b = u:A->X")
 >-- accept_tac ((conjE1 o assume) (rapf 
"(p1(X, Y) o eqa((f:X->Z) o p1(X, Y), g o p2(X, Y))) o b = u:A->X & (p2(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y))) o b = v:A->Y"
                ))
 >> once_arw_tac[GSYM o_assoc] >> arw_tac[] >>
 accept_tac ((conjE2 o assume) (rapf 
"(p1(X, Y) o eqa((f:X->Z) o p1(X, Y), g o p2(X, Y))) o b = u:A->X & (p2(X, Y) o eqa(f o p1(X, Y), g o p2(X, Y))) o b = v:A->Y"
                ))
)
(rapg
"ALL f:X->Z. ALL g:Y->Z. EXISTS P. EXISTS p:P->X. EXISTS q:P-> Y. ispb(P,p,q,f,g)")
)

(*
pb_fac_exists
∀X Y Z f g. g∶ Y → Z ∧  f∶ X → Z  ⇒ ∃P p q. p∶ P → X ∧ q∶ P → Y ∧ f o p = g o q ∧
            (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
             ∃a. a∶ A → P ∧ p o a = u ∧ q o a = v)
*)

(*TODO: BUG! spec_all pb_exists does not work, but (spec_all (gen_all pb_exists)) does
specl pb_exists (List.map readt ["f:X->Z","g:Y->Z"]) does the correct thing
*)

(*?a. ?b. P(a,b) 

P(m,n) 
qexistsl_tac

X_CHOOSE_THEN n (X_CHOOSE_THEN m assume_tac)*)

(*TODO:AQ one thing ugly about choose_tac is that is cannot use the map_every, since it takes two arguments, but there might be multiple quantifiers

may add existential to rw?
*)

(*TO-DO: implement and test first_assum here, seems irrelevant to mp_then stuff done*)

(*TODO: a rule of turning unique existence into existence*)

val pb_fac_exists = proved_th(
e
(repeat stp_tac >>
mp_tac (spec_all (gen_all pb_exists)) >> rw_tac[spec_all is_pb_def] >>
stp_tac >> 
choose_tac "P" 
(rapf "EXISTS P. EXISTS (p : P -> X). EXISTS (q : P -> Y). ispb(P, p, q, f:X->Z, g:Y->Z)") >>
choose_tac "p"
(rapf "EXISTS (p :P -> X).EXISTS (q: P -> Y). ispb(P, p, q, f:X->Z, g:Y->Z)") >>
choose_tac "q"
(rapf "EXISTS (q : P -> Y). ispb(P, p:P->X, q, f:X->Z, g:Y->Z)") >>
rule_assum_tac (conv_rule (rewr_fconv (spec_all is_pb_def))) >>
map_every wexists_tac (List.map readt ["P","p:P->X","q:P->Y"]) >>
stp_tac
>-- accept_tac (conjE1 (assume 
   (rapf "(f:X->Z) o (p:P->X) = g o q & ALL A. ALL (u : A -> X).ALL (v : A -> Y).f o u = g o v ==> EXISTS (a : A -> P). p o a = u & q o a = v & ALL (b : A -> P). p o b = u & q o b = v ==> a = b"))) 
>> repeat stp_tac
>> assume_tac 
(mp
    (specl (conjE2 (assume 
                        (rapf "(f:X->Z) o (p:P->X) = g o q & ALL A. ALL (u : A -> X).ALL (v : A -> Y).f o u = g o v ==> EXISTS (a : A -> P). p o a = u & q o a = v & ALL (b : A -> P). p o b = u & q o b = v ==> a = b"))) (List.map readt ["A","u:A->X","v:A->Y"]))
    (assume (rapf "(f:X->Z) o (u:A->X) = (g:Y->Z) o v"))
) 
>> choose_tac "a" 
(rapf "EXISTS (a : A -> P).(p:P->X) o a = u & (q:P->Y) o a = v & ALL (b : A -> P). p o b = u & q o b = v ==> a = b")
>> wexists_tac (readt "a:A->P") 
>> accept_tac (
let val f = rapf "(p:P->X) o a = u & (q:P->Y) o a = v & ALL (b : A -> P). p o b = u & q o b = v ==> a = b"
in
conjI ((conjE1 o assume) f) ((conjE1 o conjE2 o assume) f)
end)
)
(rapg 
"ALL X. ALL Z. ALL f:X->Z. ALL Y. ALL g:Y->Z.EXISTS P. EXISTS p:P->X.EXISTS q:P->Y. f o p = g o q & (ALL A.ALL u:A->X.ALL v:A->Y. f o u = g o v ==>EXISTS a:A->P. p o a = u & q o a = v)")
)

(*

pb_mono_mono:
!P p q f g. is_pb P p q f g /\ is_mono g ==> is_mono p

rule_assum_tac ((conv_rule o try_fconv) (rewr_fconv (spec_all is_pb_def)))

need try_fconv because there are two assumptions! ugly


ALL X'. ALL (g : X' -> P). ALL (h : X' -> P). p o g = p o h ==> h = g
TODO:
rename tactic, deal with above

 f o p = g o q &
       ALL A.
         ALL (u : A -> X).
           ALL (v : A -> Y).
             f o u = g o v ==>
               EXISTS (a : A -> P).
                 p o a = u &
                   q o a = v &
                     ALL (b : A -> P). p o b = u & q o b = v ==> a = b

cannot be stripped by  STRIP_ASM_CONJ_TAC
*)

(*TODO: AQ
match_mp_tac is_mono_applied renaming!
 (Z : ob),
   (f : X -> Z),
   (g : Y -> Z),
   (p : P -> X),
   (q : P -> Y)
   ismono(g),
     f o p = g o q &
       ALL A.
         ALL (u : A -> X).
           ALL (v : A -> Y).
             f o u = g o v ==>
               EXISTS (a : A -> P).
                 p o a = u &
                   q o a = v &
                     ALL (b : A -> P). p o b = u & q o b = v ==> a = b
   ----------------------------------------------------------------------
   ALL X'. ALL (g : X' -> P). ALL (h : X' -> P). p o g = p o h ==> h = g

rename tac then strip?

TODO: is_mono_applied  should be p o h = p o k ==> h = k, not k = h, just comfusing

  f o p = g o q &
       ALL A.
         ALL (u : A -> X).
           ALL (v : A -> Y).
             f o u = g o v ==>
               EXISTS (a : A -> P).
                 p o a = u &
                   q o a = v &
                     ALL (b : A -> P). p o b = u & q o b = v ==> a = b

split the conjunct, but not all assumptions are conjunctions

 once_rw_tac[GSYM o_assoc] >> arw_tac[] works, once_arw_tac[GSYM o_assoc] does not 

again

arw_tac[spec_all o_assoc] works.

seems like once and arw not same as once rw and then arw

Check the () works for >--
*)


val pb_mono_mono = proved_th
(let val f0 = rapf "(f:X->Z) o (p:P->X) = (g:Y->Z) o q & ALL A. ALL (u : A -> X).ALL (v : A -> Y). f o u = g o v ==> EXISTS (a : A -> P).p o a = u &q o a = v & ALL (b : A -> P). p o b = u & q o b = v ==> a = b" 
     val f' = rapf "EXISTS (a : D -> P).(p:P->X) o a = p o (k1:D->P) &(q:P->Y) o a = q o k2 & ALL (b : D -> P). p o b = p o k1 & q o b = q o k2 ==> a = b"
     val f'' = rapf "(p:P->X) o a = p o (k1:D->P) &(q:P->Y) o a = q o k2 & ALL (b : D -> P). p o b = p o k1 & q o b = q o k2 ==> a = b"
in
e
(repeat stp_tac >> pop_assum_list (map_every STRIP_ASM_CONJ_TAC) >> 
rule_assum_tac ((conv_rule o try_fconv) (rewr_fconv (spec_all is_pb_def))) >>
match_mp_tac is_mono_applied >>
suffices_tac
(rapf "ALL D. ALL k1:D -> P. ALL k2:D ->P. (p:P->X) o k1 = p o k2 ==> k2 = k1")
>-- stp_tac >-- accept_tac (assume ((rapf "ALL D. ALL k1:D -> P. ALL k2:D ->P. (p:P->X) o k1 = p o k2 ==> k2 = k1"))) >> repeat stp_tac >>
assume_tac (conjE2 (assume f0)) >> 
first_assum (fn th => (assume_tac (specl th (List.map readt ["D","(p:P->X) o (k1:D->P)","(q:P->Y) o (k2:D->P)"]))))
>> by_tac (rapf "(q:P->Y) o (k1:D->P) = q o k2")
>-- (drule is_mono_thm >> first_assum match_mp_tac >>
    assume_tac ((sym o conjE1 o assume) f0) >> once_rw_tac[GSYM o_assoc] >> arw_tac[] >>
    arw_tac[spec_all o_assoc])
>> suffices_tac (rapf "(f:X->Z) o (p:P->X) o (k1:D->P) = (g:Y->Z) o (q:P->Y) o k2")
>-- (stp_tac >> first_assum drule >> choose_tac "a" f' >>
    first_assum (fn th => assume_tac (conjE2 (conjE2 th)))
    >-- suffices_tac (rapf "k1=a:D->P") >-- suffices_tac (rapf "k2=a:D->P")
    >-- repeat stp_tac >> arw_tac[]
    >--(* up to here, have k2 = a ,k1=a as goals, and f o p o k1 = g o q o k2*)
    suffices_tac (rapf "a = k2:D->P") >-- stp_tac >-- arw_tac[]
    >-- (*solving a = k2*) first_assum match_mp_tac >-- conj_tac >-- arw_tac[] >-- arw_tac[]
    >-- (suffices_tac (rapf "a = k1:D->P") >-- stp_tac >-- arw_tac[] >-- 
                      first_assum match_mp_tac >-- conj_tac >-- arw_tac[] >-- arw_tac[])) >>
(*only remains f o p o k1 = g o q o k2*)
assume_tac (conjE1 (assume f0)) >> once_rw_tac[GSYM o_assoc] >> arw_tac[] >>
rw_tac[spec_all o_assoc] >> arw_tac[]
)
(rapg "ispb(P,p:P->X,q:P->Y,f:X->Z,g:Y->Z) & ismono(g) ==> ismono(p)")
end
)

(*non_zero_pinv:∀A B f. f∶ A → B ∧ ¬(A ≅ zero) ⇒ ∃g. g∶B → A ∧ f ∘ g ∘ f = f
also need the tactic for existence

Already have choose_tac, this is a simple example for test exists relative things
*)

(*TODO: ASM_ACCEPT_TAC, accepts an assumption*)

(*Q: Want to extract the current goal for testing tactic form the goal stack, how to do this?*)


val non_zero_pinv = proved_th(
e
(repeat stp_tac >> drule ax6 >> 
 choose_tac "x" (rapf"EXISTS x:1->A.T") >> 
 assume_tac (specl ax5 (List.map readt ["A","x:1->A","B","f:A->B"])) >>
 accept_tac ((assume o rapf) "EXISTS (g : B -> A). f o g o f = f"))
(rapg "ALL A. ~ areiso(A,0) ==> ALL f:A -> B. EXISTS g. f o g o f = f")
)

(*
 epi_pinv_pre_inv:
∀A B f g. f∶ A → B ∧ g∶B → A ∧ is_epi f ∧ f ∘ g ∘ f = f ⇒ f o g = id B
*)

(*TODO:AQ can certainly be better if have first x assum stuff (the x?)

*)
val epi_pinv_pre_inv = proved_th(
e
(stp_tac >>
by_tac (rapf "isepi(f:A->B)")
>-- accept_tac (conjE1 (assume (rapf"(isepi(f) & f o g o f = f)"))) 
>> drule is_epi_thm
>> rule_assum_tac (fn th => specl th (List.map readt ["B","(f:A-> B) o (g:B->A)","id(B)"]))
>> by_tac (rapf "f o g o f = f:A->B")
>-- accept_tac (conjE2 (assume (rapf"(isepi(f) & f o g o f = f)")))
>> by_tac (rapf "(f o g) o f = id(B) o f")
>-- arw_tac[spec_all idL,spec_all o_assoc] 
>> accept_tac (mp (assume (rapf "(f o g) o f = id(B) o f ==> f o g = id(B)"))
                  (assume (rapf "(f o g) o f = id(B) o f"))))
(rapg "(isepi(f) & f o g o f = f) ==> f o g = id(B)")
)



(*
mono_pinv_post_inv:
∀A B f g. f∶ A → B ∧ g∶B → A ∧ is_mono f ∧ f ∘ g ∘ f = f ⇒
          g o f = id A

want first_x_assum, the missing ingredient is undisch_then, what is Lib.pluck?
*)


val mono_pinv_post_inv = proved_th(
e
(stp_tac >>
pop_assum_list (map_every STRIP_ASM_CONJ_TAC)
>> drule is_mono_thm
>> first_assum (fn th => (assume_tac (specl th (List.map readt ["A","id(A)","(g:B->A) o (f:A->B)"]))))
>> first_x_assum match_mp_tac >> arw_tac[spec_all idR] 
)
(rapg "(ismono(f) & f o g o f = f) ==> g o f = id(A)")
)

(*TODO:AQ want turn out pp and still get everything work. should I have a document which stores all types?*)

(*
Theorem epi_non_zero_pre_inv:
∀A B f. f∶ A → B ∧ is_epi f ∧ ¬(A ≅ zero) ⇒ ∃g. g∶ B → A ∧ f o g = id B
*)

val epi_non_zero_pre_inv = proved_th(
e
(stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> )
(rapg "isepi(f:A->B) & ~(areiso(A,0)) ==> EXISTS g:B ->A. f o g = id(B)")
)











