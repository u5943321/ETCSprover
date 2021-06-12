

read_goal "ALL X.ALL A.ALL f.(id(A) o (f: X -> A) = f)"

expandf ((repeat gen_tac) >> rw_tac[spec_all idL] >> T_INTRO_TAC) it

read_goal "ALL X.ALL Y.ALL g.(id(X) o (g: Y -> X) = g)"

read_goal "h o f o g = (h o f) o g";
e (rw_tac[spec_all o_assoc] (*>> assum_list rw_tac *) >> T_INTRO_TAC) it

val ax1_5_applied = prove 
(readf "ALL A.ALL B.ALL g. ALL f.ALL X.ALL h.(f: A ->B) o (h:X -> A) = g o h ==> (eqa(f, g) o eqinduce(f, g, h)) = h")
(repeat stp_tac >> drule
                 (conjE2 (specl ax1_5
                      (List.map readt 
                                ["A","B","f:A -> B","g:A -> B","X",
                                 "eqinduce(f:A -> B, g: A -> B, h:X -> A)",
                                 "h: X ->A"])
                     )) >> assum_list rw_tac >> T_INTRO_TAC)

val ax1_5_applied = 
    gen_all
        (disch (readf "(f: A -> B) o (h: X -> A) = g o h")
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
 (rw_tac [spec_all o_assoc] (*>> T_INTRO_TAC*)))

val compose_assoc_5_4_left_SYM = gen_all
(prove (readf "(f5 o f4 o f3 o f2) o f1 = f5 o f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))

val compose_assoc_5_2_left = gen_all
(prove (readf "(f5 o f4) o f3 o f2 o f1 = f5 o f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_3_left = gen_all
(prove (readf "(f4 o f3 o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_5_2_left_SYM = gen_all
(prove (readf "f5 o f4 o f3 o f2 o f1 = (f5 o f4) o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))

val compose_assoc_4_2_left = gen_all
(prove (readf "(f4 o f3) o f2 o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_middle = gen_all
(prove (readf "f4 o (f3 o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_middle_SYM = gen_all
(prove (readf "f4 o f3 o f2 o f1 = f4 o (f3 o f2) o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_left_SYM = gen_all
(prove (readf "f4 o f3 o f2 o f1 = (f4 o f3) o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_left_middle = gen_all
(prove (readf "(f4 o f3) o f2 o f1 = f4 o (f3 o f2) o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))



val compose_assoc_4_2_left_left = gen_all
(prove (readf "((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_4_2_left_left = gen_all
(prove (readf "((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


(*is rw's job for proving o_bracket_left/right? avoid T_INTRO_TAC?*)

val compose_assoc_5_2_left1_left = gen_all
(prove (readf "f5 o (f4 o f3) o f2 o f1 = (f5 o f4) o f3 o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))



val compose_assoc_6_3_2_left_middle = gen_all
(prove (readf "(f6 o f5 o f4) o f3 o f2 o f1 = f6 o f5 o (f4 o f3) o f2 o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))


val compose_assoc_6_left_left_left_right2 = gen_all
(prove (readf "(((f6 o f5 o f4) o f3) o f2) o f1 = f6 o f5 o f4 o (f3 o f2) o f1")
 (rw_tac [spec_all o_assoc] >> T_INTRO_TAC))

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


(*TODO: reverse the order of pp of gstk*)

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
 >> assume_tac (negE (assume f) (assume (mk_neg f))) >> accept_tac (falseE [FALSE,f,mk_neg f] FALSE)
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

val to_p_eq_one_side = proved_th(
expandf 
(stp_tac >>
by_tac (rapf "p2(A,B) o <id(A),f> = p2(A,B) o <id(A),g>")
>-- arw_tac[])
(rapg "<id(A),f> = <id(A),g> ==> f = g")

)
(**)
end







