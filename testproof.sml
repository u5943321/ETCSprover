fun readfq [QUOTE s] = readf s

structure Parse = struct val Term=readfq end

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


val o_bracket_left = proved_th
                         (expandf 
                              ((repeat gen_tac) >> rw_tac[spec_all o_assoc] >>
                                                stp_tac >> 
                                               accept_tac (assume (readf "((f:Z->A) o ((b:Y->Z) o (a:X ->Y)))=((g:Z ->A) o ((d:Y -> Z) o c))"))   ) 
                              (read_goal "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.f o b o a = g o d o c ==> (f o b) o a = (g o d) o c"))


val o_bracket_left0 =
                         (expandf 
                              ((repeat stp_tac) >> arw_tac[spec_all o_assoc])
                              (rpg "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.f o b o a = g o d o c ==> (f o b) o a = (g o d) o c"))



val o_bracket_left0 =
                         (expandf 
                              ((repeat stp_tac) >> rw_tac[spec_all o_assoc] >> assum_list rw_tac)
                              (read_goal "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.f o b o a = g o d o c ==> (f o b) o a = (g o d) o c"))




(*should be proved if rw with o_assoc and assum list, but will loop if we actually do this*)


val o_bracket_right = proved_th
                         (expandf 
                              ((repeat gen_tac) >> rw_tac[spec_all o_assoc] >>
                                                stp_tac >>
accept_tac (assume (readf "((f:Z->A) o ((b:Y->Z) o (a:X ->Y)))=((g:Z ->A) o ((d:Y -> Z) o c))"))) 
                              (read_goal "ALL f:Z -> A. ALL b:Y -> Z. ALL a:X -> Y. ALL g:Z ->A. ALL d:Y -> Z. ALL c: X -> Y.(f o b) o a = (g o d) o c ==> f o b o a = g o d o c"))


val eq_fac = proved_th 
(expandf (repeat stp_tac >> drule (spec_all ax1_5_applied) >> 
accept_tac (assume (readf "eqa(f:A -> B,g) o eqinduce(f,g,h:X -> A) = h"))) 
(read_goal "ALL A.ALL B.ALL f:A -> B. ALL g:A -> B.ALL X. ALL h: X -> A. f o h = g o h ==>eqa(f,g) o eqinduce(f,g,h) = h"))

(*Q3: unique exists!*)

(*put it into the kernel and let the parser parse it/ a rule for it, turing it into a definition/
only up to isomorphism for objects?

 *)

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


val ax_exp0 =  
    gen_all 
        (dimp_mp_r2l
             (specl ax_exp 
                    [mk_ob "A",mk_ob "B",mk_ob "X",
                     Var("g",mk_ar_sort (po (mk_ob "A") (mk_ob "X")) (mk_ob "B")),readt "tp(g: A * X -> B)"])
             (refl (readt "tp(g: A * X -> B)")))


val ev_of_tp = proved_th
(expandf (assume_tac (refl (readt "tp(f:A * X -> B)")) >> 
         drule (dimpr2l (spec_all ax_exp)) >>
         accept_tac (assume (readf "ev(A,B) o pa(p1(A,X),tp(f) o p2(A,X)) = f")))
(read_goal "ev(A,B) o pa(p1(A,X),tp(f) o p2(A,X)) = f"))
 
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
                                   (List.map readt ["A","B","X","g:A * X -> B"])))
                       (assume (readf "ev(A,B) o pa(p1(A, X), tp(g) o p2(A, X)) = ev(A,B) o pa(p1(A, X), tp(f) o p2(A, X))")))

                  (specl ax_exp0
                         (List.map readt ["A","B","X","f:A * X -> B"]))))


(*
Theorem ev_eq_eq:
∀A B X f g. f∶ X →(exp A B) ∧ g∶X → (exp A B) ∧
            (ev A B) o ⟨p1 A X,f o (p2 A X)⟩ =
            (ev A B) o ⟨p1 A X,g o (p2 A X)⟩ ⇒
            f = g
Proof
rw[] >>
‘f = tp ((ev A B) o ⟨p1 A X,f o (p2 A X)⟩)’
 by metis_tac[is_tp,ev_of_pair_hom] >>
‘g = tp ((ev A B) o ⟨p1 A X,g o (p2 A X)⟩)’
 by metis_tac[is_tp,ev_of_pair_hom] >>
metis_tac[]
QED
*)
val ev_eq_eq = proved_th(
e
(stp_tac >> drule is_tp >> last_x_assum (assume_tac o GSYM) >> drule is_tp >> once_arw_tac[] >>
 first_x_assum (K all_tac) >> last_x_assum (K all_tac) >> once_arw_tac[] >> rw_tac[])
(rapg "ev(A,B) o <p1(A,X),f o p2(A,X)> = ev(A,B) o <p1(A,X),g o p2(A,X)> ==> f = g")
)


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


val prop_5_lemma = 
let 

    val eq1 = 
EQ_fsym "o" 
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


(*

AQ: rw loop if given refl
e
(rw_tac[spec_all ax_copr,refl (readt "(fg:A + B -> C) o i1(A,B)"),
        refl (readt "(fg:A + B -> C) o i2(A,B)")])
e
(rw_tac[spec_all ax_copr,refl (readt "a")])
(rapg "copa(fg o i1(A,B), fg o i2(A,B)) = fg")
loops

maybe add changed_conv somewhere
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


val from_cop_eq = proved_th
(
e (rw_tac[spec_all ax_copr] >> dimp_tac >> stp_tac >> arw_tac[]
         >> rw_tac [spec_all from_cop_components])
(rapg "f o i1(A,B) = g o i1(A,B) & f o i2(A,B) = g o i2(A,B) <=> f = g")

)


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

(*todo: maybe let the inst rename if discovered different bounded names*)




val th = thm(essps,[],mk_dimp (Quant("EXISTS","a",ob,fVar "f0")) 
                              (mk_neg(Quant("ALL","a",ob,mk_neg (fVar "f0")))))




(*contradiction between forall and exists, TODO: derive such a thm*)


(*TODO: turn off the pp and then the whole thing still works AQ: want the pp things for error message, so want pp on top level, so can print out the thing causes error in sort/form/thm*)


val p1_of_pa = gen_all
(conjE1 (dimp_mp_r2l 
     (specl ax_pr (List.map readt ["A","B","X","pa(f:X->A,g:X -> B)","f:X->A","g:X->B"])) (refl (readt "pa(f:X->A,g:X -> B)"))))


val p2_of_pa = gen_all
(conjE2 (dimp_mp_r2l 
     (specl ax_pr (List.map readt ["A","B","X","pa(f:X->A,g:X -> B)","f:X->A","g:X->B"])) (refl (readt "pa(f:X->A,g:X -> B)"))))


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
 >-- rw_tac[spec_all to1_unique] TODO: if do so, then loops,better approch? *)
 >-- accept_tac (specl to1_unique (List.map readt ["A * 1","to1(A) o p1(A, 1)","p2(A, 1)"]))
 >> by_tac (rapf "p1(A, 1) o pa(id(A), to1(A)) o p1(A, 1)=(p1(A, 1) o pa(id(A), to1(A))) o p1(A, 1)")
 >> rw_tac[spec_all o_assoc] >> arw_tac[spec_all p1_of_pa] >>
 rw_tac[spec_all idL]
)
(rapg "areiso(A * 1,A)")
)

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


val parallel_p_one_side = proved_th(
e
(match_mp_tac to_p_eq' >> conj_tac >> rw_tac[spec_all p1_of_pa,spec_all p2_of_pa] >> once_rw_tac[GSYM o_assoc] >>  rw_tac[spec_all p1_of_pa,spec_all p2_of_pa] 
  >> rw_tac[spec_all o_assoc,spec_all p2_of_pa] )
(rapg "<p1(A,B),g o f o p2(A,B)> = <p1(A,C), g o p2(A,C)> o <p1(A,B),f o p2(A,B)>")
)

val parallel_p_one_side' = proved_th(
e 
(rw_tac[spec_all o_assoc] >> accept_tac parallel_p_one_side)
(rapg "<p1(A,B),(g o f) o p2(A,B)> = <p1(A,C), g o p2(A,C)> o <p1(A,B),f o p2(A,B)>")
)

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


val iterated_p_eq = proved_th(
e
(dimp_tac >> repeat stp_tac >> arw_tac[] >> 
match_mp_tac to_p_eq' >> conj_tac >> arw_tac[] >> 
match_mp_tac to_p_eq' >> conj_tac >> arw_tac[])
(rapg 
"f = g <=> p1(A,B) o p1 (A * B,C) o f = p1(A,B) o p1(A * B,C) o g & p2(A,B) o p1(A*B,C) o f = p2(A,B) o p1(A*B,C) o g& p2(A*B,C) o f =p2(A*B,C) o g")
)


val iterated_p_eq_applied = (conjE2 o dimpE) iterated_p_eq

val N_ind_z_s_id = proved_th
(
e 
(match_mp_tac
 (dimpl2r (specl ax_N (List.map readt ["N","z","id(N)","s"]))) >> rw_tac[idL,idR])
(rapg "id(N) = Nind(z,s)")
)
 

val comm_with_s_id = proved_th(
expandf 
(stp_tac >> rw_tac[N_ind_z_s_id] >>
match_mp_tac (dimpl2r (spec_all ax3)) >> arw_tac[]
 )
(rapg "f o z = z & f o s = s o f ==> f = id(N)")
)


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

val psyms0 = insert_psym "isinc";

val isinc_def = define_pred(rapf "ALL A.ALL A0.ALL a:A0 ->A.ALL A1. ALL b:A1 ->A. isinc(a,b,A) <=> EXISTS h. b o h = a")

val is_mono_thm = (gen_all o dimpl2r o spec_all) ismono_def

val is_mono_applied = (gen_all o dimpr2l o spec_all) ismono_def


val post_inv_mono = proved_th(
e
(stp_tac >> match_mp_tac is_mono_applied >> repeat stp_tac >>
suffices_tac (rapf "((i:B->A) o (m:A-> B)) o (h:X-> A) = (i o m) o g") 
(*solving the suffices*)
>-- arw_tac[] >-- rw_tac[spec_all idL]
>> (*done with suffices*)
rw_tac[spec_all o_assoc] >> arw_tac[]
)
(rapg "i o m = id(A) ==> ismono(m)")
)

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

val post_inv_mono = proved_th(
e
(stp_tac >> match_mp_tac is_mono_applied >> repeat stp_tac >>
suffices_tac (rapf "((i:B->A) o (m:A-> B)) o (h:X-> A) = (i o m) o g") 
(*solving thesuffices*)
>-- (arw_tac[idL] >> stp_tac >> accept_tac (assume (rapf "h:X->A = g")))
>> (*done with suffices*)
rw_tac[spec_all o_assoc] >> arw_tac[]
)
(rapg "i o m = id(A) ==> ismono(m)")
)

val pre_inv_epi = proved_th(
e
(stp_tac >> match_mp_tac is_epi_applied >> repeat stp_tac >>
 suffices_tac (rapf "(f:B->X) o (e:A->B) o (i:B->A) = g o e o i") 
 >-- arw_tac[spec_all idR] >>
 once_rw_tac[GSYM o_assoc] >> arw_tac[]
 )
(rapg "e o i = id(B) ==> isepi(e)")
)


val psyms0 = insert_psym "ispb"


val is_pb_def = define_pred (rapf 
"ALL X. ALL Z. ALL f: X -> Z. ALL Y. ALL g:Y -> Z. ALL P. ALL p:P-> X. ALL q:P->Y. ispb(P,p,q,f,g) <=> f o p = g o q & ALL A. ALL u: A -> X. ALL v: A -> Y. f o u = g o v ==> EXISTS a:A -> P. p o a = u & q o a = v & ALL b:A -> P. p o b = u & q o b = v ==> a = b"
)

val eq_equality = (conjE1 o spec_all) ax_eq'

val coeq_equality = (conjE1 o spec_all) ax_coeq'


val coeq_of_equal = proved_th(
e
(wexists_tac (readt "coeqinduce(f:A-> B,f,id(B))") >> 
match_mp_tac ax1_6_applied >> rw_tac[]
)
(rapg "EXISTS ki. ki o (coeqa(f,f)) = id(B)")
)


(*TODO:want match_mp_tac to work for 
f o h = g o h ==>
                     eqa(f, g) o x0 = h ==> x0 = eqinduce(f, g, h): thm

still to write the canon function...
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


(*TODO: type inference for ispb does not work
 (f : ob),
   (g : ob)
   
   ----------------------------------------------------------------------
   EXISTS P. EXISTS p. EXISTS q. ispb(P, p, q, f, g)
*)


(*TODO:test abbrev tac*)



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
 by_tac (readf "(p1(X, Y) o eqa((f:X->Z) o p1(X, Y), g o p2(X, Y))) o b = u:A->X") >>
 pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[o_assoc]
)
(rapg
"ALL f:X->Z. ALL g:Y->Z. EXISTS P. EXISTS p:P->X. EXISTS q:P-> Y. ispb(P,p,q,f,g)")
)

(*TODO: a rule of turning unique existence into existence*)

val pb_fac_exists = proved_th(
e
(repeat stp_tac >>
mp_tac (spec_all pb_exists) >> rw_tac[spec_all is_pb_def] >>
stp_tac >> 
first_x_assum (x_choosel_tac ["P","p","q"]) >>
map_every wexists_tac (List.map readt ["P","p:P->X","q:P->Y"]) >>
stp_tac >-- pop_assum_list (map_every STRIP_ASSUME_TAC) >-- arw_tac[] >>
repeat stp_tac
>> assume_tac 
(mp
    (specl (conjE2 (assume 
                        (rapf "(f:X->Z) o (p:P->X) = g o q & ALL A. ALL (u : A -> X).ALL (v : A -> Y).f o u = g o v ==> EXISTS (a : A -> P). p o a = u & q o a = v & ALL (b : A -> P). p o b = u & q o b = v ==> a = b"))) (List.map readt ["A","u:A->X","v:A->Y"]))
    (assume (rapf "(f:X->Z) o (u:A->X) = (g:Y->Z) o v"))
)  >> 
first_x_assum (x_choose_tac "a") >> wexists_tac (readt "a:A->P") >>
 pop_assum_list (map_every STRIP_ASSUME_TAC) >-- arw_tac[] 
)
(rapg 
"ALL X. ALL Z. ALL f:X->Z. ALL Y. ALL g:Y->Z.EXISTS P. EXISTS p:P->X.EXISTS q:P->Y. f o p = g o q & (ALL A.ALL u:A->X.ALL v:A->Y. f o u = g o v ==>EXISTS a:A->P. p o a = u & q o a = v)")
)

(*

rule_assum_tac ((conv_rule o try_fconv) (rewr_fconv (spec_all is_pb_def)))

need try_fconv because there are two assumptions! ugly


ALL X'. ALL (g : X' -> P). ALL (h : X' -> P). p o g = p o h ==> h = g
*)

(*TODO: 
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


(*!!!!!!AQ2: Want to extract the current goal for testing tactic form the goal stack, how to do this?*)


val non_zero_pinv = proved_th(
e
(repeat stp_tac >> drule ax6 >> 
 choose_tac "x" (rapf"EXISTS x:1->A.T") >> 
 assume_tac (specl ax5 (List.map readt ["A","x:1->A","B","f:A->B"])) >>
 accept_tac ((assume o rapf) "EXISTS (g : B -> A). f o g o f = f"))
(rapg "ALL A. ~ areiso(A,0) ==> ALL f:A -> B. EXISTS g. f o g o f = f")
)


val epi_pinv_pre_inv = proved_th(
e
(stp_tac >>
by_tac (rapf "isepi(f:A->B)")
>-- accept_tac (conjE1 (assume (rapf"(isepi(f) & f o g o f = f)"))) 
>> drule is_epi_thm
>> first_x_assum (specl_then  (List.map readt ["B","(f:A-> B) o (g:B->A)","id(B)"]) assume_tac)
>> by_tac (rapf "f o g o f = f:A->B")
>-- accept_tac (conjE2 (assume (rapf"(isepi(f) & f o g o f = f)")))
>> by_tac (rapf "(f o g) o f = id(B) o f")
>-- arw_tac[spec_all idL,spec_all o_assoc] 
>> accept_tac (mp (assume (rapf "(f o g) o f = id(B) o f ==> f o g = id(B)"))
                  (assume (rapf "(f o g) o f = id(B) o f"))))
(rapg "(isepi(f) & f o g o f = f) ==> f o g = id(B)")
)


val mono_pinv_post_inv = proved_th(
e
(stp_tac >>
pop_assum_list (map_every STRIP_ASM_CONJ_TAC)
>> drule is_mono_thm
>> first_x_assum (specl_then  (List.map readt ["A","id(A)","(g:B->A) o (f:A->B)"]) assume_tac)
>> first_x_assum match_mp_tac >> arw_tac[spec_all idR] 
)
(rapg "(ismono(f) & f o g o f = f) ==> g o f = id(A)")
)



(*TODO: quotation for specl, and switch the order of input
bug here, x_choose gives disch has extra variables

*)



(*TODO: AQ introduce a machinary to check that at each step we have all the variables in the goal are in the context
at this stage, since have less context makes the thm weaker, so something should be proved cannot be proved. 

*)


val epi_non_zero_pre_inv = proved_th(
e
(stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> drule non_zero_pinv >>
 first_x_assum (specl_then [readt "f:A->B"] assume_tac) >>
 first_x_assum (x_choose_tac "a") >>
 wexists_tac (readt "a:B->A") >> match_mp_tac epi_pinv_pre_inv >> 
 arw_tac[])
(rapg "isepi(f:A->B) & ~(areiso(A,0)) ==> EXISTS g:B ->A. f o g = id(B)")
)


val mono_non_zero_post_inv = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> drule non_zero_pinv >> 
 first_x_assum (specl_then [readt "f:A->B"] assume_tac) >> 
 first_x_assum (x_choose_tac "a") >>
 wexists_tac (readt "a:B->A") >> match_mp_tac mono_pinv_post_inv >> arw_tac[])
(rapg "ismono(f:A->B) & ~(areiso(A,0)) ==> EXISTS g:B ->A. g o f = id(A)")
)


(*TODO: edit stp_tac using 
fun STRIP_GOAL_THEN ttac = FIRST [GEN_TAC, CONJ_TAC, DISCH_THEN ttac]
add a tactic of removing assumption

rule assume tac on first rule which the function applies

*)


val o_mono_mono = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >>
 rule_assum_tac ((conv_rule o try_fconv) (rewr_fconv (spec_all ismono_def))) >>
 match_mp_tac is_mono_applied >> repeat gen_tac >> 
 rw_tac[o_assoc]  >> stp_tac >>
 by_tac“(f:A->B) o g' = f o (h:X->A)”>--
 (first_x_assum drule >> arw_tac[]) >> 
 first_x_assum match_mp_tac >> arw_tac[]
 )
(rapg "ismono(f:A->B) & ismono(g:B->C) ==> ismono(g o f)")
)



val psyms0 = insert_psym "isiso";

val isiso_def = define_pred (readf "ALL A. ALL B. ALL f:A->B. isiso(f) <=> EXISTS g: B -> A. f o g = id(B) & g o f = id(A)") 



val is_iso_thm = isiso_def|> spec_all |> dimpl2r


val mono_o_iso_mono = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> match_mp_tac is_mono_applied >> rw_tac[o_assoc] >>
 repeat stp_tac >> drule is_iso_thm >> first_x_assum (x_choose_tac "i'") >> 
 pop_assum STRIP_ASSUME_TAC >> drule is_mono_thm >> 
 by_tac “(i:X->A) o (g:X'->X) = i o h” 
 >-- (first_x_assum match_mp_tac >> arw_tac[]) >> 
 by_tac “(i':A->X) o (i:X->A) o (g:X'->X) = i' o i o h” >-- arw_tac[] >>
 by_tac “h:X' ->X = (i':A->X) o i o h” >-- arw_tac[idL,GSYM o_assoc] >>
 by_tac “g:X' ->X = (i':A->X) o i o g” >-- once_rw_tac[GSYM o_assoc] >> once_arw_tac[] >> 
 rw_tac[idL] >>
 accept_tac (sym (assume “i' o i o g = (i':A->X) o (i:X->A) o (h:X'->X)”)))
(rapg "isiso(i:X->A) & ismono(f:A->B) ==> ismono(f o i)")
)


val o_mono_imp_mono = proved_th(
e
(rw_tac[ismono_def] >> repeat stp_tac >> first_x_assum match_mp_tac >> 
 rw_tac[o_assoc] >> arw_tac[])
(rapg "ismono((m:B ->C) o (f:A->B)) ==> ismono(f)")
)

val o_epi_imp_epi = proved_th(
e
(rw_tac[isepi_def] >> repeat stp_tac >>first_x_assum match_mp_tac >> rw_tac[GSYM o_assoc] >>
arw_tac[])
(rapg "isepi((f:A->B) o (e:C->A)) ==> isepi(f)")
)



val fun_ext = proved_th(
e
(stp_tac >> ccontra_tac >> drule ax4 >> 
first_x_assum (x_choose_tac "a") >> 
first_x_assum (specl_then [readt "a:1->A"] assume_tac)  >>
first_x_assum OPPOSITE_TAC)
(rapg "(ALL a:1->A. f o a = g o a) ==> f = g")
)



val surj_is_epi = proved_th(
e
(repeat stp_tac >> match_mp_tac is_epi_applied >> repeat stp_tac >> match_mp_tac fun_ext >>
 stp_tac >> 
 first_x_assum (specl_then [readt "a:1->B"] assume_tac)>>
 first_x_assum (x_choose_tac "b0") >> 
 rule_assum_tac sym >> arw_tac[] >> rw_tac[GSYM o_assoc] >> arw_tac[])
(rapg "(ALL b:1 ->B. EXISTS b0:1 ->A. f o b0 = b) ==> isepi(f)")
)        

val are_iso_is_iso = proved_th(
e
(rw_tac[areiso_def,isiso_def] >> dimp_tac >> repeat stp_tac >> first_x_assum accept_tac)
(rapg "areiso(A,B) <=> EXISTS f:A->B. isiso(f)")
)

(*TODO: maybe drule: permute order of exists quantifier

(A : ob),
   (B : ob),
   (f : B -> A),
   (g : A -> B)
   f o g = id(A) & g o f = id(B)
   ----------------------------------------------------------------------
   f o g = id(B) & g o f = id(A)

can missing cont in goal

if use same x_choose for both of the two directions

*)
val are_iso_is_iso' = proved_th(
e
(rw_tac[areiso_def,isiso_def] >> dimp_tac >> repeat stp_tac 
 >--(first_x_assum (x_choose_tac "f") >>  first_x_assum (x_choose_tac "g") >> 
    wexists_tac (readt "g: B-> A") >> wexists_tac (readt "f:A->B") >>
     conj_tac >> arw_tac[]) 
 >> first_x_assum (x_choose_tac "g") >>  first_x_assum (x_choose_tac "f") >>
 wexists_tac (readt "f: A -> B") >> wexists_tac (readt "g:B->A") >>
 conj_tac >> arw_tac[])
(rapg "areiso(A,B) <=> EXISTS f:B->A. isiso(f)")
)

(*TODO: rw does not treat connction for equality, so need snd pop_assum STRIP_ASSUME_TAC,unexpected∀*)


val o_iso_eq_eq = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> drule is_iso_thm >>
 first_x_assum (x_choose_tac "j") >> 
 suffices_tac “(f:B->C) o (i:A->B) o (j:B->A) = g o i o j” >>
 pop_assum STRIP_ASSUME_TAC >--
 (arw_tac[idR] >> stp_tac >> first_x_assum accept_tac) >> 
 rw_tac[GSYM o_assoc] >> arw_tac[])
(rapg "isiso(i) & f o i = g o i ==> f = g")
) 

(*
want solve

(A : ob),
   (B : ob),
   (f : A -> B),
   (g : A -> B),
   (i : 0 -> A)
   f o i = g o
     i,
     isiso(i)
   ----------------------------------------------------------------------
   f = g

from the thm

   (A : ob),
   (B : ob),
   (C : ob),
   (f : B -> C),
   (g : B -> C),
   (i : A -> B)
   
   |-
   isiso(i) & f o i = g o i ==> f = g: thm

TODO: bug match_mp
if use match_mp_tac o_iso_eq_eq, then # Exception- ERR "VALIDInvalid tactic: theorem has extra variable involved i"
   raised

The i is the i:A->B, not the one from 0, and i is not matched anywhere.
*)

val from_iso_zero_eq = proved_th(
e
(rw_tac[are_iso_is_iso'] >> stp_tac >> first_x_assum (x_choose_tac "i") >> repeat stp_tac >>
assume_tac (specl from0_unique 
                  (List.map readt ["B","(f:A->B) o (i:0->A)","(g:A->B) o (i:0->A)"]))>>
match_mp_tac (gen_all o_iso_eq_eq) >> wexists_tac (readt "0") >> wexists_tac (readt "i:0->A") >>
conj_tac >> arw_tac[]
)
(rapg "areiso(A,0) ==> ALL f:A->B. ALL g.f = g")
)


val eq_pre_o_eq = proved_th(
e
(stp_tac >> arw_tac[GSYM o_assoc])
(rapg "b o a = d o c ==> b o a o f = d o c o f")
)


val one_to_one_id = proved_th(
e
(stp_tac >> assume_tac (specl to1_unique (List.map readt ["1","f:1->1","id(1)"])) >> arw_tac[])
(rapg "ALL f:1 -> 1. f = id(1)")
)     
   

(*
stp_tac >> pop_assum STRIP_ASSUME_TAC >> drule is_epi_thm >> 
 contra_tac >> drule (gen_all from_iso_zero_eq) gives

(f : A -> B)
   ALL (f : A -> B). ALL (g : A -> B). f = g,
     A areiso
     0,
     ALL X. ALL (f' : B -> X). ALL (g : B -> X). f' o f = g o f ==> f' = g,
     ~B areiso
     0,
     isepi(f)
   ----------------------------------------------------------------------
   F(),

want B to be ALL B.

add the normalising procedure to drule?
*)

val from_iso_zero_eq' = from_iso_zero_eq |> undisch |> gen_all |> disch_all |> gen_all


(*TODO:

 rw_tac[GSYM o_assoc] >-- once_arw_tac[] >-- rw_tac[] do not understand why loop

BUG? if replace the last once arw with accept, then not work
*)


val no_epi_from_zero = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> drule is_epi_thm >> 
 ccontra_tac >> drule from_iso_zero_eq' >> 
 first_x_assum (specl_then (List.map readt ["1+1","i1(1,1) o to1(B) o (f:A->B)",
                                                "i2(1,1) o to1(B) o (f:A->B)"]) assume_tac) >>
by_tac “(i1(1, 1) o to1(B)) o f = (i2(1, 1) o to1(B)) o (f:A->B)” >> arw_tac[o_assoc] >>
first_x_assum drule >> drule ax6 >> first_x_assum (x_choose_tac "b") >> 
by_tac “i1(1, 1) o to1(B) o (b:1->B) = i2(1, 1) o to1(B) o b” 
>-- rw_tac[GSYM o_assoc] >-- once_arw_tac[] >-- rw_tac[]
>> by_tac “to1(B) o b = id(1)”
>-- assume_tac (specl one_to_one_id [readt "to1(B) o (b:1->B)"]) >-- once_arw_tac[] >-- rw_tac[]
>> by_tac “i1(1, 1) = i2(1,1)” >>
rule_assum_tac (
let val fc = basic_fconv (rewr_conv (assume “to1(B) o b = id(1)”)) no_fconv
in (fn th => dimp_mp_l2r th (fc (concl th)))
end) >>
rule_assum_tac (let val fc = basic_fconv (rewr_conv (spec_all idR)) no_fconv
in (fn th => dimp_mp_l2r th (fc (concl th)))
end) >> once_arw_tac[] >> rw_tac[] >>
OPPOSITE_TAC i1_ne_i2
(*
>-- suffices_tac “i1(1,1) o id(1) = i2(1,1) o id(1)” >-- rw_tac[idR] >-- stp_tac
>-- once_arw_tac[] >-- rw_tac[] *))
(rapg "isepi(f:A->B) & ~(areiso(B,0)) ==> ~(areiso(A,0))")
)

(*TODO: should we check contra tac work for both ~f f and f ~f? *)


(*TODO: goal is proved after strip assume, understand this*)

val epi_pre_inv = proved_th(
e
(stp_tac >> drule no_epi_from_zero >> match_mp_tac epi_non_zero_pre_inv >> conj_tac >>
pop_assum_list (map_every STRIP_ASSUME_TAC))
(rapg "isepi(f:A->B) & ~(areiso(B,0)) ==> EXISTS g:B->A. f o g = id(B)")
)

(*todo: 
match_mp_tac (gen_all o_iso_eq_eq)
same as before, need gen all
aQ: should match_mp with th and gen_all th/ spec th always give the same
*)
val zero_no_mem = proved_th(
e
(ccontra_tac >> first_x_assum (x_choose_tac "f") >> 
suffices_tac “ALL X. ALL f1:1->X. ALL f2:1->X. f1 = f2” 
>-- assume_tac ax8 >-- first_x_assum (x_choose_tac "X")
>-- first_x_assum (x_choosel_tac ["x1","x2"]) >> 
stp_tac >-- first_x_assum (specl_then (List.map readt ["X","x1:1->X","x2:1->X"]) assume_tac)
>-- first_x_assum OPPOSITE_TAC>>
(*return to main proof*)
repeat stp_tac >> match_mp_tac (gen_all o_iso_eq_eq) >>
wexists_tac (readt "0") >> wexists_tac (readt "to1(0)")>> conj_tac (*2 *)
>-- (rw_tac[isiso_def] >> wexists_tac (readt "f:1->0") >> conj_tac
    >-- accept_tac (specl to1_unique (List.map readt ["1","to1(0) o (f:1->0)","id(1)"]))
    >-- accept_tac (specl from0_unique (List.map readt ["0","(f:1->0)o to1(0)","id(0)"])))
>> accept_tac (specl from0_unique (List.map readt ["X","(f1:1->X) o to1(0)","(f2:1->X) o to1(0)"]))
)
(rapg "~(EXISTS f:1->0.T)")
)

val is_zero_no_mem = proved_th(
e
(rw_tac[are_iso_is_iso] >> repeat stp_tac >> last_x_assum (x_choose_tac "f0") >>
first_x_assum (x_choose_tac "x") >>  
by_tac “EXISTS x:1->0. T” 
>-- (wexists_tac (readt "(f0:A->0) o (x:1->A)") >> rw_tac[]) >>
OPPOSITE_TAC zero_no_mem)
(rapg "areiso(A,0) ==> ~(EXISTS x:1->A. T)")
)

val is_epi_surj = proved_th(
e
(cases_on “areiso(B,0)”
>-- (drule is_zero_no_mem >> repeat stp_tac >> 
    by_tac “EXISTS x : 1 -> B. T” >-- (wexists_tac (readt "b:1->B") >> rw_tac[])
    >-- first_x_assum OPPOSITE_TAC)
>> repeat stp_tac >> by_tac “~(areiso(A,0))”
>-- (match_mp_tac no_epi_from_zero >> conj_tac >> first_x_assum accept_tac) >>
by_tac “EXISTS g : B -> A. f o g = id(B)”
>-- (match_mp_tac epi_non_zero_pre_inv >> conj_tac >> first_x_assum accept_tac) >>
first_x_assum (x_choose_tac "g") >>
wexists_tac (readt "(g:B->A) o (b:1->B)")  >> rw_tac[GSYM o_assoc] >> arw_tac[] >> 
rw_tac[idL]
)
(rapg "isepi(f:A->B) ==> ALL b:1->B. EXISTS b0:1->A. f o b0 = b")
)
   
val distinct_endo_2 = proved_th(
e
(ccontra_tac >> drule (from_cop_eq |> iff_swap |> dimpl2r) >> 
 pop_assum_list (map_every STRIP_ASSUME_TAC) >>
rule_assum_tac (
let val fc = basic_fconv (rewr_conv (spec_all i1_of_copa)) no_fconv
in (fn th => dimp_mp_l2r th (fc (concl th)))
end ) >> 
OPPOSITE_TAC i1_ne_i2)
(rpg "~(copa(i1(1,1),i2(1,1)) = copa(i2(1,1),i1(1,1)))")
)


val distinct_endo_exists = proved_th(
e
(wexists_tac (readt "1+1") >> wexists_tac (readt "copa(i1(1,1),i2(1,1))") >>
             wexists_tac (readt "copa(i2(1,1),i1(1,1))") >> 
accept_tac distinct_endo_2)
(rapg "EXISTS X. EXISTS e1: X -> X. EXISTS e2:X->X. ~(e1 = e2)")
)

val not_to_zero = proved_th(
e
(stp_tac >> ccontra_tac >> drule ax6 >> 
 assume_tac zero_no_mem >> 
 by_tac “EXISTS f:1 -> 0. T” >-- first_x_assum (x_choose_tac "x")
 >-- wexists_tac (readt "(f:A->0) o (x:1->A)") >-- first_x_assum accept_tac >>
 first_x_assum OPPOSITE_TAC)
(rapg "ALL f:A -> 0. areiso(A,0)")
)

val have_to_0 = proved_th(
e
(stp_tac >> first_x_assum (x_choose_tac "a0") >> accept_tac (specl not_to_zero [readt "a0:A->0"]))
(rapg "(EXISTS f0: A ->0. T) ==> areiso(A,0)"))




(*TODO: rethink exists taut rws, original problem fixed
*)
val to_zero_zero = proved_th(
expandf
(repeat stp_tac >> 
 suffices_tac “EXISTS f0: A ->0. T” 
 >-- (stp_tac >> first_x_assum (x_choose_tac "a0")>>
      accept_tac (specl not_to_zero [readt "a0:A->0"])) >> 
      pop_assum mp_tac >> rw_tac[areiso_def] >> stp_tac >>
  first_x_assum (x_choose_tac "f1") >> wexists_tac (readt "(f1:B->0) o (f:A->B)") >>
rw_tac[])
(rapg "ALL f:A->B. areiso(B,0) ==> areiso(A,0)")
)


val to_iso_zero_iso = proved_th(
e
(repeat stp_tac >> drule to_zero_zero >> pop_assum mp_tac >> pop_assum mp_tac >> 
rw_tac[areiso_def,isiso_def] >> repeat stp_tac >> 
first_x_assum (x_choosel_tac ["az","za"]) >> 
first_x_assum (x_choosel_tac ["xz","zx"]) >>
wexists_tac (readt "(za: 0->A) o (xz:X->0)") >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> 
assume_tac (specl from0_unique (List.map readt ["X","(f:A->X) o (za:0 -> A)","zx:0->X"])) >> 
rw_tac[GSYM o_assoc] >> once_arw_tac[] >>once_arw_tac[] >> rw_tac[] >> 
match_mp_tac from_iso_zero_eq >> rw_tac[areiso_def,isiso_def] >> 
wexists_tac (readt "az:A->0") >> wexists_tac (readt "za:0->A") >> arw_tac[]
)
(rapg "areiso(X,0) ==> ALL f:A->X. isiso(f)")
)



(*TODO: match_mp bug: need (gen_all no_epi_from_zero)

 arw bug arw_tac[] >> first_x_assum accept_tac should just be arw

 do not understand why loop if use arw_tac[idL] in the epi case proof*)

val mono_epi_is_iso = proved_th(
e
(cases_on “areiso(B,0)” 
 >-- (stp_tac >> drule to_iso_zero_iso >> 
      first_x_assum (specl_then [readt "a:A->B"] assume_tac)>>
      first_x_assum accept_tac) >> 
 stp_tac >> pop_assum STRIP_ASSUME_TAC >> rw_tac[isiso_def] >> 
 by_tac “~(areiso(A,0))” 
 >-- (match_mp_tac (gen_all no_epi_from_zero) 
      >> wexists_tac (readt "B") >> wexists_tac (readt "a:A->B") >>
      arw_tac[] >> first_x_assum accept_tac) >>
 drule ax6 >> first_x_assum (x_choose_tac "a0") >> 
 assume_tac (specl ax5 (List.map readt ["A","a0:1->A","B","a:A->B"])) >>
 first_x_assum (x_choose_tac "g") >> wexists_tac (readt "g:B->A") >> conj_tac
 >-- (drule is_epi_thm >> first_x_assum match_mp_tac >> rw_tac[o_assoc]>>
      once_arw_tac[idL] >> rw_tac[idL]) >>
drule is_mono_thm >> first_x_assum match_mp_tac >> once_arw_tac[] >>
rw_tac[idR])
(rpg "(ismono(a:A->B)&isepi(a)) ==>isiso(a)")
)

val to_copa_fac = proved_th(
e
(assume_tac (specl ax7 (List.map readt ["A","B","x:1->A+B"])) >> 
 pop_assum mp_tac >> rw_tac[ismem_def] >> stp_tac >>
 pop_assum STRIP_ASSUME_TAC (* 2 *)
 >-- (disj1_tac >> wexists_tac (readt "x0:1->A") >> arw_tac[]) >>
 disj2_tac >> wexists_tac (readt "x0:1->B") >> arw_tac[])
(rapg "(EXISTS x0:1->A. i1(A,B) o x0 = x)|(EXISTS x0:1->B. i2(A,B) o x0 = x)")
)

val one_ne_zero = proved_th(
e
(ccontra_tac >> drule is_zero_no_mem >> 
by_tac “EXISTS x:1->1.T” 
>-- (wexists_tac (readt "id(1)") >> rw_tac[]) >>
first_x_assum OPPOSITE_TAC)
(rapg "~ (areiso(1,0))")
)

val tp_elements_ev = proved_th(
e
(by_tac (rapf "<x:1->X,tp(f o p1(X,1))> = <p1(X,1),tp((f:X->Y) o p1(X,1)) o p2(X,1)> o <x,id(1)>") 
 >-- (match_mp_tac to_p_eq' >> rw_tac[p1_of_pa,p2_of_pa] >> rw_tac[GSYM o_assoc,p1_of_pa,p2_of_pa] >> rw_tac[o_assoc,p2_of_pa,idR]) >> 
 by_tac (rapf "(f:X->Y) o p1(X,1) = ev(X,Y) o <p1(X,1),tp(f o p1(X,1)) o p2(X,1)>") 
 >-- rw_tac[ev_of_tp] >> once_arw_tac[] >> rw_tac[GSYM o_assoc,ev_of_tp] >>
 rw_tac[o_assoc,p1_of_pa])
(rapg "ev(X,Y) o <x:1->X,tp(f o p1(X,1))> = f o x")
)
 
(*
TODO: The pp of goalstack order is messed up
*)
val copa_not_mem_mono_mono = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> match_mp_tac is_mono_applied >> 
 repeat stp_tac >> match_mp_tac fun_ext >> repeat stp_tac >>
 assume_tac (specl (gen_all to_copa_fac)
            (List.map readt ["A","1","(g:X' ->A+1) o (a':1->X')"])) >> 
 assume_tac (specl (gen_all to_copa_fac)
            (List.map readt ["A","1","(h:X' ->A+1) o (a':1->X')"])) >>
 pop_assum_list (map_every STRIP_ASSUME_TAC) (* 4 *)
 >-- (suffices_tac “x0':1->A = x0”
      >-- (stp_tac >> 
           rule_assum_tac (fn th => sym th handle _ => th) >> 
           once_arw_tac[] >> once_arw_tac[] >> rw_tac[]) >>
      drule is_mono_thm >> first_x_assum match_mp_tac >> 
      by_tac “a = copa(a:A->X, x) o i1(A,1)”
      >-- rw_tac[i1_of_copa] >> once_arw_tac[] >> rw_tac[o_assoc] >>
      pop_assum mp_tac >> once_arw_tac[] >> rw_tac[GSYM o_assoc] >>
      once_arw_tac[] >> stp_tac >> rw_tac[])
 >-- (assume_tac (specl to1_unique (List.map readt ["1","x0':1->1","id(1)"])) >>
      suffices_tac “EXISTS x0 : 1 -> A. (a:A->X) o x0 = x”
      >-- (stp_tac >> first_x_assum OPPOSITE_TAC) >>
      wexists_tac (readt "x0:1->A") >> 
      by_tac “copa(a,x) o i2(A,1) o (x0':1->1) = copa(a:A->X,x:1->X) o i1(A,1) o (x0:1->A)”
      >-- (arw_tac[] >> arw_tac[GSYM o_assoc]) >>
      pop_assum mp_tac >> rw_tac[GSYM o_assoc,i1_of_copa,i2_of_copa] >> arw_tac[idR] >>
      stp_tac >> pop_assum (mp_tac o GSYM) >> stp_tac >> first_x_assum accept_tac)
>-- (assume_tac (specl to1_unique (List.map readt ["1","x0:1->1","id(1)"])) >> 
     suffices_tac “EXISTS x0 : 1 -> A. (a:A->X) o x0 = x”
      >-- (stp_tac >> first_x_assum OPPOSITE_TAC) >>
      wexists_tac (readt "x0':1->A") >> 
      by_tac “copa(a,x) o i2(A,1) o (x0:1->1) = copa(a:A->X,x:1->X) o i1(A,1) o (x0':1->A)”
      >-- (arw_tac[] >> arw_tac[GSYM o_assoc]) >> 
      pop_assum mp_tac >> rw_tac[GSYM o_assoc,i1_of_copa,i2_of_copa] >> arw_tac[idR] >> 
      stp_tac >> pop_assum (mp_tac o GSYM) >> stp_tac >> first_x_assum accept_tac) >> 
assume_tac (specl to1_unique (List.map readt ["1","x0:1->1","x0':1->1"])) >> 
suffices_tac “i2(A, 1) o x0' = i2(A, 1) o (x0:1->1)” 
>-- (arw_tac[] >> repeat stp_tac >> pop_assum (mp_tac o GSYM) >> stp_tac >> 
    first_x_assum accept_tac) >> 
rule_assum_tac (fn th => GSYM th handle _ => th) >> once_arw_tac[] >> rw_tac[])
(rpg "(ismono(a:A->X) & ~(EXISTS x0:1->A. a o x0 = x)) ==> ismono(copa(a,x))")
)
        
  
val iso_symm = proved_th(
e
(rw_tac[areiso_def,isiso_def] >> dimp_tac >> stp_tac 
 >-- (pop_assum STRIP_ASSUME_TAC >> wexists_tac (readt "g:Y->X") >>
       wexists_tac (readt "f:X->Y") >> conj_tac >> arw_tac[]) >>
 pop_assum STRIP_ASSUME_TAC >> wexists_tac (readt "g:X->Y") >>
       wexists_tac (readt "f:Y->X") >> conj_tac >> arw_tac[])
(rapg "areiso(X,Y) <=> areiso(Y,X)")
)


val iso_compose_iso = proved_th(
e
(rw_tac[isiso_def] >> stp_tac >> pop_assum STRIP_ASSUME_TAC
 >> wexists_tac (readt "(g':Y->X) o (g'':Z-> Y)") >>
 by_tac “((g:Y->Z) o (f:X->Y)) o (g':Y->X) o (g'':Z->Y) = g o (f o g') o g''”
 >-- rw_tac[o_assoc] >>
 by_tac “((g':Y->X) o (g'':Z->Y)) o (g:Y->Z) o (f:X->Y) = g' o (g'' o g) o f”
 >-- rw_tac[o_assoc] >>
 arw_tac[] >> rw_tac[idL,idR] >> arw_tac[])
(rapg "isiso(f:X->Y) & isiso(g:Y->Z) ==> isiso(g o f)")
)


val iso_trans = proved_th(
e
(rw_tac[areiso_def,isiso_def] >> stp_tac >> pop_assum STRIP_ASSUME_TAC >>
 wexists_tac (readt "(f':Y->Z) o (f:X-> Y)") >>
 wexists_tac (readt "(g:Y->X) o (g':Z-> Y)") >>
 by_tac “(f' o f) o g o g' = (f':Y->Z) o ((f:X->Y) o (g:Y->X)) o (g':Z->Y)” 
 >-- rw_tac[o_assoc] >>
 by_tac “(g o g') o f' o f = (g:Y->X) o ((g':Z->Y) o (f':Y->Z)) o (f:X->Y)”
 >-- rw_tac[o_assoc] >>
 arw_tac[idL,idR]
 )
(rapg "areiso(X,Y) & areiso(Y,Z) ==> areiso(X,Z)")
)

val iso_to_same = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >>
 by_tac “areiso(A,Y)” 
 >-- (drule (iso_symm |> dimpl2r) >> first_x_assum accept_tac) >>
 by_tac “areiso(X,A) & areiso(A,Y)”
 >-- (conj_tac>> arw_tac[]) >> 
 drule iso_trans >> first_x_assum accept_tac)
(rapg "areiso(X,A) & areiso(Y,A) ==> areiso(X,Y)")
)


val iso_to_same = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >>
 by_tac “areiso(A,Y)” 
 >-- (drule (iso_symm |> dimpl2r) >> first_x_assum accept_tac) >>
 by_tac “areiso(X,A) & areiso(A,Y)”
 >-- (conj_tac>> arw_tac[]) >> 
 drule iso_trans >> first_x_assum accept_tac)
(rapg "areiso(X,A) & areiso(Y,A) ==> areiso(X,Y)")
)

(*match_mp_tac (gen_all iso_to_same) and without genall gives different things

*)


val inc_inc_iso0 = proved_th(
e
(cases_on “areiso(X,0)” >> cases_on “areiso(Y,0)” (* 4 *)
>-- (*x= 0 ,y=0*)
    (repeat stp_tac >> match_mp_tac (gen_all iso_to_same) >> 
     wexists_tac (readt "0") >> repeat stp_tac >> arw_tac[])
>-- (*x= 0,y,> 0*)
    (repeat stp_tac >>
     assume_tac (to_zero_zero |> gen_all |> ((C specl) (List.map readt ["Y","X","h2:Y->X"]))|> ((C mp) (assume “areiso(X,0)”))) >> first_x_assum OPPOSITE_TAC
    )
>-- (*y = 0, x <> 0*)
   (repeat stp_tac >>
    assume_tac (to_zero_zero |> gen_all |> ((C specl) (List.map readt ["X","Y","h1:X->Y"]))|> ((C mp) (assume “areiso(Y,0)”))) >> first_x_assum OPPOSITE_TAC)
>> repeat stp_tac >>  
   by_tac “EXISTS a':A ->X. a' o a = id(X)”
   >-- (match_mp_tac mono_non_zero_post_inv >> stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[]) >>
   by_tac “EXISTS b':A ->Y. b' o b = id(Y)”
   >-- (match_mp_tac mono_non_zero_post_inv >> stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[]) >> 
   pop_assum_list (map_every STRIP_ASSUME_TAC) >>
   rw_tac[areiso_def,isiso_def] >> wexists_tac (readt "h1:X->Y") >>
   wexists_tac (readt "h2:Y->X") >> stp_tac (* 2 *)
   >-- (by_tac “(b':A->Y) o (b:Y->A) o (h1:X->Y) = b' o a”
       >-- arw_tac[] >>
       by_tac “h1 = (b':A->Y) o (a:X->A)” 
       >-- (suffices_tac “h1 = (b':A->Y) o (b:Y->A) o (h1:X->Y)”
           >-- (stp_tac >> once_arw_tac[] >> once_arw_tac[] >> rw_tac[]) >>
           rw_tac[GSYM o_assoc] >> once_arw_tac[] >> rw_tac[idL]) >>
       arw_tac[] >> rw_tac[o_assoc] >> arw_tac[]) >>
   by_tac “h2 o h1 = ((a':A->X) o (a:X->A)) o (h2:Y->X) o (h1:X->Y)”
   >-- arw_tac[idL] >>
   once_arw_tac[] >>
   by_tac “((a':A->X) o (a:X->A)) o (h2:Y->X) o (h1:X->Y) = 
           (a':A->X) o ((a:X->A) o (h2:Y->X)) o (h1:X->Y)”
   >-- rw_tac[o_assoc] >> once_arw_tac[] >> once_arw_tac[] >> once_arw_tac[] >>
   once_arw_tac[] >> rw_tac[]
)
(rapg "ismono(a:X->A) & ismono(b:Y->A) ==> ALL h1:X->Y. ALL h2:Y->X. b o h1 = a & a o h2 = b ==> areiso(X,Y)")
)

(*
TODO: test unique definition here

TODO:
assumption ALL B. ALL (f : A -> B). ALL (g : A -> B). f = g,goal

x1 = from0(X) o f
*)

val iso_zero_zero = proved_th(
e
(rw_tac[are_iso_is_iso] >> stp_tac >> pop_assum STRIP_ASSUME_TAC >> 
 stp_tac >> wexists_tac (readt "from0(X) o (f:A->0)") >> stp_tac >>
 by_tac “areiso(A,0)”
 >-- (rw_tac[are_iso_is_iso] >> wexists_tac (readt "f:A->0") >> arw_tac[])>>
 drule (from_iso_zero_eq|> undisch |> gen_all|> disch_all |> gen_all) >>
 first_x_assum (specl_then (List.map readt ["X","x1:A->X","from0(X) o (f:A->0)"]) assume_tac) >>
 first_x_assum accept_tac)
(rapg "areiso(A,0) ==> ALL X. EXISTS x0:A->X. ALL x1:A->X. x1 = x0")
)

val prop_2_half2 = proved_th(
e
(repeat stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> cases_on “areiso(Y,0)”
 >-- (by_tac “areiso(X,0)” 
      >-- (ccontra_tac >> drule ax6 >> pop_assum STRIP_ASSUME_TAC(*first_x_assum (x_choose_tac "x") *)>> 
          by_tac “EXISTS xb':1->Y. T” 
          >-- (first_x_assum (specl_then (List.map readt ["(a:X->A) o (x:1->X)","x:1->X"]) assume_tac) >> 
              by_tac “(a:X->A) o (x:1->X) = a o x” >-- rw_tac[] >>
              first_x_assum drule >> first_x_assum (x_choose_tac "xb'") >> 
              wexists_tac (readt "xb':1->Y") >> rw_tac[]) >>
          drule is_zero_no_mem >> first_x_assum OPPOSITE_TAC) >> 
      drule from_iso_zero_eq' >>
      pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >> rw_tac[areiso_def,isiso_def] >> 
      repeat stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >>
      wexists_tac (readt "(g':0->Y) o (f:X->0)") >>
      first_x_assum (specl_then (List.map readt ["A","(b:Y->A) o (g':0->Y) o (f:X->0)","a:X->A"]) assume_tac) >> arw_tac[])  >>
 by_tac “EXISTS g:A->Y. g o b = id(Y)”
 >-- (match_mp_tac mono_non_zero_post_inv >> conj_tac >> first_x_assum accept_tac) >>
 pop_assum STRIP_ASSUME_TAC >> wexists_tac (readt "(g:A->Y) o (a:X->A)") >> 
 match_mp_tac fun_ext >> stp_tac >> rw_tac[o_assoc] >>
 first_x_assum (specl_then (List.map readt ["(a:X->A) o (a':1->X)","a':1->X"]) assume_tac) >> 
 by_tac “(a:X->A) o (a':1->X) = a o a'” >-- rw_tac[] >> first_x_assum drule >> 
 pop_assum STRIP_ASSUME_TAC >> 
 pop_assum (mp_tac o GSYM) >> stp_tac >> arw_tac[] >> 
 by_tac “b o g o b o xb' = (b:Y->A) o ((g:A->Y) o (b:Y->A)) o (xb':1->Y)” >-- rw_tac[o_assoc] >>
 arw_tac[idL])
(rapg "ismono(a:X->A) & ismono(b:Y->A) & (ALL x:1->A. ALL xb:1->X. a o xb = x ==> EXISTS xb':1->Y. b o xb' = x) ==>EXISTS h:X->Y. b o h = a")
)


(*AQ:do not understand why strip asm does not work here*)


(*

AQ3: cannot solve by arw tac because negation is normalised to be false, but the goal is not. Should I change conv_canon or also normalise the goal when rw? 

I think all first_x_assum accept_tac can just be arw in prop_half2

*)


val prop_2_corollary = proved_th(
e
(repeat stp_tac >> assume_tac inc_inc_iso0 >> pop_assum_list (map_every STRIP_ASSUME_TAC) >>
 by_tac “ismono(a:X->A) & ismono(b:Y->A)” >-- (conj_tac >> first_x_assum accept_tac) >>
 first_x_assum drule >> first_x_assum match_mp_tac >> 
 by_tac “EXISTS h1:X->Y. (b:Y->A) o h1 = a”
 >-- (match_mp_tac prop_2_half2 >> pop_assum_list (map_every STRIP_ASSUME_TAC)
      >> repeat stp_tac (* 3 *)
      >-- first_x_assum accept_tac 
      >-- first_x_assum accept_tac >>
      first_x_assum (specl_then [readt "xb:1->X"] assume_tac) >>
      first_x_assum (x_choose_tac "xb'") >> wexists_tac (readt "xb':1->Y") >> 
      pop_assum (mp_tac o GSYM) >> once_arw_tac[] >> stp_tac >> once_arw_tac[] >> rw_tac[])>>
 by_tac “EXISTS h2:Y->X. (a:X->A) o h2 = b”
 >-- (match_mp_tac prop_2_half2 >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> 
     repeat stp_tac >-- first_x_assum accept_tac >-- first_x_assum accept_tac >> 
      first_x_assum (specl_then [readt "xb:1->Y"] assume_tac) >>
      first_x_assum (x_choose_tac "xb'") >> wexists_tac (readt "xb':1->X") >> 
      pop_assum (mp_tac o GSYM) >> once_arw_tac[] >> stp_tac >> once_arw_tac[] >> rw_tac[]) >>
 pop_assum_list (map_every STRIP_ASSUME_TAC) >> wexists_tac (readt "h1:X->Y") >> wexists_tac (readt "h2:Y->X") >> conj_tac >> first_x_assum accept_tac)
(rapg "ismono(a:X->A) & ismono(b:Y->A) & (ALL y:1->Y.EXISTS x:1->X.a o x = b o y) & (ALL x:1->X.EXISTS y:1->Y. a o x = b o y) ==> areiso(X,Y)")
)

(*

TODO: maybe have a function which takes a thm to move quantifier innermost, current gen_all of to_0_0 does nothing with f since it is not in the concl

test remove_asm_tac
*)


val epi_has_section = proved_th(
e
(cases_on “areiso(B,0)”
 >-- (drule (to_zero_zero|> spec_all |> undisch |> allI ("f",ar(mk_ob "A",mk_ob"B"))|> gen_all|>
             disch_all) >> 
      first_x_assum (specl_then (List.map readt ["A","e:A->B"]) assume_tac) >> 
      assume_tac (iso_zero_zero|> gen_all |> (C specl) [readt "B"]) >>
      first_x_assum drule >> 
      first_x_assum (specl_then (List.map readt ["A"]) assume_tac) >> 
      first_x_assum (x_choose_tac "x0") >> stp_tac >> wexists_tac (readt "x0:B->A") >>
      assume_tac (iso_zero_zero|> gen_all |> (C specl) [readt "B"]) >>
      first_x_assum drule >>
      rule_assum_tac (fn th => specl th (List.map readt ["B"]) handle _ => th) >> 
      pop_assum STRIP_ASSUME_TAC >> 
      by_tac “(e:A->B) o (x0:B->A) = x0'”
      >-- (first_x_assum (specl_then (List.map readt ["(e:A->B) o (x0:B->A)"]) assume_tac)  >> first_x_assum accept_tac) >>
      by_tac “id(B) = x0'”
      >-- (first_x_assum (specl_then (List.map readt ["id(B)"]) assume_tac) >> first_x_assum accept_tac) >>
      once_arw_tac[](*if replace with rw, then loop, do not understand why*) >> rw_tac[]) >>
stp_tac >>
by_tac “isepi(e:A->B)&~(areiso(B,0))”
>-- (conj_tac >> first_x_assum accept_tac) >> drule epi_pre_inv >> pop_assum STRIP_ASSUME_TAC >> 
wexists_tac (readt "g:B->A") >> once_arw_tac[] >> rw_tac[])
(rapg "isepi(e) ==> EXISTS sec:B->A. e o sec = id(B)")
)

(*TODO: maybe a thm says eq(f,g) = eq(g,f)*)

val fac_through_eq = proved_th(
e
(stp_tac >> rule_assum_tac sym >> arw_tac[] >> 
suffices_tac “f o eqa(f,g) = g o eqa(f:B->C,g:B->C)”
>-- (stp_tac >> rw_tac[GSYM o_assoc] >> arw_tac[]) >> 
assume_tac ((specl ax_eq' (List.map readt ["B","C","f:B->C","g:B->C"]))|>conjE1)>> arw_tac[])
(rapg "eqa(f,g) o h0 = h ==> f o h = g o h")
)

val fac_through_eq_iff = proved_th(
e
(dimp_tac >> stp_tac >> pop_assum STRIP_ASSUME_TAC (* 2 *)
 >-- (drule fac_through_eq >> first_x_assum accept_tac) >> 
 wexists_tac (readt "eqinduce(f:A->B,g:A->B,h:X->A)") >> 
 drule eq_fac >> first_x_assum accept_tac)
(rapg "(EXISTS h0: X-> eqo(f,g).eqa(f,g) o h0 = h) <=> f o h = g o h")
)




val psyms0 = insert_psym "isrefl";

val psyms0 = insert_psym "issymm";

val psyms0 = insert_psym "istrans";

val isrefl_def = define_pred(rapf "ALL X. ALL Y. ALL f0:X->Y. ALL f1:X->Y. isrefl(f0,f1) <=> EXISTS d:Y->X.f0 o d = id(Y) & f1 o d = id(Y)")

val issymm_def = define_pred(rapf "ALL X. ALL Y. ALL f0:X->Y. ALL f1:X->Y. issymm(f0,f1) <=> EXISTS t:X->X.f0 o t = f1 & f1 o t = f0")

val istrans_def = define_pred(rapf "ALL A. ALL B. ALL f0:A->B. ALL f1:A->B. istrans(f0,f1) <=> (ALL X. ALL h0:X->A. ALL h1:X->A. f1 o h0 = f0 o h1 ==> EXISTS u:X->A. f0 o u = f0 o h0 & f1 o u = f1 o h1)")


val to_zero_zero' = to_zero_zero|> spec_all|> undisch
                                |> allI (dest_var (readt "f:A->B"))|> gen_all
                                |> disch_all |> gen_all

(*TODO: 
ALL B. areiso(B?, 0) ==> ALL A. ALL (f : A? -> B?). areiso(A?, 0): thm does not work on commented out line, may add normalisation procedure that transforms the thm into 
ALL B. ALL A. areiso(B?, 0) /\ ?f:A->B. T ==> areiso(A,0)
*)

val inc_inc_iso_as_subobj = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> cases_on “areiso(X,0)” >> cases_on “areiso(Y,0)”
 >-- (stp_tac (*2*)>> match_mp_tac from_iso_zero_eq' >> arw_tac[])
 >-- (suffices_tac “areiso(Y,0)”
     >-- (stp_tac >> first_x_assum OPPOSITE_TAC) >>
     assume_tac (to_zero_zero |> gen_all |> ((C specl) (List.map readt ["Y","X","h2:Y->X"]))|> ((C mp) (assume “areiso(X,0)”))) >> arw_tac[])
     (*match_mp_tac (spec_all to_zero_zero') instead of assum*)
 >-- (suffices_tac “areiso(X,0)”
     >-- (stp_tac >> first_x_assum OPPOSITE_TAC) >>
     assume_tac (to_zero_zero |> gen_all |> ((C specl) (List.map readt ["X","Y","h1:X->Y"]))|> ((C mp) (assume “areiso(Y,0)”))) >> arw_tac[]) >>
by_tac “EXISTS a':A ->X. a' o a = id(X)”
>-- (match_mp_tac mono_non_zero_post_inv >> stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[]) >>
by_tac “EXISTS b':A ->Y. b' o b = id(Y)”
>-- (match_mp_tac mono_non_zero_post_inv >> stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[]) >> 
conj_tac (*2 *)
>-- (pop_assum_list (map_every STRIP_ASSUME_TAC) >>
    suffices_tac “(b':A->Y) o (b:Y->A) o (h1:X->Y) o (h2:Y->X) = id(Y)”
    >-- (rw_tac[GSYM o_assoc] >> once_arw_tac[] >> rw_tac[idL,o_assoc]) >>
    suffices_tac “(b':A->Y) o ((b:Y->A) o (h1:X->Y)) o (h2:Y->X) = id(Y)”
    >-- rw_tac[o_assoc] >>
    once_arw_tac[] >> once_arw_tac[] >> arw_tac[]) >> 
pop_assum_list (map_every STRIP_ASSUME_TAC) >>
suffices_tac “(a':A->X) o (a:X->A) o (h2:Y->X) o (h1:X->Y) = id(X)”
>-- (rw_tac[GSYM o_assoc] >> once_arw_tac[] >> rw_tac[idL,o_assoc]) >> 
suffices_tac “(a':A->X) o ((a:X->A) o (h2:Y->X)) o (h1:X->Y) = id(X)”
>-- rw_tac[o_assoc] >> arw_tac[]
)
(rpg "(ismono(a:X->A) & ismono(b:Y->A) & b o h1 = a & a o h2 = b) ==> h1 o h2 = id(Y) & h2 o h1 = id(X)")
)

val prop_2_corollary_as_subobj = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> 
 by_tac “EXISTS h1:X->Y. (b:Y->A) o h1 = a”
 >-- (match_mp_tac prop_2_half2 >> arw_tac[] >> repeat stp_tac >> 
     first_x_assum (specl_then [readt "xb:1->X"] assume_tac) >> 
     first_x_assum (x_choose_tac "xb'") >> wexists_tac (readt "xb':1->Y") >> 
     pop_assum (mp_tac o GSYM) >> once_arw_tac[] >> stp_tac >> once_arw_tac[] >> rw_tac[]) >>
 by_tac “EXISTS h2:Y->X. (a:X->A) o h2 = b”
 >-- (match_mp_tac prop_2_half2 >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> 
     repeat stp_tac >-- first_x_assum accept_tac >-- first_x_assum accept_tac >> 
      first_x_assum (specl_then [readt "xb:1->Y"] assume_tac) >>
      first_x_assum (x_choose_tac "xb'") >> wexists_tac (readt "xb':1->X") >> 
      pop_assum (mp_tac o GSYM) >> once_arw_tac[] >> stp_tac >> once_arw_tac[] >> rw_tac[]) >>
 pop_assum_list (map_every STRIP_ASSUME_TAC) >> wexists_tac (readt "h1:X->Y") >>
 wexists_tac (readt "h2:Y->X") >> arw_tac[] >> match_mp_tac inc_inc_iso_as_subobj >> arw_tac[])
(rapg "(ismono(a:X->A) & ismono(b:Y->A) & (ALL y:1->Y. EXISTS x:1->X. a o x = b o y) & (ALL x:1->X. EXISTS y:1->Y. a o x = b o y)) ==>EXISTS h1:X->Y. EXISTS h2:Y->X. b o h1 = a & a o h2 = b & h1 o h2 = id(Y) & h2 o h1 = id(X)")
)
    

(*
Theorem aa:
a = a
Proof
cheat
QED

“a = b” rw[aa]
*)


(*Thm1*)

(*
Theorem Thm1_case_1_comm_condition_left:
∀B f g. f∶ N → B ∧ g∶ one → B ⇒
          (f o z = g  ⇔ ⟨id N,f⟩ o z = ⟨z,g⟩)
Proof
rw[] >>
‘⟨id N,f⟩∶ N → (N× B) ∧ ⟨z,g⟩∶ one → (N×B) ∧ ⟨id N,f⟩ o z∶ one → (N×B)’
 by metis_tac[id1,pa_hom,compose_hom,ax3] >>
‘z∶ one → N’ by metis_tac[ax3] >>
‘f o z ∶ one → B’ by metis_tac[compose_hom] >>
rw[EQ_IMP_THM] (* 2 *)
>- (irule to_p_eq_applied >> qexistsl_tac [‘N’,‘B’,‘one’] >> rw[] (* 2 *)
   >- (‘p1 N B ∘ ⟨z,f ∘ z⟩ = z’ by metis_tac[p1_of_pa] >>
      ‘p1 N B ∘ ⟨id N,f⟩ ∘ z = (p1 N B ∘ ⟨id N,f⟩) ∘ z’ by metis_tac[compose_assoc,p1_hom] >>
      metis_tac[idL,id1,p1_of_pa])
   >- (‘p2 N B ∘ ⟨z,f ∘ z⟩ = f o z’ by metis_tac[p2_of_pa] >>
      ‘p2 N B ∘ ⟨id N,f⟩ ∘ z = (p2 N B ∘ ⟨id N,f⟩) ∘ z’ by metis_tac[compose_assoc,p2_hom] >>
      metis_tac[idL,id1,p2_of_pa]))
>- (‘p2 N B o ⟨id N,f⟩ ∘ z = p2 N B o ⟨z,g⟩’ by metis_tac[] >>
   ‘p2 N B ∘ ⟨id N,f⟩ ∘ z = (p2 N B ∘ ⟨id N,f⟩) ∘ z’ by metis_tac[compose_assoc,p2_hom] >>
   ‘(p2 N B ∘ ⟨id N,f⟩) = f’ by metis_tac[id1,p2_of_pa] >>
    metis_tac[p2_of_pa])
QED
*)

(*TODO:  Exception- Fail "unexpected term constructor" raised more helpful error message*)


val Thm1_case_1_comm_condition_left = proved_th(
e
(dimp_tac >> stp_tac
 >-- (match_mp_tac to_p_eq' >> arw_tac[GSYM o_assoc,p1_of_pa,p2_of_pa,idL]) >>
 suffices_tac “p2(N,B) o pa(id(N), f) o z = p2(N,B) o pa(z, g)”
 >-- rw_tac[GSYM o_assoc,p2_of_pa] >> 
 arw_tac[])
(rapg "(f:N->B) o z = g <=> <id(N),f> o z = <z,g>")
)

val Thm1_case1_comm_condition_right = proved_th(
e
(dimp_tac >> stp_tac
 >-- (match_mp_tac to_p_eq' >> arw_tac[GSYM o_assoc,p1_of_pa,p2_of_pa] >> rw_tac[o_assoc,p1_of_pa,idR,idL])>>
 suffices_tac “p2(N,B) o pa((s o p1(N, B)), h) o pa(id(N), f) = p2(N,B) o pa(id(N), f) o s”  
 >-- rw_tac[GSYM o_assoc,p2_of_pa] >> arw_tac[])
(rapg "h o <id(N),f> = f o s <=> <s o p1(N,B),h> o <id(N),f> = <id(N),f> o s")
)

val Thm1_case1_comm_condition = proved_th(
e
(dimp_tac >> stp_tac 
 >-- (pop_assum STRIP_ASSUME_TAC >> drule (Thm1_case_1_comm_condition_left|> dimpl2r) >>
     drule (Thm1_case1_comm_condition_right |> dimpl2r |> GSYM) >> arw_tac[]) >>
 pop_assum STRIP_ASSUME_TAC >> drule (Thm1_case_1_comm_condition_left|> dimpr2l) >>
 drule (Thm1_case1_comm_condition_right |> dimpr2l) >> arw_tac[])
(rapg "(f0 o z = g & f0 o s = h o <id(N),f0>) <=> (<id(N),f0> o z = <z,g> & <s o p1(N,B),h> o <id(N),f0> = <id(N),f0> o s)")
)

val ax3_equality = ax3 |> spec_all |> dimpr2l |> allI ("x",sort_of (readt "x:N->X"))|> (C allE) (readt "Nind(x0:1->X,t)")|> (C mp) (refl (readt "Nind(x0:1->X,t:X->X)"))|> gen_all

(*!!!!!!!once arw has the canon, but still need the strip asume, do not understand why*)

(*TODO: unabbrev, ntac*)
val Thm1_case_1 = proved_th(
e
(abbrev_tac “Nind(pa(z,g:1->B),pa(s o p1(N,B), h)) = f'” >> 
 assume_tac ax3_equality >> first_x_assum (specl_then
 (List.map readt ["N * B","pa(s o p1(N,B),h:N*B ->B)","pa(z,g:1->B)"]) assume_tac) >>
 by_tac “p1(N,B) o f' = id(N)”
 >-- (match_mp_tac comm_with_s_id >> last_x_assum (assume_tac o GSYM) >> once_arw_tac[] >> rw_tac[o_assoc] >> 
      pop_assum_list (map_every STRIP_ASSUME_TAC) >> conj_tac (* 2 *)
      >-- arw_tac[p1_of_pa] >>
      arw_tac[GSYM o_assoc,p1_of_pa] >> arw_tac[o_assoc] >> rw_tac[GSYM o_assoc,p1_of_pa]) >>
 abbrev_tac “p2(N,B) o (f':N->N*B) = f” >>
 by_tac “f':N->N*B = pa(id(N),f)”
 >-- (match_mp_tac to_p_eq' >> pop_assum (assume_tac o GSYM) >> arw_tac[p2_of_pa,p1_of_pa]) >> 
 wexists_tac (readt "f:N->B") >> stp_tac (*2*)
 >-- (pop_assum_list (map_every STRIP_ASSUME_TAC) >> 
     pick_x_assum “p2(N,B) o f' = f:N->B” (assume_tac o GSYM) >> 
     pick_x_assum “Nind(pa(z, g:1->B), pa(s o p1(N, B), h:N*B ->B)) = f'” (assume_tac o GSYM) >>
     once_arw_tac[] >> once_arw_tac[] >> rw_tac[o_assoc] >> once_arw_tac[] >> rw_tac[p2_of_pa] >>
     rw_tac[GSYM o_assoc,p2_of_pa] >>
     pop_assum (assume_tac o GSYM) >> once_arw_tac[] >> once_arw_tac[] >> rw_tac[p2_of_pa]) >>
 pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >> once_arw_tac[] >>
 repeat stp_tac >> pop_assum mp_tac >> rw_tac[Thm1_case1_comm_condition] >> stp_tac >>
 pop_assum STRIP_ASSUME_TAC >> pop_assum (assume_tac o GSYM) >>
 by_tac “pa(id(N),f0:N->B) = f'” >> last_x_assum (assume_tac o GSYM) >> once_arw_tac[] >>
 rw_tac[GSYM ax3] >> arw_tac[] >> 
 match_mp_tac (gen_all to_p_eq_one_side) >> once_arw_tac[] >> first_x_assum accept_tac
 (*the accept is necessary, cannot be solved by arw, not unexpected*)
 (*drule (ax3 |> spec_all |> dimpl2r|> undisch |> split_assum “(x:N->X) o z = x0 & x o s = t o x”|> disch_all|>*)
 (*wexists_tac (readt "f:N->B") >> stp_tac (*2-exists and uniqueness*)
 >-- (rw_tac[Thm1_case1_comm_condition] >> )*))
(rapg "EXISTS f:N->B. (f o z = g & f o s = h o <id(N),f>) & (ALL f0. f0 o z = g & f0 o s = h o <id(N),f0> ==> f0 = f)")
)

(*TOdO: think about the drule commented out, both drule and match mp does not work there*)

val Thm1_comm_eq_left = proved_th(
e
(by_tac “pa(p1(A,1),tp(f:A * N -> B) o z o p2(A,1)) = pa(p1(A,N),tp(f) o p2(A,N)) o pa(p1(A,1),z o p2(A,1))”
>-- rw_tac[parallel_p_one_side] >> dimp_tac (* 2 *) >> stp_tac
>-- (by_tac “f o pa(p1(A, 1), z o p2(A, 1)) = ev(A,B) o pa(p1(A,1),tp(f:A * N -> B) o z o p2(A,1))”      >-- (arw_tac[] >> rw_tac[GSYM o_assoc,ev_of_tp]) >>
     once_arw_tac[] >> rw_tac[GSYM o_assoc] >> once_arw_tac[] >> rw_tac[ev_of_tp]) >>
match_mp_tac ev_eq_eq >> rw_tac[o_assoc] >> once_arw_tac[] >> rw_tac[GSYM o_assoc,ev_of_tp] >>
arw_tac[]
)
(rapg "tp(f) o z = tp (g o p1(A,1)) <=> f o <p1(A,1),z o (p2(A,1))> = g o p1(A,1)")
)

val dom = fst o dest_ar o sort_of
val cod = snd o dest_ar o sort_of

fun mk_o g f = Fun("o",mk_ar_sort (dom f) (cod g),[g,f])
fun mk_eq t1 t2 = if sort_of t1 = sort_of t2 then Pred("=",[t1,t2])
                  else raise ERR "inconsistent sorts"

val pm1 = readt "pa(p1(A,N* exp(A,B)),p1(N,exp(A,B)) o p2(A,N * exp(A,B)))"
val pm2 = readt "pa(p1(A,N * exp(A,B)),p2(N,exp(A,B)) o p2(A,N * exp(A,B)))"
val l = pa pm1 (mk_o (readt "ev(A,B)") pm2)
val l_def = mk_eq l (readt "l:A * (N * exp(A,B)) -> (A * N) * B")



val mgf_RL = mk_o (tp (mk_o (readt "h: (A * N) * B -> B") l)) (readt "pa(id(N),tp(f:A*N ->B))")
val mgf_R = mk_eq mgf_RL (readt "tp(f:A*N ->B) o s")

val mgf = mk_dimp
         (rapf "h o <id(A*N),(f:A*N->B)> = (f:A * N ->B) o <p1(A,N),s o p2(A,N)>") mgf_R
   
(*TODO: rapf bug: *)

val by_def_l1_f = mk_eq
(mk_o (readt "p1(A,N)") (mk_o (readt "p1(A*N,B)")
 (mk_o l (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))))
(readt "p1(A,N) o p1(A*N,B) o pa(id(A*N),f:A*N ->B)")

val by_def_l1_f0 = mk_eq
(mk_o (mk_o (readt "p1(A,N)") (mk_o (readt "p1(A*N,B)") l))
  (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))
(readt "p1(A,N) o p1(A*N,B) o pa(id(A*N),f:A*N ->B)")

val by_def_l1_f_eq_f0 = mk_eq
(mk_o (readt "p1(A,N)") (mk_o (readt "p1(A*N,B)")
 (mk_o l (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))))
(mk_o (mk_o (readt "p1(A,N)") (mk_o (readt "p1(A*N,B)") l))
  (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))



fun goal_of_form f = (fvf f,[]:form list,f)

(*TODO: use conv rule on the goal to transform the goal, think this is just fconv_tac*)

val by_def_l10 = proved_th(
e
(rw_tac[p1_of_pa,idR])
(new_goal (goal_of_form by_def_l1_f0))
)

val by_def_l1eq0 = proved_th(
e
(rw_tac[o_assoc])
(new_goal (goal_of_form by_def_l1_f_eq_f0))
)

val by_def_l1 = conv_rule (once_depth_fconv (rewr_conv (GSYM by_def_l1eq0)) no_fconv) by_def_l10


(*p2 ver*)
val by_def_l2_f = mk_eq
(mk_o (readt "p2(A,N)") (mk_o (readt "p1(A*N,B)")
 (mk_o l (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))))
(readt "p2(A,N) o p1(A*N,B) o pa(id(A*N),f:A*N ->B)")

val by_def_l2_f0 = mk_eq
(mk_o (mk_o (readt "p2(A,N)") (mk_o (readt "p1(A*N,B)") l))
  (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))
(readt "p2(A,N) o p1(A*N,B) o pa(id(A*N),f:A*N ->B)")

val by_def_l2_f_eq_f0 = mk_eq
(mk_o (readt "p2(A,N)") (mk_o (readt "p1(A*N,B)")
 (mk_o l (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))))
(mk_o (mk_o (readt "p2(A,N)") (mk_o (readt "p1(A*N,B)") l))
  (readt "pa(p1(A,N),pa(id(N),tp(f:A*N ->B)) o p2(A,N))"))


val by_def_l20 = proved_th(
e
(rw_tac[p1_of_pa,idR,p2_of_pa] >> rw_tac[o_assoc,p2_of_pa] >> rw_tac[GSYM o_assoc,p1_of_pa,idL])
(new_goal (goal_of_form by_def_l2_f0))
)

val by_def_l2eq0 = proved_th(
e
(rw_tac[o_assoc])
(new_goal (goal_of_form by_def_l2_f_eq_f0))
)

val by_def_l2 = conv_rule (once_depth_fconv (rewr_conv (GSYM by_def_l2eq0)) no_fconv) by_def_l20


val by_def_l3_f = mk_eq
(mk_o (readt "p2(A*N,B)") (mk_o l (readt "pa(p1(A,N),pa(id(N),tp(f:A*N->B)) o p2(A,N))")))
(readt "p2(A*N,B) o pa(id(A*N),f:A*N->B)")


val by_def_l3_lemma = proved_th(
e
(match_mp_tac to_p_eq' >> stp_tac
>-- (rw_tac[GSYM o_assoc,p2_of_pa] >> rw_tac[o_assoc,p2_of_pa] >> rw_tac[GSYM o_assoc,p2_of_pa])>>
rw_tac[GSYM o_assoc,p1_of_pa])
(rapg "<p1(A,N*exp(A,B)),p2(N,exp(A,B)) o p2(A,N*exp(A,B))> o <p1(A,N),<id(N),tp(f:A*N->B)> o p2(A,N)> = <p1(A,N),tp(f) o p2(A,N)>")
)

val by_def_l3 = proved_th(
e
(rw_tac[GSYM o_assoc,p2_of_pa] >> rw_tac[o_assoc,by_def_l3_lemma,ev_of_tp])
(new_goal (goal_of_form by_def_l3_f))
)

val suff_1_f = mk_eq
(mk_o (tp (mk_o (readt "h:(A * N) * B -> B") l)) (readt "pa(id(N),tp(f:A*N-> B))"))
(tp (readt "(h:(A * N) * B -> B) o pa(id(A * N),f:A*N -> B)"))

val suff_1 = proved_th(
e
(match_mp_tac is_tp >> abbrev_tac l_def >> arw_tac[] >> rw_tac[o_assoc,parallel_p_one_side] >>
rw_tac[GSYM o_assoc,ev_of_tp] >> rw_tac[o_assoc] >> 
suffices_tac “l o pa(p1(A, N), pa(id(N), tp(f)) o p2(A, N)) = pa(id((A * N)), f:A*N->B)”
>-- (stp_tac >> arw_tac[]) >>
match_mp_tac iterated_p_eq_applied >> stp_tac
>-- (pop_assum (assume_tac o GSYM) >> arw_tac[] >> rw_tac[by_def_l1]) >> conj_tac
>-- (pop_assum (assume_tac o GSYM) >> arw_tac[] >> rw_tac[by_def_l2]) >>
pop_assum (assume_tac o GSYM) >> arw_tac[] >> rw_tac[o_assoc,by_def_l3])
(new_goal (goal_of_form suff_1_f))
)

val suff_2 = proved_th(
e
(fconv_tac sym_fconv >> match_mp_tac is_tp >> rw_tac[o_assoc,parallel_p_one_side] >>
 rw_tac[GSYM o_assoc,ev_of_tp])
(rapg "tp(f o <p1(A,N),s o p2(A,N)>) = tp(f:A * N -> B) o s")
)

val Thm1_comm_eq_right = proved_th(
e
(suffices_tac (mk_conj suff_1_f (rapf "tp((f:A * N -> B) o <p1(A,N),s o p2(A,N)>) = tp(f:A * N -> B) o s")) 
>-- (stp_tac >> pop_assum STRIP_ASSUME_TAC >> dimp_tac 
    >-- (stp_tac >> arw_tac[]) >>
    stp_tac >> match_mp_tac (dimpl2r tp_eq) >> arw_tac[] >> 
    pop_assum_list (map_every (assume_tac o GSYM)) >>
    pick_x_assum “tp(f:A * N ->B) o s = tp(f o pa(p1(A, N), s o p2(A, N)))” (K all_tac) >>
    arw_tac[]) >>
conj_tac >-- rw_tac[suff_1] >-- rw_tac[suff_2])
(new_goal (goal_of_form mgf))
)

val Thm1_comm_eq_condition = 
dimpI
(
(conjI
(Thm1_comm_eq_left|> GSYM |> dimpl2r |> undisch) 
(Thm1_comm_eq_right|> dimpl2r|> undisch)
)|> conj_all_assum |> disch_all
)
(
(conjI
(Thm1_comm_eq_left|> GSYM |> dimpr2l |> undisch) 
(Thm1_comm_eq_right|> dimpr2l|> undisch)
)|> conj_all_assum |> disch_all
)

val g' = readt "tp((g:A->B) o p1(A,1))"
val h' = tp (mk_o (readt "h:(A*N)*B ->B") l)

val Thm1_case_1_speced = Thm1_case_1|> gen_all |> (C specl) [readt "exp(A,B)",g',h']
(*arw in commented place does not work because of the conj*)


val Thm1_existence = proved_th(
e
(x_choose_tac "fb" Thm1_case_1_speced >> 
pop_assum mp_tac >> abbrev_tac l_def >> arw_tac[] >> stp_tac >> 
wexists_tac (readt "ev(A,B) o pa(p1(A,N),(fb:N-> exp(A,B)) o p2(A,N))") >>
rw_tac[Thm1_comm_eq_condition] >> 
by_tac “tp(ev(A,B) o pa(p1(A,N),(fb:N-> exp(A,B)) o p2(A,N))) = fb”
>-- (fconv_tac sym_fconv >> match_mp_tac is_tp >> rw_tac[])>>
arw_tac[] >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[])
(rapg "EXISTS f:A * N -> B. f o <p1(A,1),z o p2(A,1)> = g o p1(A,1) & h o <id(A*N),f> = f o <p1(A,N),s o p2(A,N)>")
)

(*TODO: and_assoc, a rule*)

val Thm1 = proved_th(
e
(x_choose_tac "fb" Thm1_case_1_speced >> 
pop_assum mp_tac >> abbrev_tac l_def >> arw_tac[] >> stp_tac >> 
wexists_tac (readt "ev(A,B) o pa(p1(A,N),(fb:N-> exp(A,B)) o p2(A,N))") >>
rw_tac[Thm1_comm_eq_condition] >> 
by_tac “tp(ev(A,B) o pa(p1(A,N),(fb:N-> exp(A,B)) o p2(A,N))) = fb”
>-- (fconv_tac sym_fconv >> match_mp_tac is_tp >> rw_tac[]) >> repeat stp_tac (* 3 *)
>-- (arw_tac[] >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[])
>-- (arw_tac[] >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[]) >> 
(*uniqueness*)
match_mp_tac (dimpl2r tp_eq) >> arw_tac[] >> pop_assum_list (map_every STRIP_ASSUME_TAC) >>
first_x_assum match_mp_tac >> arw_tac[] >> rev_pop_assum mp_tac >> rev_pop_assum mp_tac >>
arw_tac[] >> repeat stp_tac >> arw_tac[])
(rapg "EXISTS f:A * N -> B. (f o <p1(A,1),z o p2(A,1)> = g o p1(A,1) & h o <id(A*N),f> = f o <p1(A,N),s o p2(A,N)>) & (ALL f0. f0 o <p1(A,1),z o p2(A,1)> = g o p1(A,1) & h o <id(A*N),f0> = f0 o <p1(A,N),s o p2(A,N)> ==> f0 = f)")
)

val pred_exists = proved_th(
e
(assume_tac (specl  (gen_all Thm1_case_1) (List.map readt ["N","z","p1(N,N)"])) >>
 first_x_assum (x_choose_tac "f") >> pop_assum STRIP_ASSUME_TAC >>
 wexists_tac (readt "f:N->N") >> arw_tac[p1_of_pa])
(rapg "EXISTS p:N->N. p o z = z & p o s = id(N)")
)


(*conv_rule (rewr_fconv (exists_all ("X",ob))) distinct_endo_exists
TODO: think of how to do this conv in one function and work for all layers.

*)

val ax3' =
specl ax3 (List.map readt ["X","a:1->X"]) |> spec_all 
|> allI (dest_var(readt"x:N->X")) |> gen_all


(*todo: a tactic of rewriting all assumptions using the newly added assumption*)

(*

X ,   
   (e1 : X -> X), (e2 : X -> X), (n : 1 -> N), (p : N -> N)
   1.s o n = z
   2.p o z = z & p o s = id(N)
   3.n = z
   4.ALL X. ALL (t : X? -> X?). t? = id(X?)
   5.~e1 = e2
   6.e1 = id(X)
   7.e2 = id(X)
   ----------------------------------------------------------------------
   F()

hard to prove e1 = e2 from it since the goal got simplified to false
*)

val Thm2_1 = proved_th(
e
(ccontra_tac >>  x_choose_then "p" assume_tac pred_exists >> by_tac “n = z” 
 >-- (suffices_tac “(p:N->N) o s o n = p o z” 
     >-- (pop_assum_list (map_every STRIP_ASSUME_TAC) >> rw_tac[GSYM o_assoc] >>
          arw_tac[idL]) >>
     arw_tac[]) >>
by_tac “ALL X. ALL t:X->X. t = id(X)”
>-- (repeat stp_tac >> match_mp_tac fun_ext >> stp_tac >>
     assume_tac (specl ax3_equality (List.map readt ["X","t:X->X","a:1->X"])) >>
     pop_assum_list (map_every STRIP_ASSUME_TAC) >> arw_tac[] >>
     pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >> arw_tac[] >> repeat stp_tac >>
     suffices_tac “(t:X->X) o Nind (a:1->X,t) o z = Nind(a,t) o s o z”
     >-- (once_arw_tac[] >> once_arw_tac[idL] >> stp_tac >> arw_tac[]) >>
     rw_tac[GSYM o_assoc] >> once_arw_tac[] >> rw_tac[]
     ) >>
assume_tac distinct_endo_exists >> 
first_x_assum (x_choosel_tac ["X","e1","e2"]) >>
first_assum (specl_then (List.map readt ["X","e1:X->X"]) assume_tac) >>
first_assum (specl_then (List.map readt ["X","e2:X->X"]) assume_tac) >>
by_tac “e1 = e2:X->X” >-- (pick_x_assum “~(e1 = e2:X->X)”  (K all_tac) >> once_arw_tac[] >>
rw_tac[])>>  first_assum OPPOSITE_TAC
 )
(rpg "~(s o n = z)")
)


(*todo: switch the order of quantifier of ax3*)

(*TODO:arw for conjunct work here, check where it works and where it does not work*)

val Thm2_2 = proved_th(
e
(match_mp_tac (gen_all post_inv_mono) >> 
 x_choose_then "x" assume_tac pred_exists >> wexists_tac (readt "x:N->N") >> arw_tac[])
(rapg "ismono(s)")
)

val Thm2_3_alt = proved_th(
e
(rw_tac[are_iso_is_iso] >> 
 specl_then (List.map readt ["A","s':A->A","z':1->A"]) assume_tac ax3_equality >>
 stp_tac >> pop_assum_list (map_every STRIP_ASSUME_TAC) >> 
 wexists_tac (readt "a:A->N") >> 
 match_mp_tac mono_epi_is_iso >> arw_tac[] >> match_mp_tac (gen_all pre_inv_epi) >>
 wexists_tac (readt "Nind(z':1->A,s':A->A)") >> match_mp_tac comm_with_s_id >>
 arw_tac[o_assoc] >> arw_tac[GSYM o_assoc])
(rapg "ismono(a:A->N) & a o s' = s o a & a o z' = z ==> areiso(A,N)")
)

fun try_on_assum th = rule_assum_tac (rewr_rule [th]) 

(*TODO:
pick_assum “ismono(a:A->N)” try_on_assum gives

  (a : A -> N), (b : 1 -> A), (p : P -> A), (q : P -> A)
   1.T()
   2.ALL (n : 1 -> N).
               EXISTS (x0 : 1 -> A). a o x0? = n? ==>
                 EXISTS (x0 : 1 -> A). a o x0? = s o n?
   3.ispb(P, p, q, s o a, a)
   ----------------------------------------------------------------------
   EXISTS (b0 : 1 -> P). p o b0? = b

omits the assumption which may be useful, fix this

*)


(*TODO: write and test existsl_tac here*)
val ind_factorization = proved_th(
e
(stp_tac >> pop_assum STRIP_ASSUME_TAC >> 
assume_tac (specl (gen_all pb_exists) (List.map readt ["A","A","N","s o (a:A->N)","a:A->N"])) >>
first_x_assum (x_choosel_tac ["P","p","q"]) >> 
suffices_tac “isiso(p:P->A)” (* 2 *)
>-- (rw_tac[isiso_def] >> stp_tac >> first_x_assum (x_choose_tac "p'") >> 
    pop_assum STRIP_ASSUME_TAC >> wexists_tac (readt "(q:P->A) o (p':A->P)") >>
    try_on_assum is_pb_def >> pop_assum_list (map_every STRIP_ASSUME_TAC) >>
    pick_x_assum “(s o a:A->N) o (p:P->A) = a o (q:P->A)” (assume_tac o GSYM) >>
    rw_tac[GSYM o_assoc] >> once_arw_tac[] >> rw_tac[o_assoc] >> arw_tac[idR]) >>
(*done with the suffices*)
match_mp_tac mono_epi_is_iso >> conj_tac (* 2 *)
>-- (match_mp_tac (gen_all pb_mono_mono) >> 
    wexists_tac (readt "A") >> wexists_tac (readt "q:P->A") >> wexists_tac (readt "N") >>
    wexists_tac (readt "s o (a: A->N)") >> wexists_tac (readt "a:A->N") >> 
    arw_tac[]) >>
match_mp_tac surj_is_epi >> stp_tac >> try_on_assum ismem_def >> try_on_assum issubset_def >>
pick_assum “ismono(a:A->N)” try_on_assum >>
first_x_assum (specl_then [readt "(a:A->N) o (b:1->A)"] assume_tac) >>
by_tac “EXISTS x0 : 1 -> A. (a:A->N) o x0 = a o b”
>-- (wexists_tac (readt "b:1->A") >> rw_tac[]) >>
first_x_assum drule >> first_x_assum (x_choose_tac "x0") >> try_on_assum is_pb_def >>
pop_assum_list (map_every STRIP_ASSUME_TAC)  >> 
first_x_assum (specl_then (List.map readt ["1","b:1->A","x0:1->A"]) assume_tac) >>
pick_x_assum “a o x0 = s o a o (b:1->A)” (assume_tac o GSYM) >>
pop_assum mp_tac >> rw_tac[GSYM o_assoc] >> stp_tac >> first_x_assum drule >>
first_x_assum (x_choose_tac "a'") >> wexists_tac (readt "a':1->P") >> arw_tac[]
(*>>
first_x_assum drule >> first_x_assum (x_choose_tac) *)

(*by_tac “ismem(s o (a:A->N) o (b:1->A),a,N)” >>
first_x_assum (specl_then [readt "(a:A->N) o (b:1->A)"] assume_tac)*)
)
(rapg "ismono(a) & (ALL n:1->N. ismem(n,a,N) ==>ismem(s o n,a,N)) ==> EXISTS t:A->A. a o t = s o a")
)


(*
Theorem Thm2_3:        
∀A a. is_subset a N ∧ (∀n. is_mem n a N ⇒ is_mem (s o n) a N) ∧
    is_mem z a A ⇒ dom a ≅ N
Proof
rw[] >> irule Thm2_3_alt >> fs[is_subset_def] >>
‘a∶ dom a → N’ by metis_tac[hom_def] >>
qabbrev_tac ‘A = dom a’ >>
drule ind_factorization >> fs[is_mem_def] >> metis_tac[]
QED
*)

(*TODO: write drule canon to make all conjunction implications
drule with assumption with extra information:

1.ismono(a) &
               ALL (n : 1 -> N). ismem(n?, a, N) ==> ismem(s o n?, a, N) &
                 ismem(z, a, A)

thm: 
   |-
   ismono(a) & ALL (n : 1 -> N). ismem(n?, a, N) ==> ismem(s o n?, a, N) ==>
       EXISTS (t : A -> A). a o t? = s o a: thm
> 

*)



val Thm2_3 = proved_th(
e
(repeat stp_tac >> match_mp_tac (gen_all Thm2_3_alt) >> try_on_assum issubset_def >>
 pop_assum STRIP_ASSUME_TAC >> 
 by_tac “ismono(a:A->N) & (ALL n : 1 -> N. ismem(n, a, N) ==> ismem(s o n, a, N))”
 >-- arw_tac[] >> drule ind_factorization >> first_x_assum (x_choose_tac "t") >>
 wexists_tac (readt "a:A->N") >> wexists_tac (readt "t:A->A") >> pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >> rw_tac[ismem_def] >> repeat stp_tac >>
pop_assum_list (map_every STRIP_ASSUME_TAC) >> wexists_tac (readt "x0:1->A") >> arw_tac[])
(rapg "issubset(a:A->N,N) & (ALL n:1->N. ismem(n,a,N) ==>ismem(s o n,a,N)) & ismem(z,a,N) ==>areiso(A,N)")
)

(*TODO: fill the constuctor functions in term.sml,with helpful error message*)

val k' = readt "coeqa(i1(B,B) o f:A->B, i2(B,B) o f)"
val R' = readt "coeqo(i1(B,B) o f:A->B, i2(B,B) o f)"

fun eqo f1 f2 = Fun("eqo",ob,[f1,f2])
fun eqa f1 f2 = Fun("eqa",mk_ar_sort (eqo f1 f2) (dom f1),[f1,f2])

val I0 = eqo (mk_o k' (readt "i1(B,B)")) (mk_o k' (readt "i2(B,B)"))
val q' = eqa (mk_o k' (readt "i1(B,B)")) (mk_o k' (readt "i2(B,B)"))

fun mk_pred p l = Pred(p,l)

val Thm3_A_zero_I_zerof = mk_imp (readf "areiso(A,0)") (mk_pred "areiso" [I0,readt"0"])

val ax6_contrapos = (assume at) |> mp th |> (C negE) (assume (mk_neg conc))
                             |> (C negI) at |> elim_double_neg |> disch (mk_neg conc) 

(*TODO: think about abbrev tac which also works on dom/cod of context*)

(*goal is F, want to prove by i1(X, X) o t = i2(X, X) o t for some t
 (X : ob),
   (t : 1 -> X)
   
   |-
   ~i1(X, X) o t = i2(X, X) o t: thm

*)

val i1_i2_disjoint2F = mp (F_imp ((dest_neg o concl) i1_i2_disjoint))  i1_i2_disjoint 


val q'_abbrev = 
    let val q'0 = (eqa (mk_o k' (readt "i1(B,B)")) (mk_o k' (readt "i2(B,B)")))
    in mk_eq q'0 (mk_var "q'" (sort_of q'0))
    end

(*wexists works here, which is good,but do not understand why it works, how does it see the equality of dom from the asl? if it can do it, should not be hard to rw the cont to be in abbrev

another thing that could happen might be it does not the variable in context has the correct sort.need check.

The usage of from_iso_zero_eq' may be replaced by drule_then, do not have drule_then yet...
*)


(*
 Exception-
   ERR
     ("VALIDInvalid tactic: theorem has extra variable involved k':(B + B)-->(((B i2 B) o f) coeqo ((B i2 B) o f))",
      [], [], []) raised

invalid error message for the commented line
*)


(*Will need equality on object, for rewriting the sorts in abbrev

messy abbrev will make arw invalid.

check where would make arw invalid...
*)

(*here already a bit slow*)
val Thm3_A_zero_I_zero = proved_th(
e
(stp_tac >> abbrev_tac “coeqa(i1(B,B) o f:A->B, i2(B,B) o f) = k'” >> 
abbrev_tac (mk_eq I0 (mk_var "I0" ob)) >> arw_tac[] >>
suffices_tac “~(EXISTS t:1->I0.T)” 
>-- (stp_tac >> drule ax6_contrapos >> arw_tac[]) >>
ccontra_tac >> pop_assum STRIP_ASSUME_TAC >> match_mp_tac (gen_all i1_i2_disjoint2F) >>
wexists_tac (readt "B") >> abbrev_tac q'_abbrev >> wexists_tac (readt "(q':I0->B) o (t:1->I0)") >>
assume_tac 
 (coeq_of_equal|> gen_all |> (C specl) (List.map readt ["A","B+B","i2(B,B) o (f: A->B)"])) >>
first_x_assum (x_choose_tac "ki") >>
try_on_assum (from_iso_zero_eq'|> spec_all |> (C mp) (assume “areiso(A,0)”)|> 
 (C specl) (List.map readt ["B+B","i1(B,B) o (f:A->B)","i2(B,B) o (f: A->B)"])) 
(*pick_assum “coeqa(i2(B, B) o (f:A->B), i2(B, B) o f) = k'” try_on_assum invalid, but should not*)
(*pop_assum_list (map_every mp_tac) >> spec_tac "q'"  *)
(*assum_list
(excl_ths (fn th => (fst o dest_var o snd o dest_eq o concl) th = "I0"
               handle _ => false) 
(map_every mp_tac)) >>
spec_tac "q'" >> pop_assum (K all_tac) >> pop_assum (K all_tac) >>  pop_assum (K all_tac) >>
rev_pop_assum (K all_tac) >> rev_pop_assum (K all_tac) >> arw_tac[]

even do this still the same error message...
*)
)
(new_goal (goal_of_form Thm3_A_zero_I_zerof))
)


val (ct, asl, w) = (fvfl [readf "A = B",readf "P(a:A->B)"],[readf "A = B"],readf "P(a:A->B)")

val th = thm (ct,asl,w)


val genth = th |> allI (dest_var(readt "a:A->B"))

val f0 = concl genth

basic_fconv (rewr_conv (assume (readf "A = B"))) no_fconv f0

basic_fconv (rewr_conv (assume (readf "A = B"))) no_fconv (readf "P(a:A->B)")

rewr_conv (assume (readf "A = B")) (readt "a:A->B")
