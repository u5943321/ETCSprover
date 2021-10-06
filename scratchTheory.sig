signature scratchTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val Forall2_def : thm
    val Forall_def : thm
    val classical : thm
    val computable : thm
    val evaluates_def : thm
    val functional : thm
    val normalizes : thm
    val rcomp : thm
    val reducible : thm
    val stepFunction : thm
    val terminatesOn_def : thm
  
  (*  Theorems  *)
    val Forall2_cases : thm
    val Forall2_impl : thm
    val Forall2_ind : thm
    val Forall2_rules : thm
    val Forall2_strongind : thm
    val Forall_cases : thm
    val Forall_ind : thm
    val Forall_map : thm
    val Forall_rules : thm
    val Forall_strongind : thm
    val computable_classical : thm
    val evaluates_cases : thm
    val evaluates_fun : thm
    val evaluates_ind : thm
    val evaluates_rules : thm
    val evaluates_strongind : thm
    val irred_evaluates_refl : thm
    val normalizes_terminates0 : thm
    val nth_error : thm
    val nth_error_Some_lt : thm
    val nth_error_compute : thm
    val nth_error_ind : thm
    val nth_error_lt_Some : thm
    val nth_error_map : thm
    val size_induction : thm
    val terminatesOn_cases : thm
    val terminatesOn_ind : thm
    val terminatesOn_rules : thm
    val terminatesOn_strongind : thm
(*
   [indexedLists] Parent theory of "scratch"
   
   [patternMatches] Parent theory of "scratch"
   
   [Forall2_def]  Definition
      
      ⊢ Forall2 =
        (λa0 a1 a2.
             ∀Forall2'.
               (∀a0 a1 a2.
                  a1 = [] ∧ a2 = [] ∨
                  (∃x y l l'.
                     a1 = x::l ∧ a2 = y::l' ∧ a0 x y ∧ Forall2' a0 l l') ⇒
                  Forall2' a0 a1 a2) ⇒
               Forall2' a0 a1 a2)
   
   [Forall_def]  Definition
      
      ⊢ Forall =
        (λP a0.
             ∀Forall'.
               (∀a0.
                  a0 = [] ∨ (∃x l. a0 = x::l ∧ P x ∧ Forall' l) ⇒
                  Forall' a0) ⇒
               Forall' a0)
   
   [classical]  Definition
      
      ⊢ ∀R. classical R ⇔ ∀s. reducible R s ∨ ¬reducible R s
   
   [computable]  Definition
      
      ⊢ ∀R. computable R ⇔ ∃f. stepFunction R f
   
   [evaluates_def]  Definition
      
      ⊢ evaluates =
        (λR a0 a1.
             ∀evaluates'.
               (∀a0 a1.
                  a1 = a0 ∧ ¬reducible R a0 ∨
                  (∃y. R a0 y ∧ evaluates' y a1) ⇒
                  evaluates' a0 a1) ⇒
               evaluates' a0 a1)
   
   [functional]  Definition
      
      ⊢ ∀R. functional R ⇔ ∀x y y'. R x y ⇒ R x y' ⇒ y = y'
   
   [normalizes]  Definition
      
      ⊢ ∀R x. normalizes R x ⇔ ∃y. evaluates R x y
   
   [rcomp]  Definition
      
      ⊢ ∀x z R S. rcomp x z R S ⇔ ∃y. R x y ∧ S y z
   
   [reducible]  Definition
      
      ⊢ ∀R x. reducible R x ⇔ ∃x'. R x x'
   
   [stepFunction]  Definition
      
      ⊢ ∀R f.
          stepFunction R f ⇔
          ∀x. case f x of NONE => ∀y. ¬R x y | SOME y => R x y
   
   [terminatesOn_def]  Definition
      
      ⊢ terminatesOn =
        (λa0 a1.
             ∀terminatesOn'.
               (∀a0 a1.
                  (∀x'. a0 a1 x' ⇒ terminatesOn' a0 x') ⇒
                  terminatesOn' a0 a1) ⇒
               terminatesOn' a0 a1)
   
   [Forall2_cases]  Theorem
      
      ⊢ ∀a0 a1 a2.
          Forall2 a0 a1 a2 ⇔
          a1 = [] ∧ a2 = [] ∨
          ∃x y l l'. a1 = x::l ∧ a2 = y::l' ∧ a0 x y ∧ Forall2 a0 l l'
   
   [Forall2_impl]  Theorem
      
      ⊢ ∀A B P1 P2.
          (∀x y. P1 x y ⇒ P2 x y) ⇒ Forall2 P1 A B ⇒ Forall2 P2 A B
   
   [Forall2_ind]  Theorem
      
      ⊢ ∀Forall2'.
          (∀R. Forall2' R [] []) ∧
          (∀x y l l' R. R x y ∧ Forall2' R l l' ⇒ Forall2' R (x::l) (y::l')) ⇒
          ∀a0 a1 a2. Forall2 a0 a1 a2 ⇒ Forall2' a0 a1 a2
   
   [Forall2_rules]  Theorem
      
      ⊢ (∀R. Forall2 R [] []) ∧
        ∀x y l l' R. R x y ∧ Forall2 R l l' ⇒ Forall2 R (x::l) (y::l')
   
   [Forall2_strongind]  Theorem
      
      ⊢ ∀Forall2'.
          (∀R. Forall2' R [] []) ∧
          (∀x y l l' R.
             R x y ∧ Forall2 R l l' ∧ Forall2' R l l' ⇒
             Forall2' R (x::l) (y::l')) ⇒
          ∀a0 a1 a2. Forall2 a0 a1 a2 ⇒ Forall2' a0 a1 a2
   
   [Forall_cases]  Theorem
      
      ⊢ ∀P a0. Forall P a0 ⇔ a0 = [] ∨ ∃x l. a0 = x::l ∧ P x ∧ Forall P l
   
   [Forall_ind]  Theorem
      
      ⊢ ∀P Forall'.
          Forall' [] ∧ (∀x l. P x ∧ Forall' l ⇒ Forall' (x::l)) ⇒
          ∀a0. Forall P a0 ⇒ Forall' a0
   
   [Forall_map]  Theorem
      
      ⊢ ∀p f x A. Forall (λx. p (f x)) A ⇒ Forall p (MAP f A)
   
   [Forall_rules]  Theorem
      
      ⊢ ∀P. Forall P [] ∧ ∀x l. P x ∧ Forall P l ⇒ Forall P (x::l)
   
   [Forall_strongind]  Theorem
      
      ⊢ ∀P Forall'.
          Forall' [] ∧
          (∀x l. P x ∧ Forall P l ∧ Forall' l ⇒ Forall' (x::l)) ⇒
          ∀a0. Forall P a0 ⇒ Forall' a0
   
   [computable_classical]  Theorem
      
      ⊢ computable R ⇒ classical R
   
   [evaluates_cases]  Theorem
      
      ⊢ ∀R a0 a1.
          evaluates R a0 a1 ⇔
          a1 = a0 ∧ ¬reducible R a0 ∨ ∃y. R a0 y ∧ evaluates R y a1
   
   [evaluates_fun]  Theorem
      
      ⊢ ∀R. functional R ⇒ functional (evaluates R)
   
   [evaluates_ind]  Theorem
      
      ⊢ ∀R evaluates'.
          (∀x. ¬reducible R x ⇒ evaluates' x x) ∧
          (∀x y z. R x y ∧ evaluates' y z ⇒ evaluates' x z) ⇒
          ∀a0 a1. evaluates R a0 a1 ⇒ evaluates' a0 a1
   
   [evaluates_rules]  Theorem
      
      ⊢ ∀R. (∀x. ¬reducible R x ⇒ evaluates R x x) ∧
            ∀x y z. R x y ∧ evaluates R y z ⇒ evaluates R x z
   
   [evaluates_strongind]  Theorem
      
      ⊢ ∀R evaluates'.
          (∀x. ¬reducible R x ⇒ evaluates' x x) ∧
          (∀x y z.
             R x y ∧ evaluates R y z ∧ evaluates' y z ⇒ evaluates' x z) ⇒
          ∀a0 a1. evaluates R a0 a1 ⇒ evaluates' a0 a1
   
   [irred_evaluates_refl]  Theorem
      
      ⊢ ∀x. (∀y. ¬R x y) ⇒ evaluates R x x
   
   [normalizes_terminates0]  Theorem
      
      ⊢ ∀R x. normalizes R x ⇒ functional R ⇒ terminatesOn R x
   
   [nth_error]  Theorem
      
      ⊢ (∀v0 h. nth_error 0 (h::v0) = SOME h) ∧
        (∀v1 t n. nth_error (SUC n) (v1::t) = nth_error n t) ∧
        ∀v2. nth_error v2 [] = NONE
   
   [nth_error_Some_lt]  Theorem
      
      ⊢ ∀n H x. nth_error n H = SOME x ⇒ n < LENGTH H
   
   [nth_error_compute]  Theorem
      
      ⊢ (∀v0 h. nth_error 0 (h::v0) = SOME h) ∧
        (∀v1 t n.
           nth_error (NUMERAL (BIT1 n)) (v1::t) =
           nth_error (NUMERAL (BIT1 n) − 1) t) ∧
        (∀v1 t n.
           nth_error (NUMERAL (BIT2 n)) (v1::t) =
           nth_error (NUMERAL (BIT1 n)) t) ∧ ∀v2. nth_error v2 [] = NONE
   
   [nth_error_ind]  Theorem
      
      ⊢ ∀P. (∀h v0. P 0 (h::v0)) ∧ (∀n v1 t. P n t ⇒ P (SUC n) (v1::t)) ∧
            (∀v2. P v2 []) ⇒
            ∀v v1. P v v1
   
   [nth_error_lt_Some]  Theorem
      
      ⊢ ∀n H. n < LENGTH H ⇒ ∃x. nth_error n H = SOME x
   
   [nth_error_map]  Theorem
      
      ⊢ ∀n H a f.
          nth_error n (MAP f H) = SOME a ⇒
          ∃b. nth_error n H = SOME b ∧ a = f b
   
   [size_induction]  Theorem
      
      ⊢ ∀f p. (∀x. (∀y. f y < f x ⇒ p y) ⇒ p x) ⇒ ∀x. p x
   
   [terminatesOn_cases]  Theorem
      
      ⊢ ∀a0 a1. terminatesOn a0 a1 ⇔ ∀x'. a0 a1 x' ⇒ terminatesOn a0 x'
   
   [terminatesOn_ind]  Theorem
      
      ⊢ ∀terminatesOn'.
          (∀R x. (∀x'. R x x' ⇒ terminatesOn' R x') ⇒ terminatesOn' R x) ⇒
          ∀a0 a1. terminatesOn a0 a1 ⇒ terminatesOn' a0 a1
   
   [terminatesOn_rules]  Theorem
      
      ⊢ ∀R x. (∀x'. R x x' ⇒ terminatesOn R x') ⇒ terminatesOn R x
   
   [terminatesOn_strongind]  Theorem
      
      ⊢ ∀terminatesOn'.
          (∀R x.
             (∀x'. R x x' ⇒ terminatesOn R x' ∧ terminatesOn' R x') ⇒
             terminatesOn' R x) ⇒
          ∀a0 a1. terminatesOn a0 a1 ⇒ terminatesOn' a0 a1
   
   
*)
end
