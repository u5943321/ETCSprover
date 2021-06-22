structure conv :> conv = 
struct
open term form thm drule pp
type conv = term -> thm
type fconv = form -> thm
type form = form.form
type term = term.term
type sort = term.sort

exception unchanged

(*think about inst_thm when names clash!!!!!!!!!!!*)

(*
fun part_tmatch partfn A t = 
    let 
        val env = 
            Binarymap.listItems
                (vd_of (match_term (partfn A) t mempty))
        val A' = abstl A (List.map (fn (a,b) => a) env)
    in specl A' (List.map (fn (a,b) => b) env)
    end

*)

(*TODO: think more carefully if use cont or recollect the variable set*)

fun part_tmatch partfn th t = 
    let 
        val env = match_term (fvfl (ant th)) (partfn th) t mempty
    in 
        inst_thm env th
    end


val rewr_conv = part_tmatch (fst o dest_eq o concl)


(*change cont or spec_all *)

(*operations on conv*)

fun all_conv t = refl t

infix thenc

fun thenc (c1,c2) t = 
    let 
        val th1 = c1 t 
    in 
        trans th1 (c2 (snd (dest_eq (concl th1))))
    end

infix orelsec

fun orelsec (c1,c2) t = 
    c1 t handle _ => c2 t

fun try_conv c = c orelsec all_conv

fun repeatc c t =
    ((c thenc (repeatc c)) orelsec all_conv) t

fun no_conv f = raise ERR "no_conv" 

fun first_conv cl = 
    case cl of [] => no_conv
             | h :: t => h orelsec (first_conv t)

(*conv on subterms*)

fun arg_conv c t = 
    case t of 
        Fun (f,s,l) => 
        (EQ_fsym f (List.map (try_conv c) l))
      | _ => refl t
               
fun sub_conv c = first_conv [arg_conv c, all_conv]

fun depth_conv c t = 
    ((try_conv (arg_conv (depth_conv c))) thenc (repeatc c)) t

fun redepth_conv c t =
    (try_conv (arg_conv (redepth_conv c)) thenc
              ((c thenc (redepth_conv c)) orelsec all_conv))
        t

fun top_depth_conv c t =
    (repeatc c thenc
             (sub_conv (top_depth_conv c)) thenc
             ((c thenc (top_depth_conv c)) 
                  orelsec all_conv))
             t

(*fconvs*)

val simp_trace = ref false

fun part_fmatch partfn th f = 
    let 
        val fvd = (match_form (fvfl (ant th)) (partfn th) f mempty)
        val th' = inst_thm fvd th
        val _ = if !simp_trace then Lib.say (printth th') else ()
    in 
        th'
    end

val rewr_fconv = part_fmatch (fst o dest_dimp o concl)

(*operation on fconvs*)

infix thenfc

fun thenfc (fc1,fc2) f = 
    let 
        val th1 = fc1 f 
    in 
        iff_trans th1 (fc2 (snd (dest_dimp (concl th1))))
    end


fun all_fconv f = frefl f

infix orelsefc;

fun orelsefc (fc1,fc2) f = fc1 f handle _ => fc2 f

fun no_fconv f = raise ERR "no_fconv"

fun first_fconv fcl = 
    case fcl of [] => no_fconv
             | h :: t => h orelsefc (first_fconv t)

fun try_fconv fc = fc orelsefc all_fconv

fun changed_fconv (fc:form -> thm) f = 
    if eq_thm (fc f) (frefl f) then raise unchanged 
    else fc f

fun repeatfc fc f = 
    ((fc thenfc (repeatfc fc)) orelsefc all_fconv) f

(*Q: should it fail if cannot make any change?*)

fun pred_fconv c f = 
    case f of 
        Pred (P,tl) => 
        (EQ_psym P (List.map (try_conv c) tl))
      | _ => raise ERR "not a predicate"

(*pred_fconv use try_conv or not?*)

(*conv on subformulas*)

fun disj_fconv fc f = 
    case f of 
        Conn("|",[p,q]) => 
        disj_iff (try_fconv fc p) (try_fconv fc q)
      | _ => raise ERR "not a disjunction"

fun conj_fconv fc f = 
    case f of 
        Conn("&",[p,q]) => 
        conj_iff (try_fconv fc p) (try_fconv fc q)
      | _ => raise ERR "not a conjunction"

fun imp_fconv fc f = 
    case f of
        Conn("==>",[p,q]) => 
        imp_iff (try_fconv fc p) (try_fconv fc q)
      | _ => raise ERR "not an implication"

fun dimp_fconv fc f = 
    case f of
        Conn("<=>",[p,q]) => 
        dimp_iff (try_fconv fc p) (try_fconv fc q)
      | _ => raise ERR "not an iff"

fun forall_fconv fc f = 
    case f of
        (Quant("ALL",n,s,b)) => 
        all_iff (try_fconv fc (subst_bound (Var(n,s)) b)) (n,s)
      | _ => raise ERR "not an all"

fun exists_fconv fc f = 
    case f of
        (Quant("EXISTS",n,s,b)) => 
        exists_iff (try_fconv fc (subst_bound (Var(n,s)) b)) (n,s)
      | _ => raise ERR "not an all"

(*
val th = 
(a : ob),
   (b : ob),
   (c : ob)
   
   |-
   P(a, b, c) <=> a Q c: thm

val f = “EXISTS b. P(a,b,c)”
val fc = rewr_fconv th

for testing, passed
*)
val reflTob = equivT (refl (Var("a",ob)))

val reflTar = equivT (refl (Var("a",ar(Var("A",ob),Var("B",ob)))))


val refl_fconv = 
    first_fconv [rewr_fconv reflTob,rewr_fconv reflTar]
     


fun sub_fconv c fc = 
    try_fconv (first_fconv [conj_fconv fc,
                 disj_fconv fc,
                 imp_fconv fc,
                 dimp_fconv fc,
                 forall_fconv fc,
                 exists_fconv fc,
                 pred_fconv c])




fun depth_fconv c fc f =
    (sub_fconv c (depth_fconv c fc) thenfc
               (repeatfc fc))
        f

fun redepth_fconv c fc f =
    (sub_fconv c (redepth_fconv c fc) thenfc
              ((fc thenfc (redepth_fconv c fc)) orelsefc all_fconv))
        f

val taut_conj_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_conj_1,T_conj_2,F_conj_1,F_conj_2])

val taut_disj_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_disj_1,T_disj_2,F_disj_1,F_disj_2])

val taut_imp_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_imp_1,T_imp_2,F_imp_1,F_imp_2])

val taut_dimp_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [T_dimp_1,T_dimp_2,F_dimp_1,F_dimp_2])



val taut_forall_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [all_true_ar,all_true_ob,
                   all_false_ar,all_false_ob])



val taut_exists_fconv = 
    first_fconv 
        (List.map rewr_fconv 
                  [exists_true_ar,exists_true_ob,
                   exists_false_ar,exists_false_ob])


val basic_taut_fconv = 
    first_fconv [taut_conj_fconv,
                 taut_disj_fconv,
                 taut_imp_fconv,
                 taut_dimp_fconv,
                 taut_forall_fconv,
                 taut_exists_fconv]

val taut_fconv = basic_taut_fconv orelsec refl_fconv 

fun top_depth_fconv c fc f =
    (repeatfc fc thenfc
             (sub_fconv c (top_depth_fconv c fc)) thenfc
             ((fc thenfc (top_depth_fconv c fc)) 
                  orelsefc all_fconv))
        f

fun once_depth_conv conv tm =
   try_conv (conv orelsec (sub_conv (once_depth_conv conv))) tm

fun once_depth_fconv c fc f =
   try_fconv (fc orelsefc (sub_fconv c (once_depth_fconv c fc))) f

fun basic_once_fconv c fc = 
    once_depth_fconv (once_depth_conv c) 
                     (fc orelsefc basic_taut_fconv orelsefc refl_fconv)


fun basic_fconv c fc =
    top_depth_fconv (top_depth_conv c) 
                    (fc orelsefc basic_taut_fconv orelsefc refl_fconv)

fun conv_rule c th = dimp_mp_l2r th (c (concl th)) 




fun right_imp_forall_fconv f  = 
    let
        val (ant,conc) = dest_imp f
        val (ns,b) = dest_all conc
        val asm1 = assume f 
        val ath = assume ant 
        val mpth = mp asm1 ath
        val sth =  specl mpth [Var ns]
        val gth = sth |> disch ant |> allI ns 
        val asm2 = assume (concl gth)
        val sasm2 = allE asm2 (Var ns) 
        val mpsasm = mp sasm2 ath
        val gmpasm = allI ns mpsasm
        val dth' = disch ant gmpasm
    in dimpI (disch f gth)  (disch (concl gth) dth')
    end

fun sym_fconv f = 
    case f of 
    Pred("=",[t1,t2]) => dimpI (assume f|> sym |> disch_all) (assume (Pred("=",[t2,t1])) |> sym |> disch_all)
  | Conn("<=>", [f1,f2]) => dimpI (assume f|> iff_swap |> disch_all) (assume (Conn("<=>", [f2,f1]))|> iff_swap |> disch_all)
  | _ => raise ERR "not an iff or equality"


val GSYM = conv_rule (once_depth_fconv no_conv sym_fconv)

end
