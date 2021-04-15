structure conv :> conv = 
struct
open term form thm 
type conv = term -> thm

exception unchanged

fun specl th l = 
    if is_all (concl th) then 
        (case l of [] => th
                 | h :: t => 
                   let val f1 = allE th h handle ERR _ => th
                   in 
                       specl f1 t
                   end)
    else th (*raise ERR "conclusion not universally quantified"*)



fun spec_all th = 
    let val fv = fvfl (ant th)
        val v2bs = snd (strip_ALL (concl th))
        val v2bs' = List.map (pvariantt fv) (List.map Var v2bs)
    in 
        specl th (rev v2bs')
    end

fun abstl th l = 
    case l of 
        [] => th
      | (n,s) :: t => allI (n,s) (abstl th t)
         


fun part_tmatch partfn A t = 
    let 
        val env = 
            Binarymap.listItems
                (vd_of (match_term (partfn A) t mempty))
        val A' = abstl A (List.map (fn (a,b) => a) env)
    in specl A' (List.map (fn (a,b) => b) env)
    end

val rewr_conv = part_tmatch (fst o dest_eq o concl)


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
        (EQ_fsym f s (List.map (try_conv c) l))
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

fun part_fmatch partfn A f = 
    let 
        val fvd = (match_form (partfn A) f mempty)
        val vd = Binarymap.listItems 
                     (vd_of (match_form (partfn A) f mempty))
        val A0 = inst A fvd
        val A' = abstl A0 (List.map (fn (a,b) => a) vd)
    in specl A' (List.map (fn (a,b) => b) vd)
    end

val rewr_fconv = part_fmatch (fst o dest_iff o concl)

(*operation on fconvs*)

infix thenfc

fun thenfc (fc1,fc2) f = 
    let 
        val th1 = fc1 f 
    in 
        iff_trans th1 (fc2 (snd (dest_iff (concl th1))))
    end


fun all_fconv f = frefl f

infix orelsefc;

fun orelsefc (fc1,fc2) f = fc1 f handle _ => fc2 f

fun no_fconv f = raise ERR "no_fconv"

fun first_fconv fcl = 
    case fcl of [] => no_fconv
             | h :: t => h orelsefc (first_fconv t)

fun try_fconv fc = fc orelsefc all_fconv

fun changed_fconv fc f = 
    if fc f =  frefl f then raise unchanged 
    else fc f

fun repeatfc fc f = 
    ((fc thenfc (repeatfc fc)) orelsefc all_fconv) f

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

fun qall_fconv fc f = 
    case f of 
        Quant("ALL",n,s,b) => 
        all_iff (try_fconv fc b) (n,s)
      | _ => raise ERR "not a forall"

fun qexists_fconv fc f = 
    case f of 
        Quant("EXISTS",n,s,b) => 
        exists_iff (try_fconv fc b) (n,s)
      | _ => raise ERR "not an exists"

fun sub_fconv c fc = 
    first_fconv (List.map changed_fconv
                [conj_fconv fc,
                 disj_fconv fc,
                 imp_fconv fc,
                 dimp_fconv fc,
                 qall_fconv fc,
                 qexists_fconv fc,
                 pred_fconv c])


val reflTob = equivT (refl (Var("a",ob)))

val reflTar = equivT (refl (Var("a",ar(Var("A",ob),Var("B",ob)))))

val refl_fconv = 
    first_fconv [rewr_fconv reflTob,rewr_fconv reflTar]
     

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


    
(*               
fun tautT_fconv f = 
    case f of
        Conn("|",[c1,c2]) =>
        if c2 = mk_neg c1 then tautT f 
        else if c1 = mk_neg c2 then disj

 orelse c2 = mk_neg c1 then
*)
(*fun taut_disj_fconv f = *)

(*above wrong should all be matching*)

val basic_taut_fconv = 
    first_fconv [taut_conj_fconv,
                 taut_disj_fconv,
                 taut_imp_fconv,
                 taut_dimp_fconv,
                 taut_forall_fconv]



fun top_depth_fconv c fc f =
    (repeatfc fc thenfc
             (try_fconv (sub_fconv (top_depth_conv c) fc)) thenfc
             ((fc thenfc (top_depth_fconv c fc)) 
                  orelsefc all_fconv))
        f


fun basic_fconv c fc =
    top_depth_fconv (top_depth_conv c) 
                    (fc orelsefc basic_taut_fconv)

val oc = rewr_conv o_assoc

val roc = redepth_conv oc

val ttest = #1  (read_t "f o (g o h) o k")

val ftest = #1 (read_f "id(A) = id(A) & f o (g o h) o k = ((f o g) o h) o k")

val ftest' =  #1 (read_f "f o (g o h) o k = ((f o g) o h) o k")

val fc = conj_conv (pred_conv roc)

val rth = refl (#1 (read_t "a: A -> B"))

val rtht = equivT rth

val refl_fconv = rewr_fconv rtht 

val readf = fst o read_f

(*

fun imp_chain_tac tac (fl,f) = 
    case f of 
        Conn("==>",[A,B]) => 
        if tac (fl,A) = (_,TRUE) then
            let val (B',func) = imp_chain_tac tac (fl,B)
            in
            ((fl,B'),
             fn [th] => dimp_mp_r2l (T_imp1 (concl th)) th)
            end
*)
(*currently wrong *)


(*
fun rewr_conv th t = 
    let val (lhs,rhs) = dest_eq (concl th)
        val env = match_term0 lhs t (Binarymap.mkDict String.compare)
    in thm(ant th, Pred("=",[t,inst_term env rhs]))
    end
*)

fun assum_list aslfun (g as (asl, _)) = aslfun (map assume asl) g




end
