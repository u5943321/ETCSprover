

fun strip_all_and_imp th = 
    if is_forall (concl th) then 
        strip_all_and_imp (spec_all th)
    else if is_imp (concl th) then 
        strip_all_and_imp (undisch th)
(*before the undisch, check two cases:
1.conjunction -> strip
2.existential -> pull extential quantifier out
otherwise just undisch, keep the disjs*)
    else th



(*
TODO: use conv to do this canon


1.A /\ B
2. C /\ D
--------
phi

A
B
C
D
------
phi

A /\ B /\ C /\ D ==> phi


*)

fun mp_canon th = 
    let val th0 = strip_all_and_imp th 
        val th1 = conj_all_assum th0
    in th1 |> disch_all |> gen_all
    end

fun imp_folk_fconv (fc1,fc2) f = 
    case view_form f of
        vConn("==>",[p,q]) => 
        imp_iff (fc1 p) (fc2 q)
      | _ => raise simple_fail "imp_fconv_fconv.not an implication"

fun conj_rand_fconv fc f = 
    case f of 
        Conn("&",[f1,f2]) =>
            conj_iff (all_fconv f1) (fc f2)
      | _ => raise simple_fail "conj_rand_fconv.not a conjunction"

val T_and = T_conj_1
val F_and = F_conj_1
val and_F = F_conj_2
val and_T = T_conj_2

fun conj_land_fconv fc f = 
    case f of 
        Conn("&",[f1,f2]) =>
            conj_iff (try_fconv fc f1) (all_fconv f2)
      | _ => raise simple_fail "conj_rand_fconv.not a conjunction"


fun every_conj_fconv fc f =
  (if is_conj f
      then conj_land_fconv (every_conj_fconv fc) thenfc
           (rewr_fconv F_and orelsefc
              (rewr_fconv T_and thenfc every_conj_fconv fc) orelsefc
                 (conj_rand_fconv (every_conj_fconv fc) thenfc
                  try_fconv (rewr_fconv and_F orelsefc rewr_fconv and_T)))
   else fc) f

fun list2HOLset ord l = List.foldr (uncurry (C (curry HOLset.add)))
                                   (HOLset.empty ord) l

fun ssl2sss l = list2HOLset (pair_compare String.compare sort_compare) l

fun pvariantt' l v = 
    let val s = list2HOLset (pair_compare String.compare sort_compare) l
    in pvariantt s v
    end
 
fun recurse avds acc th =
      case Lib.total dest_all (concl th) of
          SOME (v,bod) =>
          let
            val v' = pvariantt' avds (Var v)
          in
            recurse ((dest_var v')::avds) ((dest_var v')::acc) (spec v' th)
          end
        | NONE => (List.rev acc, th)

fun avspec_all avds th =  recurse avds [] th
 


fun part_fmatch' f th fm =
  let
    val (_, vs) = strip_all (concl th)
    val hypfvs_set = fvfl (ant th)
    val hypfvs = HOLset.listItems hypfvs_set
    val ffvs = fvf fm
    val dontspec = HOLset.union(ffvs,hypfvs_set)
    val (vs, speccedth) = avspec_all (HOLset.listItems dontspec) th
    val fvd =
        match_form (fvfl (ant th)) (f (concl speccedth)) fm mempty
    val dontgen =
                HOLset.union(dontspec,
                             ssl2sss (List.map fst (Binarymap.listItems (vd_of fvd))))
    val vs = 
        HOLset.difference (mk_sss (List.map (fvt o (inst_term fvd) o Var) vs), 
                           dontgen)
    val vl = List.map (find_var (HOLset.listItems vs)) (order_of vs)
(*op_union aconv (map #redex tmsig) dontspec*)
  in
    genl vl (inst_thm fvd speccedth)
  end

val Timp = T_imp_1
val impF = F_imp_2

fun rth_eqT rth = eqT_intro rth
fun rth_eq rth = eqF_intro rth handle _ => rth_eqT rth
val notT = 
    let val l2r = assume (mk_neg TRUE) |> negE (trueI []) |> disch_all
        val r2l = falseE [FALSE] (mk_neg TRUE) |> disch_all
    in dimpI l2r r2l
    end

fun strip_forall_fconv fc = 
    top_depth_fconv no_conv (changed_fconv (forall_fconv fc))

fun mp_procedure th0 rth = 
conv_rule (strip_forall_fconv 
               (imp_folk_fconv (every_conj_fconv $ try_fconv $ rewr_fconv (rth_eqT rth),rewr_fconv (rth_eq rth) orelsefc 
               try_fconv (conj_rand_fconv (rewr_fconv (rth_eq rth)) thenfc
                                          rewr_fconv notT)) thenfc
                               try_fconv (rewr_fconv Timp)))


val ith = (*mp_canon*) (gen_all ith0)


fun conj f t = t |> dest_imp |> #1 |> strip_conj |> f


fun strip dest A [] = rev A
        | strip dest A (h :: t) =
            case dest h of
               NONE => strip dest (h :: A) t
             | SOME (c1, c2) => strip dest A (c1 :: c2 :: t)

fun strip_binop_opt dest = strip dest [] o Lib.list_of_singleton
   
fun strip_binop dest = strip_binop_opt (total dest);

val strip_conj = strip_binop dest_conj

fun conj f f0 = f0 |> dest_imp |> #1 |> strip_conj |> f

fun max ith = ith |> concl |> strip_all |> #1 |> conj length

fun t rth = concl rth
