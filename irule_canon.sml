open term form logic drule


fun aimp_rule th =
    let
      val (l, r) = dest_imp (concl th)
      val (c1, c2) = dest_conj l
      val cth = conjI (assume c1) (assume c2)
    in
      disch c1 (disch c2 (mp th cth))
    end

fun (s1 - s2) = HOLset.difference(s1,s2)

fun is_forall f = 
    case f of 
        Quant(q,_,_,_) => if q = "!" then true else false
      | _ => false

fun dest_imp_only f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("dest_imp_only.not a implication",[],[],[f])

fun norm th =
    if is_forall (concl th) then norm (spec_all th)
    else
      case Lib.total dest_imp_only (concl th) of
          NONE => th
        | SOME (l,r) =>
          if is_conj l then norm (aimp_rule th)
          else norm (undisch th)

fun overlaps fvset (tfvs,_) =
      not (HOLset.isEmpty (HOLset.intersection(fvset, tfvs)))

fun union ((fvset1, tlist1), (fvset2, tlist2)) =
      (HOLset.union(fvset1, fvset2), tlist1 @ tlist2)

fun recurse gfvs acc tlist =
      case tlist of
          [] => acc
        | t::ts =>
          let
            val tfvs = (fvf t) - gfvs
          in
            case List.partition (overlaps tfvs) acc of
                ([], _) => recurse gfvs ((tfvs,[t])::acc) ts
              | (ovlaps, rest) =>
                recurse gfvs (List.foldl union (tfvs, [t]) ovlaps :: rest) ts
          end

fun group_hyps gfvs tlist = recurse gfvs [] tlist

fun foldthis ((n,s),(t,th)) =
      let val ext = mk_exists n s t
      in
        (ext, existsE (n,s) (assume ext) th)
      end

fun choosel vs t th = List.foldr foldthis (t,th) vs


val conjuncts =
   let
      fun aux acc th =
         aux (aux acc (conjE2 th)) (conjE1 th)
         handle _ => th :: acc
   in
      aux []
   end

(*to get consistent order, foldl, or rev and take hd and tl, then foldr
current gives 
 ["P(a)","P(b)","P(c)"] |-> P(c) & (P(b) & P(a))
*)
fun list_mk_conj fl = List.foldl (uncurry mk_conj) (List.hd fl) (List.tl fl)



fun conjl ts th = let
  val c = list_mk_conj ts
  val cths = conjuncts (assume c)
in
  (List.foldl (fn (c,th) => prove_hyp c th) th cths, c)
end

fun recurse acc groups th =
      case groups of
          [] => (acc, th)
        | (fvset, ts) :: rest =>
          let
            val (th1,c) = conjl ts th
            val (ext, th2) = choosel (HOLset.listItems fvset) c th1
          in
            recurse (ext::acc) rest th2
          end



fun recurse acc groups th =
      case groups of
          [] => (acc, th)
        | (fvset, ts) :: rest =>
          let
            val (th1,c) = conjl ts th
            val (ext, th2) = choosel (HOLset.listItems fvset) c th1
          in
            recurse (ext::acc) rest th2
          end

fun reconstitute groups th = recurse [] groups th

fun form_list_diff l1 l2 = 
    case l1 of 
        [] => []
      | h :: t => if fmem h l2 then list_diff t l2 else h :: list_diff t l2


fun irule_canon th =
  let
    val th1 = norm (gen_all th)
    val origl = ant th
    val gfvs = fvfl (concl th1 :: origl) 
    val newhyps = form_list_diff (ant th1)  origl
    val grouped = group_hyps gfvs newhyps
    val (cs, th2) = reconstitute grouped th1
  in
    case cs of
        [] => gen_all th2
      | _ =>
        let
          val (th3,c) = conjl cs th2
        in
          disch c th3 |> gen_all
        end
  end

