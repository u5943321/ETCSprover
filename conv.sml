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

(*find the sort of a variable with name n in a name-sort list*)
(*
fun find_sort n nsl = 
    case nsl of [] => raise ERR "not found"
              | (n0,s) :: t => if n = n0 then s else find_sort n t
*)

fun abstl th l = 
    case l of 
        [] => th
      | (n,s) :: t => allI (n,s) (abstl th t)
         


fun part_tmatch partfn A t = 
    let val env = Binarymap.listItems (match_term0 (partfn A) t (Binarymap.mkDict (pair_compare String.compare sort_compare)))
        val A' = abstl A (List.map (fn (a,b) => a) env)
    in specl A' (List.map (fn (a,b) => b) env)
    end

val rewr_conv = part_tmatch (fst o dest_eq o concl)


fun part_fmatch partfn A f = 
    let val env = Binarymap.listItems (match_form (partfn A) f (Binarymap.mkDict (pair_compare String.compare sort_compare)))
        val A'= abstl A(List.map (fn (a,b) => a) env)
    in specl A' (List.map (fn (a,b) => b) env)
    end

val rewr_fconv = part_fmatch (fst o dest_iff o concl)



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


fun repeatc c t =
    ((c thenc (repeatc c)) orelsec all_conv) t


fun first_conv cl = 
    case cl of [] => all_conv
             | h :: t => h orelsec (first_conv t)

fun try_conv c = c orelsec all_conv

fun arg_conv c t = 
    case t of 
        Fun (f,s,l) => 
        (EQ_fsym f s (List.map (try_conv c) l))
      | _ => refl t
               
fun sub_conv c = first_conv [arg_conv c, all_conv]

val idR_conv = rewr_conv (spec_all idR)
val idL_conv = rewr_conv (spec_all idL)

val id_conv = idR_conv orelsec idL_conv

(*
((try_conv idR_conv) thenc (try_conv idL_conv))
*)

val o_conv = rewr_conv o_assoc

fun depth_conv c t = 
    ((try_conv (arg_conv (depth_conv c))) thenc (repeatc c)) t

fun redepth_conv c t =
    (try_conv (arg_conv (redepth_conv c)) thenc
              ((c thenc (redepth_conv c)) orelsec all_conv))
        t



(*
fun rewr_conv th t = 
    let val (lhs,rhs) = dest_eq (concl th)
        val env = match_term0 lhs t (Binarymap.mkDict String.compare)
    in thm(ant th, Pred("=",[t,inst_term env rhs]))
    end
*)



end
