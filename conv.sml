structure conv :> conv = 
struct
open term form thm 

exception unchanged

fun all_conv t = raise unchanged

infix thenc

fun thenc (c1,c2) t = 
    let 
        val th1 = c1 t 
    in 
        trans th1 (c2 (snd (dest_eq (concl th1))))
    end


infix orelsec

fun orelsec (c1,c2) t = 
    c1 t handle ERR _ => c2 t


fun repeatc c t =
    ((c thenc (repeatc c)) orelsec all_conv) t


fun first_conv cl = 
    case cl of [] => all_conv
             | h :: t => orelsec h (first_conv t)

fun sub_conv c t = 
    case t of 
        Fun (f,s,l) => EQ_fsym f s (List.map c l)
      | _ => c t

fun depth_conv c t = 
    ((sub_conv (depth_conv c)) thenc (repeatc c)) t

(*
fun rewr_conv th t = 
    let val (lhs,rhs) = dest_eq (concl th)
        val env = match_term0 lhs t (Binarymap.mkDict String.compare)
    in thm(ant th, Pred("=",[t,inst_term env rhs]))
    end
*)


fun specl th l = 
    if is_all (concl th) then 
        (case l of [] => th
                 | h :: t => allE (specl th t) h)
    else raise ERR "conclusion not universally quantified"



fun spec_all th = 
    let val fv = fvfl (ant th)
        val v2bs = snd (strip_ALL (concl th))
        val v2bs' = List.map (pvariantt fv) (List.map Var v2bs)
    in 
        specl th (rev v2bs')
    end

(*find the sort of a variable with name n in a name-sort list*)

fun find_sort n nsl = 
    case nsl of [] => raise ERR "not found"
              | (n0,s) :: t => if n = n0 then s else find_sort n t


fun abstl th l = 
    case l of 
        [] => th
      | n :: t => 
        (let val fv = fvf (concl th)
             val s = find_sort n fv
         in
             allI (n,s) (abstl th t)
         end)



fun dict2l dict = Binarymap.foldl (fn (k:string,v:term,A) => (k,v) :: A) [] dict



fun part_tmatch partfn A t = 
    let val env = dict2l (match_term0 (partfn A) t (Binarymap.mkDict String.compare))
        val A' = abstl A (List.map (fn (a,b) => a) env)
    in specl A' (List.map (fn (a,b) => b) env)
    end

val rewr_conv = part_tmatch (snd o dest_eq o concl o spec_all)


end
