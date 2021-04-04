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

fun rewr_conv th t = 
    let val (lhs,rhs) = dest_eq (strip_all (concl th))
        val env = match_term0 lhs t (Binarymap.mkDict String.compare)
    in thm(ant th, Pred("=",[t,inst_term env rhs]))
    end

