open term form logic drule

fun dest_imp_only f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("dest_imp_only.not a implication",[],[],[f])


fun eq_imp_rule th = (dimpl2r th,dimpr2l th)

datatype AI = imp of form | fa of {orig:string * sort, new:string * sort}

fun dest_forall f = 
    case f of
        Quant("!",n,s,b) => ((n,s),b)
      | _ => raise ERR ("dest_forall.not a forall",[],[],[f])

fun spec t = specl [t]

fun AIdestAll th =
    case total dest_forall (concl th) of
        NONE => NONE
      | SOME ((n,s),b) =>
        let
          val hfvs = fvfl (ant th)
        in
          if HOLset.member(hfvs, (n,s)) then
            let val new = dest_var (pvariantt hfvs (Var(n,s)))
            in
              SOME (fa{orig=(n,s),new=new}, spec (Var new) th)
            end
          else
            SOME (fa{orig=(n,s),new=(n,s)}, spec (Var(n,s)) th)
        end

(*!y.P(y)<=> !x.P(x)*)

fun all_rename x f = 
    case f of
        Quant("!",n,s,b) =>
        let 
            val l2r =  assume f |> allE (Var(x,s)) |> allI (x,s) |> disch_all
            val r2l =  assume (Quant("!",x,s,b)) |> allE (Var(n,s)) |> allI (n,s) |> disch_all
        in dimpI l2r r2l
        end
      | _ => raise ERR ("all_rename.not a forall",[],[],[f])

(*
fun exists_rename x f = 
    case f of
        Quant("?",n,s,b) =>
        let val l2r =  assume f |> existsE (Var(y,s)) |> allI (x,s) |> disch_all
            val r2l =  assume (Quant("!",x,s,b)) |> allE (Var(y,s)) |> allI (y,s) |> disch_all
        in dimpI l2r r2l
        end
      | _ => raise ERR ("all_rename.not a forall",[],[],[f])



fun gen_rename_fconv x 
*)

(*restore first deal with the AI list, once AI list is reduced empty, then add all assumptions in hs into the thm, but why this is a single function instead of just take acs and th as parameters, and then another function which adds all assumptions?*)

fun restore hs (acs, th) =
    case acs of
        [] => rev_itlist add_assum hs th
      | imp t :: rest => restore hs (rest, disch t th)
      | fa{orig,new} :: rest =>
        if orig = new then
          restore hs (rest, allI orig th)
        else
          restore hs (rest, th |> allI new |> conv_rule (all_rename (fst orig)))


(*what if the iff is in a subformula with conjunction?*)

fun underAIs f th =
    let
      fun getbase A th =
          case AIdestAll th of
              NONE => (case total dest_imp_only (concl th) of
                           NONE => (A, f th)
                         | SOME (l,r) => getbase (imp l :: A) (undisch th))
            | SOME (act,th') => getbase (act::A) th'
    in
      restore (ant th) (getbase [] th)
    end

val iffLR = underAIs (#1 o eq_imp_rule)
