structure pterm :> pterm = 
struct
open token pterm_dtype form

structure Env = 
struct
open Binarymap List
type env = (string,pterm)Binarymap.dict * (string,psort)Binarymap.dict * (string,psort)Binarymap.dict * int

val empty : env = (Binarymap.mkDict String.compare, Binarymap.mkDict String.compare,Binarymap.mkDict String.compare,0)

fun insert_ps n s ((dpt,dps,dv,i):env):env = (dpt,insert (dps,n,s),dv,i)
    
fun insert_pt n t ((dpt,dps,dv,i):env):env = (insert (dpt,n,t),dps,dv,i)

fun dps_of ((dpt,dps,dv,i):env) = dps

fun dpt_of ((dpt,dps,dv,i):env) = dpt

fun dv_of ((dpt,dps,dv,i):env) = dv

fun var_of ((dpt,dps,dv,i):env) = i

fun fresh_var ((td,sd,dv,i):env):string * env = (" " ^ Int.toString i,(td,sd,dv, i + 1))

fun lookup_pt ((dpt,_,_,_):env) n = peek (dpt,n)

fun lookup_ps ((_,dps,_,_):env) n = peek (dps,n)

fun ps_of ((_,_,dv,_):env) n:psort option = peek (dv,n)

fun record_ps n s ((dpt,dps,dv,i):env):env = (dpt,dps,insert (dv,n,s),i)

fun clear_ps n ((dpt,dps,dv,i):env):env = 
    case ps_of (dpt,dps,dv,i) n of
        SOME ps => 
        let val (dv1,_) = remove(dv, n) in (dpt,dps,dv1,i) end
      | NONE => (dpt,dps,dv,i)

fun clear_psn n ((dpt,dps,dv,i):env):env = 
    case lookup_ps (dpt,dps,dv,i) n of 
        SOME ps => 
        let val (dps1,_) = remove(dps, n) in (dpt,dps1,dv,i) end
      | NONE => (dpt,dps,dv,i)
end

open Binarymap List Env


fun conc_list sep [] = ""
  | conc_list sep (b::bs) = (sep ^ b) ^ (conc_list sep bs);

fun conc_list1 sep [] = " "
  | conc_list1 sep (b::bs) = b ^ (conc_list sep bs);

fun stringof_pt pt = 
    case pt of 
        pVar (name,ps) => "pv" ^ " " ^ name ^ " : " ^ stringof_ps ps
      | ptUVar a => "ptu" ^ " " ^ a
      | pFun (f,ps,l) => f ^ " " ^ (stringof_ps ps) ^ stringof_args l 
      | pAnno (pt,ps) => enclose (stringof_pt pt ^ "," ^ stringof_ps ps)
and stringof_args [] = ""
  | stringof_args ts = enclose (conc_list1 "," (map stringof_pt ts))
and stringof_ps ps = 
    case ps of
        psvar name => "psv" ^ " " ^ name 
      | pob => "pob"
      | par (pt1,pt2) => stringof_pt pt1 ^ "-->" ^ stringof_pt pt2 


fun psdict (dict:(string,psort) dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_ps v ^ ")") :: A) [] dict


fun ptdict (dict:(string,pterm) dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_pt v ^ ")") :: A) [] dict


fun pdv (dict:(string,psort) dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_ps v ^ ")") :: A) [] dict


fun pdict env = (ptdict (dpt_of env),psdict (dps_of env),pdv (dv_of env),
                var_of env)

fun occs_ps psname env ps = 
    case ps of
        pob => false 
      | par (pt1,pt2) => occs_pt psname env pt1 
                         orelse occs_pt psname env pt2
      | psvar s => psname = s orelse 
                   (case lookup_ps env s of 
                        SOME ps' => occs_ps psname env ps'
                      | NONE => false)                       
and occs_pt ptname env pt = 
    case pt of 
        ptUVar n => (case lookup_pt env n of 
                         SOME pt' => occs_pt ptname env pt'
                       | NONE => false)
      | pAnno (pt,ps) => occs_pt ptname env pt orelse  
                         occs_ps ptname env ps
      | pVar (n,ps) => occs_ps ptname env ps
      | pFun (f,ps,l) => exists (occs_pt ptname env) l orelse
                         occs_ps ptname env ps  

exception UNIFY of string

fun chasevart pt env = 
    case pt of 
        ptUVar s => (case lookup_pt env s of
                         SOME pt' =>  chasevart pt' env
                       | NONE => pt)
      | _ => pt 
    

fun chasevars ps env = 
    case ps of 
        psvar s => (case lookup_ps env s of
                         SOME ps' =>  chasevars ps' env
                       | NONE => ps)
      | _ => ps

fun unify_ps env (ps1:psort) (ps2:psort):env = 
    case (chasevars ps1 env,chasevars ps2 env) of
        (psvar n1,psvar n2) => 
        if n1 = n2 then env else insert_ps n1 (psvar n2) env
      | (psvar n,ps) =>
        if occs_ps n env ps 
        then raise UNIFY 
                   ("occurs check(ps):" ^ stringof_ps (psvar n) ^ " " ^
                   stringof_ps ps)
        else insert_ps n ps env
      | (ps,psvar n) => 
        if occs_ps n env ps 
        then raise UNIFY  
                   ("occurs check(ps):" ^ stringof_ps (psvar n) ^ " " ^
                   stringof_ps ps)
        else insert_ps n ps env
      | (par (dom1,cod1),par (dom2,cod2)) => 
        let val env1 = unify_pt env dom1 dom2
        in unify_pt env1 cod1 cod2
        end
      | (pob,pob) => env
      | _ => raise (UNIFY "sort cannot be unified")
and unify_pt env pt1 pt2: env= 
    case (chasevart pt1 env,chasevart pt2 env) of 
        (ptUVar a,ptUVar b) => 
        if a = b then env else insert_pt a (ptUVar b) env
      | (ptUVar a, t) => 
        if occs_pt a env t 
        then raise UNIFY ("occurs check(pt):" ^
             stringof_pt (ptUVar a) ^ " " ^ stringof_pt t)
        else insert_pt a t env
      | (t, ptUVar a) => 
        if occs_pt a env t 
        then raise UNIFY ("occurs check(pt):" ^
             stringof_pt t ^ " " ^ stringof_pt (ptUVar a))
        else insert_pt a t env
      | (pVar (a1,ps1), pVar (a2,ps2)) => 
        if a1 = a2 then unify_ps env ps1 ps2
        else raise (UNIFY "different variable name")
      | (pFun(f,ps1,l1),pFun(g,ps2,l2)) => 
        if f = g andalso length l1 = length l2 
        then (let val env = unify_ps env ps1 ps2 in
                  case (l1,l2) of 
                  ([],[]) => env 
                | (h1::r1,h2::r2) => 
                  let val env1 = unify_pt env h1 h2
                  in unify_pt env1 (pFun(f,ps1,r1)) (pFun(g,ps2,r2))
                  end
                | _ => raise UNIFY "term list cannot be unified"
              end)
        else raise (UNIFY "different functions")
      | (pAnno(pt,ps),t) => unify_pt env pt t
      | (t,pAnno(pt,ps)) => unify_pt env pt t
      | _ => raise (UNIFY "terms cannot be unified")

fun ps_of_pt pt =
    case pt of 
        ptUVar n => pob
      | pVar (n,ps) => ps
      | pFun (n,ps,l) => ps
      | pAnno(pt,ps) => ps

fun type_infer env t ty = 
    case t of 
        pFun("o",ps,[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val (Cv,env4) = fresh_var env3
            val env5 = type_infer env4 g (par (ptUVar Bv, ptUVar Cv))
            val env6 = unify_ps env5 ty (par(ptUVar Av, ptUVar Cv))
        in
            unify_ps env6 ps ty
        end
      | pFun ("N",ps,[]) =>
        unify_ps (unify_ps env ps ty) ty pob
      | pFun ("s",ps,[]) => 
        unify_ps (unify_ps env ps ty) 
                 ty (par (pFun("N",pob,[]),pFun("N",pob,[]))) 
      | pFun ("z",ps,[]) => 
        unify_ps (unify_ps env ps ty) 
                 ty (par (pFun("1",pob,[]),pFun("N",pob,[])))
      | pFun ("N_ind",ps,[x0,t]) => 
        let val (Av,env1) = fresh_var env
            val env2 = type_infer env1 x0 (par (pFun("1",pob,[]),ptUVar Av))
            val env3 = type_infer env2 t (par (ptUVar Av,ptUVar Av))
            val env4 = unify_ps env3 ps ty
        in 
            unify_ps env4 ty (par (pFun("N",pob,[]),ptUVar Av))
        end
      | pFun ("1",ps,[]) => 
        unify_ps (unify_ps env ps ty) ty pob
      | pFun ("0",ps,[]) => 
        unify_ps (unify_ps env ps ty) ty pob
      | pFun ("to1",ps,[X]) => 
        let val env1 = type_infer env X pob
            val env2 = unify_ps env1 ty (par (X,pFun ("1",pob,[])))
        in 
            unify_ps env2 ps ty
        end
      | pFun ("from0",ps,[X]) => 
        let val env1 = type_infer env X pob
            val env2 = unify_ps env1 ty (par (pFun ("1",pob,[]),X))
        in 
            unify_ps env2 ps ty
        end
      | pFun ("po",ps,[A,B]) =>
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env2 ty pob
        in 
            unify_ps env3 ps ty
        end
      | pFun ("copo",ps,[A,B]) =>
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env2 ty pob
        in 
            unify_ps env2 ps ty
        end
      | pFun ("p1",ps,[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env2 ty (par(pFun("po",pob,[A,B]), A))
        in
            unify_ps env3 ps ty
        end
      | pFun ("i1",ps,[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env2 ty (par(A,pFun("copo",pob,[A,B])))
        in
            unify_ps env3 ps ty
        end
      | pFun ("p2",ps,[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env2 ty (par(pFun("po",pob,[A,B]), B))
        in
            unify_ps env3 ps ty
        end
      | pFun ("i2",ps,[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env2 ty (par(B,pFun("copo",pob,[A,B])))
        in
            unify_ps env3 ps ty
        end
      | pFun ("pa",ps,[f,g]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val (Xv,env3) = fresh_var env2
            val env4 = type_infer env3 f (par (ptUVar Xv, ptUVar Av))
            val env5 = type_infer env4 g (par (ptUVar Xv, ptUVar Bv))
            val env6 = unify_ps env ty (par (ptUVar Xv, 
                                  pFun ("po",pob,[ptUVar Av,ptUVar Bv])))
        in
            unify_ps env6 ps ty
        end
      | pFun ("copa",ps,[f,g]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val (Xv,env3) = fresh_var env2
            val env4 = type_infer env3 f (par (ptUVar Av, ptUVar Xv))
            val env5 = type_infer env4 g (par (ptUVar Bv, ptUVar Xv))
            val env6 = unify_ps env ty
                       (par (pFun ("copo",pob,[ptUVar Av,ptUVar Bv]),
                             ptUVar Xv))
        in
            unify_ps env6 ps ty
        end
      | pFun ("eqo",ps,[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val env5 = unify_ps env4 ty pob
        in
            unify_ps env5 ps ty
        end
      | pFun ("coeqo",ps,[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val env5 = unify_ps env4 ty pob
        in
            unify_ps env5 ps ty
        end
      | pFun ("eqa",ps,[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val env5 = unify_ps env4 ty (par (pFun ("coeqo",pob,[f,g]),
                                              ptUVar Av))
        in
            unify_ps env5 ps ty
        end
      | pFun ("coeqa",ps,[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val env5 = unify_ps env4 ty (par (ptUVar Bv,pFun ("coeqo",pob,[f,g])))
        in
            unify_ps env5 ps ty
        end
      | pFun ("eq_induce",ps,[f,g,h]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val (Xv,env4) = fresh_var env4
            val env5 = type_infer env4 h (par (ptUVar Xv, ptUVar Av))
            val env6 = unify_ps env5 ty (par(ptUVar Xv, pFun ("eqo",pob,[f,g])))
        in
           unify_ps env6 ps ty
        end
      | pFun ("coeq_induce",ps,[f,g,h]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val (Xv,env4) = fresh_var env4
            val env5 = type_infer env4 h (par (ptUVar Bv, ptUVar Xv))
            val env6 = unify_ps env5 ty (par(pFun ("coeqo",pob,[f,g]),ptUVar Xv))
        in
            unify_ps env6 ps ty
        end
      | pFun ("exp",ps,[A,B]) =>  
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env2 ty pob
        in 
           unify_ps env3 ps ty
        end
      | pFun ("tp",ps,[f]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val (Cv,env3) = fresh_var env2
            val env4 = type_infer env2 f 
                                  (par (pFun("po",pob,[ptUVar Av,ptUVar Bv]),
                                       ptUVar Cv))
            val env5 = unify_ps env4 ty 
                  (par(ptUVar Bv, pFun ("exp",pob,[ptUVar Av,ptUVar Cv])))
        in unify_ps env5 ps ty 
        end 
      | pFun ("ev",ps,[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
            val env3 = unify_ps env ty 
                                (par (pFun("po",pob,[B,pFun("exp",pob,[A,B])]),A))
        in
            unify_ps env3 ps ty
        end
      | pFun("id",ps,[A]) => 
        let val env1 = type_infer env A pob
        in unify_ps (unify_ps env1 ps ty) ty (par (A,A))
        end
      | pAnno (pt,ps) => 
        let val env1 = type_infer env pt ps
            val env2 = type_infer env1 pt (ps_of_pt pt)
        in unify_ps env2 ty ps
        end
      | pVar (name,ps) => unify_ps env ty ps 
      | ptUVar name => unify_ps env ty pob
      | _ => env 


fun env_from_ptl env ptl = 
    case ptl of 
        [] => env
      | h::t => 
        let val env1 = type_infer env h (ps_of_pt h)
        in env_from_ptl env1 t
        end
 
fun type_infer_pf env pf = 
    case pf of 
        pQuant(q,n,ps,pb) => type_infer_pf env pb
      | pConn(co,pfl) => 
        (case pfl of 
             [] => env
           | h::t => let val env1 = type_infer_pf env h
                     in type_infer_pf env1 (pConn(co,t))
                     end)
      | pPred("ismono",[f]) => 
        let val env1 = type_infer env f (ps_of_pt f)
            val (Av,env2) = fresh_var env1
            val (Bv,env3) = fresh_var env2
        in unify_ps env3 (ps_of_pt f) (par (ptUVar Av,ptUVar Bv))
        end
      | pPred("=",[pt1,pt2]) => 
        let val env1 = type_infer env pt1 (ps_of_pt pt1)
            val env2 = type_infer env1 pt2 (ps_of_pt pt2)
        in unify_ps env2 (ps_of_pt pt1) (ps_of_pt pt2)
        end
      | pPred(_,ptl) => env_from_ptl env ptl

fun apfst f (x,tl,env) = (f x, tl,env);

fun cons x xs = x::xs;

fun parse_repeat (a,parsefn) tl env = 
    case tl of 
        (Key(b)::tl1) => if b = a then 
                             parse_repeat1 (a,parsefn) tl1 env
                         else ([],tl,env)
      | _ => ([],tl,env)
and parse_repeat1 (a,parsefn) tl env =
    let val (u,tl1,env1) = parsefn tl env
    in apfst (cons u) (parse_repeat (a,parsefn) tl1 env1)
    end

exception ERROR of string

fun rightparen (x, Key")"::toks,env) = (x, toks,env)
  | rightparen _ = raise ERROR "Symbol ) expected";

(*
fun parse_until (al,parsefn) tl env = 
    case tl of 
        (Key(b)::tl1) => if mem b al then 
                             parse_until1 (al,parsefn) tl1 env
                         else ([],tl,env)
      | _ => ([],tl,env)
and parse_until1 (al,parsefn) tl env =
    let val (u,tl1,env1) = parsefn tl env
    in (parse_until (al,parsefn) tl1 env1)
    end
*)

(*really parse pob/par because they are actually doing type-infer. ?*)

(*type inference during parsing : 
from f: A -> B, know that f is an arrow and A and B are objects

use pAnno for this type-infer?
*)

fun fprec_of "*" = 2
  | fprec_of "+" = 1
  | fprec_of _ = ~1 


fun mk_pt_conn env co s1 s2 =
    let val (n,env) = fresh_var env in 
        pFun (co,psvar n,[s1,s2])
    end


fun parse_pt tl env = parse_pt_fix 0 (parse_pt_atom tl env)
and parse_pt_atom tl env = 
    case tl of
        (Id(a)::tl1) => 
        (case tl1 of
             (Key":"::tl2) =>      
             (case (ps_of env a) of 
                  SOME ps => let val (pas,tl3,env1) = parse_par tl2 env
                             in (pAnno (pVar(a,ps),pas),tl3,env1)
                             end
                | NONE => let val (n,env1) = fresh_var env
                              val (ps,tl3,env2) = parse_par tl2 env1
                              val env3 = record_ps a (psvar n) env2
                          in (pAnno (pVar(a,psvar n),ps),tl3,env3)
                          end)
           | (Key"("::tl2) => 
             let val (ptl,tl3,env1) = 
                     rightparen (parse_repeat1 (",",parse_pt_atom) tl2 env)
             in (case tl3 of 
                     (Key":"::tl4) => 
                     (let val (ps,tl5,env2) = parse_par tl4 env1
                          val (n,env3) = fresh_var env2
                      in (pAnno(pFun(a,psvar n,ptl),ps),tl5,env3)
                             (*pAnno or pVar with ps?*)
                      end)
                   | _ =>
                     let val (n,env2) = fresh_var env1
                     in (pFun(a,psvar n,ptl),tl3,env2)
                     end)
             end
           | _ => 
             (case (ps_of env a) of 
                  SOME ps => (pVar (a,ps),tl1,env)
                | NONE => let val (n,env1) = fresh_var env
                              val env2 = record_ps a (psvar n) env1
                          in (pVar (a,psvar n),tl1,env2)
                          end))
      | [] => raise ERROR "Syntax of preterm: unexpected end of file"
      | t::_ => raise ERROR ("Syntax of preterm: " ^ tokentoString t) 
and parse_pt_fix prec (pt,tl,env) = 
    case tl of
        Key(co)::tl => 
        if fprec_of co < prec then (pt, Key(co)::tl,env)
        else
            let val (pt1,tl1,env1) = parse_pt_atom tl env
                val (pt2,tl2,env2) = parse_pt_fix (fprec_of co) (pt1,tl1,env1)
            in parse_pt_fix prec (mk_pt_conn env co pt pt2,tl2,env2)
            end
      | _ => (pt,tl,env)
and parse_par tl env = 
    (case (parse_pob tl env) of 
         (A,Key"->"::tl1,env1) => 
         apfst (fn B => par(A,B)) (parse_pob tl1 env1)
       | _ => raise ERROR "Expected arrow")  
and parse_pob tl env = 
    let val (pt,tl1,env1) = parse_pt tl env
    in (pAnno (pt,pob),tl1,env1)
    end
(*
fun parse_pt tl env = 
    case tl of
        (Id(a)::tl1) => 
        (case tl1 of
             (Key":"::tl2) =>      
             (case (ps_of env a) of 
                 SOME ps => let val (pas,tl3,env1) = parse_par tl2 env
                            in (pAnno (pVar(a,ps),pas),tl3,env1)
                            end
               | NONE => let val (n,env1) = fresh_var env
                             val (ps,tl3,env2) = parse_par tl2 env1
                             val env3 = record_ps a (psvar n) env2
                         in (pAnno (pVar(a,psvar n),ps),tl3,env3)
                         end)
           | (Key"("::tl2) => 
             let val (ptl,tl3,env1) = 
                     rightparen (parse_repeat1 (",",parse_pt) tl2 env)
             in (case tl3 of 
                     (Key":"::tl4) => 
                     (let val (ps,tl5,env2) = parse_par tl4 env1
                          val (n,env3) = fresh_var env2
                      in (pAnno(pFun(a,psvar n,ptl),ps),tl5,env3)
                             (*pAnno or pVar with ps?*)
                      end)
                   | _ =>
                     let val (n,env2) = fresh_var env1
                     in (pFun(a,psvar n,ptl),tl3,env2)
                     end)
             end
           | _ => 
             (case (ps_of env a) of 
                  SOME ps => (pVar (a,ps),tl1,env)
                | NONE => let val (n,env1) = fresh_var env
                              val env2 = record_ps a (psvar n) env1
                          in (pVar (a,psvar n),tl1,env2)
                          end))
      | [] => raise ERROR "Syntax of preterm: unexpected end of file"
      | t::_ => raise ERROR ("Syntax of preterm: " ^ tokentoString t) 
and parse_par tl env = 
    (case (parse_pob tl env) of 
         (A,Key"->"::tl1,env1) => 
         apfst (fn B => par(A,B)) (parse_pob tl1 env1)
       | _ => raise ERROR "Expected arrow")  
and parse_pob tl env = 
    let val (pt,tl1,env1) = parse_pt tl env
    in (pAnno (pt,pob),tl1,env1)
    end
*)
 
fun mk_quant q n ps pf = pQuant (q,n,ps,pf)

fun mk_pConn co pf1 pf2 = pConn(co,[pf1,pf2])

fun mk_neg pf = pConn("~",[pf])

fun mk_pPred P ptl = pPred(P,ptl)


fun prec_of "~" = 4
  | prec_of "&" = 3
  | prec_of "|" = 2
  | prec_of "<=>" = 1
  | prec_of "==>" = 1
  | prec_of _ = ~1;

val fsdict:(string,psort list) dict = insert (Binarymap.mkDict String.compare,"=",[])

val psdict:(string,psort list) dict = insert(insert (Binarymap.mkDict String.compare,"P",[]),"=",[])

fun is_fun sr = 
    case (peek (fsdict,sr)) of 
        SOME _ => true
      | _ => false

fun is_pred sr =
    case (peek (psdict,sr)) of
        SOME _ => true
      | _ => false 


fun parse_pf tl env = 
    case tl of 
        (Key"ALL"::Id(a)::tl) =>
        (case tl of 
             (Key"."::tl1) =>
             let val (n,env1) = fresh_var env
                 val env2 = record_ps a (psvar n) env1
                 val (pb,tl2,env3) = parse_pf tl1 env2
             in (mk_quant "ALL" a (psvar n) pb,tl2,clear_ps a env3)
             end
           | (Key":"::tl1) => 
             let val (ps,tl2,env1) = parse_par tl1 env
             in case tl2 of 
                    (Key"."::tl3) => 
                    let  val env2 = record_ps a ps env1
                         val (pb,tl3,env3) = parse_pf tl2 env2
                    in
                        (mk_quant "ALL" a ps pb,tl3,clear_ps a env3) 
                    end
                  | _ => raise ERROR "Expected dot"
             end
           | _ => raise ERROR "Syntax of pform")
      | (Key"EXISTS"::Id(a)::tl) =>
        (case tl of 
             (Key"."::tl1) =>
             let val (n,env1) = fresh_var env
                 val env2 = record_ps a (psvar n) env1
                 val (pb,tl2,env3) = parse_pf tl1 env2
             in (mk_quant "EXISTS" a (psvar n) pb,tl2,clear_ps a env3)
             end
           | (Key":"::tl1) => 
             let val (ps,tl2,env1) = parse_par tl1 env
             in case tl2 of 
                    (Key"."::tl3) => 
                    let  val env2 = record_ps a ps env1
                         val (pb,tl3,env3) = parse_pf tl2 env2
                    in
                        (mk_quant "EXISTS" a ps pb,tl3,clear_ps a env3) 
                    end
                  | _ => raise ERROR "Expected dot"
             end
           | _ => raise ERROR "Syntax of pform")
      | _ => parsefix 0 (parse_atom tl env)
and parsefix prec (pf,tl,env) =
    case tl of 
        (Key(co)::tl1) => 
        if prec_of co < prec then (pf,tl,env)
        else parsefix prec
                      (apfst (mk_pConn co pf)
                             (parsefix (prec_of co) 
                                       (parse_pf tl1 env)))
      | _ => (pf,tl,env) 
and parse_atom tl env =
    case tl of 
        (Key"~"::tl1) => apfst mk_neg (parse_atom tl1 env)
      | (Key"("::tl1) => rightparen (parse_pf tl1 env)
      | (Id(a)::tl1) => 
        if is_pred a then
            (case tl1 of 
                (Key"("::tl2) =>
                (apfst (mk_pPred a) 
                       (rightparen 
                            (parse_repeat1 (",",parse_pt) tl2 env)))
              | _ => raise ERROR "bracket expected")
        else let val (pt1,tl1,env1) = parse_pt tl env 
             in (case tl1 of 
                     (Key(p)::tl2) => 
                     (*check p is a pred sy here and perhaps an error message?*)
                     let val (pt2,tl2,env2) = parse_pt tl2 env1
                     in (pPred(p,[pt1,pt2]),tl2,env2)
                     end
                   | _ => raise ERROR "Pred expected")
             end
      | _ => raise ERROR "Syntax of formula"




fun parse_end (x, l, env) =
    if l = [] then (x,env) 
    else raise ERROR "Extra characters in formula";

fun read_pt a = parse_end (parse_pt (lex a) empty)

fun print_read_pt a = 
    let val (pt,env) = parse_end (parse_pt (lex a) empty)
    in (pt,pdict env)
    end

fun read_pf a = parse_end (parse_pf (lex a) empty);


fun print_read_pf a = 
    let val (pf,env) = parse_end (parse_pf (lex a) empty)
    in (pf,pdict env)
    end


(*do we really need to change the env so it records ptUVars -> pob?*)

fun term_from_pt env pt = 
    case (chasevart pt env) of 
        ptUVar n => Var(n,ob)
      | pVar(n,ps) => Var(n,sort_from_ps env ps) 
      | pFun(f,ps,ptl) => Fun(f,sort_from_ps env ps,
                              List.map (term_from_pt env) ptl)
      | pAnno(pt,ps) => term_from_pt env pt
and sort_from_ps env ps = 
    case (chasevars ps env) of
        psvar n => ob
      | pob => ob
      | par(A,B) => ar(term_from_pt env A,term_from_pt env B)


fun form_from_pf env pf = 
    case pf of 
        pQuant(q,n,ps,pb) => 
        Quant(q,n,sort_from_ps env ps,form_from_pf env pb)
      | pConn(co,pfl) => 
        Conn(co,List.map (form_from_pf env) pfl)
      | pPred(P,ptl) => 
        Pred(P,List.map (term_from_pt env) ptl)



fun read_f f = 
    let val (pf,env) = read_pf f
        val env1 = type_infer_pf env pf
    in (form_from_pf env1 pf,pdict env1)
    end

end
