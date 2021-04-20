structure pterm :> pterm = 
struct
open token pterm_dtype term form

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


fun enclose a = "(" ^ a ^ ")"

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
      | pAnno(pt,ps) => ps_of_pt pt



fun type_infer env t ty = 
    case t of 
        pFun(f,ps,ptl) =>
        (case (f,ptl) of 
             ("o",[f,g]) => 
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val env3 = type_infer env2 g (par (ptUVar Av, ptUVar Bv))
                 val (Cv,env4) = fresh_var env3
                 val env5 = type_infer env4 f (par (ptUVar Bv, ptUVar Cv))
                 val env6 = unify_ps env5 ty (par(ptUVar Av, ptUVar Cv))
             in
                 unify_ps env6 ps ty
             end
           | ("N",[]) =>
             unify_ps (unify_ps env ps ty) ty pob
           | ("s",[]) => 
             unify_ps (unify_ps env ps ty) 
                      ty (par (pFun("N",pob,[]),pFun("N",pob,[]))) 
           | ("z",[]) => 
             unify_ps (unify_ps env ps ty) 
                      ty (par (pFun("1",pob,[]),pFun("N",pob,[])))
           | ("Nind",[x0,t]) => 
             let val (Av,env1) = fresh_var env
                 val env2 = type_infer env1 x0 (par (pFun("1",pob,[]),ptUVar Av))
                 val env3 = type_infer env2 t (par (ptUVar Av,ptUVar Av))
                 val env4 = unify_ps env3 ps ty
             in 
                 unify_ps env4 ty (par (pFun("N",pob,[]),ptUVar Av))
             end
           | ("1",[]) => 
             unify_ps (unify_ps env ps ty) ty pob
           | ("0",[]) => 
             unify_ps (unify_ps env ps ty) ty pob
           | ("to1",[X]) => 
             let val env1 = type_infer env X pob
                 val env2 = unify_ps env1 ty (par (X,pFun ("1",pob,[])))
             in 
                 unify_ps env2 ps ty
             end
           | ("from0",[X]) => 
             let val env1 = type_infer env X pob
                 val env2 = unify_ps env1 ty (par (pFun ("0",pob,[]),X))
             in 
                 unify_ps env2 ps ty
             end
           | ("*",[A,B]) =>
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty pob
             in 
                 unify_ps env3 ps ty
             end
           | ("copo",[A,B]) =>
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty pob
             in 
                 unify_ps env2 ps ty
             end
           | ("p1",[A,B]) => 
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty (par(pFun("*",pob,[A,B]), A))
             in
                 unify_ps env3 ps ty
             end
           | ("i1",[A,B]) => 
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty (par(A,pFun("+",pob,[A,B])))
             in
                 unify_ps env3 ps ty
             end
           | ("p2",[A,B]) => 
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty (par(pFun("*",pob,[A,B]), B))
             in
                 unify_ps env3 ps ty
             end
           | ("i2",[A,B]) => 
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty (par(B,pFun("+",pob,[A,B])))
             in
                 unify_ps env3 ps ty
             end
           | ("pa",[f,g]) => 
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val (Xv,env3) = fresh_var env2
                 val env4 = type_infer env3 f (par (ptUVar Xv, ptUVar Av))
                 val env5 = type_infer env4 g (par (ptUVar Xv, ptUVar Bv))
                 val env6 = unify_ps env5 ty (par (ptUVar Xv, 
                                                  pFun ("*",pob,[ptUVar Av,ptUVar Bv])))
             in
                 unify_ps env6 ps ty
             end
           | ("copa",[f,g]) => 
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val (Xv,env3) = fresh_var env2
                 val env4 = type_infer env3 f (par (ptUVar Av, ptUVar Xv))
                 val env5 = type_infer env4 g (par (ptUVar Bv, ptUVar Xv))
                 val env6 = unify_ps env ty
                                     (par (pFun ("+",pob,[ptUVar Av,ptUVar Bv]),
                                           ptUVar Xv))
             in
                 unify_ps env6 ps ty
             end
           | ("eqo",[f,g]) =>
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
                 val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
                 val env5 = unify_ps env4 ty pob
             in
                 unify_ps env5 ps ty
             end
           | ("coeqo",[f,g]) =>
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
                 val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
                 val env5 = unify_ps env4 ty pob
             in
                 unify_ps env5 ps ty
             end
           | ("eqa",[f,g]) =>
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
                 val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
                 val env5 = unify_ps env4 ty (par (pFun ("eqo",pob,[f,g]),
                                                   ptUVar Av))
             in
                 unify_ps env5 ps ty
             end
           | ("coeqa",[f,g]) =>
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
                 val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
                 val env5 = unify_ps env4 ty (par (ptUVar Bv,pFun ("coeqo",pob,[f,g])))
             in
                 unify_ps env5 ps ty
             end
           | ("eqinduce",[f,g,h]) => 
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
           | ("coeqinduce",[f,g,h]) => 
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
           | ("exp",[A,B]) =>  
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty pob
             in 
                 unify_ps env3 ps ty
             end
           | ("tp",[f]) => 
             let val (Av,env1) = fresh_var env
                 val (Bv,env2) = fresh_var env1
                 val (Cv,env3) = fresh_var env2
                 val env4 = type_infer env3 f 
                                       (par (pFun("*",pob,[ptUVar Av,ptUVar Bv]),
                                             ptUVar Cv))
                 val env5 = unify_ps env4 ty 
                                     (par(ptUVar Bv, pFun ("exp",pob,[ptUVar Av,ptUVar Cv])))
             in unify_ps env5 ps ty 
             end 
           | ("ev",[A,B]) => 
             let val env1 = type_infer env A pob
                 val env2 = type_infer env1 B pob
                 val env3 = unify_ps env2 ty 
                                     (par (pFun("*",pob,[A,pFun("exp",pob,[A,B])]),B))
             in
                 unify_ps env3 ps ty
             end
           | ("id",[A]) => 
             let val env1 = type_infer env A pob
             in unify_ps (unify_ps env1 ps ty) ty (par (A,A))
             end
           | _ => let val env1 = env_from_ptl env ptl
                  in unify_ps env1 ty ps
                  end
        )
      | pAnno (pt,ps) => 
        let val env1 = type_infer env pt ps
            val env2 = type_infer env1 pt (ps_of_pt pt)
        in unify_ps env2 ty ps
        end
      | pVar (name,ps) => unify_ps env ty ps 
      | ptUVar name => unify_ps env ty pob
and env_from_ptl env ptl = 
    case ptl of 
        [] => env
      | h::t => 
        let val env1 = type_infer env h (ps_of_pt h)
        in env_from_ptl env1 t
        end

(*change ptUVar takes a ps*)

(*working on pred type inference*)

type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict



type psymd = (string, (string * sort) list) Binarymap.dict

type uvd = ((string * sort), pterm) Binarymap.dict

fun lookup_pred (pd:psymd) p = Binarymap.peek (pd,p)

fun lookup_ns (ud:uvd) (n,s) = Binarymap.peek (ud,(n,s))

fun insert_ns2pt (n,s) pt (ud:uvd) = Binarymap.insert (ud,(n,s),pt)

val emptypsd: psymd = (Binarymap.mkDict 
                             (pair_compare String.compare))

(*take the sig list -> give a pterm term list*)
val psyms0:psymd = List.foldr (fn ((p:string,l:(string * sort) list),d) =>
                                  Binarymap.insert (d,p,l)) 
                        (Binarymap.mkDict String.compare)
                        [("ismono",[("a",ar(mk_ob "A",mk_ob "B"))]),
                         ("isgroup",[("G",ob),
                                     ("m",ar (mk_fun "*" ob [mk_ob "G",mk_ob "G"],
                                              mk_ob "G")),
                                     ("i",ar (mk_fun "1" ob [],mk_ob "G")),
                                     ("inv",ar (mk_ob "G",mk_ob "G"))])]
(*should we allow definition to take only function terms?*)

fun new_pred p tl = Binarymap.insert (psyms0,p,tl)

val n2u0:uvd = Binarymap.mkDict (pair_compare String.compare sort_compare)


(*clause for pFun/pAnno : do type_infer for fun sym first?
do not do type_infer for other clauses because on pFun/pAnno gives information*)

(*do chase somewhere?*)


(*define chase which chase the var and convert it to a pt for others*)

fun t2pt t = 
    case t of 
        Var(n,s) => pVar(n,s2ps s)
      | Fun(f,s,l) => pFun(f,s2ps s,map t2pt l)
      | _ => raise ERR "bounded variable cannot be converted into pterm"
and s2ps s = 
    case s of
        ob => pob
      | ar(t1,t2) => par(t2pt t2,t2pt t2)

(*do not look at the pterms to compare, just turn a ptl (obtained by turning tl into ptl) into a pt list where names are replaced by unification variables.*)

fun ptwUVar pt nd env = 
    case pt of
        pVar(name,ps) =>
        (case Binarymap.peek(nd,name) of 
            SOME u => 
            let val (ps1,nd1,env1) = pswUVar ps
            in (ptUVar(n,pswUVar),nd1,env1)
            end                   
            | NONE => 
              let val (Av, env1) = fresh_var env 
                  val nd1 = Binarymap.insert(nd,name,Av)
                  val (ps1,nd2,env2) = pswUVar ps nd1 env1
              in (ptUVar(Av,ps1),nd2,env2)
              end)
      | pFun(f,ps,ptl) => 
        let val (ptl1,nd1,env1) = 
                foldr
                    (fn (pt0,(ptl0,nd0,env0)) => 
                        let val (pt',nd',env') = ptwUVar pt0 nd0 env0 
                        in (pt':: ptl,nd',env')
                        end)
                    ([],nd,env) ptl
            val (ps1,nd2,env2) = pswUVar ps nd1 env1
        in pFun(f,ps1,ptl1)
        end
      | ptUVar(name,ps) => 
        let val (ps1,nd1,env1) = pswUVar ps nd env
        in (ptUVar (name,ps1),nd1,env1)
        end
      | pAnno _ =>  raise ERR "unexpected pterm constructor"
and pswUVar ps nd env = 
    case ps of
        pob => (pob,nd,env)
      | psvar _ => raise ERR "unexpected psort constructor"
      | par(pt1,pt2) => 
        let val (pt3,nd1,env1) = ptwUVar pt1 nd env
            val (pt4,nd2,env2) = ptwUVar pt2 nd1 env1
        in (par(pt3,pt4),nd2,env2)
        end
      
(*      
fun ptwUVar ptl nd env = 
    case ptl of 
        [] => 
      | h :: t => 
        case h of 
            pVar(name,ps) => 
            case Binarymap.peek(nd,name) of 
                SOME uvn => 
                let val (ps1,nd1,env1) = pswUVar s
                in (ptUVar (n,ps1),nd1,env1)
                end
              | NONE => 
                let val env1 = fresh_var env 

*)
fun unify_tpt t pt env (ns2pt:uvd) = 
    case (t,pt) of 
        (Var(n,s),ptUVar m) => 
        if s = ob then
            case lookup_ns ns2pt (n,s) of 
                SOME pt0 => (unify_pt env pt pt0,ns2pt)
              | NONE => 
                (env, insert_ns2pt (n,s) pt ns2pt)
        else 
            raise ERR ("ptUVar with name " ^ m ^ "cannot be an arrow")
      | (Var(n,s),pVar(n0,s0)) => 
        (case lookup_ns ns2pt (n,s) of
            SOME pt0 => 
            let
                val env1 = unify_pt env pt pt0
            in unify_sps s s0 env1 ns2pt
            end
          | NONE => 
            let val ns2pt1 = insert_ns2pt (n,s) pt ns2pt
            in unify_sps s s0 env ns2pt1
            end)
      | (Var(n,s),pFun(f,ps,ptl)) => 
        let 
            val env = type_infer env pt ps 
        in
            case lookup_ns ns2pt (n,s) of
                SOME pt0 => (unify_pt env pt0 pt,ns2pt)
              | NONE => 
                let 
                    val ns2pt1 = insert_ns2pt (n,s) pt ns2pt
                in unify_sps s ps env ns2pt1
                end
        end
      | (Var(n,s),pAnno(pt0,ps)) => 
        let
            val env = type_infer env pt ps
        in
            case lookup_ns ns2pt (n,s) of
                SOME pt0 => (unify_pt env pt0 pt0,ns2pt)
              | NONE => 
                let 
                    val ns2pt1 = insert_ns2pt (n,s) pt ns2pt
                in
                    unify_sps s ps env ns2pt1
                end
        end
      | (Fun(f,s,l),pFun(pf,ps,pl)) => 
        if f = pf then
            let val env = type_infer env pt ps
                val (env1,ns2pt1) = unify_sps s ps env ns2pt
            in
                foldr (fn ((t0,pt0),(e,nspt)) => unify_tpt t0 pt0 e nspt)
                      (env1,ns2pt1)
                      (zip l pl)
            end
        else 
            raise ERR ("different function symbols: " ^ f ^ " , " ^ pf)
      (*convert to pFun and unify*)
     (* | (Fun(f,s,l),ptUVar m) => 
        if s = ob then 
            let fun t2pt t = 
                    case t of 
                        Var(n0,s0) =>
                        (case lookup_ns ns2pt (n0,s0) of
                             SOME pt0 => (pt0,env,ns2pt)
                           | NONE => 
                             case s0 of
                                 ob =>
                                 ar(A,B))
                fun ptl2l l = 
                    case l of
                        [] => []
                      | h :: t => 
        else
            raise ERR ("ptUVar " ^ m ^ "must be an object") *)
      | _ => raise ERR "unexpected constructors"
and unify_sps s ps env (ns2pt:uvd) = 
    case (s,ps) of
        (ob,pob) => (env,ns2pt)
      | (ar(d1,c1),par(d2,c2)) => 
        let val env1 = unify_ps env pob (ps_of_pt d2)
            val env2 = unify_ps env1 pob (ps_of_pt c2)
            val (env3,ns2pt1) = unify_tpt d1 d2 env2 ns2pt
        in unify_tpt c1 c2 env3 ns2pt1
        end
      | (ob,psvar n) => (unify_ps env pob ps,ns2pt)
      | (ar(d,c),psvar n) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = unify_ps env2 (psvar n) (par(ptUVar Av,ptUVar Bv))
            val (env4,ns2pt1) = unify_tpt d (ptUVar Av) env3 ns2pt
        in unify_tpt c (ptUVar Bv) env4 ns2pt1
        end
      | (ob,par(_,_)) => raise ERR "cannot unify ob with par"
      | (ar(_,_),pob) => raise ERR "cannot unify ar with pob"


fun pdpair (env,uvd) =  (pdict env,Binarymap.listItems uvd)

fun unify_tpt' ((t,pt),(env,n2t)) = unify_tpt t pt env n2t

fun type_infer_args env pf = 
    case pf of 
        pPred(p,l) => 
        (case (lookup_p psyms0 p) of 
            SOME tl =>
            List.foldr
                unify_tpt' 
                (env,Binarymap.mkDict 
                         (pair_compare String.compare sort_compare))
                (zip tl l)
          | _ => (env,Binarymap.mkDict 
                          (pair_compare String.compare sort_compare)))
      | _ => raise ERR "not a predicate"
             


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

(*really parse pob/par because they are actually doing type-infer. ?*)

(*type inference during parsing : 
from f: A -> B, know that f is an arrow and A and B are objects

use pAnno for this type-infer?
*)

fun fprec_of "*" = 2
  | fprec_of "+" = 1
  | fprec_of "o" = 3
  | fprec_of _ = ~1 


fun mk_pt_conn env co s1 s2 =
    let val (n,env1) = fresh_var env in 
        (pFun (co,psvar n,[s1,s2]),env1)
    end


val cdict0:(string,psort) dict = insert(insert(insert(insert(Binarymap.mkDict String.compare,"N",pob),"z",par(pFun("1",pob,[]),pFun("N",pob,[]))),"s",par(pFun("N",pob,[]),pFun("N",pob,[]))),"1",pob)



(*

val cdict0 = foldr 

*)
val cdict = ref cdict0

fun is_const sr = 
    case (peek (!cdict,sr)) of 
        SOME _ => true
      | _ => false

fun ps_of_const c = 
    case (peek (!cdict,c)) of 
        SOME ps => ps 
      | _ => raise ERROR "not a constant"



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
             (if (is_const a) then (pFun (a,ps_of_const a,[]),tl1,env) else
               case (ps_of env a) of 
                  SOME ps => (pVar (a,ps),tl1,env)
                | NONE => let val (n,env1) = fresh_var env
                              val env2 = record_ps a (psvar n) env1
                          in (pVar (a,psvar n),tl1,env2)
                          end))
      | (Key"("::tl1) => rightparen (parse_pt tl1 env) 
      | [] => raise ERROR "Syntax of preterm: unexpected end of file"
      | t::_ => raise ERROR ("Syntax of preterm: " ^ tokentoString t) 
and parse_pt_fix prec (pt,tl,env) = 
    case tl of
        Key(co)::tl => 
        if fprec_of co < prec then (pt, Key(co)::tl,env)
        else
            let val (pt1,tl1,env1) = parse_pt_atom tl env
                val (pt2,tl2,env2) = parse_pt_fix (fprec_of co) (pt1,tl1,env1)
                val (cpt, env3) = mk_pt_conn env2 co pt pt2
            in parse_pt_fix prec (cpt,tl2,env3)
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
 
fun mk_quant q n ps pf = pQuant (q,n,ps,pf)

fun mk_pConn co pf1 pf2 = pConn(co,[pf1,pf2])

fun mk_pneg pf = pConn("~",[pf])

fun mk_pPred P ptl = pPred(P,ptl)


fun prec_of "~" = 4
  | prec_of "&" = 3
  | prec_of "|" = 2
  | prec_of "<=>" = 1
  | prec_of "==>" = 1
  | prec_of _ = ~1;

datatype ForP = fsym | psym

val fpdict0:(string,ForP) Binarymap.dict =
    foldr (fn ((n,forp),d) => Binarymap.insert(d,n,forp)) (Binarymap.mkDict String.compare) 
          [("=",psym),("P",psym),("o",fsym),("id",fsym),("to1",fsym),
           ("from0",fsym),("p1",fsym),("p2",fsym),("pa",fsym),("ismono",psym),
           ("T",psym),("F",psym)]

(*change to fold*)

val fpdict = ref fpdict0

fun is_fun sr = 
    case (peek (!fpdict,sr)) of 
        SOME fsym => true
      | _ => false

fun is_pred sr =
    case (peek (!fpdict,sr)) of
        SOME psym => true
      | _ => false

fun insert_fsym s = fpdict:= insert(!fpdict,s,fsym) 
fun insert_psym s = fpdict:= insert(!fpdict,s,psym)


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
                         val (pb,tl3,env3) = parse_pf tl3 env2
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
                         val (pb,tl3,env3) = parse_pf tl3 env2
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
        (Key"~"::tl1) => apfst mk_pneg (parse_atom tl1 env)
      | (Key"("::tl1) =>
        (rightparen (parse_pf tl1 env)
         handle ERROR _ => 
                let val (pt1,tl1,env1) = parse_pt tl env 
                in (case tl1 of 
                        (Key(p)::tl2) => 
                        (*check p is a pred sy here and perhaps an error message?*)
                        let val (pt2,tl2,env2) = parse_pt tl2 env1
                        in (pPred(p,[pt1,pt2]),tl2,env2)
                        end
                      | _ => raise ERROR "Pred expected")
                end)
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
        Quant(q,n,sort_from_ps env ps,abstract (n,sort_from_ps env ps)
                                               (form_from_pf env pb))
      | pConn(co,pfl) => 
        Conn(co,List.map (form_from_pf env) pfl)
      | pPred(P,ptl) => 
        Pred(P,List.map (term_from_pt env) ptl)

fun read_t t = 
    let val (pt,env) = read_pt t
        val pd = type_infer env pt (ps_of_pt pt)
    in (term_from_pt pd pt,pdict pd)
    end


fun read_f0 f = 
    let val (pf,env) = read_pf f
        val env1 = type_infer_pf env pf
    in (form_from_pf env1 pf,env1)
    end

fun read_f f = 
    let val (pf,env) = read_pf f
        val env1 = type_infer_pf env pf
    in (form_from_pf env1 pf,pdict env1)
    end

val readf = fst o read_f

val readt = fst o read_t

end
