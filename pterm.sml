structure pterm :> pterm = 
struct
open token pterm_dtype

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
      | pFun (f,l) => f ^ stringof_args l 
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
      | pFun (f,l) => exists (occs_pt ptname env) l   

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
      | (pFun(f,l1),pFun(g,l2)) => 
        if f = g andalso length l1 = length l2 
        then (case (l1,l2) of 
                  ([],[]) => env 
                | (h1::r1,h2::r2) => 
                  let val env1 = unify_pt env h1 h2
                  in unify_pt env1 (pFun(f,r1)) (pFun(g,r2))
                  end
                | _ => raise (UNIFY "term list cannot be unified"))
        else raise (UNIFY "different functions")
      | _ => raise (UNIFY "terms cannot be unified")


fun type_infer env t ty = 
    case t of 
        pFun("o",[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val (Cv,env4) = fresh_var env3
            val env5 = type_infer env4 g (par (ptUVar Bv, ptUVar Cv))
        in
            unify_ps env5 ty (par(ptUVar Av, ptUVar Cv))
        end
      | pFun ("N",[]) => unify_ps env ty pob
      | pFun ("s",[]) => unify_ps env ty (par (pFun("N",[]),pFun("N",[]))) 
      | pFun ("z",[]) => unify_ps env ty (par (pFun("1",[]),pFun("N",[])))
      | pFun ("N_ind",[x0,t]) => 
        let val (Av,env1) = fresh_var env
            val env2 = type_infer env1 x0 (par (pFun("1",[]),ptUVar Av))
            val env3 = type_infer env2 t (par (ptUVar Av,ptUVar Av))
        in 
            unify_ps env3 ty (par (pFun("N",[]),ptUVar Av))
        end
      | pFun ("1",[]) => unify_ps env ty pob
      | pFun ("0",[]) => unify_ps env ty pob
      | pFun ("to1",[X]) => 
        let val env1 = type_infer env X pob
        in 
            unify_ps env1 ty (par (X,pFun ("1",[])))
        end
      | pFun ("from0",[X]) => 
        let val env1 = type_infer env X pob
        in 
            unify_ps env1 ty (par (pFun ("1",[]),X))
        end
      | pFun ("po",[A,B]) =>
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in 
            unify_ps env2 ty pob
        end
      | pFun ("copo",[A,B]) =>
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in 
            unify_ps env2 ty pob
        end
      | pFun ("p1",[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in
            unify_ps env2 ty (par(pFun("po",[A,B]), A))
        end
      | pFun ("i1",[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in
            unify_ps env2 ty (par(A,pFun("copo",[A,B])))
        end
      | pFun ("p2",[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in
            unify_ps env2 ty (par(pFun("po",[A,B]), B))
        end
      | pFun ("i2",[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in
            unify_ps env2 ty (par(B,pFun("copo",[A,B])))
        end
      | pFun ("pa",[f,g]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val (Xv,env3) = fresh_var env2
            val env4 = type_infer env3 f (par (ptUVar Xv, ptUVar Av))
            val env5 = type_infer env4 g (par (ptUVar Xv, ptUVar Bv))
        in
            unify_ps env ty (par (ptUVar Xv, 
                                  pFun ("po",[ptUVar Av,ptUVar Bv])))
        end
      | pFun ("copa",[f,g]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val (Xv,env3) = fresh_var env2
            val env4 = type_infer env3 f (par (ptUVar Av, ptUVar Xv))
            val env5 = type_infer env4 g (par (ptUVar Bv, ptUVar Xv))
        in
            unify_ps env ty (par (pFun ("copo",[ptUVar Av,ptUVar Bv]),
                                  ptUVar Xv))
        end
      | pFun ("eqo",[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
        in
            unify_ps env4 ty pob
        end
      | pFun ("coeqo",[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
        in
            unify_ps env4 ty pob
        end
      | pFun ("eqa",[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
        in
            unify_ps env4 ty (par (pFun ("coeqo",[f,g]),ptUVar Av))
        end
      | pFun ("coeqa",[f,g]) =>
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
        in
            unify_ps env4 ty (par (ptUVar Bv,pFun ("coeqo",[f,g])))
        end
      | pFun ("eq_induce",[f,g,h]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val (Xv,env4) = fresh_var env4
            val env5 = type_infer env4 h (par (ptUVar Xv, ptUVar Av))
        in
            unify_ps env5 ty (par(ptUVar Xv, pFun ("eqo",[f,g])))
        end
      | pFun ("coeq_induce",[f,g,h]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val env3 = type_infer env2 f (par (ptUVar Av, ptUVar Bv))
            val env4 = type_infer env3 g (par (ptUVar Av, ptUVar Bv))
            val (Xv,env4) = fresh_var env4
            val env5 = type_infer env4 h (par (ptUVar Bv, ptUVar Xv))
        in
            unify_ps env5 ty (par(pFun ("coeqo",[f,g]),ptUVar Xv))
        end
      | pFun ("exp",[A,B]) =>  
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in 
            unify_ps env2 ty pob
        end
      | pFun ("tp",[f]) => 
        let val (Av,env1) = fresh_var env
            val (Bv,env2) = fresh_var env1
            val (Cv,env3) = fresh_var env2
            val env4 = type_infer env2 f 
                                  (par (pFun("po",[ptUVar Av,ptUVar Bv]),
                                       ptUVar Cv))
        in
            unify_ps env4 ty 
                  (par(ptUVar Bv, pFun ("exp",[ptUVar Av,ptUVar Cv])))
        end 
      | pFun ("ev",[A,B]) => 
        let val env1 = type_infer env A pob
            val env2 = type_infer env1 B pob
        in
            unify_ps env ty (par (pFun("po",[B,pFun("exp",[A,B])]),A))
        end
      | pFun("id",[A]) => 
        let val env1 = type_infer env A pob
        in unify_ps env1 ty (par (A,A))
        end
      | pAnno (pt,ps) => 
        let val env1 = type_infer env pt ps
        in unify_ps env1 ty ps
        end
      | pVar (name,ps) => unify_ps env ty ps 
      | ptUVar name => unify_ps env ty pob
      | _ => env 


fun type_infer_pform pf env pt = 
    case pf of
        pPred("ismono",[f]) => 
        if f = pt then
            let val (Av,env1) = fresh_var env 
                val (Bv,env2) = fresh_var env1
                val (n,env3) = fresh_var env2 
                val env4 = type_infer env2 f (psvar n)
            in unify_ps env4 (psvar n) 
                        (par (ptUVar Av,ptUVar Bv))
        end
        else env
      | pPred("eq",[a,b]) =>
        if a = pt orelse b = pt then
            let val (n1,env1) = fresh_var env
                val (n2,env2) = fresh_var env1
                val env3 = type_infer env2 a (psvar n1)
                val env4 = type_infer env3 b (psvar n2)
            in unify_ps env4 (psvar n1) (psvar n2)
            end
        else env
      | pConn(co,[]) => env
      | pConn(co,h::pfs) => 
        let val env1 = type_infer_pform h env pt
        in type_infer_pform (pConn(co,pfs)) env1 pt
        end 
      | _ => env 
 


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


(*make ":" an infix*)

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
                     (let val (ps,tl5,env2) = parse_par tl4 env
                      in (pAnno(pFun(a,ptl),ps),tl5,env2)
                      end)
                   | _ => (pFun(a,ptl),tl3,env1))
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

fun parse_pf tl env = 
    case tl of 
        (Key"ALL"::Id(a)::tl) =>
        (case tl of 
             (Key"."::tl1) =>
             (case (ps_of env a) of 
                 SOME ps => apfst (mk_quant "ALL" a ps) (parse_pf tl1 env)
               | NONE => 
                 let val (n,env1) = fresh_var env
                     val env2 = record_ps a (psvar n) env1
                 in apfst (mk_quant "ALL" a (psvar n)) (parse_pf tl1 env2)
                 end)
           | (Key":"::tl1) => 
             let val (ps,tl2,env1) = parse_par tl1 env
                 val env2 = record_ps a ps env1
             in (case tl2 of 
                     (Key"."::tl3) => 
                     apfst (mk_quant "ALL" a ps) (parse_pf tl3 env2)
                   | _ => raise ERROR "Expected dot")
             end
           | _ => raise ERROR "Syntax of pform")
      | (Key"EXISTS"::Id(a)::tl) =>
        (case tl of 
             (Key"."::tl1) =>
             let val (n,env1) = fresh_var env
             in apfst (mk_quant "EXISTS" a (psvar n)) (parse_pf tl1 env1)
             end
           | (Key":"::tl1) => 
             let val (n,env1) = fresh_var env
                 val (ps,tl2,env2) = parse_par tl1 env1
             in (case tl2 of 
                     (Key"."::tl3) => 
                     apfst (mk_quant "EXISTS" a ps) (parse_pf tl3 env2)
                   | _ => raise ERROR "Expected dot")
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
                                       (parse_atom tl1 env)))
      | _ => (pf,tl,env) 
and parse_atom tl env =
    case tl of 
        (Key"~"::tl1) => apfst mk_neg (parse_atom tl1 env)
      | (Key"("::tl1) => rightparen (parse_atom tl1 env)
      | (Id(P)::Key"("::tl1) => 
        apfst (mk_pPred P) (rightparen 
                                (parse_repeat1 (",",parse_pt) tl1 env))
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


datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Param of string * sort * (string * sort) list
    | Bound of int
    | Fun of string * sort * term list;

datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form;     

fun dest_Fun (Fun (f,s,t)) = (f,s,t)
  | dest_Fun _ = raise ERROR "not a function" 

fun l_from_pl pl env cf = 
    case pl of 
        [] => ([],env)
      | h::t => let val (h1,env1) = cf h env
                    val (t1,env2) = l_from_pl t env1 cf
                in (h1 :: t1,env2) 
                end

fun term_from_pt pt env = 
    case (chasevart pt env) of
        pVar (n,ps) => 
        let val (s,env1) = sort_from_ps ps env
        in (Var (n, s),env1)
        end
     | pFun (f,l) => 
        let val (n,env1) = fresh_var env 
            val env2 = type_infer env1 pt (psvar n)
            val ps = 
                (case lookup_ps env2 n of 
                     SOME ps1 => ps1
                   | NONE => pob)
            val (s,env3) = sort_from_ps ps env2
            val (l1,env4) = l_from_pl l env3 term_from_pt
        in (Fun (f,s,l1),env4)
        end
      | ptUVar n => (Var (n,ob),env)
      | pAnno (pt1,ps) => 
        let val (n,env1) = fresh_var env
            val env2 = type_infer env1 pt (psvar n)
        in term_from_pt pt1 env2
        end
and sort_from_ps ps env = 
    case (chasevars ps env) of 
        psvar n => 
        (case (lookup_ps env n) of 
             SOME ps1 => sort_from_ps ps1 env
           | NONE => (ob,env))
      | pob => (ob,env)
      | par (A,B) => 
        let val (d,env1) = term_from_pt A env
            val (c,env2) = term_from_pt B env1
        in (ar (d,c),env2)
        end

fun pl2l_in_pPred pf env l = 
    case l of [] => ([],env)
            | h::t => 
              let val (n,env1) = fresh_var env
                  val env2 = type_infer env1 h (psvar n)
                  val env3 = type_infer_pform pf env2 h
                  val (l,env4) = (pl2l_in_pPred pf env3 t)
                  val (t,env5) = (term_from_pt h env4)
              in 
                  (t :: l, env5)
              end

fun form_from_pf pf env =
    case pf of
        pQuant(q,name,ps,pb) =>
        let val (b,env1) = form_from_pf pb env
            val (s,env2) = sort_from_ps ps env1
        in (Quant (q,name,s,b),env2)
        end
      | pConn(co,l) => 
        let val (l1,env1) = l_from_pl l env form_from_pf
        in (Conn(co,l1),env1)
        end
      | pPred(P,pl) => 
        let val (l,env1) = pl2l_in_pPred pf env pl
        in (Pred(P,l),env1)
        end




fun read_t t = 
    let val (pt,env) = read_pt t
    in term_from_pt pt env
    end

fun read_f f = 
    let val (pf,env) = read_pf f
        val (f,env1) = form_from_pf pf env
    in (f,pdict env1)
    end

end
