structure pterm :> pterm = 
struct
open token pterm_dtype term form symbols


fun mk_pQuant q n ps pf = pQuant (q,n,ps,pf)

fun mk_pConn co pf1 pf2 = pConn(co,[pf1,pf2])

fun mk_pNeg pf = pConn("~",[pf])

fun mk_pPred P ptl = pPred(P,ptl)

(*TODO: let the parse parse " ' ". *)

structure Env = 
struct
open Binarymap List
type env = (string,pterm)Binarymap.dict * (string,psort)Binarymap.dict * 
           (string,psort)Binarymap.dict * (string,psort)Binarymap.dict * int


(*components:
  1. records where does the ptUVars go to, 
  2. records where does the psvar goes to,
  3. records how names obtained by parsing is associated to a psvar.
  4. records the sort of ptUVars  *)
val empty : env = (Binarymap.mkDict String.compare, 
                   Binarymap.mkDict String.compare,
                   Binarymap.mkDict String.compare,
                   Binarymap.mkDict String.compare,
                   0)

fun insert_ps n s ((dpt,dps,dv,dus,i):env):env = (dpt,insert (dps,n,s),dv,dus,i)
    
fun insert_pt n t ((dpt,dps,dv,dus,i):env):env = (insert (dpt,n,t),dps,dv,dus,i)

fun insert_us Av s ((dpt,dps,dv,dus,i):env):env = (dpt,dps,dv,insert (dus,Av,s),i)

fun dps_of ((dpt,dps,dv,dus,i):env) = dps

fun dpt_of ((dpt,dps,dv,dus,i):env) = dpt

fun dv_of ((dpt,dps,dv,dus,i):env) = dv

fun dus_of ((dpt,dps,dv,dus,i):env) = dus

fun var_of ((dpt,dps,dv,dus,i):env) = i

fun fresh_var ((td,sd,dv,dus,i):env):string * env = (" " ^ Int.toString i,(td,sd,dv,dus,i + 1))

fun lookup_pt ((dpt,_,_,_,_):env) n = peek (dpt,n)

fun lookup_ps ((_,dps,_,_,_):env) n = peek (dps,n)

fun lookup_us ((_,_,_,dus,_):env) n = peek (dus,n)

fun ps_of ((_,_,dv,_,_):env) n:psort option = peek (dv,n)

fun record_ps n s ((dpt,dps,dv,dus,i):env):env = (dpt,dps,insert (dv,n,s),dus,i)

fun clear_ps n ((dpt,dps,dv,dus,i):env):env = 
    case ps_of (dpt,dps,dv,dus,i) n of
        SOME ps => 
        let val (dv1,_) = remove(dv, n) in (dpt,dps,dv1,dus,i) end
      | NONE => (dpt,dps,dv,dus,i)

fun clear_psn n ((dpt,dps,dv,dus,i):env):env = 
    case lookup_ps (dpt,dps,dv,dus,i) n of 
        SOME ps => 
        let val (dps1,_) = remove(dps, n) in (dpt,dps1,dv,dus,i) end
      | NONE => (dpt,dps,dv,dus,i)
end

open Binarymap List Env


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

fun pdus (dict:(string,psort) dict) =  Binarymap.foldl (fn (k,v,A) => ("(" ^ k ^ " -> " ^ stringof_ps v ^ ")") :: A) [] dict


fun pdict env = (ptdict (dpt_of env),psdict (dps_of env),pdv (dv_of env),pdus (dus_of env),
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
      (*should we check ptname does not occur in the current ps of ptUVar?*)
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


fun ps_of_pt pt env =
    case pt of 
        ptUVar n =>
        (case lookup_us env n of 
             SOME ps => (ps,env) 
           | _ => 
             let val (Av,env1) = fresh_var env
                 val env2 = insert_us n (psvar Av) env1
             in (psvar Av,env2)
             end)
      | pVar (n,ps) => (ps,env)
      | pFun (n,ps,l) => (ps,env)
      | pAnno(pt,ps) => ps_of_pt pt env

(*TODO: read_ast_f "! A. ! B.! f: A -> B. ! g:A ->B.~(f = g) ==> ? a: 1 -> A. ~(f o a = g o a)";
Exception- UNIFY "occurs check(pt):pv a : psv  4 ptu  4" raised*)

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
    (*clear up repeated cases?*)
    case (chasevart pt1 env,chasevart pt2 env) of 
        (ptUVar a,ptUVar b) => 
        if a = b then env else 
        let val (psa, env1) = ps_of_pt pt1 env
            val (psb, env2) = ps_of_pt pt2 env1
            val env3 = unify_ps env2 psa psb
        in insert_pt a (ptUVar b) env3
        end
      | (ptUVar a, t) => 
        if occs_pt a env t 
        then raise UNIFY ("occurs check(pt):" ^
             stringof_pt (ptUVar a) ^ " " ^ stringof_pt t)
        else 
            let val (ps1, env1) = ps_of_pt pt1 env
                val (ps2, env2) = ps_of_pt pt2 env1
                val env3 = unify_ps env2 ps1 ps2
            in 
                insert_pt a t env3
            end
      | (t, ptUVar a) => 
        if occs_pt a env t 
        then raise UNIFY ("occurs check(pt):" ^
             stringof_pt t ^ " " ^ stringof_pt (ptUVar a))
        else
            let val (ps1, env1) = ps_of_pt pt1 env
                val (ps2, env2) = ps_of_pt pt2 env1
                val env3 = unify_ps env2 ps1 ps2
            in 
                insert_pt a t env3
            end
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


fun t2pt t = 
    case t of 
        Var(n,s) => pVar(n,s2ps s)
      | Fun(f,s,l) => pFun(f,s2ps s,map t2pt l)
      | _ => simple_fail"bounded variable cannot be converted into pterm"
and s2ps s = 
    case s of
        ob => pob
      | ar(t1,t2) => par(t2pt t1,t2pt t2)

val ns2nps =  (fn (a,b) => (a,s2ps b))

val essd:(string , string) dict = Binarymap.mkDict String.compare


(*the name in the dictionary does not matter, what does matter is that different name corresponds to different unification variables. fgt name functions forgets the name strings and turns them into unification variables which corresponds to natural numbers.*)

fun fgt_name_pt pt (nd:(string , string) dict) env = 
    case pt of
        pVar (name,ps) =>
        (case Binarymap.peek(nd,name) of 
            SOME uv => 
            let val (ps1,nd1,env1) = fgt_name_ps ps nd env
                val env2 = case (lookup_us env1 uv) of 
                               SOME ps2 => unify_ps env ps1 ps2
                             | NONE => insert_us uv ps1 env1
            in 
                (ptUVar uv,nd1,env2)
            end
          | NONE => 
            let val (Av,env1) = fresh_var env
                val nd1 = Binarymap.insert(nd,name,Av)
                val (ps1,nd2,env2) = fgt_name_ps ps nd1 env1
                val env3 = insert_us Av ps1 env2
            in 
                (ptUVar Av, nd2,env3)
            end)
      | pFun(f,ps,ptl) => 
        let val (ptl1,nd1,env1) = 
                foldr 
                    (fn (pt,(l,nd,env)) => 
                        let val (pt',nd',env') = fgt_name_pt pt nd env
                        in (pt':: l,nd',env')
                        end)
                    ([],nd,env)
                    ptl
            val (ps1,nd2,env2) = fgt_name_ps ps nd1 env1
        in
            (pFun(f,ps1,ptl1),nd2,env2)
        end
      | _ => simple_fail("unexpected pretype constructor" ^ (stringof_pt pt))
and fgt_name_ps ps nd env = 
    case ps of 
        pob => (pob,nd,env)
      | par(t1,t2) => 
        let val (t1',nd1,env1) = fgt_name_pt t1 nd env
            val (t2',nd2,env2) = fgt_name_pt t2 nd1 env1
        in 
            (par(t1',t2'),nd2,env2)
        end
      | _ => simple_fail"unexpected presort variable"

fun nps2ptUVar (n,ps) nd env = fgt_name_pt (pVar(n,ps)) nd env

fun npsl2ptUVarl l env = 
    foldr (fn (p,(l,nd,env)) => 
              let val (pt,nd1,env1) = nps2ptUVar p nd env
              in (pt :: l,nd1,env1)
              end)
          ([],essd,env)
          l

fun mk_pob A = pVar(A,pob)

fun type_infer_pfun env t ty = 
    case t of 
        pFun(f,ps,ptl) =>
        let 
            val env = 
                foldr (fn (pt,env) => 
                          let val (ps,env1) = ps_of_pt pt env 
                          in type_infer env1 pt ps
                          end)
                      env ptl
        in
        (case lookup_fun fsyms0 f of 
             SOME (s,l) => 
             let val (uvs,nd,env1) = npsl2ptUVarl (map ns2nps l) env 
                 val (s1,nd1,env2) = fgt_name_ps (s2ps s) nd env1
                 val tounify = zip ptl uvs
                 val env3 = foldr
                                (fn ((a,b),env) => unify_pt env a b) 
                                env1 tounify
             in
                 unify_ps (unify_ps env3 ty s1) ty ps
             end
           | _ => env)
        end
      | _ => simple_fail("not a function term" ^ (stringof_pt t))
and type_infer env t ty = 
    case t of 
        pFun(f,ps,ptl) => type_infer_pfun env t ty
      | pAnno (pt,ps) => 
        (*order to be think more about*)
        let val env1 = type_infer env pt ps
            val (ps',env1') = (ps_of_pt pt env1)
            val env2 = type_infer env1' pt ps'
        in unify_ps env2 ty ps
        end
      | pVar (name,ps) => unify_ps env ty ps 
      | ptUVar name => 
        (*to be carefully considered, worry about looping if generate a psvar here*)
        (case lookup_us env name of
             SOME ps => unify_ps env ps ty
          | _ => insert_us name ty env)

fun type_infer_args env pf = 
    case pf of
       pPred("=",[t1,t2]) => 
       let val (ps1,env1) = ps_of_pt t1 env
           val (ps2,env2) = ps_of_pt t2 env1
       in unify_ps env2 ps1 ps2
       end
     | pPred(p,ptl) => 
        (case lookup_pred psyms0 p of 
             SOME l => 
             let val (uvs,_,env1) = npsl2ptUVarl (map ns2nps l) env 
                 val tounify = zip ptl uvs
             in
                 foldr
                     (fn ((a,b),env) => unify_pt env a b) 
                     env1 tounify
             end
           | _ => foldr (fn (pt,env) => 
                            let val (ps,env1) = ps_of_pt pt env 
                            in type_infer env1 pt ps
                            end)
                        env
                        ptl)
      | _ => simple_fail"not a predicate" 
   
fun type_infer_pf env pf = 
    case pf of 
        pQuant(q,n,ps,pb) => type_infer_pf env pb
      | pConn(co,pfl) => 
        (case pfl of 
             [] => env
           | h::t => let val env1 = type_infer_pf env h
                     in type_infer_pf env1 (pConn(co,t))
                     end)
      | pPred(p,ptl) => 
        let val env1 = foldr (fn (pt,env) => 
                                 let val (ps,env0) = (ps_of_pt pt env)
                                 in
                                     type_infer env0 pt ps
                                 end) env ptl
        in
            type_infer_args env1 pf
        end

(*delete one of the repeated code in type_infer_pf and args!

let pred and function type-infer share common function*)

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


fun fprec_of "*" = 2
  | fprec_of "+" = 1
  | fprec_of "o" = 3
  | fprec_of "^" = 4
  | fprec_of _ = ~1 


fun mk_pt_conn env co s1 s2 =
    let val (n,env1) = fresh_var env in 
        (pFun (co,psvar n,[s1,s2]),env1)
    end


datatype ast = 
         aId of string 
         | aApp of string * ast list
         | aInfix of ast * string * ast
         | aBinder of string * ast(*variable and sort*) * ast (*body*)

(*all it have to do is to turn a token list into a tree, do not need add interesting sort/term/form*)

(*fixity table, to be ordered according to the numbers*)



(**)

 
fun parse_arepeat (a,parsefn) tl = 
    case tl of 
        (Key(b)::tl1) => if b = a then 
                             parse_arepeat1 (a,parsefn) tl1
                         else ([],tl)
      | _ => ([],tl)
and parse_arepeat1 (a,parsefn) tl =
    let val (u,tl1) = parsefn tl
        val (asts,tl2) =  (parse_arepeat (a,parsefn) tl1)
    in (u::asts,tl2)
    end

exception ERROR of string


fun rparen s (x, Key(s')::toks) = 
    if s = s' then (x, toks) else
    raise ERROR ("Symbol:" ^ (s) ^ " expected")
  | rparen s _ =  raise ERROR ("Symbol:" ^ (s) ^ " expected")

(*doing rparen and then nothing is wrong, see parse_pt_atom*)

fun parse_ast tl =
    case tl of
        Key"!"::tl =>
        let 
            val (ns,tl1) = parse_ast tl
            val tl1' = List.tl tl1
            val (b,tl2) = parse_ast tl1'
        in
            (aBinder ("!",ns,b), tl2)
        end
      | Key"?"::tl =>
        let 
            val (ns,tl1) = parse_ast tl
            val tl1' = List.tl tl1
            val (b,tl2) = parse_ast tl1'
        in
            (aBinder ("?",ns,b), tl2)
        end 
      | _ => parse_ast_fix 0 (parse_ast_atom tl)
and parse_ast_fix n (ast,tl) = 
    case tl of 
        Key(k) :: tl =>
        if fxty k < n then (ast,Key(k) :: tl)
        else
            let
                val (ast1,tl1) =
                    if List.hd tl = Key "!" orelse 
                       List.hd tl = Key "?" then 
                        parse_ast tl 
                    else 
                    parse_ast_atom tl
                val (ast2,tl2) = parse_ast_fix (fxty k) (ast1,tl1)
                val ast' = aInfix (ast,k,ast2)
            in parse_ast_fix n (ast',tl2)
            end
      | _ => (ast,tl)
and parse_ast_atom tl = 
    case tl of
        (Key"~"::tl1) =>
        let val (ast,tl2) = parse_ast tl1
        in (aApp("~",[ast]),tl2)
        end
     | Id(a)::Key"("::tl1 => 
       let 
           val (astl,tl2) = rparen ")" (parse_arepeat1 (",",parse_ast) tl1)
       in (aApp(a,astl),tl2)
       end
     | Key"("::tl => rparen ")" (parse_ast tl) 
     | Id(a)::tl => (aId(a),tl)
     | Key"<"::tl => 
       let 
           val (astl,tl2) = rparen ">" (parse_arepeat1 (",",parse_ast) tl)
       in (aApp("pa",astl),tl2)
       end
     | _ => simple_fail""


(*
parse_ast (lex "! X. ~ areiso(X,0) ==> ? x: 1 -> X. T");
Exception- ERR "" raised
*)
(*handle "()"*)



(*need dict of infixes*)

fun pPred_cons pf pt = 
    case pf of 
        pPred(p,tl) => pPred(p,pt :: tl)
      | _ => simple_fail"not a pPred"

fun pFun_cons pt0 pt = 
    case pt0 of 
        pFun(f,ps,tl) => pFun(f,ps,pt :: tl)
      | _ => simple_fail"not a pFun"
 

(*clear ps when move out of a env*)
fun ast2pf ast (env:env) = 
    case ast of 
        aId(a) => 
        if a = "T" then (pPred("T",[]),env) else 
        if a = "F" then (pPred("F",[]),env) else
        simple_fail("variable:" ^ a ^ " is parsed as a predicate")
      | aApp("~",[ast]) => 
        let val (pf,env1) = ast2pf ast env in
            (pConn("~",[pf]),env1)
        end
      | aApp(str,astl) => 
        if is_pred str then 
            case astl of
                [] => (pPred(str,[]),env)
              | h :: t => 
                let val (pf,env1) = ast2pf (aApp(str,t)) env
                    val (pt,env2) = ast2pt h env1
                in (pPred_cons pf pt,env2)
                end
        else simple_fail("not a predicate symbol: "^ str)
      | aInfix(ast1,str,ast2) => 
        if mem str ["&","|","<=>","==>"] then
            let
                val (pf1,env1) = ast2pf ast1 env
                val (pf2,env2) = ast2pf ast2 env1
            in
                (pConn(str,[pf1,pf2]),env2)
            end else 
        if mem str ["="] then
            let
                val (pt1,env1) = ast2pt ast1 env
                val (pt2,env2) = ast2pt ast2 env1
            in
                (pPred(str,[pt1,pt2]),env2)
            end else
        simple_fail"not an infix operator"
      | aBinder(str,ns,b) => 
        if str = "!" orelse str = "?" then
            let val (pt,env1) = ast2pt ns env in 
                case pt of 
                    pVar(n,s) => 
(*TODO: need to record sort of n here!*)
                    let 
                        val (pf,env2) = ast2pf b env1 in
                        (mk_pQuant str n s pf,clear_ps n env2)
                    end
                  | pAnno(pVar(n,s),ps) => 
                    let val (pf,env2) = ast2pf b env1 in
                        (mk_pQuant str n ps pf,clear_ps n env2)
                    end
                  | _ => simple_fail"err in parsing bound variable"
            end
   (*this does not allow us to use constants for bounded variable names*)
        else simple_fail"not a quantifier"
and ast2pt ast env = 
    case ast of 
        aId(a) =>
        if is_const a then
            (pFun(a,ps_of_const a,[]),env)
        else
        (case ps_of env a of 
             NONE => let val (Av,env1) = fresh_var env 
                         val env2 = record_ps a (psvar Av) env1
                     in (pVar(a,psvar Av),env2)
                     end
           | SOME ps => (pVar(a,ps),env))
      | aApp(str,astl) => 
        if is_fun str then 
            case astl of
                [] => 
                let val (Av,env1) = fresh_var env
                in (pFun(str,psvar Av,[]),env1)
                end
              | h :: t => 
                let val (pt0,env1) = ast2pt (aApp(str,t)) env
                    val (pt,env2) = ast2pt h env1
                in (pFun_cons pt0 pt,env2)
                end
        else simple_fail("not a function symbol: " ^ str) 
      | aInfix(aId(n),":",aInfix(ast1,"->",ast2)) =>
        let 
            val (dom,env1) = ast2pt ast1 env
            val (cod,env2) = ast2pt ast2 env1
        in 
            case ps_of env n of 
            NONE => let val env3 = record_ps n (par(dom,cod)) env2
                     in (pVar(n,par(dom,cod)),env3)
                     end
           | SOME ps =>  (pAnno(pVar(n,ps),par(dom,cod)),env2)
        end
        (*let 
            val (pt1,env1) = ast2pt ast1 env
            val (pt2,env2) = ast2pt ast2 env1
            val env3 = record_ps n (par(pAnno(pt1,pob),pAnno(pt2,pob))) env2
        in  (pVar(n,par(pAnno(pt1,pob),pAnno(pt2,pob))),env3)
        end *)
      | aInfix(ast1,str,ast2) => 
        if mem str ["*","+","^","o"] then
            let val (pt1,env1) = ast2pt ast1 env
                val (pt2,env2) = ast2pt ast2 env1
                val (Av,env3) = fresh_var env2
            in
                (pFun(str,psvar Av,[pt1,pt2]),env3)
            end
        else simple_fail"not an infix operator"
      | aBinder(str,ns,b) => 
        simple_fail "quantified formula parsed as a term!"

fun dest_Binder (aBinder(q,ns,b)) = (q,ns,b)


fun parse_ast_end (x:ast, l:token list) =
    if l = [] then x
    else raise ERROR "Extra characters in formula";

fun read_ast_pf a = ast2pf (parse_ast_end (parse_ast (lex a))) empty

fun read_ast_pt a = ast2pt (parse_ast_end (parse_ast (lex a))) empty

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
 



fun prec_of "~" = 4
  | prec_of "&" = 3
  | prec_of "|" = 2
  | prec_of "<=>" = 1
  | prec_of "==>" = 1
  | prec_of _ = ~1;


fun parse_pf tl env = 
    case tl of 
        (Key"!"::Id(a)::tl) =>
        (case tl of 
             (Key"."::tl1) =>
             let val (n,env1) = fresh_var env
                 val env2 = record_ps a (psvar n) env1
                 val (pb,tl2,env3) = parse_pf tl1 env2
             in (mk_pQuant "!" a (psvar n) pb,tl2,clear_ps a env3)
             end
           | (Key":"::tl1) => 
             let val (ps,tl2,env1) = parse_par tl1 env
             in case tl2 of 
                    (Key"."::tl3) => 
                    let  val env2 = record_ps a ps env1
                         val (pb,tl3,env3) = parse_pf tl3 env2
                    in
                        (mk_pQuant "!" a ps pb,tl3,clear_ps a env3) 
                    end
                  | _ => raise ERROR "Expected dot"
             end
           | _ => raise ERROR "Syntax of pform")
      | (Key"?"::Id(a)::tl) =>
        (case tl of 
             (Key"."::tl1) =>
             let val (n,env1) = fresh_var env
                 val env2 = record_ps a (psvar n) env1
                 val (pb,tl2,env3) = parse_pf tl1 env2
             in (mk_pQuant "?" a (psvar n) pb,tl2,clear_ps a env3)
             end
           | (Key":"::tl1) => 
             let val (ps,tl2,env1) = parse_par tl1 env
             in case tl2 of 
                    (Key"."::tl3) => 
                    let  val env2 = record_ps a ps env1
                         val (pb,tl3,env3) = parse_pf tl3 env2
                    in
                        (mk_pQuant "?" a ps pb,tl3,clear_ps a env3) 
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
      (*else let val (pf1,tl1,env1) = parse_pf tl1 env 
                 val (pf2,tl2,env2) = parse_fix (prec_of co) (pf1,tl1,env1)
                 val *)
      | _ => (pf,tl,env) 
and parse_atom tl env (*unkw*) =
    case tl of 
        (Key"~"::tl1) => apfst mk_pNeg (parse_atom tl1 env)
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
        if a = "T" orelse a = "F" then (pPred(a,[]),tl1,env) else
        if is_pred a then
            (case tl1 of 
                (Key"("::tl2) =>
                (apfst (mk_pPred a) 
                       (rightparen 
                            (parse_repeat1 (",",parse_pt) tl2 env)))
              | _ => raise ERROR "bracket expected")
        else 
            (*if is_fun*)
let val (pt1,tl1,env1) = parse_pt tl env 
             in (case tl1 of 
                     (Key(p)::tl2) => 
                     (*check p is a pred sy here and perhaps an error message?*)
                     let val (pt2,tl2,env2) = parse_pt tl2 env1
                     in (pPred(p,[pt1,pt2]),tl2,env2)
                     end
                   | _ => raise ERROR "Pred expected")
             end
      (* else case unkw of 
       error => raise ERROR "unknown name"
        | asfun  => fun code 
| aspred =>      pred code *)
      | _ => raise ERROR "Syntax of formula"

(*parser may have another flag: parse as fun, as pred

datatype unkh = error | asfun | aspred *)


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

fun term_from_pt env pt = 
    case (chasevart pt env) of 
        ptUVar n =>
        let val s = case (lookup_us env n) of
                        SOME ps => sort_from_ps env ps 
                      | NONE => ob
        in Var(n,s)
        end
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
        val (ps,env1) = (ps_of_pt pt env)
        val pd = type_infer env1 pt ps
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

fun read_ast_t t = 
    let val (pt,env) = read_ast_pt t
        val (ps,env0) = ps_of_pt pt env
        val env1 = type_infer env0 pt ps
    in (term_from_pt env1 pt,pdict env1)
    end

fun read_ast_f f = 
    let val (pf,env) = read_ast_pf f
        val env1 = type_infer_pf env pf
    in (form_from_pf env1 pf,pdict env1)
    end

(*pretty name environment*)


(*collect all the variables in f. 
use explode to turn string into list, if begin with a space, it means the variable is generated. 

keep a dict or ? to store name correspondence and already used names, not only just the one which has a number mapped to , but also the ones which has already present in the formula.

capital letter for objects, lower case for arrows, add "'" if clashed. 

generating letter which does not clash should be done in the function int 2 name, takes 2 arguments, a number and a set of variables names.

need to ensure does not clash with existing names in the formula.*)

type pne = (string,int)Binarymap.dict * int


fun n2l n = 
    if n > 0 then n :: (n2l (n - 1)) else [] 
  

fun bad_name (n,s:sort) = if List.hd (explode n) = #" " then true else false

fun try_until_ok n uns = 
    if HOLset.member(uns,str(chr (n+64))) = false then str(chr (n+64)) else try_until_ok (n + 1) uns

fun map_HOLset f s order = 
    let val l = HOLset.listItems s
        val l' = List.map f l
    in HOLset.fromList order l'
    end

fun pretty_form f = 
    let val s0 = fvf f 
        val bad_names = rev (HOLset.listItems (HOLset.filter bad_name s0))
        val used_names0 = HOLset.filter (fn ns => not (bad_name ns)) s0
(*bad name list, used names, *) 
        val l = zip (List.map fst bad_names) (n2l (List.length bad_names))
        fun foldfun ((bn,n), (uns,nr)) = 
            let val gn = try_until_ok n uns
                val uns' = HOLset.add(uns,gn)
                val nr' = (bn,gn) :: nr 
            in
                (uns',nr')
            end
        val envl = snd (List.foldr foldfun (map_HOLset fst used_names0 String.compare,[]) l)
        val env0 = mk_tenv (List.map (fn (n1,n2) => ((n1,ob),Var(n2,ob))) envl) 
        val env = mk_menv env0 (Binarymap.mkDict String.compare)
    in
        inst_form env f
    end

fun rpf f = pretty_form (readf f)

fun rapf f = pretty_form (fst (read_ast_f f))

end
