structure term :> term = 
struct

datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Bound of int
    | Fun of string * sort * term list;

val mk_ob_sort = ob

val ob_sort = mk_ob_sort



datatype term_view =
    vVar of string * sort
  | vB of int 
  | vFun of string * sort * term list

(*
datatype 'a term_view =
    vVar of string * sort
  | vB of int 
  | vFun of string * sort * 'a list
*)

datatype sort_view = 
         vo
         | va of term * term

fun view_term t = 
    case t of
        Var v => vVar v
      | Bound i => vB i
      | Fun sst => vFun sst

fun view_sort s = 
    case s of 
        ar dc => va dc
      | _ => vo
(*
datatype 'a terinfo = TERI of sort list * 'a list

exception TER of string * term terinfo
*)



exception TER of string * sort list * term list




fun wrap_ter s sl tl e = case e of TER (s0,sl0,tl0) => TER (s ^ s0,sl @ sl0,tl @ tl0)
                           | _ => e


fun sort_of t = 
    case t of Var (_,s) => s
            | Fun (_,s,_) => s 
            | _ => ob 

fun is_var t = 
    case t of Var _ => true | _ => false

fun is_fun t = 
    case t of Fun _ => true | _ => false

fun is_bound t = 
    case t of Bound _ => true | _ => false

fun is_ob t = if sort_of t = ob then true else false

fun is_ar t = case sort_of t of ar _ => true | _ => false

fun dest_ar s =
    case s of ar(d,c) => (d,c)
            | _  => raise TER ("dest_ar.not an arrow",[s],[])

fun dom a = #1 (dest_ar a)

fun cod a = #2 (dest_ar a)


fun dest_pair (Fun ("*",s,[A,B])) = (A,B)
  | dest_pair _ =  raise Fail "dest_pair : Error"

fun dest_o t = case t of Fun("o",s,[f,g]) => (f,g)
                       | _ => raise TER ("dest_o.wrong input",[],[t])


fun dest_var t = 
    case t of Var(n,s) => (n,s)
            | _ => raise TER ("not a variable: ",[],[t])

fun dest_fun t = 
    case  t of 
        Fun(n,s,l) => (n,s,l)
      | _ => raise TER ("not a function: ",[],[t])


(*
fun dest_fun' t = 
    case  t of 
        Fun(n,s,l) => (n,s,l)
      | _ => raise TER ("not a function: ",TERI ([],[t])


*)


fun mk_ar_sort t1 t2 = ar(t1,t2)

fun mk_ob a = Var(a,ob)

fun mk_ar a t1 t2 = Var(a,ar(t1,t2))

fun mk_ar0 a A B = Var(a,ar(mk_ob A,mk_ob B))

fun mk_var n s = Var(n,s)

val var = uncurry mk_var

fun mk_fun0 f s l = Fun(f,s,l)

fun mk_bound i = Bound i

fun mk_const n s = mk_fun0 n s []


val one = mk_fun0 "1" ob []
val zero = mk_fun0 "0" ob []
val N = mk_fun0 "N" ob []
val z = mk_fun0 "z" (ar (one,N)) []
val s = mk_fun0 "s" (ar (N,N)) []


(*construct terms that appears in axioms*)

fun id A = if sort_of A = ob 
           then mk_fun0 "id" (ar(A,A)) [A]
           else raise TER ("id.wrong sort of input",[],[A])

fun replacet (u,new) t = 
    if t=u then new else 
    case t 
     of Fun(f,s,tl) => 
        Fun(f,replaces (u,new) s, List.map (replacet(u,new)) tl) 
      | _=> t
and replaces (u,new) s = 
    case s of 
        ob => ob
      | ar(t1,t2) => ar(replacet (u,new) t1, replacet  (u,new) t2)

fun eq_term (t1,t2) = 
    case (t1,t2) of 
        (Var(n1,s1),Var(n2,s2)) => 
        n1 = n2 andalso eq_sort(s1,s2)
      | (Fun(f1,s1,l1),Fun(f2,s2,l2)) =>
        f1 = f2 andalso eq_sort(s1,s2) andalso
        List.all eq_term (zip l1 l2)
      | (Bound i1,Bound i2) => i1 = i2
      | _ => false
and eq_sort (s1,s2) = 
    case (s1,s2) of 
        (ob,ob) => true 
      | (ar(d1,c1),ar(d2,c2)) =>
        eq_term(d1,d2) andalso eq_term(c1,c2)
      | _ => false


fun substt (V as (m,s:sort),t2) t = 
    case view_term t of
        vVar(n,s') => 
        if m = n andalso (* eq_sort(s,s')*) s = s' then t2 
        else mk_var n (substs (V,t2) s')
      | vFun(f,s',tl) => mk_fun0 f (substs (V,t2) s') (List.map (substt (V,t2)) tl)
      | _ => t
and substs (V,t2) s = 
    case view_sort s of 
        vo => s
      | va(d,c) => mk_ar_sort(substt (V,t2) d) (substt (V,t2) c)



fun pair_compare ac bc ((a1,b1),(a2,b2)) = 
    case (ac (a1,a2)) of 
        EQUAL => bc (b1,b2)
      | x => x

fun inv_image_compare f c (x,y) = 
    c (f x, f y)

fun list_compare c (l1,l2) = 
    case (l1,l2) of
        ([],[]) => EQUAL
      | (h1 :: t1, h2 :: t2) => pair_compare c (list_compare c)
                                             ((h1,t1),(h2,t2))
      | ([],_) => LESS
      | (_,[]) => GREATER

fun sort_compare (s1,s2) = 
    if PolyML.pointerEq(s1,s2) then EQUAL else
    case (s1,s2) of 
        (ob,ob) => EQUAL
      | (ob,_) => LESS
      | (_,ob) => GREATER
      | (ar dc1,ar dc2) => pair_compare term_compare term_compare (dc1,dc2)
and term_compare (t1,t2) = 
    if PolyML.pointerEq(t1,t2) then EQUAL else
    case (t1,t2) of 
        (Var ns1,Var ns2) => pair_compare String.compare sort_compare (ns1,ns2)
     | (Var _ , _) => LESS
     | (_,Var _) => GREATER
     | (Bound i1, Bound i2) => Int.compare (i1,i2)
     | (Bound _ , _) => LESS
     | (_, Bound _) => GREATER
     | (Fun fsl1, Fun fsl2) => 
       inv_image_compare (fn (a,b,c) => (a,(b,c))) 
                         (pair_compare String.compare 
                                       (pair_compare sort_compare 
                                                     (list_compare term_compare))) 
                         (fsl1,fsl2)  

(*empty string-sort-pair set*)
val essps = 
    HOLset.empty (pair_compare String.compare sort_compare)



type vd = ((string * sort),term)Binarymap.dict

fun pvd vd = Binarymap.listItems vd

val emptyvd:vd = Binarymap.mkDict (pair_compare String.compare sort_compare)

fun mk_tenv l = 
    case l of 
        [] => emptyvd
      | ((n,s),t) :: l0 => Binarymap.insert(mk_tenv l0,(n,s),t)

fun v2t (V:string * sort) (t:term) (vd:vd):vd = Binarymap.insert(vd,V,t)

fun lookup_t (vd:vd) V = Binarymap.peek (vd,V)


fun match_term nss pat ct (env:vd) = 
    case (view_term pat,view_term ct) of 
        (vFun(f1,s1,l1),vFun(f2,s2,l2)) => 
        if f1 <> f2 then 
            raise TER("match_term.different function names: ",[],[pat,ct])
        else (match_sort nss s1 s2 (match_tl nss l1 l2 env)  
             handle e => raise wrap_ter "match_term." [s1,s2] [pat,ct] e)
      | (vVar(n1,s1),_) => 
        if HOLset.member(nss,(n1,s1)) then
            if (*eq_term(pat,ct)*) pat = ct then env 
            else raise TER ("match_term.current term is local constant: ",[],[pat,ct])
        else 
            (case (lookup_t env (n1,s1)) of
                 SOME t => if (* eq_term(t,ct) *) t = ct then env else
                           raise TER ("match_term.double bind: ",[],[pat,t,ct])
               | _ => 
                 v2t (n1,s1) ct (match_sort nss s1 (sort_of ct) env)
                 handle e => raise wrap_ter "match_term." [] [pat,ct] e)
      | (vB i1,vB i2) => 
        if i1 <> i2 then 
            raise TER ("match_term.bound variables have different levels: ",[],[pat,ct])
        else env
      | _ => raise Fail "match_term.unexpected term constructor"
and match_sort nss sp cs env = 
    case (view_sort sp,view_sort cs) of 
        (vo,vo) => env
      | (va(d1,c1),va(d2,c2)) => 
        match_term nss c1 c2 (match_term nss d1 d2 env)
      | _ => raise TER ("match_sort.cannot match ob with ar: ",[sp,cs],[])
and match_tl nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl nss t1 t2 (match_term nss h1 h2 env)
      | _ => raise TER ("match_sort.incorrect length of list",[],[])



fun inst_term (env:vd) t = 
    case view_term t of 
        vVar(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => mk_var n (inst_sort env s))
      | vFun(f,s,tl) => mk_fun0 f (inst_sort env s) (List.map (inst_term env) tl)
      | _ => t
and inst_sort env s = 
    case view_sort s of
        vo => s
      | va(t1,t2) => mk_ar_sort (inst_term env t1) (inst_term env t2)


fun pvariantt vd t = 
    case t of 
        Var(n,s) => 
        if mem n (List.map fst (HOLset.listItems vd))
        then pvariantt vd (Var(n ^ "'",s))
        else Var (n, s)
      | Fun(f,s,l) => Fun(f,s,List.map (pvariantt vd) l)
      | _ => t


fun fsymss s = 
    case s of
        ob => HOLset.empty String.compare
      | ar(d,c) => HOLset.union(fsymst d,fsymst c)
and fsymst t = 
    case t of
        Var(n,s) => fsymss s
      | Fun(_,s,l) => 
        let val argfs = List.foldr 
                            (fn (t,fs) => HOLset.union (fsymst t,fs))
                            (HOLset.empty String.compare)
                            l
        in HOLset.union(argfs,fsymss s)
        end
      | _ => HOLset.empty String.compare


fun fvt t = 
    case t of 
        Var(n,s) => HOLset.add (fvs s,(n,s)) 
      | Bound i => essps
      | Fun(f,s,tl) => 
        (case tl of 
             [] => essps
           | h :: t => HOLset.union 
                           (HOLset.union ((fvt h),(fvs s)), 
                            fvtl t))
and fvs s = 
    case s of 
        ob => essps
      | ar(t1,t2) => HOLset.union (fvt t1,fvt t2)
and fvtl tl = 
    case tl of 
        [] => essps
      | h :: t => HOLset.union (fvt h,fvtl t)




fun fxty i = 
    case i of 
       "<=>" => 100
      | "==>" => 200
      | "|" => 300
      | "&" => 400
      | "=" => 450
      | "==" => 450
      | "o" => 455
      | ":" => 460 (*900*)
      | "->" => 470 (*900*)
      | "+" => 500
      | "*" => 600
      | "^" => 700
      | "~" => 900
      | _ => ~1

type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict

type psymd = (string, (string * sort) list) Binarymap.dict

fun lookup_pred (pd:psymd) p = Binarymap.peek (pd,p)

fun lookup_fun (fd:fsymd) f = Binarymap.peek (fd,f)


val psyms0:psymd =
    List.foldr (fn ((p:string,l:(string * sort) list),d) =>
                   Binarymap.insert (d,p,l)) (Binarymap.mkDict String.compare)
               [("isgroup",[("G",mk_ob_sort),
                            ("m",mk_ar_sort
                                     (mk_fun0 "*" mk_ob_sort [mk_ob "G",mk_ob "G"]) (mk_ob "G")),
                            ("i",mk_ar_sort one (mk_ob "G")),
                            ("inv",mk_ar_sort (mk_ob "G") (mk_ob "G"))]),
                ("=",[("a",mk_ar_sort (mk_ob "A") (mk_ob "B")),
                      ("b",mk_ar_sort (mk_ob "A") (mk_ob "B"))]),
                ("==",[("A",ob_sort),("B",ob_sort)]),
                ("ispr",[("p1",ar(mk_ob "AB",mk_ob "A")),
                         ("p2",ar(mk_ob "AB",mk_ob "B"))]),
                ("iscopr",[("i1",ar(mk_ob "A",mk_ob "AB")),
                         ("i2",ar(mk_ob "B",mk_ob "AB"))]),
                ("iseq",[("e",ar(mk_ob "E",mk_ob "A")),
                         ("f",ar(mk_ob "A",mk_ob "B")),
                         ("g",ar(mk_ob "A",mk_ob "B"))]),
                ("iscoeq",[("e",ar(mk_ob "B",mk_ob "cE")),
                           ("f",ar(mk_ob "A",mk_ob "B")),
                           ("g",ar(mk_ob "A",mk_ob "B"))]),
                ("isexp",[("p1",ar(mk_ob "efs",mk_ob "A")),
                          ("p2",ar(mk_ob "efs",mk_ob "A2B")),
                          ("ev",ar(mk_ob "efs",mk_ob "B"))]),
                ("ismono",[("f",mk_ar_sort (mk_ob "A") (mk_ob "B"))]),
                ("ismem",[("x",mk_ar_sort (mk_const "1" mk_ob_sort) (mk_ob "A")),("a",mk_ar_sort (mk_ob "A0") (mk_ob "A"))]),
                ("is0",[("zero",ob)]),
                ("is1",[("one",ob)]),
                ("isN0",[("z0",mk_ar_sort (mk_ob "one") (mk_ob "N0")),("s0",mk_ar_sort (mk_ob "N0") (mk_ob "N0"))]),
                ("T",[]),("F",[])]


type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict



                  
val fsyms0:fsymd =  
    List.foldr 
        (fn ((p:string,(s:sort,l:(string * sort) list)),d) =>
            Binarymap.insert (d,p,(s,l)))
        (Binarymap.mkDict String.compare)
        [("N",(ob_sort,[])),
         ("0",(ob_sort,[])),
         ("1",(ob_sort,[])),
         ("id",(mk_ar_sort (mk_ob "A") (mk_ob "A"),
                [("A",ob_sort)])),
         ("to1",(mk_ar_sort (mk_ob "X") (mk_ob "one"),
                 [("X",ob_sort),("one",ob_sort)])),
         ("from0",(mk_ar_sort (mk_ob "zero") (mk_ob "X"),
                   [("zero",ob_sort),("X",ob_sort)])),
         ("o",(ar(mk_ob "A",mk_ob "C"),[("f",ar(mk_ob "B",mk_ob "C")),
                                        ("g",ar(mk_ob "A",mk_ob "B"))])),
         ("pa",(ar(mk_ob "X",mk_ob "AB"),
                [("p1",ar(mk_ob "AB",mk_ob "A")),
                 ("p2",ar(mk_ob "AB",mk_ob "B")),
                 ("f",ar(mk_ob "X",mk_ob "A")),
                 ("g",ar(mk_ob "X",mk_ob "B"))])),
         ("copa",(ar(mk_ob "AB",mk_ob "X"),
                  [("i1",ar(mk_ob "A",mk_ob "AB")),
                   ("i2",ar(mk_ob "B",mk_ob "AB")),
                   ("f",ar(mk_ob "A",mk_ob "X")),
                   ("g",ar(mk_ob "B",mk_ob "X"))])),
         ("eqind",(ar(mk_ob "X",mk_ob "E"),
                      [("e",ar(mk_ob "E",mk_ob "A")),
                       ("f",ar(mk_ob "A",mk_ob "B")),
                       ("g",ar(mk_ob "A",mk_ob "B")),
                       ("x",ar(mk_ob "X",mk_ob "A"))])),
         ("coeqind",(ar(mk_ob "cE",mk_ob "X"),
                      [("ce",ar(mk_ob "B",mk_ob "cE")),
                       ("f",ar(mk_ob "A",mk_ob "B")),
                       ("g",ar(mk_ob "A",mk_ob "B")),
                       ("x",ar(mk_ob "B",mk_ob "X"))])),
         ("tp",(ar(mk_ob "X",mk_ob "A2B"),
                [("p1",ar(mk_ob "efs",mk_ob "A")),
                 ("p2",ar(mk_ob "efs",mk_ob "A2B")),
                 ("ev",ar(mk_ob "efs",mk_ob "B")),
                 ("p1'",ar(mk_ob "AX",mk_ob "A")),
                 ("p2'",ar(mk_ob "AX",mk_ob "X")),
                 ("f",ar(mk_ob "AX",mk_ob "B"))])),
         ("s",(ar(mk_const "N" ob,mk_const "N" ob),[])),
         ("z",(ar(mk_const "1" ob,mk_const "N" ob),[])),
         ("Nind0",(ar(mk_ob "N0",mk_ob "X"),
                  [("z0",ar (mk_ob "one0",mk_ob "N0")),
                   ("s0",ar (mk_ob "N0",mk_ob "N0")),
                   ("x0",ar(mk_ob "one0",mk_ob "X")),
                   ("t",ar(mk_ob "X",mk_ob "X"))])),
          ("Nind",(ar(mk_const "N" ob,mk_ob "X"),
                  [("x0",ar(one,mk_ob "X")),
                   ("t",ar(mk_ob "X",mk_ob "X"))]))
        ]

(*

datatype ForP = fsym | psym

val fpdict0:(string,ForP) Binarymap.dict =
    foldr (fn ((n,forp),d) => Binarymap.insert(d,n,forp)) (Binarymap.mkDict String.compare) 
          [("=",psym),("T",psym),("F",psym),
           ("P",psym),("Q",psym),("R",psym),("S",psym),
           ("ismono",psym),("isgroup",psym),("ismem",psym),("areiso",psym),
           ("o",fsym),("id",fsym),
           ("to1",fsym),("from0",fsym),
           ("p1",fsym),("p2",fsym),("pa",fsym),("po",fsym),
           ("i1",fsym),("i2",fsym),("copa",fsym),("copo",fsym),
           ("eqo",fsym),("eqa",fsym),("coeqo",fsym),("coeqa",fsym),
           ("*",fsym),("+",fsym),("^",fsym),
           ("exp",fsym),("ev",fsym),("tp",fsym),
           ("eqinduce",fsym),("coeqinduce",fsym),("Nind",fsym)
           ]




val fpdict = ref fpdict0

*)


val fsyms = ref fsyms0
val psyms = ref psyms0


fun mk_fun f tl = 
    case lookup_fun (!fsyms) f of 
        NONE => raise TER ("mk_fun.function: " ^ f ^ " not found",[],tl)
      | SOME(s,l) => 
        let val vd = (match_tl essps (List.map (uncurry mk_var) l) tl emptyvd)
            val s' = inst_sort vd s
        in mk_fun0 f s' tl
        end

(*
fun insert_fsym s = fpdict:= Binarymap.insert(!fpdict,s,fsym) 
fun insert_psym s = fpdict:= Binarymap.insert(!fpdict,s,psym)
*)

fun is_fun sr = 
    case (Binarymap.peek (!fsyms,sr)) of 
        SOME _ => true
      | _ => false

fun is_pred sr =
    case (Binarymap.peek (!psyms,sr)) of
        SOME _ => true
      | _ => false


fun is_const sr = 
    case (Binarymap.peek (!fsyms,sr)) of 
        SOME (_,l) => if length l = 0 then true else false
      | _ => false


fun new_pred p tl = psyms := Binarymap.insert (!psyms,p,tl)

fun new_fun f (s,tl) = fsyms := Binarymap.insert (!fsyms,f,(s,tl))



(**********************************************************************
pretty printing
**********************************************************************)
(*
open smpp pp 

fun ppterm ss g t = 
    case view_term t of 
        vVar(n,s) => 
        if ss then paren 
                       (add_string n >> add_string " :" >>
                                   add_break (1,2) >> ppsort g s)
        else add_string n
      | vFun(f,s,[t1,t2]) => 
        if is_infix f then 
            case g of 
                LR(lg,rg) => 
                let 
                    val g1 = LR (lg, SOME (fxty f))
                    val g2 = LR (SOME (fxty f),rg)
                in 
                    if int_option_less (fxty f, lg) orelse int_option_leq (fxty f, rg) then 
                        add_string "(" >> 
                                   ppterm ss (LR (NONE, SOME (fxty f))) t1 >>  add_break(1,0) >> add_string f >> add_break(1,0) >>
                                   ppterm ss (LR (SOME (fxty f), NONE)) t2 >> add_string ")"
                    else 
                        ppterm ss g1 t1 >>  add_break(1,0) >> add_string f >> add_break(1,0) >>
                               ppterm ss g2 t2
                end
        else 
            if f = "pa" then 
                add_string "<" >> ppterm ss g t1 >> add_string " , " >> ppterm ss g t2 >> add_string ">"
            else
            add_string f >> paren (pr_list (ppterm ss g) (add_string "," >> add_break (1,0)) [t1,t2])
      | vFun(f,s,args) => 
        if length args = 0 then add_string f else
        add_string f >> paren (pr_list (ppterm ss g) (add_string "," >> add_break (1,0)) args)
      | vB i => add_string "B" >> paren (add_string (int_to_string i))
and ppsort g s =
    case view_sort s of
        vo => add_string "ob"
      | va(d,c) => 
        block HOLPP.INCONSISTENT 2 
              (ppterm false g d >> add_string " ->" >>
                      add_break(1,0) >> ppterm false g c)


fun PPsort printdepth _ st = let val s = ppsort (LR (NONE,NONE)) st
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPsort

val show_types = ref false
                     
fun PPterm printdepth _ t = let val s = ppterm (!show_types) (LR (NONE,NONE)) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end
*)

fun is_bound t = 
    case t of Bound i => true 
            | _ => false

fun ill_formed_fv (n,s) = 
    case s of ob => false
            | ar(d,c) => is_bound d orelse is_bound c

val ob_sort = mk_ob_sort
val ar_sort = mk_ar_sort

end
