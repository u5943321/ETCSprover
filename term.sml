structure term :> term = 
struct

datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Bound of int
    | Fun of string * sort * term list;

datatype term_view =
    vVar of string * sort
  | vB of int 
  | vFun of string * sort * term list

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

exception TER of string * sort list * term list 

(*
fun enclose a = "(" ^ a ^ ")";

fun conc_list sep l = 
    case l of 
        [] => ""
      | h :: t => sep ^ h ^ conc_list sep t

fun conc_list1 sep l = 
    case l of [] => ""
            | h :: t => h  ^ (conc_list sep t);


fun string_of_tl l = 
    case l of
        [] => ""
      | h :: t => 
        enclose (conc_list1 ","
                            (List.map string_of_term (h :: t)))
and string_of_term t = 
    case t of
        Var(n,s) => n
      | Fun(f,s,[t1,t2]) => 
        enclose 
            ((string_of_term t1) ^ " " ^ f ^ " " ^ 
             (string_of_term t2)) 
      | Fun(f,s,l) => 
        f ^ (string_of_tl l)
      | _ => ""
and string_of_sort s = 
    case s of 
        ob => "ob"
      | ar(A,B) => (string_of_term A) ^ "-->" ^ (string_of_term B)
*)


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

val mk_ob_sort = ob

fun mk_ar_sort t1 t2 = ar(t1,t2)

fun mk_ob a = Var(a,ob)

fun mk_ar a t1 t2 = Var(a,ar(t1,t2))

fun mk_ar0 a A B = Var(a,ar(mk_ob A,mk_ob B))

fun mk_var n s = Var(n,s)

fun mk_fun f s l = Fun(f,s,l)

fun mk_bound i = Bound i

fun mk_const n s = mk_fun n s []


val one = mk_fun "one" ob []
val zero = mk_fun "zero" ob []
val N = mk_fun "N" ob []
val z = mk_fun "z" (ar (one,N)) []
val s = mk_fun "s" (ar (N,N)) []


(*construct terms that appears in axioms*)

fun id A = if sort_of A = ob 
           then mk_fun "id" (ar(A,A)) [A]
           else raise TER ("id.wrong sort of input",[],[A])

fun to1 X = if sort_of X = ob
            then mk_fun "to1" (ar(X,one)) [X]
            else raise TER ("to1.wrong sort of input",[],[X])

fun from0 X = if sort_of X = ob then
                  mk_fun "form0" (ar(zero, X)) [X]
              else raise TER ("form0.wrong sort of input",[],[X])

fun po A B = if sort_of A = ob andalso 
                sort_of B = ob then mk_fun "*" ob [A,B]
             else raise TER ("po.wrong sort of input",[],[A,B]) 

fun pa f g = case (sort_of f, sort_of g) of 
                 (ar (C1,A), ar (C2,B)) => 
                 if C1 = C2
                 then mk_fun "pa" (ar(C1, po A B)) [f,g]
                 else raise TER ("pa.different domains",[],[f,g]) 
               | _ => raise TER ("pa.wrong sort of input",[],[f,g]) 

fun p1 A B = if sort_of A = ob andalso sort_of B = ob
             then mk_fun "p1" (ar(po A B,A)) [A,B]
             else raise TER ("p1.wrong sort of input",[],[A,B]) 


fun p2 A B = if sort_of A = ob andalso sort_of B = ob
             then mk_fun "p1" (ar(po A B,B)) [A,B]
             else raise TER ("p2.wrong sort of input",[],[A,B]) 

(*
fun copo A B = if sort_of A = ob andalso sort_of B = ob
               then mk_fun "+" (ar(A,B)) [A,B]
             else raise TER ("copo.wrong sort of input",[],[A,B]) 

fun copa f g = case (sort_of f, sort_of g) of 
                   (ar (A,C1), ar (B,C2)) =>
                   if C1 = C2 then mk_fun "copo" (ar(copo A B,C1)) [A,B] else raise TER ("copa.different codomains",[],[f,g])   | _ => raise TER ("copa.wrong sort of input",[],[f,g])

fun i1 A B = if sort_of A = ob andalso sort_of B = ob then 
                 mk_fun "i1" (ar(A,copo A B)) [A,B]
             else raise TER ("i1.wrong sort of input",[],[A,B])  


fun i2 A B = if sort_of A = ob andalso sort_of B = ob then 
                 mk_fun "i2" (ar(B,copo A B)) [A,B]
             else raise TER ("i2.wrong sort of input",[],[A,B])  

fun eqo f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then Fun("eqo",ob,[f,g])
                                                 else raise no_sort
                     | _ => raise no_sort)

fun eqa f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then Fun("eqa",ar(eqo f g,A2),[f,g])
                                                 else raise no_sort
                     | _ => raise no_sort)


fun coeqo f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then Fun("coeqo",ob,[f,g])
                                                 else raise no_sort
                     | _ => raise no_sort)

fun coeqa f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then Fun("coeqa",ar(B2,coeqo f g),[f,g])
                                                 else raise no_sort
                     | _ => raise no_sort)

fun exp A B = Fun("exp",ob,[A,B])

fun tp f =  (case sort_of f of 
                 (ar (P,C)) =>
                 (case P of (Fun ("*",ob,[A,B])) => 
                            Fun ("tp",ar(B, exp A C),[f])
                          | _ => raise no_sort) 
               | _ => raise no_sort) 

fun N_ind X x0 t = (case (sort_of X, sort_of x0, sort_of t) of 
                       (ob, ar (A,B), ar (C,D)) => if (A = one andalso B = X
                                                               andalso C = X
                                                               andalso D = X)
                                                   then Fun("N_ind",ar(N,X),[X,x0,t])
                                                 else raise no_sort
                     | _ => raise no_sort)

infix O
fun op O (f,g) = (case (sort_of f,sort_of g) of 
                       (ar (A,B1),ar (B2,C)) => if B1 = B2 then Fun("o",ar(A,C),[f,g])
                                                 else raise no_sort
                                     | _ => raise no_sort)
*)

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
        if m = n andalso eq_sort(s,s') then t2 
        else mk_var n (substs (V,t2) s')
      | vFun(f,s',tl) => mk_fun f (substs (V,t2) s') (List.map (substt (V,t2)) tl)
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
    case (s1,s2) of 
        (ob,ob) => EQUAL
      | (ob,_) => LESS
      | (_,ob) => GREATER
      | (ar dc1,ar dc2) => pair_compare term_compare term_compare (dc1,dc2)
and term_compare (t1,t2) = 
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

val emptyvd:(string * sort,term)Binarymap.dict = Binarymap.mkDict (pair_compare String.compare sort_compare)


fun mk_tenv l = 
    case l of 
        [] => emptyvd
      | ((n,s),t) :: l0 => Binarymap.insert(mk_tenv l0,(n,s),t)


fun pvariantt vd t = 
    case t of 
        Var(n,s) => 
        if mem n (List.map fst (HOLset.listItems vd))
        then Var (n ^ "'",s)
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
        ":" =>(* 460 *) 900
      | "->" =>(* 470 *) 900
      | "=" => 450
      | "==>" => 200
      | "<=>" => 100
      | "~" => 900
      | "&" => 400
      | "|" => 300
      | "*" => 600
      | "+" => 500
      | "^" => 700
      | "o" => 800
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
                                     (mk_fun "*" mk_ob_sort [mk_ob "G",mk_ob "G"]) (mk_ob "G")),
                            ("i",mk_ar_sort one (mk_ob "G")),
                            ("inv",mk_ar_sort (mk_ob "G") (mk_ob "G"))]),
                ("=",[("a",mk_ar_sort (mk_ob "A") (mk_ob "B")),
                      ("b",mk_ar_sort (mk_ob "A") (mk_ob "B"))])]


type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict


val fsyms0:fsymd =  
    List.foldr 
        (fn ((p:string,(s:sort,l:(string * sort) list)),d) =>
            Binarymap.insert (d,p,(s,l)))
        (Binarymap.mkDict String.compare)
        [("N",(mk_ob_sort,[])),
         ("0",(mk_ob_sort,[])),
         ("1",(mk_ob_sort,[])),
         ("id",(mk_ar_sort (mk_ob "A") (mk_ob "A"),
                [("A",mk_ob_sort)])),
         ("to1",(mk_ar_sort (mk_ob "X") one,
                 [("X",mk_ob_sort)])),
         ("from0",(mk_ar_sort zero (mk_ob "X"),
                   [("X",mk_ob_sort)])),
         ("o",(ar(mk_ob "A",mk_ob "C"),[("f",ar(mk_ob "B",mk_ob "C")),
                                        ("g",ar(mk_ob "A",mk_ob "B"))])),
         ("*",(ob,[("A",ob),("B",ob)])),
         ("+",(ob,[("A",ob),("B",ob)])),
         ("p1",(ar(mk_fun "*" ob [mk_ob "A",mk_ob "B"],mk_ob "A"),[("A",ob),("B",ob)])),
         ("p2",(ar(mk_fun "*" ob [mk_ob "A",mk_ob "B"],mk_ob "B"),[("A",ob),("B",ob)])),
         ("i1",(ar(mk_ob "A",mk_fun "+" ob [mk_ob "A",mk_ob "B"]),[("A",ob),("B",ob)])),
         ("i2",(ar(mk_ob "B",mk_fun "+" ob [mk_ob "A",mk_ob "B"]),[("A",ob),("B",ob)])),
         ("pa",(ar(mk_ob "X",mk_fun "*" ob [mk_ob "A",mk_ob "B"]),
                [("f",ar(mk_ob "X",mk_ob "A")),("g",ar(mk_ob "X",mk_ob "B"))])),
         ("copa",(ar(mk_fun "+" ob [mk_ob "A",mk_ob "B"],mk_ob "X"),
                [("f",ar(mk_ob "A",mk_ob "X")),("g",ar(mk_ob "B",mk_ob "X"))])),
         ("eqo",(ob,[("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("coeqo",(ob,[("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("eqa",(ar(mk_fun "eqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"],mk_ob "A"),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("coeqa",(ar(mk_ob "B",mk_fun "coeqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"]),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("eqinduce",(ar(mk_ob "X",mk_fun "eqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"]),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B")),
                  ("h",ar(mk_ob "X",mk_ob "A"))])),
         ("coeqinduce",(ar(mk_fun "coeqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"],mk_ob "X"),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B")),
                  ("h",ar(mk_ob "B",mk_ob "X"))])),
         ("exp",(ob,[("A",ob),("B",ob)])),
         ("tp",(mk_ar_sort (mk_ob "B") (mk_fun "exp" ob [mk_ob "A", mk_ob "C"]),
                [("f",ar(mk_fun "*" ob [mk_ob "A", mk_ob "B"],mk_ob "C"))])),
         ("ev",(mk_ar_sort 
                    (mk_fun "*" ob [mk_ob "A",mk_fun "exp" ob [mk_ob "A",mk_ob "B"]]) 
                    (mk_ob "B"),
                [("A",ob),("B",ob)])),
         ("s",(ar(mk_const "N" ob,mk_const "N" ob),[])),
         ("z",(ar(mk_const "1" ob,mk_const "N" ob),[])),
         ("Nind",(ar(mk_const "N" ob,mk_ob "X"),
                  [("x0",ar(mk_const "1" ob,mk_ob "X")),
                   ("t",ar(mk_ob "X",mk_ob "X"))]))
        ]



datatype ForP = fsym | psym

val fpdict0:(string,ForP) Binarymap.dict =
    foldr (fn ((n,forp),d) => Binarymap.insert(d,n,forp)) (Binarymap.mkDict String.compare) 
          [("=",psym),(*"\cong",psym*) ("T",psym),("F",psym),
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
val fsyms = ref fsyms0
val psyms = ref psyms0

fun insert_fsym s = fpdict:= Binarymap.insert(!fpdict,s,fsym) 
fun insert_psym s = fpdict:= Binarymap.insert(!fpdict,s,psym)


fun is_fun sr = 
    case (Binarymap.peek (!fpdict,sr)) of 
        SOME fsym => true
      | _ => false

fun is_pred sr =
    case (Binarymap.peek (!fpdict,sr)) of
        SOME psym => true
      | _ => false


fun is_const sr = 
    case (Binarymap.peek (!fsyms,sr)) of 
        SOME (_,l) => if l = [] then true else false
      | _ => false


fun new_pred p tl = psyms := Binarymap.insert (!psyms,p,tl)

fun new_fun f (s,tl) = fsyms := Binarymap.insert (!fsyms,f,(s,tl))


(**********************************************************************
pretty printing
**********************************************************************)
(*
open pp

fun ppterm ss g t = 
    case t of 
        Var(n,s) => 
        if ss then paren 
                       (add_string n >> add_string " :" >>
                                   add_break (1,2) >> ppsort g s)
        else add_string n
      | Fun(f,s,[t1,t2]) => 
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
      | Fun(f,s,args) => 
        if args = [] then add_string f else
        add_string f >> paren (pr_list (ppterm ss g) (add_string "," >> add_break (1,0)) args)
      | Bound i => add_string "B" >> paren (add_string (int_to_string i))
and ppsort g s =
    case s of
        ob => add_string "ob"
      | ar(d,c) => 
        block HOLPP.INCONSISTENT 2 
              (ppterm false g d >> add_string " ->" >>
                      add_break(1,0) >> ppterm false g c)

val show_types = ref false

fun PPsort printdepth _ st = let val s = ppsort (LR (NONE,NONE)) st
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val pps = PolyML.addPrettyPrinter PPsort
                     
fun PPterm printdepth _ t = let val s = ppterm (!show_types) (LR (NONE,NONE)) t 
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val ppt = PolyML.addPrettyPrinter PPterm

*)
end
