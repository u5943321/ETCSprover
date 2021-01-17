datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Param of (string * sort) * (string * sort) list
    | Bound of int
    | Fun of (string * sort) * term list;




val one = Fun ("one",[])
val zero = Fun ("zero",[])        
val N = Fun ("N",[])              
val z = Fun ("z",[])           
val s = Fun ("s",[])                        

exception no_sort 

fun po_i A B = Fun ("po",[A,B]) 

fun pa_i f g = Fun ("pa",[f,g])

fun copo_i A B = Fun ("copo",[A,B]) 

fun copa_i f g = Fun ("copa",[f,g])

fun eqo_i f g = Fun ("eqo",[f,g])

fun eqa_i f g = Fun ("eqa",[f,g])

fun coeqo_i f g = Fun ("coeqo",[f,g])

fun coeqa_i f g = Fun ("coeqa",[f,g])

fun exp_i A B = Fun ("exp",[A,B])

fun tp_i f = Fun ("tp",[f])

fun N_ind_i X x0 t = Fun ("N_ind",[X,x0,t])

fun dest_arrow (ar (S,T)) = (S,T)
  | dest_arrow _  = raise Fail "dest_arrow : Error"

fun source a = #1 (dest_arrow a)

fun target a = #2 (dest_arrow a)

(*more of these functions*)

fun dest_pair (Fun ("po",[A,B])) = (A,B)
  | dest_pair _ =  raise Fail "dest_pair : Error"

fun sort_of t =  
    case t of Fun ("one",[]) => ob
            | Fun ("to1",[X]) => ar (X,one)
            | Fun ("zero",[]) => ob
            | Fun ("from0",[X]) => ar (zero,X) 
            | Fun ("o",[g,f]) => (case (sort_of g, sort_of f) of 
                                      (ar (_,C), ar (A,_)) => ar (A,C)
                                    | _ => raise no_sort)
            | Fun ("po",[A,B]) => ob
            | Fun ("p1",[A,B]) => ar (po_i A B,A)                                           
            | Fun ("p2",[A,B]) => ar (po_i A B,B)
            | Fun ("pa",[f,g]) => (case (sort_of f, sort_of g) of 
                                       (ar (C1,A), ar (C2,B)) => ar (C1,po_i A B)
                                     | _ => raise no_sort) 
            | Fun ("exp",[A,B]) => ob 
            | Fun ("tp",[f]) => let val (P,C) = dest_arrow f 
                                    val (A,B) = dest_pair P
                                in ar (A,exp_i B C)
                                end
            | Fun ("copo",[A,B]) => ob
            | Fun ("i1",[A,B]) => ar (A, copo_i A B)                                       
            | Fun ("i2",[A,B]) => ar (B, copo_i A B)
            | Fun ("copa",[f,g]) => (case (sort_of f, sort_of g) of 
                                       (ar (A,C1), ar (B,C2)) => ar (copo_i A B,C1)
                                     | _ => raise no_sort) 
            | Fun ("eqa",[f,g]) => (case (sort_of g, sort_of f) of 
                                      (ar (A1,B1), ar (A2,B2)) => ar (eqo_i f g,A1)
                                    | _ => raise no_sort) 
            | Fun ("eqo",[f,g]) => ob 
            | Fun ("coeqa",[f,g]) => (case (sort_of g, sort_of f) of 
                                      (ar (A1,B1), ar (A2,B2)) => ar (B1,coeqo_i f g)
                                    | _ => raise no_sort) 
            | Fun ("coeqo",[f,g]) => ob 
            | Fun ("N",[]) => ob
            | Fun ("z",[]) => ar (one,N) 
            | Fun ("s",[]) => ar (N,N)
            | Fun ("N_ind",[X,x0,t]) => ar (N,X) 
            | _ => ob
(*do sort check within fun , rewrite everything about sort check as let in *)

fun to1 X = if sort_of X = ob then Fun ("to1",[X]) else raise no_sort

fun from0 X = if sort_of X = ob then Fun ("form0",[X]) else raise no_sort

fun po A B = if sort_of A = ob andalso sort_of B = ob then po_i A B
             else raise no_sort 

fun pa f g = (case (sort_of f, sort_of g) of 
                       (ar (C1,A), ar (C2,B)) => if C1 = C2 then pa_i f g
                                                 else raise no_sort
                     | _ => raise no_sort)

fun p1 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p1",[A,B])
             else raise no_sort 

fun p2 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p2",[A,B])
             else raise no_sort 

fun copo A B = if sort_of A = ob andalso sort_of B = ob then copo_i A B
             else raise no_sort 

fun copa f g = (case (sort_of f, sort_of g) of 
                       (ar (A,C1), ar (B,C2)) => if C1 = C2 then copa_i f g
                                                 else raise no_sort
                     | _ => raise no_sort)

fun i1 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("i1",[A,B])
             else raise no_sort 

fun i2 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("i2",[A,B])
             else raise no_sort 

fun eqo f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then eqo_i f g
                                                 else raise no_sort
                     | _ => raise no_sort)

fun eqa f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then eqa_i f g
                                                 else raise no_sort
                     | _ => raise no_sort)


fun coeqo f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then coeqo_i f g
                                                 else raise no_sort
                     | _ => raise no_sort)

fun coeqa f g = (case (sort_of f, sort_of g) of 
                       (ar (A1,B1), ar (A2,B2)) => if (A1 = A2 andalso B1 = B2)
                                                   then coeqa_i f g
                                                 else raise no_sort
                     | _ => raise no_sort)

fun tp f =  (case sort_of f of 
                 (ar (P,C)) =>
                 (case P of (Fun ("po",[A,B])) => 
                            tp_i f
                          | _ => raise no_sort) 
               | _ => raise no_sort) 

fun N_ind X x0 t = (case (sort_of X, sort_of x0, sort_of t) of 
                       (ob, ar (A,B), ar (C,D)) => if (A = one andalso B = X
                                                               andalso C = X
                                                               andalso D = X)
                                                   then N_ind_i X x0 t
                                                 else raise no_sort
                     | _ => raise no_sort)

infix O
fun O_i f g = Fun ("o",[f,g])
fun op O (f,g) = (case (sort_of g, sort_of f) of 
                       (ar (B2,C), ar (A,B1)) => if B1 = B2 then O_i f g
                                                 else raise no_sort
                                     | _ => raise no_sort)


datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form;     


(**fill the mk of Conn**)

fun mk_conj f1 f2 = Conn ("and",[f1,f2])

fun mk_or f1 f2 = Conn ("or",[f1,f2])

fun mk_conj f1 f2 = Conn ("or",[f1,f2])



(*Length of a list*)
local fun length1 (n, [ ]) = n
| length1 (n, x::l) = length1 (n+1, l)
in fun length l = length1 (0,l) end;

(*The elements of a list satisfying the predicate p.*)

fun filter p [] = []
| filter p (x::xs) = if p(x) then x :: filter p xs else filter p xs;


infix mem; (*membership in a list*)

fun x mem [] = false
| x mem (y::l) = (x=y) orelse (x mem l);

infix ins; (*insertion into list if not already there*)
fun x ins xs = if x mem xs then xs else x::xs;

fun repeat x 0 = []
| repeat x n = x :: (repeat x (n-1));

fun accumulate f ([], y) = y
| accumulate f (x::xs, y) = accumulate f (xs, f(x,y));

(*Look for a pair (X,z) in environment, return [z] if found, else [] 
fun lookup ((X,s), []) = []
  | lookup ((X,s), ((Y,s1),(Z,s2))::env) = if X = (Y:string) then [(Z,s2)] else lookup((X,s),env);
*)
exception ERROR of string;

(*Operationson terms and formulae*)

fun replace_term (u,new) t = 
    if t = u then new else
    case t of Fun (a,ts) => Fun(a, map (replace_term(u,new)) ts)
            | _ => t; 

(*abstraction*)
fun abstract t =
let fun abs i (Pred(a,ts)) = Pred(a, map (replace_term (t, Bound i)) ts)
| abs i (Conn(b,As)) = Conn(b, map (abs i) As)
| abs i (Quant(q,b,s,A)) = Quant(q, b,s, abs (i+1) A)
in abs 0 end;


(*Replace (Bound 0) in formula with t (containing no bound vars).*)
fun subst_bound t =
let fun subst i (Pred(a,ts)) = Pred(a, map (replace_term (Bound i, t)) ts)
| subst i (Conn(b,As)) = Conn(b, map (subst i) As)
| subst i (Quant(q,b,s,A)) = Quant(q, b,s, subst (i+1) A)
in subst 0 end;

(*SYNTAX: SCANNING, PARSING, AND DISPLAY*)
(*Scanning a list of characters into a list of tokens*)
datatype token = Key of string | Id of string;
fun is_char(l,c,u) = ord l <= ord c andalso ord c <= ord u;


fun is_letter_or_digit c =
is_char(#"A",c,#"Z") orelse is_char(#"a",c,#"z") orelse is_char(#"0",c,#"9");

(*Scanning of identifiers and keywords*)
fun token_of a = if a mem ["ALL","EXISTS"] then Key(a) else Id(a);



fun scan_ident (front, c::cs) =
    if is_letter_or_digit c
    then scan_ident (c::front, cs)
    else (token_of (implode(rev front)), c::cs)
  | scan_ident (front, []) = (token_of (implode(rev front)), []);


(*Scanning, recognizing --> and <->, skipping blanks, etc.*)
fun scan (front_toks, []) = rev front_toks (*end of char list*)
  (*long infix operators*)
  | scan (front_toks, (#"-")::(#"-")::(#">")::cs) = scan (Key"-->" ::front_toks, cs)
  | scan (front_toks, (#"<")::(#"-")::(#">")::cs) = scan (Key"<->" ::front_toks, cs)
  (*blanks, tabs, newlines*)
  | scan (front_toks, (#" ")::cs) = scan (front_toks, cs)
  | scan (front_toks, (#"\t")::cs) = scan (front_toks, cs)
  | scan (front_toks, (#"\n")::cs) = scan (front_toks, cs)
  | scan (front_toks, c::cs) =
    if is_letter_or_digit c then scannext(front_toks, scan_ident([c], cs))
    else scan (Key(str c)::front_toks, cs)
and scannext (front_toks, (tok, cs)) = scan (tok::front_toks, cs);

(*Parsing a list of tokens*)
fun apfst f (x,toks) = (f x, toks);
(*Functions for constructing results*)
fun cons x xs = x::xs;
fun makeFun fu ts = Fun(fu,ts);
fun makePred id ts = Pred(id,ts);
fun makeNeg A = Conn("~", [A]);
fun makeConn a A B= Conn(a, [A,B]);
fun makeQuant q b s A = Quant(q, b,s, abstract (Fun(b,[])) A);

(*Repeated parsing, returning the list of results *)
fun parse_repeat (a,parsefn) (Key(b)::toks) = (* a<phrase>...a<phrase> *)
    if a=b then parse_repeat1 (a,parsefn) toks
    else ([], Key(b)::toks)
  | parse_repeat (a, parsefn) toks = ([], toks)
and parse_repeat1 (a,parsefn) toks = (* <phrase>a...a<phrase> *)
    let val (u,toks2) = parsefn toks
    in apfst (cons u) (parse_repeat (a, parsefn) toks2) end;

fun rightparen (x, Key")"::toks) = (x, toks)
  | rightparen _ = raise ERROR "Symbol ) expected";

(a,ob) (a, ar (A,B))

a: ob  a: A -> B


(*modifty the prec table*)
(**)

fun parse_term (Id(a)::Key"("::toks) =
    apfst (makeFun a) (rightparen (parse_repeat1 (",", parse_term) toks))
  | parse_term (Id(a)::toks) = (Fun(a,[]), toks)
  | parse_term (Key"?"::Key"("::Id(a)::Key","::Key"ob"::Key")"::toks) = 
    (Var (a,ob), toks)
  | parse_term (Key"?"::Key"("::Id(a)::Key","::Key"ar"::Key"("::Id(A)::Key","::Id(B)::Key")"::Key")"::toks) = 
    (Var (a,ar(Fun(A,[]), Fun(B,[]))), toks)
  | parse_term _ = raise ERROR "Syntax of term";

(*above modified*)

(*Precedence table*)
fun prec_of "~" = 4
  | prec_of "&" = 3
  | prec_of "|" = 2
  | prec_of "<->" = 1
  | prec_of "-->" = 1
  | prec_of _ = ~1 (*means not an infix*);


(*Parsing of formulae; prec is the precedence of the operator to the left;
parsing stops at an operator with lower precedence*)
fun parse (Key"ALL" ::Key"("::Id(a)::Key","::Key"ob"::Key")"::Key"."::toks) =
    apfst (makeQuant "ALL" a ob) (parse toks)
  | parse (Key"EXISTS"::Key"("::Id(a)::Key","::Key"ob"::Key")"::Key"."::toks) =
    apfst (makeQuant "EXISTS" a ob) (parse toks)
  | parse toks = parsefix 0 (parse_atom toks)
and parsefix prec (A, Key(co)::toks) =
    if prec_of co < prec then (A, Key(co)::toks)
    else parsefix prec
                  (apfst (makeConn co A)
                         (parsefix (prec_of co) (parse_atom toks)))
  | parsefix prec (A, toks) = (A, toks)
and parse_atom (Key"~"::toks) = apfst makeNeg (parse_atom toks)
  | parse_atom (Key"("::toks) = rightparen (parse toks)
  | parse_atom (Id(pr)::Key"("::toks) =
    apfst (makePred pr) (rightparen (parse_repeat1 (",", parse_term) toks))
  | parse_atom (Id(pr)::toks) = (Pred(pr,[]), toks)
  | parse_atom _ = raise ERROR "Syntax of formula";



fun parse_end (x, []) = x
  | parse_end (_, _::_) = raise ERROR "Extra characters in formula";

fun read a = parse_end (parse (scan([], explode a)));

(*Printing: conversion of terms/formulae to strings*)
fun enclose a = "(" ^ a ^ ")";
fun conc_list sep [] = ""
  | conc_list sep (b::bs) = (sep ^ b) ^ (conc_list sep bs);

fun conc_list1 sep (b::bs)=b^ (conc_list sep bs);
(*why it is okay?*)

a: ob 

a: A ==> B

fun stringof_term (Param(a,_)) = a
  | stringof_term (Var (a,s)) = "?"  ^ a ^ ":" ^ stringof_sort s
  | stringof_term (Bound i) = "B." ^ str #"i"
  | stringof_term (Fun (a,ts)) = a ^ stringof_args ts
and stringof_args [] = ""
  | stringof_args ts = enclose (conc_list1 "," (map stringof_term ts))
and stringof_sort ob = "ob"
  | stringof_sort (ar (A,B)) = "ar" ^ "(" ^ (stringof_term A) ^ "," ^ (stringof_term B) ^ ")"

(*modified*)

fun max(m,n) : int = if m>n then m else n;

fun stringof_form prec (Pred (a,ts)) = a ^ stringof_args ts
  | stringof_form prec (Conn("~", [A])) = "~" ^ stringof_form (prec_of "~") A
  | stringof_form prec (Conn(C, [A,B])) =
    let val stringf = stringof_form (max(prec_of C, prec));
        val Z = stringf A ^ " " ^ C ^ " " ^ stringf B
    in if (prec_of C <= prec) then (enclose Z) else Z
    end
  | stringof_form prec (Quant(q,b,s,A)) =
    let val B = subst_bound (Fun(b,[])) A
        val Z = q^" "^b ^ ":" ^ stringof_sort s ^ ". " ^ stringof_form 0 B
    in if prec>0 then (enclose Z) else Z
    end
  | stringof_form prec _ = raise ERROR "stringof_form: Bad formula";
(*modified*)

val stringof = stringof_form 0;

(*UNIFICATION*)
exception UNIFY;
(*Naive unification of terms containing no bound variables*)


(*Look for a pair (X,z) in environment, return [z] if found, else [] *)
fun lookup ((X,(s:sort)), []) = []
  | lookup ((X,s), ((Y,(s1:sort)),(z:term))::env) = if X = (Y:string) then [z] else lookup((X,s),env);
(*
fun lookup (X, []) = []
| lookup (X, (Y,z)::env) = if X = (Y:string) then [z] else lookup(X,env); *)

fun chasevar (Var (a,s)) env = (*Chase variable assignments*)
    (case lookup((a,s),env) of
         u ::_ => chasevar u env
       | [] => Var (a,s))
  | chasevar t env = t;

(*what if an arrow and an object has the same name*)

(*unification work list item*)

datatype uwli = us of sort * sort 
              | ut of term * term
              | uv of (string * sort) * term

open Binarymap
              
fun unify_w (wl,env) = 
    case wl of 
        [] => env
      | us (s1,s2) :: rest => unify_sorts s1 s2 rest env
      | ut (t1,t2) :: rest => unify_term t1 t2 rest env
and unify_term t1 t2 rest env = 
    case (chasevar t1,chasevar t2) of
        (Param(a,_), Param(b,_)) =>
        if a=b then unify_w (rest,env) else raise UNIFY
      | (Fun((a,s1),ts), Fun((b,s2),us)) =>
        if a = b andalso length ts = length us then 
            unify_w (us (s1,s2) ::  ListPair.map ut (ts,us) @ rest,env)
        else raise UNIFY
      | (Var v, t)  => unify_w (uv (v,t) ::rest,env)
      | (t, Var v) => unify_w (uv (v,t) ::rest,env)
and chasevar (Var (a,s)) env = (*Chase variable assignments*)
    (case Binarymap.peek(env,a) of
         SOME u => chasevar u env
       | NONE => Var (a,s))
  | chasevar t env = t
and unify_sorts s1 s2 rest env = 
    case (s1,s2) of
         (ob,ob) => unify_w (rest,env)
      | (ar (A,B), ar (C,D)) => unify_w (ut (A,C) :: ut (B,D) :: rest,env)
      | _ => raise UNIFY 

fun unify_terms ([],[], env) = env
  | unify_terms (t::ts, u::us, env) =
    let fun chasevar (Var (a,s)) = (*Chase variable assignments*)
            (case lookup((a,s),env) of
                 u::_ => chasevar u 
                | [] => Var (a,s))
          | chasevar t = t;
        fun unify_var ((a,s), t) = (*unification with var*)
            let fun occs (Fun(_,ts)) = occsl ts
                  | occs (Param(_,bs)) = 
                    occsl (map Var bs)
                  | occs (Var (b,s')) = a=b andalso s = s' 
                                        orelse occsl(lookup((b,s'),env))
                  | occs _ = false
                and occsl [] = false
                  | occsl(t::ts) = occs t orelse occsl ts
            in if t = Var (a,s) then 
                   let val env' = unify_sorts
                   env
               else if occs t then raise UNIFY else ((a,s),t)::env
            end
        and unify_term (Var (a,s), t) = unify_var ((a,s), t)
          | unify_term (t, Var (a,s)) = unify_var ((a,s), t)
          | unify_term (Param(a,_), Param(b,_)) = 
            if a=b then env else raise UNIFY
          | unify_term (Fun(a,ts), Fun(b,us)) =
            if a=b then unify_terms (ts,us,env) else raise UNIFY
          | unify_term _ = raise UNIFY
    in unify_terms (ts, us, unify_term (chasevar t, chasevar u)) end
  | unify_terms _ = raise UNIFY
  and unify_sorts ([],[],env) = env 
    | unify_sorts  = (r::rs,s::ss,env)



(*Unification of atomic formulae*)
fun unify (Pred(a,ts), Pred(b,us), env) =
    if a=b then unify_terms(ts,us,env) else raise UNIFY
  | unify _ = raise UNIFY;


(*Accumulate all Vars in the term (not Vars attached to a Param).*)
fun vars_in_term (Var a, bs) = a ins bs
  | vars_in_term (Fun(_,ts), bs) = accumulate vars_in_term (ts,bs)
  | vars_in_term (_, bs) = bs;

(*Instantiate a term by an environment*)
fun inst_term env (Fun(a,ts)) = Fun(a, map (inst_term env) ts)
  | inst_term env (Param(a,bs)) =
    Param(a, accumulate vars_in_term (map (inst_term env o Var) bs, []))
  | inst_term env (Var a) =
    (case lookup(a,env) of
         u::_ => inst_term env u
       | [] => Var a)
  | inst_term env t = t;



(*INFERENCE: GOALS AND PROOF STATES: GOALS AND PROOF STATES*)
datatype side = Left | Right;
type entry = int * side * form;
type goal = entry list;
type goaltable = goal list;


fun inst_form [] A = A
  | inst_form env (Pred(a,ts)) = Pred(a, map (inst_term env) ts)
  | inst_form env (Conn(b,As)) = Conn(b, map (inst_form env) As)
  | inst_form env (Quant(q,b,s,A)) = Quant(q, b,s, inst_form env A);

fun inst_goal env [] = []
  | inst_goal env ((m,si,A)::G) = (m, si, inst_form env A) :: inst_goal env G;
fun inst_goals [] Gs = Gs
  | inst_goals env Gs = map (inst_goal env) Gs : goaltable;

(*Accumulate over all terms in a formula*)
fun accum_form f (Pred(_,ts), bs) = accumulate f (ts, bs)
  | accum_form f (Conn(_,As), bs) = accumulate (accum_form f) (As, bs)
  | accum_form f (Quant(_,_,_,A), bs) = accum_form f (A,bs);

(*Accumulate over all formulae in a goal*)
fun accum_goal f ([], bs) = bs
  | accum_goal f ((_,_,A)::G, bs) = accum_goal f (G, f(A,bs));

val vars_in_form = accum_form vars_in_term;

val vars_in_goal = accum_goal vars_in_form;


(*Accumulate all Params*)
fun params_in_term (Param (a,bs), pairs) = (a,bs) ins pairs
  | params_in_term (Fun(_,ts), pairs) = accumulate params_in_term (ts, pairs)
  | params_in_term (_, pairs) = pairs;
val params_in_form = accum_form params_in_term;
val params_in_goal = accum_goal params_in_form;


(*Returns (As,Bs),preserving order of elements
As = Left entries, Bs = Right entries *)
fun split_goal G =
    let fun split (As,Bs, []: goal) = (As,Bs)
          | split (As,Bs, (_,Left,A)::H) = split (A::As,Bs, H)
          | split (As,Bs, (_,Right,B)::H) = split (As, B::Bs, H)
    in split([], [], rev G) end;

fun is_pred (Pred _) = true
  | is_pred _ = false;

(*Solve the goal (A|-A’) by unifying A with A’, Left and Right atomic formulae.
Returns list [ (A,env) ] if successful, otherwise []. *)
fun solve_goal G =
    let fun findA ([], _) = [] (*failure*)
          | findA (A::As, Bs) =
            let fun findB [] = findA (As,Bs)
                  | findB (B::Bs) = [ (A, unify(A,B,[])) ]
                                    handle UNIFY => findB Bs
            in findB Bs end
        val (As,Bs) = split_goal G
    in findA(filter is_pred As, filter is_pred Bs) end;


(*Insert goals into a goaltable. For each solved goal (A,env),
accumulates the formula (in reverse) and instantiates all other goals.*)
fun insert_goals ([], As, tab) = (As,tab)
  | insert_goals (G::Gs, As, tab) =
    case solve_goal G of
        (A,env)::_ => (*instantiate other goals*)
        insert_goals (inst_goals env Gs,
                      (inst_form env A) :: As,
                      inst_goals env tab)
      | [] => insert_goals (Gs, As, G::tab);


fun stringof_sy (Pred(a,_)) = a
  | stringof_sy (Conn(a,_)) = a
  | stringof_sy (Quant(q,_,_,_)) = q;
fun stringof_side Right = ":right"
  | stringof_side Left = ":left";


(*Generation of new variable names*)
local
    fun make_letter n = str (chr(ord(#"a")+n));
    fun make_varname (n,tail) =
        if n<26 then make_letter n ^ tail
        else make_varname (n div 26, make_letter(n mod 26) ^ tail);
    val varcount = ref 1
in
fun gensym() = (varcount := !varcount+1; make_varname (!varcount,""))
and init_gensym() = varcount := 1
end;


(*The "cost" of reducing a connective*)
fun cost (_, Conn("~", _)) = 1 (*a single subgoal*)
  | cost (Left, Conn("&", _)) = 1
  | cost (Right, Conn("|", _)) = 1
  | cost (Right, Conn("-->", _)) = 1
  | cost (Right, Quant("ALL",_,_,_)) = 1
  | cost (Left, Quant("EXISTS",_,_,_)) = 1
  | cost (Right, Conn("&", _)) = 2 (*case split: 2 subgoals*)
  | cost (Left, Conn("|", _)) = 2
  | cost (Left, Conn("-->", _)) = 2
  | cost (_ , Conn("<->", _)) = 2
  | cost (Left, Quant("ALL",_,_,_)) = 3 (*quantifier expansion*)
  | cost (Right, Quant("EXISTS",_,_,_)) = 3 (*quantifier expansion*)
  | cost _ = 4 ; (*no reductions possible*)
fun paircost (si,A) = (cost(si,A), si, A);

(*Insertion into a list, ordered by sort keys. *)
fun insert less =
    let fun insr (x, []) = [x]
          | insr (x, y::ys) = if less(y,x) then y :: insr (x,ys) else x::y::ys
    in insr end;
(*Insert an entry into a goal, in correct order *)
fun entry_less ((m,_,_): entry, (n,_,_): entry) = m<n;
val insert_early = insert entry_less;


(*Quantified formulae are put back at end -- they are used in a cycle*)
fun entry_lesseq ((m,_,_): entry, (n,_,_): entry) = m<=n;
val insert_late = insert entry_lesseq;
(*Extend the goal G by inserting a list of (side,form) pairs*)
fun new_goal G pairs = accumulate insert_early (map paircost pairs, G);
(*Extend the goal G, making a list of goals*)
fun new_goals G pairslist = map (new_goal G) pairslist;
exception REDUCE;

(*Reduce the pair using the rest of the goal (G) to make new goals*)
fun reduce_goal (pair, G) =
    let val goals = new_goals G;
        fun vars_in A = vars_in_goal (G, vars_in_form(A,[]));
        fun subparam A = subst_bound (Param((gensym(),ob), vars_in A)) A;
        fun subvar A = subst_bound (Var (gensym(),ob)) A;
        fun red(_,Right,Conn("~", [A])) = goals[[(Left,A)]]
          | red(_,Left, Conn("~", [A])) = goals[[(Right,A)]]
          | red(_,Right,Conn("&", [A,B])) = goals[[(Right,A)], [(Right,B)]]
          | red(_,Left, Conn("&", [A,B])) = goals[[(Left,A),(Left,B)]]
          | red(_,Right,Conn("|", [A,B])) = goals[[(Right,A),(Right,B)]]
          | red(_,Left, Conn("|", [A,B])) = goals[[(Left,A)], [(Left,B)]]
          | red(_,Right,Conn("-->", [A,B])) = goals[[(Left,A),(Right,B)]]
          | red(_,Left, Conn("-->", [A,B])) = goals[[(Right,A)], [(Left,B)]]
          | red(_,Right,Conn("<->", [A,B])) =
            goals[[(Left,A),(Right,B)], [(Right,A),(Left,B)]]
          | red(_,Left, Conn("<->", [A,B])) =
            goals[[(Left,A),(Left,B)], [(Right,A),(Right,B)]]
          | red(_,Right,Quant("ALL",_,_,A)) = goals[[(Right, subparam A)]]
          | red(_,Left, Quant("ALL",_,_,A)) =
            [ insert_early (paircost(Left, subvar A), insert_late(pair,G)) ]
          | red(_,Right,Quant("EXISTS",_,_,A)) =
            [ insert_early (paircost(Right, subvar A), insert_late(pair,G)) ]
          | red(_,Left, Quant("EXISTS",_,_,A)) = goals[[(Left, subparam A)]]
          | red _ = raise REDUCE
    in red pair end;
