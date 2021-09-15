



val _ = new_fun "P1" (ar_sort (po (mk_ob "A") (mk_ob "B")) (mk_ob "A"),[("A",ob_sort),("B",ob_sort)])

val _ = new_fun "P2" (ar_sort (po (mk_ob "A") (mk_ob "B")) (mk_ob "B"),[("A",ob_sort),("B",ob_sort)])

val _ = new_fun "PROD" (ar_sort (mk_ob "X") (po (mk_ob "A") (mk_ob "B")),
[("f",ar_sort (mk_ob "X") (mk_ob "A")),("g",ar_sort (mk_ob "X") (mk_ob "B"))])


val PROD_def = new_ax 
“!A B X f:X->A g:X->B fg:X->A * B.P1(A,B) o fg = f & P2(A,B) o fg = g <=> 
 fg = PROD(f,g)”


val _ = new_fun "TP" (ar_sort (mk_ob "B") (exp (mk_ob "A") (mk_ob "C")),
                       [("f",ar_sort (po (mk_ob "A") (mk_ob "B")) (mk_ob "C"))])

val _ = new_fun "EV" (ar_sort (po (mk_ob "A") (exp (mk_ob "A") (mk_ob "B"))) (mk_ob "B"),[("A",ob_sort),("B",ob_sort)])

val TP_def = new_ax 
“!A X B f:A * X ->B fbar:X->exp(A,B). 
 EV(A,B) o PROD(P1(A,X),fbar o P2(A,X)) = f <=> fbar = TP(f)”

fun TP f = mk_fun "TP" [f]

val _ = new_fun "ALL" (ar_sort (exp (mk_ob "X") two) two,[("X",ob_sort)])

val ALL_def = new_ax
“!X Y pxy:X * Y -> 2 y:1-> Y.ALL(X) o TP(pxy) o y = true <=>
 !x:1->X. pxy o PROD(x,y) = true”

val ALL_def' = new_ax
“!X px:X -> 2.ALL(X) o TP(px o P1(X,1)) = true <=>
 !x:1->X. px o x = true”

fun ALL X = mk_fun "ALL" [X]

val _ = new_fun "EX" (ar_sort (exp (mk_ob "X") two) two,[("X",ob_sort)])

val EX_def = new_ax
“!X Y pxy:X * Y -> 2 y:1-> Y.EX(X) o TP(pxy) o y = true <=>
 ?x:1->X. pxy o PROD(x,y) = true”

fun EX X = mk_fun "EX" [X]

val CONJ_ex = proved_th $
e0
cheat
(form_goal 
“?CONJ.!pred1 pred2.CONJ o PROD(pred1,pred2) = true <=> 
 pred1 = true & pred2 = true”)

val CONJ_def =  CONJ_ex |> eqT_intro
                        |> iffRL |> ex2fsym "CONJ" [] |> C mp (trueI [])

val CONJ = mk_fun "CONJ" []

val DISJ_ex = proved_th $
e0
cheat
(form_goal 
“?DISJ.!pred1 pred2.DISJ o PROD(pred1,pred2) = true <=> 
 pred1 = true | pred2 = true”)

val DISJ_def =  DISJ_ex |> eqT_intro
                        |> iffRL |> ex2fsym "DISJ" [] |> C mp (trueI [])

val DISJ = mk_fun "DISJ" []

val IMP_ex = proved_th $
e0
cheat
(form_goal 
“?IMP.!pred1 pred2.IMP o PROD(pred1,pred2) = true <=> 
 (pred1 = true ==> pred2 = true)”)

val IMP_def =  IMP_ex |> eqT_intro
                      |> iffRL |> ex2fsym "IMP" [] |> C mp (trueI [])

val IMP = mk_fun "IMP" []


val IFF_ex = proved_th $
e0
cheat
(form_goal 
“?IFF.!pred1 pred2.IFF o PROD(pred1,pred2) = true <=> 
 (pred1 = true <=> pred2 = true)”)

val IFF_def =  IFF_ex |> eqT_intro
                      |> iffRL |> ex2fsym "IFF" [] |> C mp (trueI [])

val IFF = mk_fun "IFF" []

val NEG_ex = proved_th $
e0
cheat
(form_goal 
“?NEG.!pred.NEG o pred = true <=> 
 ~(pred = true)”)

val NEG_def =  NEG_ex |> eqT_intro
                      |> iffRL |> ex2fsym "NEG" [] |> C mp (trueI [])

val NEG = mk_fun "NEG" []

fun mk_o a1 a2 = mk_fun "o" [a1,a2]

fun PROD f g = mk_fun "PROD" [f,g]

fun dom f = fst $ dest_ar (sort_of f)

fun cod f = snd $ dest_ar (sort_of f)

val distr_PROD = proved_th $
e0
cheat
(form_goal
“!A B X f:X->A g:X->B P a:P->X.PROD(f o a, g o a) = PROD(f,g) o a”)

fun split_input t (n:string,s:sort) = (var(n,s),var(n,s),refl t) 

fun dest_o t = 
    case view_term t of 
        vFun("o",s,[t1,t2]) => (t1,t2)
      | _ => raise ERR ("not a composition",[],[t],[])

fun pred_of f = 
    case (view_form f) of
        vPred(_,_) =>
        (*assumed that f is some pred o x = true*)
        (fst $ dest_eq f,frefl f)
      | vConn("&",[f1,f2]) =>
        let val (pred1,th1) = pred_of f1
            val (pred2,th2) = pred_of f2
        in (mk_o CONJ (PROD pred1 pred2),CONJ_def |> allE pred1 |> allE pred2 |> GSYM)
        end
      | vConn("|",[f1,f2]) =>
        let val (pred1,th1) = pred_of f1
            val (pred2,th2) = pred_of f2
        in (mk_o DISJ (PROD pred1 pred2),DISJ_def |> allE pred1 |> allE pred2 |> GSYM)
        end
      | vConn("==>",[f1,f2]) =>
        let val (pred1,th1) = pred_of f1
            val (pred2,th2) = pred_of f2
        in (mk_o IMP (PROD pred1 pred2),
            GSYM IMP_def |> allE pred1 |> allE pred2)
        end
      | vConn("<=>",[f1,f2]) =>
        let val (pred1,th1) = pred_of f1
            val (pred2,th2) = pred_of f2
        in (mk_o IFF (PROD pred1 pred2),
            GSYM IFF_def |> allE pred1 |> allE pred2)
        end
      | vQ("!",x,s0,b) =>
        let val (p0,th0) = pred_of b 
            val (lhs,rhs) = dest_dimp (concl th0)
            val tosplit = fst $ dest_eq rhs
            val X = snd $ dest_ar s0
            val (y,p,th) = split_input (fst $ dest_eq rhs) (x,s0)
            val Y = dom y
            val rhs = dest_eq (concl th)
        in (p,GSYM ALL_def |> allE X |> allE Y |> allE p |> allE y)
        end
      | vQ("?",x,s0,b) =>
        let val (p0,th0) = pred_of b 
            val (lhs,rhs) = dest_dimp (concl th0)
            val tosplit = fst $ dest_eq rhs
            val X = snd $ dest_ar s0
            val (y,p,th) = split_input (fst $ dest_eq rhs) (x,s0)
            val Y = dom y
            val rhs = dest_eq (concl th)
        in (p,GSYM EX_def |> allE X |> allE Y |> allE p |> allE y)
        end
      | _ => raise simple_fail "ill_formed formula"
input : !m n. char(lt) o (m,n) = t | char(le) o (n,m) = t
output: (pred, |- !m. (pred o m = t <=> !n. char(lt) o (m,n) = t | char(le) o (n,m) = t))
