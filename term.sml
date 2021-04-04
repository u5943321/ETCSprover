structure term :> term = 
struct

datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
 (*   | Param of string * sort * (string * sort) list*)
    | Bound of int
    | Fun of string * sort * term list;

fun dest_arrow (ar (S,T)) = (S,T)
  | dest_arrow _  = raise Fail "dest_arrow : Error"

fun dom a = #1 (dest_arrow a)

fun cod a = #2 (dest_arrow a)

val one = Fun ("one",ob,[])
val zero = Fun ("zero",ob,[])        
val N = Fun ("N",ob,[])              
val z = Fun ("z",ar (one,N),[])           
val s = Fun ("s",ar (N,N),[])                        

exception no_sort 

fun dest_pair (Fun ("po",s,[A,B])) = (A,B)
  | dest_pair _ =  raise Fail "dest_pair : Error"

fun sort_of t = 
    case t of Var (_,s) => s
            | Fun (_,s,_) => s 
            | _ => ob 

fun id A = if sort_of A = ob then Fun("id",ar(A,A),[A])
           else raise no_sort

fun to1 X = if sort_of X = ob then Fun ("to1",ar(X, one), [X]) 
            else raise no_sort

fun from0 X = if sort_of X = ob then Fun ("form0",ar(zero, X),[X])
              else raise no_sort

fun po A B = if sort_of A = ob andalso sort_of B = ob then Fun ("po",ob,[A,B]) 
             else raise no_sort 

fun pa f g = (case (sort_of f, sort_of g) of 
                       (ar (C1,A), ar (C2,B)) => 
                       if C1 = C2 then Fun ("pa",ar(C1, po A B),[f,g])
                       else raise no_sort
                     | _ => raise no_sort)

fun p1 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p1",ar(po A B,A),[A,B])
             else raise no_sort 

fun p2 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p2",ar(po A B,B),[A,B])
             else raise no_sort 

fun copo A B = if sort_of A = ob andalso sort_of B = ob then Fun ("po",ar(A,B),[A,B]) 
             else raise no_sort 

fun copa f g = (case (sort_of f, sort_of g) of 
                       (ar (A,C1), ar (B,C2)) => if C1 = C2 then Fun ("copo",ar(copo A B,C1),[A,B]) 
                                                 else raise no_sort
                     | _ => raise no_sort)

fun i1 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("i1",ar(A,copo A B),[A,B])
             else raise no_sort 

fun i2 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("i2",ar(B,copo A B),[A,B])
             else raise no_sort 

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
                 (case P of (Fun ("po",ob,[A,B])) => 
                            Fun ("tp",ar(B, exp B C),[f])
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



end
