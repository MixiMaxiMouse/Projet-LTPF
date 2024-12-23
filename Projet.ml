(* -------------------------------------------------------------------------------------------------*
 *                                                                                                  *
 *                        ___  ___  ____     ____________  __ _________  ____                       * 
 *                       / _ \/ _ \/ __ \__ / / __/_  __/ / //_  __/ _ \/ __/                       *
 *                      / ___/ , _/ /_/ / // / _/  / /   / /__/ / / ___/ _/                         *
 *                     /_/  /_/|_|\____/\___/___/ /_/   /____/_/ /_/  /_/                           *
 *                                                                                                  *
 *                                                                                                  *
 *                        Maxime Bossant, Erwan Poncin, Maxence Maury                               *
 *                                                                                                  *
 * -------------------------------------------------------------------------------------------------*)


(* Exercice 1.1.1 Définir une hiérarchie de types OCaml permettant de représenter tous les programmes 
admis par la description ci-dessus.*)


type variable = A | B | C | D;;

type constant = Zero | Un;;



type expr =
  | Var of variable
  | Const of constant
;;

type instruction =
  | Skip
  | Assign of (variable * expr)
  | Seq of (instruction * instruction)
  | If of (variable * instruction * instruction)
  | While of (variable * instruction)
;;



(*
a := 1 ;
b := 1 ;
c := 1 ;
while(a) {
   if(c) {
      c := 0 ;
      a := b
   } else {
      b := 0 ;
      c := a
   }
}


let example =
Seq (
  Assign (A, Cons Un),
  Seq(
    Assign (B,Cons Un),
    Seq(
      Assign (C, Cons Un),
      While(
        Var A,
        If (
          Var C,
          Seq(
            Assign (C, Cons Zero),
            Assign (A, Var B)
          ),
          Seq(
            Assign (B, Cons Zero),
            Assign (C, Var A)
          )
        )
      )  
    )  
  )   
)
;;
*)


(* -------------------------------------------------------------------------------------------------*)
(*                                              LES GRAMMAIRES                                      *)

(*** Exercice 1.1.2 Donner une grammaire décrivant le langage WHILEb--

WHILEB--
   P ::= I
   
   I ::= 
      |V ':=' E
      |I ';' I
      |'w' '(' V ')' '{' I '}'
      |'i' '(' V ')' '{' I '}' '{' I '}'
      |skip
   
   E::=V | C
   
   V::='a'∣'b'∣'c'∣'d'
*)

(*** Exercice 1.1.3 Grammaire non récursive gauche
   
   P ::= I

     X := I S
     
   I ::=
      |V ':=' E
      |'w' '(' V ')' '{' I '}' S
      |i '(' V ')' '{' I '}' '{' I '}' S 
      |'skip' S

   S ::= ';' I S | epsilon
      
   E ::= V | C

   C ::= '0' | '1'
   
   V ::= 'a'|'b'|'c'|'d'
   
*)

(*** Exercice 1.1.4

WHILEB
   P ::= I
   
   I ::= 
      |V ':=' E
      |I ';' I
      |'w' '(' E ')' '{' I '}'
      |'i' '(' E ')' '{' I '}' '{' I '}'
      |skip

   C ::= '0' | '1'
   V ::= 'a' | 'b' | 'c' | 'd'
   A ::= C | V
   E ::= E '+' T | T
   T ::= T '.' F | F
   F ::= '!' F | A | '(' E ')'
     
   Grammaire non récursive :

   P ::= I
   
   I ::=
      |V ':=' E S
      |'w' '(' E ')' '{' I '}' S
      |i '(' E ')' '{' I '}' '{' I '}' S 
      |'skip' S

   S ::= ';' I S | epsilon
      
   C ::= '0' | '1'
   V ::= 'a' | 'b' | 'c' | 'd'
   A ::= C | V
   E ::= T E'
   E' ::= '+' T E' | epsilon 
   T ::= F T'
   T' ::= '.' F T' | epsilon 
   F ::= '!' F | A | '(' E ')'
*)

(* -------------------------------------------------------------------------------------------------*)


(** 1.2 Sémantique naturelle (SN), dite aussi sémantique opérationnelle à grands pas*)

(*** Exercice 1.2.1 Écrire, en utilisant le format précédent, les règles de SN pour un programme de la forme if expr then P else Q.*)

(*
                             Q
   [expr] = false      s1 -------> s2          
----------------------------------------
        if expr then P else Q
     s1 ----------------------> s2



                            P
   [expr] = true      s1 -------> s2
--------------------------------------
        if expr then P else Q
     s1 ----------------------> s2
 *)



(* -------------------------------------------------------------------------------------------------*)
(* -------------------------------------------------------------------------------------------------*)
(* -------------------------------------------------------------------------------------------------*)
(*                                      PARSER DE WHILEB--                                          *)

(* 2 Partie principale *)

(** 2.1 Implémentation de l’analyseur simple *)

(*** Exercice 2.1.1 Implémenter un analyseur syntaxique en OCaml pour la grammaire obtenue du langage WHILEb-- .*)

#use "anacomb.ml";;
  

let p_C l =
  l |>
  
  terminal_res (fun c ->
      match c with
      | '0' -> Some Zero
      | '1' -> Some Un
      | _ -> None)
;;

let p_V l =
  l |>
  
  terminal_res (function
      | 'a' -> Some A
      | 'b' -> Some B
      | 'c' -> Some C
      | 'd' -> Some D
      | _ -> None)
;;

(* E ::= V | C *)
let p_E l =
  l |>
  
  (* Variable *)
  (p_V ++> (fun v -> epsilon_res (Var v)))
  +|
  (* Constante *)
  (p_C ++> (fun c -> epsilon_res (Const c)))
;;



let rec p_I l =
  l |>
     
  (* Assign : V ':=' E S *)
  (p_V ++> (fun v ->
       terminal ':' --> terminal '=' -+> p_E ++> (fun e ->
           p_S (Assign (v, e)))))

  +|

  (* While : 'w' '(' V ')' '{' I '}' S *)
  (terminal 'w' --> terminal '(' -+> p_V ++> (fun v ->
       terminal ')' --> terminal '{' -+> p_I ++> (fun i ->
           terminal '}' -+> p_S (While (v, i)))))

  +|

  (*  i '(' V ')' '{' I '}' '{' I '}' S *)
  (terminal 'i' --> terminal '(' -+> p_V ++> (fun v ->
      terminal  ')' --> terminal '{' -+> p_I ++> (fun i_then ->
          terminal '}' --> terminal '{' -+> p_I ++> (fun i_else ->
               terminal '}' -+> p_S (If (v, i_then, i_else))))))

  +|

  (* Skip *)
  (terminal 's' --> terminal 'k' --> terminal 'i' --> terminal 'p' -+> p_S Skip)

and

  p_S acc l =
  
  l |>
  (terminal ';' -+> p_I ++> (fun i ->
      p_S i ++> (fun s ->
           epsilon_res (Seq (acc, s)))))
  
  +|
  
  epsilon_res acc
;;



(* Nettoyage *)

let rec nettoyage l =
  match l with
  | [] -> l
  | c::l1 -> match c with
    | ' ' | '\n' | '\r' | '\t' -> nettoyage l1
    | _ -> c::(nettoyage l1)
;;

(* Parsing d'un programme complet *)
let p_P l =
  let nettoye = nettoyage l in
  p_I nettoye
;;

(* Tests *)
let input1 = list_of_string
    "a := 1;
     b := a"
let result1 = p_P input1;;

let input2 = list_of_string
    "a := 1;
     b := 0;
     c := 1;
     d := 0"
let result2 = p_P input2;;

let input3 = list_of_string
    "a := 1;
     w(a){
        a := 0
     }"
let result3 = p_P input3;;

let input4 = list_of_string
    "c := 1;
     i(c){
        a := 1
     }{
        b := 1
     }"
let result4 = p_P input4;;

let input5 = list_of_string
    "a := 1;
     b := 1;
     c := 1;
     w(a){
        i(c){
            c := 0;
            a := b
        }{
            b := 0;
            c := a
        }
     }"
let result5 = p_P input5;;

let input6 = list_of_string
    "skip;
     a := 1"
let result6 = p_P input6;;

let input7 = list_of_string
    "a := 0;
     w(a){
        b := 1
     }"
let result7 = p_P input7;;


(* -------------------------------------------------------------------------------------------------*)
(*                                          PARSER DE WHILEB                                       *)

(***Exercice 2.1.3  Compléter l’analyseur pour accepter le langage d’expressions considéré à la fin de la *)
(*partie 1.1.*)


type bexpr =
  | And of bexpr * bexpr
  | Or of bexpr * bexpr
  | Not of bexpr
  | BConst of constant
  | BVar of variable
;;

type binstr =
  | BSkip
  | BAssign of (variable * bexpr)
  | BSeq of (binstr * binstr)
  | BIf of (bexpr * binstr * binstr)
  | BWhile of (bexpr * binstr)
;;



let b_C l =
  l |>
  
  terminal_res (fun c ->
      match c with
      | '0' -> Some Zero
      | '1' -> Some Un
      | _ -> None)
;;

let b_V l =
  l |>
  
  terminal_res (function
      | 'a' -> Some A
      | 'b' -> Some B
      | 'c' -> Some C
      | 'd' -> Some D
      | _ -> None)
;;

(* A ::= V | C *)
let b_A l =
  l |>
  
  (* Variable *)
  (b_V ++> (fun v -> epsilon_res (BVar v)))
  +|
  (* Constante *)
  (b_C ++> (fun c -> epsilon_res (BConst c)))
;;


let rec b_E l =
  l |>
  
  (* E ::= T E' *)
  (b_T ++> (fun t -> b_E' t))
  
and
  
  (*E' ::= '+' T E' | epsilon *)
  b_E' acc l =
  l |>
  
  (terminal '+' -+> b_T ++> (fun t -> b_E' t ++> (fun e -> epsilon_res (And (acc, e)))))
  +|
  (epsilon_res acc)
  
and
  
  (* T ::= F T' *)
  b_T l=
  l |>
  
  (b_F ++>( fun f -> b_T' f))
  
and
  
  (* T' ::= '.' F T' | epsilon *)
  b_T' acc l =
  l |>
  
  (terminal '.' -+> b_F ++>( fun f -> b_T' f ++> (fun t -> epsilon_res (Or (acc, f)))))
  +|
  (epsilon_res acc)
  
and
  
  (* F ::= '!' F | A | '(' E ')' *)
  b_F l =
  l |>
  
  (terminal '!' -+> b_F ++> (fun f -> epsilon_res (Not f)))
  
  +|
  
  (b_A)
  
  +|
  
  (terminal '(' -+> b_E ++> (fun e ->
       terminal ')' -+> epsilon_res (e)))
;;



(*
     I ::=
      |V ':=' E S
      |'w' '(' E ')' '{' I '}' S
      |i '(' E ')' '{' I '}' '{' I '}' S 
      |'skip' S
*)

let rec b_I l =
  l |>
  
  (* Assign : V ':=' E S *)
  (b_V ++> (fun v ->
       terminal ':' --> terminal '=' -+> b_E ++> (fun e ->
           b_S (BAssign (v, e)))))
  +|
  (* While : 'w' '(' E ')' '{' I '}' S *)
  (terminal 'w' --> terminal '(' -+> b_E ++> (fun e ->
       terminal ')' --> terminal '{' -+> b_I ++> (fun i ->
           terminal '}' -+> b_S (BWhile (e, i)))))
  +|
  (*  i '(' E ')' '{' I '}' '{' I '}' S *)
  (terminal 'i' --> terminal '(' -+> b_E ++> (fun e ->
       terminal  ')' --> terminal '{' -+> b_I ++> (fun i_then ->
           terminal '}' --> terminal '{' -+> b_I ++> (fun i_else ->
               terminal '}' -+> b_S (BIf (e, i_then, i_else))))))

  +|
  
  (* Skip *)
  (terminal 's' --> terminal 'k' --> terminal 'i' --> terminal 'p' -+> b_S BSkip)
  
and

  b_S acc l =
  
  l |>
  (terminal ';' -+> b_I ++> (fun i ->
       b_S i ++> (fun s ->
           epsilon_res (BSeq (acc, s)))))
  
  +|
  
  epsilon_res acc
;;

(* Parsing d'un programme complet *)
let b_P l =
  let nettoye = nettoyage l in
  b_I nettoye
;;

(* Jeu de tests pour binstr *)

let test1_input = list_of_string "a := a+b.!1+!1";;
let (resultat1, reste1) = b_P test1_input;;
let test1_expected = BAssign (A, And (BVar A, And (Or (BVar B, BConst Zero), Not (BConst Un))));;

let test2_input = list_of_string "a := 1; b := (a+(b.0))+(!1)";;
let (resultat2, reste2) = b_P test2_input;;
let test2_expected = BSeq
    (BAssign (A, BConst Un),
     BAssign
      (B, And (And (BVar A, Or (BVar B, BConst Zero)), Not (BConst Un))));;

let test3_input = list_of_string "w(a){ a := 0 }";;
let (resultat3, reste3) = b_P test3_input;;
let test3_expected = BWhile (BVar A, BAssign (A, BConst Zero));;

let test4_input = list_of_string "skip";;
let (resultat4, reste4) = b_P test4_input;;
let test4_expected = BSkip;;

(** programme faux, renvoie un échec*)
let test5_input = list_of_string "a := ;";;

let test6_input = list_of_string "a := 1; w(a){ i(b){ a := 0 }{ b := 1 } }; skip";;
let (resultat6, reste6) = b_P test6_input;;
let test6_expected =
  BSeq (
    BAssign (A, BConst Un),
    BSeq (
      BWhile (
        BVar A,
        BIf (
          BVar B,
          BAssign (A, BConst Zero),
          BAssign (B, BConst Un)
        )
      ),
      BSkip
    )
  );;


(* Assertions pour valider les tests *)
let _ =
  assert (resultat1 = test1_expected);
  assert (resultat2 = test2_expected);
  assert (resultat3 = test3_expected);
  assert (resultat4 = test4_expected);
  assert (resultat6 = test6_expected);
;;

(* -------------------------------------------------------------------------------------------------*)
(*                                        EVALUATION DES AST                                        *)

(*
Exercice 2.2.1 
Écrire un programme OCaml qui, étant donné un AST WHILEb simplifié et un état
Initial, rend l’état final obtenu après exécution tel que spécifié par la 
sémantique SN. *) 

type state = int list;;

(** La fonction get x s rend la valeur de x dans s.
    Elle rend 0 par défaut, par exemple si la variable
    n'est pas définie/initialisée    *)
let rec get : int -> state -> int =
  fun x s ->
  match x, s with
  | 0, v::_  -> v
  | _, _::l1 -> get (x - 1) l1
  | _, _     -> 0
;;

(** La mise à jour d'une variable v par un nouvel entier n dans un état s
    s'écrit 'update s v n'
    Cette fonction n'échoue jamais et écrit la valeur à sa place même
    si elle n'est pas encore définie dans l'état *)
let rec update : state -> int -> int -> state =
  fun s v n ->
    match v, s with
    | 0, a :: l1 -> n :: l1
    | 0, []      -> n :: []
    | _, a :: l1 -> a :: (update l1 (v - 1) n)
    | _, []      -> 0 :: (update [] (v - 1) n)
;;

let rec evalB : bexpr -> state -> bool =
  fun b s ->
  match b with
  | And (b1, b2) -> (evalB b1 s) && (evalB b2 s)
  | Or (b1, b2) -> (evalB b1 s) || (evalB b2 s)
  | Not b1 -> not (evalB b1 s)
  | BConst n -> if (n = Un) then true else false
  | BVar v -> match v with
    | A -> if ((get 0 s) = 0) then false else true
    | B -> if ((get 1 s) = 0) then false else true
    | C -> if ((get 2 s) = 0) then false else true
    | D -> if ((get 3 s) = 0) then false else true
;; 

let rec evalI : binstr -> state -> state =
  fun i s ->
  match i with
  | BSkip -> s
  | BSeq (i1, i2) -> evalI i2 (evalI i1 s)
  | BIf (b, i1, i2) -> if (evalB b s) then (evalI i1 s) else (evalI i2 s)
  | BWhile (b, i1) -> if (evalB b s) then (evalI i (evalI i1 s)) else s
  | BAssign (v, b) -> match v with
    | A -> update s 0 (if (evalB b s) then 1 else 0) 
    | B -> update s 1 (if (evalB b s) then 1 else 0)  
    | C -> update s 2 (if (evalB b s) then 1 else 0)  
    | D -> update s 3 (if (evalB b s) then 1 else 0) 
;;

(* tests de l'évaluation des AST sur les programmes tests du parser de WHILEB *)
evalI resultat1 [0; 0; 0; 0];;
evalI resultat1 [1; 1; 1; 1];;

evalI resultat2 [0; 0; 0; 0];;
evalI resultat2 [1; 1; 1; 1];;

evalI resultat3 [0; 0; 0; 0];;
evalI resultat3 [1; 1; 1; 1];;

evalI resultat4 [0; 0; 0; 0];;
evalI resultat4 [1; 1; 1; 1];;

evalI resultat6 [0; 0; 0; 0];;
evalI resultat6 [1; 1; 1; 1];;

(* Pour écrire votre propre test, décommentez les lignes ci-dessous et écrivez votre programme 
dans le langage WHILEB dans l'expression "mon_programme" et l'état de départ du programme dans 
   l'expression "mon_state" *)


(* en l'état, ces lignes ne renvoient une erreur car le programme est pas en langage WHILEB *)

(*
let mon_programme = list_of_string "ecrire programme ici";; (* écrire le programme ici *)
let mon_state = [0; 0; 0; 0];; (* écrire l'état de départ du programme ici *)

let (resultat, reste) = b_P mon_programme;;
evalI resultat mon_state;;
*)



 (*
    ___________   __
   / ____/  _/ | / /
  / /_   / //  |/ / 
 / __/ _/ // /|  /  
/_/   /___/_/ |_/   
                    
*)
