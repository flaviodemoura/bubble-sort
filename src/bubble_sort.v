(* begin hide *)
Require Import Arith List Lia Permutation.
Require Import Recdef.
Require Import ord_equiv.
Require Import perm_equiv.
(* end hide*)

(** A função [bubble] a seguir recebe uma lista de naturais como argumento, e percorre esta lista comparando elementos consecutivos: *)

Function bubble (l: list nat ) {measure length l} :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::y::l =>
      if x <=? y
      then x::(bubble (y::l))
            else y::(bubble (x::l))
            end.
Proof.
  - auto.
  - auto.
Defined.

(** Observe que esta função não é estruturalmente recursiva porque, por exemplo, a lista [(x::l)] não é uma sublista da lista original [(x::y::l)]. Neste caso, utilizamos [Function] para construir esta função e precisamos fornecer a medida que decresce em cada chamada recursiva, além de provar que esta medida efetivamente decresce a cada chamada recursiva. Por exemplo, [bubble (2::1::nil)] retorna a lista [(1::2::nil)].

 *)

Eval compute in bubble (2::1::nil).

(**

<<
   = 1 :: 2 :: nil
     : list nat
>>

*)

Eval compute in bubble (3::2::1::nil).

(**

<<
    = 2 :: 1 :: 3 :: nil
     : list nat
>>

*)

(** A função principal, ou seja, o algoritmo bubble sort propriamente dito, é dada pela função [bs] abaixo que recebe uma lista de naturais como argumento:

*)

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l => bubble (h::(bs l))
  end.           
(* begin hide *)
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)

(** Sabemos que aplicar a função [bubble] a uma lista qualquer, não necessariamente vai retornar uma lista ordenada, mas o lema [bubble_ord1] a seguir nos mostra que se o primeiro elemento é o único elemento fora de ordem em uma lista, ao aplicarmos a função [bubble], obtemos uma lista ordenada:
*)

Lemma bubble_ord1: forall l a, ord1 l -> ord1(bubble (a::l)).  
Proof.
  Admitted.
  
Lemma bs_ordena: forall l, ord1 (bs l).
Proof.
  induction l.
  - simpl. apply ord1_nil.
  - simpl. apply bubble_ord1. apply IHl.
Qed.

(** A seguir, mostraremos que o algoritmo bubblesort gera como saída uma permutação da lista de entrada:

 *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l.
  functional induction (bubble l).
  - apply perm_nil.
  - apply perm_skip. apply perm_nil.
  - apply perm_skip. apply IHl0.
  - apply perm_trans with (y::x::l0).
    + apply perm_swap.
    + apply perm_skip. apply IHl0.
Qed.

Lemma bubble_cons: forall l x, Permutation (bubble (x::l)) (x::(bubble l)) .
Proof.
Admitted.  

Lemma bubble_perm2: forall l l', Permutation l l' -> Permutation (bubble l) (bubble l').
Proof.
  induction 1.
  - rewrite bubble_equation. apply perm_nil.
  - apply perm_trans with (x::bubble l).
    + apply bubble_cons.
    + apply perm_trans with (x::bubble l').
      * apply perm_skip. apply IHPermutation.
      * apply Permutation_sym. apply bubble_cons.
  - Admitted.

  
Lemma bs_permuta: forall l, Permutation l (bs l).
Proof.
  induction l.
  - simpl. apply perm_nil.
  - simpl. apply perm_trans with (bubble (a::l)).
    + apply bubble_perm.
    + apply bubble_perm2. apply perm_skip. apply IHl.
Qed.

    


    
Theorem bs_correto: forall l, ord1 (bs l) /\ Permutation l (bs l).
Proof.
  
