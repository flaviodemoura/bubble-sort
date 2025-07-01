(* begin hide *)
Require Import Arith List Lia.
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
  | h::l' => bubble (h::(bs l'))
  end.           
(* begin hide *)
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)

(** Sabemos que aplicar a função [bubble] a uma lista qualquer, não necessariamente vai retornar uma lista ordenada, mas o lema [bubble_ord1] a seguir nos mostra que se o primeiro elemento é o único elemento fora de ordem em uma lista, ao aplicarmos a função [bubble], obtemos uma lista ordenada:
*)

Lemma bubble_ord_ord: forall l, ord1 l -> bubble l = l.
Proof.
  intros l H. induction H.
  - rewrite bubble_equation. reflexivity.
  - rewrite bubble_equation. reflexivity.
  - rewrite bubble_equation. apply leb_correct in H. rewrite H. rewrite IHord1. reflexivity.
Qed.

(** O lema a seguir consiste em uma propriedade do predicado [le_all], e portanto poderia ter sido colocado no arquivo [ord_equiv]. No entanto, por simplicidade, o deixaremos aqui:

*)

Lemma le_all_cons: forall l x y, x <= y -> x <=* l -> x <=* (y::l).
Proof.
  intros l x y Hle Hall. unfold le_all in *.
  intros y' Hin. simpl in Hin. destruct Hin.
  - subst. assumption.
  - apply Hall. assumption.
Qed.

Lemma bubble_le_all: forall l a a0, a <= a0 -> a <=* l -> a <=* bubble (a0 :: l).
Proof.
  induction l.
  - intros a a0 Hle Hall. rewrite bubble_equation. unfold le_all. intros y Hin. apply in_inv in Hin. destruct Hin.
    + subst. assumption.
    + inversion H.
  - intros a1 a0 Hle Hall. rewrite bubble_equation. destruct (a0 <=? a).
    + apply le_all_cons.
      * assumption.
      * apply IHl.
        ** unfold le_all in Hall. apply Hall. apply in_eq.
        ** unfold le_all in *. intros y H. apply Hall. simpl. right. assumption.
    + apply le_all_cons.
      * unfold le_all in Hall. apply Hall. apply in_eq.
      * apply IHl.
        ** assumption.
        ** unfold le_all in *. intros y H. apply Hall. simpl. right. assumption.
Qed.

Lemma le_all_ord: forall l a, ord1 (a::l) -> a <=* l.
Proof.  
Admitted.

Lemma bubble_ord1: forall l a, ord1 l -> ord1(bubble (a::l)).  
Proof.
  induction l.
  - intros a H. rewrite bubble_equation. apply ord1_one.
  - intros a0 H. rewrite bubble_equation. destruct (a0 <=? a) eqn:Hle.
    + rewrite bubble_ord_ord.
      * apply ord1_all.
        ** apply leb_complete in Hle. assumption.
        ** assumption.
      * assumption.
    + apply ord1_equiv_ord2. apply ord2_all.
      * apply bubble_le_all.
        ** apply leb_complete_conv in Hle. lia.
        ** apply le_all_ord. assumption.
      * apply ord1_equiv_ord2. apply IHl. inversion H; subst.
        ** apply ord1_nil.
        ** assumption.
Qed.                      

(**

Os dois lemas a seguir, apresentam provas (parciais) alternativas à prova do lema anterior, e portanto constituem atividades que completaremos apenas se houver tempo.

*)

Lemma bubble_ord1': forall l a, ord1 l -> ord1(bubble (a::l)).  
Proof.
  intros l a H. induction H.
  - rewrite bubble_equation. apply ord1_one.
  - rewrite bubble_equation. destruct (a <=? x) eqn: H.
    + rewrite bubble_equation. apply ord1_all.
      * apply leb_complete. assumption.
      * apply ord1_one.
    + rewrite bubble_equation. apply ord1_all.
      * apply leb_complete_conv in H. lia.
      * apply ord1_one.
  - rewrite bubble_equation.
  Admitted.

Lemma bubble_ord1'': forall l a, ord1 l -> ord1(bubble (a::l)).  
Proof.
  intros l a.
  functional induction (bubble (a::l)).
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
  intro l. functional induction (bubble l).
  - intro x. auto.
  - intro x0. rewrite bubble_equation. destruct (x0 <=? x).
    + auto.
    + rewrite bubble_equation. constructor.
  - intros x0. rewrite bubble_equation. destruct (x0 <=? x).
    + constructor. apply IHl0.
    + apply perm_trans with (x :: x0 :: bubble (y :: l0)).
      * constructor. apply IHl0.
      * constructor.
  - intro x0. apply perm_trans with (bubble (x0 :: y :: x :: l0)).
    + apply perm_trans with (x0 :: x :: y :: l0).
      * apply Permutation_sym. apply bubble_perm.
      * apply perm_trans with  (x0 :: y :: x :: l0).
        ** repeat constructor.
        ** apply bubble_perm.
    + rewrite bubble_equation. destruct (x0 <=? y).
      * constructor. apply IHl0.
      * apply perm_trans with (y :: x0 :: bubble (x :: l0)).
        ** constructor. apply IHl0.
        ** constructor.
Qed.

Lemma bubble_perm2: forall l l', Permutation l l' -> Permutation (bubble l) (bubble l').
Proof.
  induction 1.
  - rewrite bubble_equation. apply perm_nil.
  - apply perm_trans with (x::bubble l).
    + apply bubble_cons.
    + apply perm_trans with (x::bubble l').
      * apply perm_skip. apply IHPermutation.
      * apply Permutation_sym. apply bubble_cons.
  - apply perm_trans with (y::x::l).
    + apply Permutation_sym. apply bubble_perm.
    + apply perm_trans with (x::y::l).
      * constructor.
      * apply bubble_perm.
  - apply perm_trans with (bubble l').
    + apply IHPermutation1.
    + apply IHPermutation2.
Qed.  

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
  
