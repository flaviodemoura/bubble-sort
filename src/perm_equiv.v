
(* begin hide *)
Require Import Arith List.
Require Export Permutation.
(* end hide *)

(**

%\noindent% onde o predicado [Permutation] é definido pelas regras a seguir:

%\begin{mathpar}
 \inferrule*[Right={$(perm\_nil)$}]{~}{Permutation\ nil\ nil} \and \inferrule*[Right={$(perm\_skip)$}]{Permutation\ l\ l'}{Permutation\ (x :: l)\ (x :: l')} \\ \inferrule*[Right={$(perm\_swap)$}]{~}{Permutation\ (y :: x :: l)\ (x :: y :: l)} \\ \inferrule*[Right={$(perm\_trans)$}]{Permutation\ l\ l' \and Permutation\ l'\ l''}{Permutation\ l\ l''}
\end{mathpar}%
%\noindent% onde $x$, $y$, $l$, $l'$ e $l''$ são variáveis universais.

O código Coq correspondente a essas regras é listado a seguir:

<<
 Inductive Permutation (A : Type) : list A -> list A -> Prop :=
  | perm_nil : Permutation nil nil
  | perm_skip : forall (x : A) (l l' : list A),
                Permutation l l' ->
                Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                Permutation (y :: x :: l)
                  (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.
>>

Alternativamente, a lista [l] é uma permutação da lista [l'] se ambas possuem os mesmos elementos. A implementação dessa ideia é feita baseada no número de ocorrência de cada elemento na lista. Assim, na definição a seguir, [num_oc x l] retorna o número de ocorrências do elemento [x] na lista [l]:

*)

Fixpoint num_oc x l := 
  match l with
    | nil => 0
    | h :: tl =>
      if x =? h then S(num_oc x tl) else  num_oc x tl 
  end.

(**

A definição [equiv] a seguir, expressa que a lista [l] é uma permutação da lista [l'] se ambas possuem o mesmo número de ocorrências de qualquer elemento:

*)

Definition equiv l l' := forall n:nat, num_oc n l = num_oc n l'.

(* begin hide *)
Lemma perm_to_equiv: forall l l', Permutation l l' -> equiv l l'.
Proof.
  intros l l' H. induction H.
  - unfold equiv. reflexivity.
  - unfold equiv in *. intro n. simpl. destruct (n =? x).
    + rewrite IHPermutation. reflexivity.
    + apply IHPermutation.
  - unfold equiv in *. intro n; simpl. destruct (n =? x).
    + destruct (n =? y); reflexivity.
    + destruct (n =? y); reflexivity.
  - unfold equiv in *. intro n. rewrite IHPermutation1. rewrite IHPermutation2. reflexivity.
Qed.

Lemma equiv_nil: forall l, equiv nil l -> l = nil.
Proof.                                                
  induction l.
  - intro H. reflexivity.
  - intro H. unfold equiv in H. specialize (H a). simpl in H. rewrite Nat.eqb_refl in H. inversion H.
Qed.

Lemma equiv_skip: forall l l' a, equiv (a :: l) (a :: l') -> equiv l l'.
Proof.
  intros l l' a H. assert (H' := H). unfold equiv in *. intro n. specialize (H n). simpl in H. destruct (n =? a).
  - inversion H. reflexivity.
  - assumption.
Qed.

Lemma equiv_perm: forall l l' a a', equiv (a::l) (a'::l') ->  (a' =? a) = false -> exists l'', equiv (a::l) (a::l'').
Proof.
  induction l.
  - intros l' a a' H1 H2. unfold equiv in H1. specialize (H1 a'). simpl in H1. rewrite H2 in H1. rewrite Nat.eqb_refl in H1. inversion H1.
  - intros l' a' a'' H1 H2. exists (a :: l). unfold equiv. intro n. reflexivity.
Qed.

Lemma num_occ_cons: forall l x n, num_oc x l = S n -> exists l1 l2, l = l1 ++ x :: l2 /\ num_oc x (l1 ++ l2) = n.
Proof.
  induction l.
  - intros x n H. simpl in H. inversion H.
  - intros x n H. simpl in H. destruct (x=?a) eqn: H1.
    + specialize (IHl x n). apply Nat.eqb_eq in H1. rewrite H1. exists nil. exists l. simpl. split.
      * reflexivity.
      * apply eq_add_S in H. replace x in H. apply H.              
    + apply IHl in H. destruct H. destruct H. destruct H. rewrite H. exists (a::x0). exists x1. split.
      * reflexivity.
      * simpl. destruct (x=?a).
        ** rewrite H0. inversion H1.
        ** apply H0.
Qed.

Lemma equiv_exists: forall l l' x, equiv (x::l) l' -> exists l'' l''', l' = l'' ++ (x::l''').
Proof.
  intros l l' x H. unfold equiv in H. specialize (H x). simpl in H. destruct (num_oc x (x :: l)) eqn:H1.
  - simpl in H1. rewrite Nat.eqb_refl in H1. inversion H1.
  - rewrite Nat.eqb_refl in H. symmetry in H. apply num_occ_cons in H as [l1 [l2 [H2 H3]]]. exists l1, l2. assumption.
Qed.

Lemma num_oc_app: forall n l1 l2, num_oc n (l1 ++ l2) = num_oc n l1 + num_oc n l2.
Proof.
  intros n l1 l2. induction l1 as [| x l1 IHl1].
  - reflexivity.
  - simpl. destruct (n =? x).
    + rewrite IHl1. reflexivity.
    + apply IHl1.
Qed.

Lemma equiv_app: forall l l1 l2, equiv l (l1 ++ l2) -> equiv l (l2 ++ l1).
Proof.
  intros l l1 l2 H. unfold equiv in *. intros n. specialize (H n). rewrite H. rewrite num_oc_app. rewrite num_oc_app. apply Nat.add_comm.
Qed.

Lemma equiv_to_perm: forall l l', equiv l l' -> Permutation l l'.
Proof.
  induction l as [| a l IHl].
  - intros l' H. apply equiv_nil in H. subst. constructor.
  - intros l' H. destruct l' as [| a' l'].
    + unfold equiv in H. specialize (H a). simpl in H. rewrite Nat.eqb_refl in H. inversion H.
    + case (Nat.eq_dec a a').
      * intros Heq. subst. apply equiv_skip in H. apply perm_skip. apply IHl. assumption.
      * intros Hneq. assert (H' := H). apply equiv_exists in H. destruct H as [l'' [l''' H]]. rewrite H in *. apply Permutation_cons_app. apply IHl. apply equiv_app in H'. simpl in H'. apply equiv_skip in H'. apply equiv_app. assumption.
Qed.
(* end hide *)

(**

O teorema a seguir formaliza que as definições [Permutation] e [equiv] são equivalentes, e portanto qualquer uma delas pode ser utilizada no projeto.

*)

Theorem perm_equiv: forall l l', Permutation l l' <-> equiv l l'.
Proof.
  intros l l'.
  split.
  - apply perm_to_equiv.
  - apply equiv_to_perm.
Qed.

