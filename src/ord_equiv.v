(** * Proposta1: Equivalência entre diferentes noções de ordenação.*)
(* begin hide *)
Require Import List Arith.
(* end hide *)

(**

A primeira definição de ordenação, chamada [ord1], é uma definição indutiva contendo 3 regras de formação:

%\begin{mathpar}
 \inferrule*[Right={$(ord1\_nil)$}]{~}{ord1\ nil} \and \inferrule*[Right={$(ord1\_one)$}]{~}{ord1\ (x::nil)} \and \inferrule*[Right={$(ord1\_all)$}]{x \leq y \and ord1(y::l)}{ord1\ (x::y::l)}
\end{mathpar}%

*)

Inductive ord1 : list nat -> Prop :=
| ord1_nil: ord1 nil
| ord1_one: forall x, ord1 (x::nil)
| ord1_all: forall l x y, x <= y -> ord1 (y::l) -> ord1 (x::y::l).

(**

A segunda definição de ordenação, chamada [ord2], é uma definição indutiva contendo 2 regras de formação:

%\begin{mathpar}
 \inferrule*[Right={$(ord2\_nil)$}]{~}{ord2\ nil} \and  \inferrule*[Right={$(ord2\_all)$}]{x \leq^* l \and ord2\ l}{ord2\ (x::l)}
\end{mathpar}%
%\noindent% onde $x \leq^* l$ significa que $x$ é menor ou igual que todo elemento da lista $l$. Formalmente, este predicado é definido como a seguir:
*)

Definition le_all x l := forall y, In y l -> x <= y.
(* begin hide *)
Notation "x <=* l" := (le_all x l) (at level 60).  
(* end hide *)
(** printing <=* %\ensuremath{\leq^*}% *)
Inductive ord2 : list nat -> Prop :=
| ord2_nil: ord2 nil
| ord2_all: forall l x, x <=* l -> ord2 l -> ord2 (x::l).
(** printing < %\ensuremath{<}% *)
(**

A terceira definição de ordenação, chamada [ord3], diz que uma lista está ordenada se cada elemento é menor ou igual ao elemento seguinte:

 *)

Definition ord3 (l : list nat) : Prop := forall i, i < length l -> nth i l 0 <= nth (S i) l 0.

(**

A quarta definição de ordenação, chamada [ord4], diz que uma lista está ordenada se cada elemento é menor ou igual que qualquer elemento que esteja em posição anterior:

 *)

Definition ord4 (l : list nat) : Prop := forall i j, i < j -> j < length l -> nth i l 0 <= nth j l 0.

Lemma ord3_nil: ord3 nil.
Proof.
  unfold ord3. intros i H. simpl in H. inversion H.
Qed.

(** Os 4 lemas a seguir são exercícios simples que serão provados em aula: *)

Lemma ord3_one: forall x, ord3 (x::nil).
Proof.
Admitted.

Lemma ord4_nil: ord4 nil.
Proof.
Admitted.

Lemma ord4_one: forall x, ord4 (x::nil).
Proof.
Admitted.

(**

%{\bf O objetivo da proposta 1 é mostrar que as definições}% [ord1], [ord2], [ord3] e [ord4] %{\bf são equivalentes. Para isto prove os 6 teoremas a seguir}%:

 *)

Theorem ord1_equiv_ord2: forall l, ord1 l <-> ord2 l.
Proof.
  Admitted.

Theorem ord1_equiv_ord3: forall l, ord1 l <-> ord3 l.
Proof.
Admitted.

Theorem ord1_equiv_ord4: forall l, ord1 l <-> ord4 l.
Proof.
Admitted.

Theorem ord2_equiv_ord3: forall l, ord2 l <-> ord3 l.
Proof.
Admitted.

Theorem ord2_equiv_ord4: forall l, ord2 l <-> ord4 l.
Proof.
Admitted.

Theorem ord3_equiv_ord4: forall l, ord3 l <-> ord4 l.
Proof.
Admitted.


