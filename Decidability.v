From Stdlib Require Import Arith.

Notation decidable A := (A \/ ~A).
Lemma decidable_not_not_elim A (A_dec : decidable A) : ~~A -> A.
Proof.
  intuition.
Qed.
Lemma decide_not A (A_dec : decidable A) : decidable (~A).
Proof.
  intuition.
Qed.
Lemma decide_and A B (A_dec : decidable A) (B_dec : decidable B) :
  decidable (A /\ B).
Proof.
  intuition.
Qed.
Lemma decide_or A B (A_dec : decidable A) (B_dec : decidable B) :
  decidable (A \/ B).
Proof.
  intuition.
Qed.
Lemma decide_impl A B (A_dec : decidable A) (B_dec : decidable B) :
  decidable (A -> B).
Proof.
  intuition.
Qed.
Lemma decide_equiv A B (A_dec : decidable A) (B_dec : decidable B) :
  decidable (A <-> B).
Proof.
  intuition.
Qed.
Lemma decide_bounded_exists (A : nat -> Prop)
  (A_dec : forall n, decidable (A n)) :
  forall m : nat, decidable (exists n, n <= m /\ A n).
Proof.
  intro. induction m.
  - destruct (A_dec 0) as [A0 | nA0].
      left. exists 0. constructor. apply le_n. exact A0.
    right.
    intro H. destruct H as [n Hn]. destruct Hn as [nle0 An].
    apply nA0.
    apply Nat.le_0_r in nle0.
    rewrite <- nle0. exact An.
  - destruct IHm as [e | ne].
    + left.
      destruct e as [n Hn]. exists n. destruct Hn as [nlem An].
      constructor. exact (le_S n m nlem). exact An.
    + destruct (A_dec (S m)) as [ASm | nASm].
        left. exists (S m). constructor. apply le_n. exact ASm.
      right.
      intro H. destruct H as [n Hn]. destruct Hn as [nleSm An].
      apply Nat.le_succ_r in nleSm. destruct nleSm as [nlem | neqSm].
        apply ne. exists n. constructor; assumption.
        apply nASm. rewrite <- neqSm. exact An.
Qed.
Lemma decide_bounded_forall (A : nat -> Prop)
  (A_dec : forall n, decidable (A n)) :
  forall m : nat, decidable (forall n, n <= m -> A n).
Proof.
  intro.
  destruct (decide_bounded_exists (fun n => ~A n)
            (fun n => decide_not (A n) (A_dec n)) m).
    right. firstorder.
    left. firstorder.
Qed.

Ltac dec_simpl_once := apply decide_not || apply decide_and
|| apply decide_or || apply decide_impl || apply decide_equiv
|| (apply decide_bounded_exists; intro)
|| (apply decide_bounded_forall; intro).
Tactic Notation "dec_simpl" := repeat dec_simpl_once.




Ltac strong_induction n :=
  apply (fun A A0 IH => Nat.strong_induction_le A A0 IH n);
  clear n;
  [ | intro n].

(*Le principe du plus petit élément n’est pas vrai en général dans
l’arithmétique de Heyting, mais il l’est pour les formules décidables.*)
Lemma smallest_element (A : nat -> Prop)
  (A_dec : forall n, decidable (A n)) (exists_element : exists n, A n) :
  exists n, A n /\ forall m, A m -> n <= m.
Proof.
  destruct exists_element as [n An].
  revert An.
  strong_induction n.
  - intro A0. exists 0. constructor.
      exact A0.
      intros m Am. apply Nat.le_0_l.
  - intros IHn ASn.
    destruct (decide_bounded_exists A A_dec n) as [exsmaller | nexsmaller].
    + destruct exsmaller as [m H]. destruct H as [mlen Am].
      apply (IHn m); assumption.
    + exists (S n).
      constructor.
        exact ASn.
      intros m Am.
      destruct (le_le_S_dec m n).
        firstorder.
        assumption.
Qed.