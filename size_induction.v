Require Import Omega.

Lemma size_induction X (f: X -> nat) (p: X -> Prop):
  (forall x, (forall y, f y < f x -> p y) -> p x) ->
  forall x, p x.
Proof.
  intros step x. apply step.
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. omega.
    - intros y B. apply step. intros z C. apply IHn. omega.
  }
  apply G.
Qed.
