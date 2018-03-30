Print bool.
Goal false <> true.
Proof.
  intros A.
  change (if false then True else False).
  rewrite A.
  exact I.
Qed.

Lemma disjoint_O_S n:
  O <> S n.
Proof.
  intro A.
  change (match O with O => False | _ => True end).
  rewrite A.
  exact I.
Qed.

Goal false <> true.
Proof.
  intros A.
  change (match true with false => True | true => False end).
  rewrite <- A.
  exact I.
Qed.

Lemma injective_S x y:
  S x = S y -> x = y.
Proof.
  intro A.
  change (pred (S x) = pred (S y)).
  rewrite A.
  reflexivity.
Qed.

Print pred.
Print Nat.pred.

Goal forall x, S x <> O.
Proof. intros x A. discriminate A. Qed.

Goal forall x y, S x = S y -> x = y.
Proof. intros x y A. injection A. auto. Qed.

Goal forall x, S x <> O.
Proof.
  intros x A.
  congruence.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof. intros x y A. congruence. Qed.
