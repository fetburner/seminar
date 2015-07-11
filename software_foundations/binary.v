Require Import Arith Omega.

Inductive binary :=
    Zero : binary
  | Twice : binary -> binary
  | SuccTwice : binary -> binary.

Fixpoint incr b :=
  match b with
    Zero => SuccTwice Zero
  | Twice b' => SuccTwice b'
  | SuccTwice b' => Twice (incr b')
  end.

Definition bin_to_nat :=
  binary_rect _ O (fun _ n => n + n) (fun _ n => S (n + n)).

Definition nat_to_bin :=
  nat_rect _ Zero (fun _ => incr).

Theorem bin_to_nat_pres_incr : forall b, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [| b' IHb' | b' IHb'].
    reflexivity.

    reflexivity.

    simpl.
    repeat (rewrite IHb').
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem nat_to_bin_pres_twice : forall n, n <> 0 -> nat_to_bin (n + n) = Twice (nat_to_bin n).
Proof.
  intros n Hnz.
  destruct n as [| n'].
    congruence.

    induction n' as [| n'' IHn''].
      reflexivity.

      repeat (rewrite <- plus_n_Sm in * |- *).
      simpl in * |- *.
      assert (S n'' <> 0) as Hcommonsence by auto.
      repeat (rewrite (IHn'' Hcommonsence)).
      reflexivity.
Qed.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
    reflexivity.

    simpl.
    rewrite bin_to_nat_pres_incr.
    rewrite IHn'.
    reflexivity.
Qed.

Definition binary_iszero_dec : forall b, {b = Zero} + {b <> Zero}.
  intros b.
  destruct b.
    left.
    reflexivity.

    right.
    congruence.

    right.
    congruence.
Defined.

Print sumbool.

Eval compute in (binary_iszero_dec Zero).
Eval compute in (binary_iszero_dec (Twice Zero)).
Eval compute in (binary_iszero_dec (Twice (SuccTwice Zero))).

Fixpoint normalize b :=
  match b with
    Zero => Zero
  | Twice b' =>
      let b'' := normalize b' in
      if binary_iszero_dec b'' then Zero
      else Twice b''
  | SuccTwice b' => SuccTwice (normalize b')
  end.

Lemma normal_exclude_ill_zero : forall b, normalize b <> Zero -> bin_to_nat (normalize b) <> 0.
Proof.
  intros b Hbnz.
  induction b as [| b' IHb' | b' IHb']; simpl in * |- *.
    auto.

    destruct (binary_iszero_dec (normalize b')) as [Hz | Hnz]; simpl.
      auto.

      assert (bin_to_nat (normalize b') <> 0) by (apply (IHb' Hnz)).
      omega.

    auto.
Qed.

Theorem normal_bin_nat_bin : forall b, nat_to_bin (bin_to_nat (normalize b)) = normalize b.
Proof.
  intros b.
  induction b as [| b' IHb' | b' IHb']; simpl.
    reflexivity.

    destruct (binary_iszero_dec (normalize b')) as [| Hnz]; simpl.
      reflexivity.

      rewrite (nat_to_bin_pres_twice _ (normal_exclude_ill_zero _ Hnz)).
      rewrite IHb'.
      reflexivity.

    destruct (binary_iszero_dec (normalize b')) as [Hz | Hnz].
        rewrite Hz.
        reflexivity.

        rewrite (nat_to_bin_pres_twice _ (normal_exclude_ill_zero _ Hnz)).
        rewrite IHb'.
        reflexivity.
Qed.
