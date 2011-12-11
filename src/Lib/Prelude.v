Section Prelude.

Require Import List.
Require Import Omega.

Lemma length_zero (a : Type) (xs : list a) : length xs = 0 -> xs = nil.
  Proof.
    intros H; induction xs as [ | x xs]; [ reflexivity | simpl in H; discriminate H].
  Qed.


Lemma forall_cong (a : Type) (P Q : a -> Prop) (xs : list a) :
  Forall P xs /\ Forall Q xs -> Forall (fun x => P x /\ Q x) xs.
  Proof.
    intros [FPx FQx]; induction xs as [ | x xs]; constructor;
    inversion FPx; inversion FQx.
      split; assumption.
      apply IHxs; assumption.
  Qed.

Lemma in_seq (x : nat) : forall l m, 
  m <= x < l + m -> In x (seq m l).
  Proof.
    induction l.
    (* Zero case *)
    intros; exfalso; omega.
    (* Succ case *)
    simpl; intros m Bounds.
    case (eq_nat_dec m x).
       intros; left; assumption.
      right; apply IHl; omega.
  Qed.

End Prelude.
