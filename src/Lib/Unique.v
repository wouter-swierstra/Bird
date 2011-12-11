Section Unique.

Require Import List.
Require Import Arith.
Require Import Lib.Pigeonhole.

Variable A : Type.
Variable eq_dec : forall (x y : A), {x = y} + {x <> y}.

Fixpoint unique_list (xs : list A) : Prop :=
  match xs with
    | nil => True
    | x :: xs => ~ In x xs /\ unique_list xs
  end.

Lemma unique_in (x : A) (xs : list A) : unique_list xs -> In x xs -> 
  occur _ eq_dec x xs = 1.
  Proof.
    induction xs as [ | y ys].
    (* Base case *)
    intros _ F; now inversion F.
    (* Cons case *)
    intros [U1 U2] I.
    simpl; case (eq_dec x y).
      (* same *)
      intros; subst; simpl. 
      destruct (eq_dec y y) as [Eq | Neq]. 
        now (rewrite notin_occur).
        now (exfalso; apply Neq).
      (* diff *)
      intros Neq; apply (IHys U2).
      destruct I as [Now | Later].
        exfalso; apply Neq; symmetry; assumption.
        assumption.
    Qed.

End Unique.