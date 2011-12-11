Section Remove.

Require Import List.
Require Import Arith.
Require Import Omega.
Require Import Lib.Unique.

Variable A : Type.
Variable eq_dec : forall (x y : A), {x = y} + {x <> y}.

Lemma remove_distinct_head (x y : A) (xs : list A) : y <> x -> 
  remove eq_dec y (x :: xs) = x :: remove eq_dec y xs.
  Proof.
    simpl; destruct (eq_dec y x); [ intros F; exfalso; apply F; trivial | trivial].
  Qed.


Lemma remove_distinct (x y : A) (xs : list A) : In x xs -> y <> x -> 
  In x (remove eq_dec y xs).
  Proof.
    intros H D; induction xs; [ exfalso; assumption | ].
    inversion H as [Now | Later].
      rewrite Now, remove_distinct_head; try constructor; trivial.
      simpl; destruct (eq_dec y a); [ | right]; apply IHxs; assumption.
   Qed.

Lemma remove_preserves_distinct (x y : A) (xs : list A) : y <> x -> 
  In x (remove eq_dec y xs) -> In x xs.
Proof.
  induction xs; [trivial | ]; simpl; generalize (eq_dec y a) as d; destruct d.
    subst y; intros; right; apply IHxs;  assumption.
    intros D H; simpl in H; destruct H.  
      left; assumption.
      right; apply IHxs; assumption.
  Qed.

Lemma incl_remove (x : A) (xs ys : list A) : incl xs ys -> ~ In x xs -> incl xs (remove eq_dec x ys).
  Proof.
    unfold incl; intros H F y I; case (eq_dec x y).
      now (intros Eq; subst x; exfalso).
      apply remove_distinct. apply H; assumption.
  Qed.

Lemma length_remove (x : A) (xs : list A) : length (remove eq_dec x xs) <= length xs.
  Proof.
    induction xs as [ | y ys]; [ simpl; omega | ].
    simpl; destruct (eq_dec x y) as [Same | Diff]; simpl; omega.
  Qed.

Lemma length_remove_element (x : A) (xs : list A) : In x xs -> length (remove eq_dec x xs) < length xs.
  Proof.    
    intros I; induction xs as [ | y ys]; [ now exfalso | ].
    simpl; destruct (eq_dec x y) as [Same | Diff].
      assert (length (remove eq_dec x ys) <= length ys) by apply length_remove; omega.
      destruct (in_inv I); [now (exfalso; apply Diff) | simpl; apply lt_n_S, IHys; assumption].
  Qed.

Lemma length_remove_nelement (x : A) (xs : list A) : ~In x xs -> length (remove eq_dec x xs) = length xs.
  Proof.
    induction xs as [ | y ys IHys]; [ trivial | ].
    intros H; simpl; destruct (eq_dec x y).
      subst x; exfalso; apply H; constructor; trivial.
      simpl; rewrite <- IHys; try reflexivity.
      intros F; apply H; right; assumption.
  Qed.

Lemma unique_remove (x : A) (us : list A) : 
   unique_list A us -> unique_list A (remove eq_dec x us).
  Proof.
    induction us as [ | y ys IHys]; [ constructor | ].
    intros H; simpl; destruct (eq_dec x y).
      apply IHys; destruct H; assumption.
      split; destruct H as [Nelem UTail].
        intros F; apply Nelem; apply (remove_preserves_distinct y x); assumption.
        apply IHys; assumption.
  Qed.

Lemma remove_least (a b : nat) (xs : list nat) : Forall (fun x => a <= x < b) xs ->
  Forall (fun x => S a <= x < b) (remove eq_nat_dec a xs).
  Proof.
    induction xs as [ | x xs]; [ intros; constructor | ].
    intros H; simpl; destruct (eq_nat_dec a x).
      subst x; apply IHxs; inversion H; assumption.
      constructor; [ inversion H; omega | inversion H; apply IHxs; assumption].
    Qed.

Lemma length_remove_unique (x : A) (us : list A) :
  unique_list A us -> In x us -> (length us) = S (length (remove eq_dec x us)).
  Proof.
    intros U Elem; induction us as [ | y ys IHys].
      (* Base case *)
      simpl in Elem; exfalso; trivial.
      (* Cons case *)
    simpl in *; destruct U as [U1 U2]; destruct (eq_dec x y).
      now (subst x; rewrite (length_remove_nelement)).
      destruct Elem as [Now | Later].
        exfalso; apply n; symmetry; trivial.
        now (rewrite IHys).
  Qed.

End Remove.