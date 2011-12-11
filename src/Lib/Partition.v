Section Partition.

Require Import Arith.
Require Import Lib.Prelude.
Require Import List.
Require Import Lib.Unique.

Variable A : Type.
Variable P : A -> Prop.
Variable p : forall n, {P n} + {~P n}.

Fixpoint partition (xs : list A) :
  list A * list A :=
  match xs with
    | nil => (nil , nil)
    | x :: xs =>
      let (ys,zs) := partition xs in
      match p x with
        | left yes => (x :: ys , zs)
        | right no => (ys , x :: zs)
      end
  end.

Lemma partition_prop (xs : list A) :
  Forall P (fst (partition xs)) /\ Forall (fun x => ~ P x) (snd (partition xs)).
  Proof.
    induction xs as [ | x xs [IHP IHNP]].
    (* Nil case *)
    split; constructor.
    (* Cons case *)
    simpl; case (p x); destruct (partition xs) as [yz zs]; split; try constructor; assumption.
  Qed.

Lemma forall_partition (Q : A -> Prop) (xs : list A) : 
  Forall Q xs -> let (ys , zs) := partition xs in
                 Forall Q ys /\ Forall Q zs.
  Proof.    
    induction xs as [ | x xs IHxs].
    (* Base case *)
    intro H; split; assumption.
    (* Cons case *)
    simpl; case (p x); destruct (partition xs) as [ys zs].
    (* P x holds *)
    intros Px Qxs; split; inversion Qxs;
      [ constructor | idtac]; try apply IHxs; assumption.
    (* P x does not hold *)
    intros notPx Qxs; split; inversion Qxs;
      [idtac | constructor]; try apply IHxs; assumption.
  Qed.

Lemma forall_partition_left (Q : A -> Prop) (xs : list A) : 
  Forall Q xs -> Forall Q (fst (partition xs)).
  Proof.
    intros Qxs.
    assert (H: let (ys,zs) := partition xs in
              Forall Q ys /\ Forall Q zs).
    apply forall_partition; assumption.
    destruct (partition xs) as [ys zs]; destruct H as [H1 H2]; assumption.
  Qed.

Lemma forall_partition_right (Q : A -> Prop) (xs : list A) : 
  Forall Q xs -> Forall Q (snd (partition xs)).
  Proof.
    intros Qxs; assert (H: let (ys,zs) := partition xs in
                           Forall Q ys /\ Forall Q zs).
    apply forall_partition; assumption.
    destruct (partition xs) as [ys zs]; destruct H as [H1 H2]; assumption.
  Qed.

Lemma partition_length (xs : list A) : 
  length (fst (partition xs)) + length (snd (partition xs)) = length xs.
  Proof.
    induction xs as [ | x xs IHxs]; [reflexivity | ].
    simpl; case (p x);
    destruct (partition xs) as [ys zs]; simpl; rewrite <- IHxs;
      [reflexivity | rewrite <- plus_Snm_nSm; reflexivity].
  Qed.

Lemma partition_length_left (xs : list A) : 
  forall us, us = fst (partition xs) -> length us = length xs -> xs = us.
  Proof.
    induction xs as [ | x xs IHxs]; simpl.
    (* Base case *)
    now (intros us Part L; symmetry; apply length_zero).
    (* Cons case *)
    destruct (p x).
      (* P x holds *)
      intros us Eq L; subst; simpl.
      destruct (partition xs) as [ys zs].
      now (rewrite (IHxs ys); try reflexivity; subst; simpl in L; auto with arith).
      (* P x does not hold *)
      intros us Eq; subst.
      rewrite <- (partition_length xs).
      destruct (partition xs) as [ys zs].
      simpl; intros F; exfalso; apply (lt_irrefl (length ys)).
      now (rewrite F at 2; auto with arith).
  Qed.

Lemma partition_in_left (xs : list A) : 
  forall x, In x (fst (partition xs)) -> In x xs.
  Proof.
    intros y; induction xs as [ | x xs IHxs].
    intros F; assumption.
    simpl; case (p x).
    (* P x branch *)
    intros Px H; destruct (partition xs) as [ys zs]; destruct H as [Eq | InTail].
      left; assumption.
      right; apply IHxs; assumption.
    (* Not P x branch *)
    intros NotPx H; destruct (partition xs) as [ys zs]; simpl in H.
    right; apply IHxs; assumption.
  Qed.

Lemma in_left_partition (xs : list A) : 
  forall x, In x xs -> P x -> In x (fst (partition xs)).
  Proof.
    induction xs as [ | x xs]; [ intros y F; destruct F | ].
    (* Cons case *)
    intros y [Now | Later] Py.
    (* x = y *)
    rewrite Now; simpl.
    case (p y).
      (* P y holds *)
      intros; destruct (partition xs) as [ys zs]; simpl; left; reflexivity.
      (* P y does not hold *)
      intros F; exfalso; intuition.
    (* In y xs *)
    simpl; destruct (partition xs) as [ys zs].
    case (p x); intros; simpl.
      right; apply IHxs; assumption.
      apply IHxs; assumption.
  Qed.

Lemma in_right_partition (xs : list A) : 
  forall x, In x xs -> ~P x -> In x (snd (partition xs)).
  Proof.
    induction xs as [ | x xs].
    (* Base case *)
    intros y F; destruct F.
    (* Cons case *)
    intros y [Now | Later] Py.
      (* x = y *)
      rewrite Now; simpl.
      case (p y).
        intros F; exfalso; intuition.
        intros; destruct (partition xs) as [ys zs]; simpl; left; reflexivity.
      (* In y xs *)
      simpl; destruct (partition xs) as [ys zs].
      case (p x); intros; simpl.
        apply IHxs; assumption.
        right; apply IHxs; assumption.
  Qed.

Lemma partition_in_right (xs : list A) : 
  forall x, In x (snd (partition xs)) -> In x xs.
  Proof.
    intros y; induction xs as [ | x xs IHxs].
    (* Base case *)
    intros F; assumption.
    (* Cons case *)
    simpl; case (p x); destruct (partition xs) as [ys zs].
      (* P x branch *)
      intros Px H; right; apply IHxs; assumption.
      (* Not P x branch *)
      simpl; intros NotPx H; destruct H as [Eq | InTail].
        left; assumption.
        right; apply IHxs; assumption.
    Qed.

Lemma partition_unique (xs : list A) : 
  unique_list A xs -> let (ys,zs) := partition xs in
  unique_list A ys /\ unique_list A zs.
  Proof.
    intros Uxs; induction xs as [ | x xs IHxs].
    split; constructor.
    (* Cons branch *)
    destruct Uxs as [NotIn Uxs]; simpl; case (p x).
    (* P x branch *)
    intros Px; assert (forall y, In y (fst (partition xs)) -> In y xs);
      [apply partition_in_left | idtac].
    destruct (partition xs) as [ys zs]; split;
      [ constructor ; [intro F; apply NotIn; apply H; assumption | idtac] | idtac];
      apply IHxs; assumption.
    (* Not P x branch *)
    intros NotPx; assert (forall y, In y (snd (partition xs)) -> In y xs);
        [apply partition_in_right | idtac].
    destruct (partition xs) as [ys zs]; split;
      [idtac | constructor; [intro F; apply NotIn; apply H; assumption | idtac]];
      apply IHxs ; assumption.
    Qed.

Lemma partition_unique_left (xs : list A) : 
  unique_list A xs -> unique_list A (fst (partition xs)).
  Proof.
    intros H; assert (U : let (ys,zs) := partition xs in 
                          unique_list A ys /\ unique_list A zs).
    apply partition_unique; assumption.
    destruct (partition xs) as [ys zs]; destruct U as [H1 H2]; assumption.
  Qed.

Lemma partition_unique_right (xs : list A) : 
  unique_list A xs -> unique_list A (snd (partition xs)).
  Proof.
    intros H; assert (U : let (ys,zs) := partition xs in 
                          unique_list A ys /\ unique_list A zs).
    apply partition_unique; assumption.
    destruct (partition xs) as [ys zs]; destruct U as [H1 H2]; assumption.
  Qed.

End Partition.