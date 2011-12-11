Section Pigeonhole.

Require Import Omega.
Require Import List.

Variable A : Type.
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Fixpoint occur x (ys : list A) : nat :=
  match ys with
    | nil => O
    | cons y ys => match eq_dec x y with
                     | left eq => S (occur x ys)
                     | right neq => occur x ys
                   end
  end.


Lemma in_occur : forall x xs, In x xs -> occur x xs > 0.
  Proof.
    induction xs as [ | y ys]; simpl.
      intros; exfalso; assumption.
      intros [Eq | InTail]; destruct (eq_dec x y) as [Same | Diff]; try omega.
        now (exfalso; apply Diff). 
        now (apply IHys).
  Qed.

Lemma occur_in (x : A) (xs : list A) : occur x xs > 0 -> In x xs.
  Proof.
    induction xs as [ | y ys IHys].
      now (simpl; omega).
      simpl; destruct (eq_dec x y) as [Eq | Neq].
        now (intros; left).
        now (intros; right; apply IHys).
  Qed.

Lemma occur_app : forall x l m, occur x (l ++ m) = occur x l + occur x m.
  Proof.
    induction l; simpl; intros;[ reflexivity | rewrite IHl].
    case (eq_dec x a); intros; omega.
  Qed.

Lemma occur_notin : forall x l, occur x l = 0 -> ~In x l. 
  Proof.
    induction l; simpl.
      now (intros _ F; contradiction). 
      case (eq_dec x a).
        intros eq F H; discriminate.
        intros Neq H [Now | Later].
          now intuition.
          now apply IHl.
  Qed.

Lemma notin_occur (y : A) (xs : list A) : ~In y xs -> occur y xs = 0.
  Proof.
    induction xs as [ | x xs IHxs].
      now trivial.
      simpl; destruct (eq_dec y x) as [Same | Diff].
         now (intros F; exfalso; apply F; left; symmetry).
         intros H; apply IHxs.
         now (intros In; apply H; intuition).
  Qed.

Definition delta x y :=
  match eq_dec x y with
    | left _ => 1
    | right _ => 0
  end.

Lemma occur_delta (x y : A) (xs : list A) :
  occur y (x :: xs) = occur y xs + delta y x.
  Proof.
    unfold delta; simpl; destruct (eq_dec y x); omega.
  Qed.

Lemma in_elim_dec (x : A) (xs : list A) :
  In x xs -> exists init, exists tail, xs = init ++ x :: tail /\ ~In x init.
  Proof.
    induction xs as [ | y ys IHxs]; simpl.
      intros; contradiction.
      intros [Now | Later].
        now (subst y; exists nil; exists ys; split; [ reflexivity | intuition ]).
        case (eq_dec y x).
          now (intro Eq; subst x; exists nil; exists ys; intuition).
          intro Neq; destruct (IHxs Later) as [init [tail [H1 H2]]].
          exists (y :: init); exists tail; split.
            now (rewrite H1).
            now (intros F; apply H2; destruct F; intuition).
  Qed.

Lemma incl_cons_l (x : A) (xs ys : list A) :
  incl (x :: xs) ys -> In x ys /\ incl xs ys.
  Proof.
    intros H; unfold incl; simpl; intuition.
  Qed.

Lemma incl_nil (xs : list A) : incl nil xs.
  Proof.
    induction xs as [ | x xs]; 
      [intuition | unfold incl; simpl; intros y F; exfalso; assumption].
  Qed.

Lemma incl_cons_r (x : A) (xs ys : list A) : 
  incl ys (x :: xs) -> In x ys \/ incl ys xs.
  Proof.
    induction ys; simpl; intros Incl.
      now (right; apply incl_nil).
      destruct (incl_cons_l _ _ _ Incl) as [Elem Incl'].
        destruct Elem as [Now | Later].
          now (left; left).
          destruct (IHys Incl') as [Elem | Incl''].
            now (left; right).
            now (right; apply incl_cons).
  Qed.
          

Lemma occur_tail (x y : A) (xs : list A) :
  occur y xs <= occur y (x :: xs).
  Proof.
    induction xs as [ | z zs IHxs]; simpl; [omega | ].
    destruct (eq_dec y z); destruct (eq_dec y x); omega.
  Qed.

Lemma incl_app_elim (xs ys zs : list A) : 
  incl (xs ++ ys) zs -> incl xs zs /\ incl ys zs.
Proof.
  intros H; split.
    apply incl_tran with (xs ++ ys); [apply incl_appl, incl_refl | assumption].
    apply incl_tran with (xs ++ ys); [apply incl_appr, incl_refl | assumption].
Qed.

Lemma pigeon_hole : forall xs ys,
  incl ys xs -> length ys > length xs -> exists x : A, (occur x ys) >= 2.
  Proof.
  (* Induction on xs *)
  intros xs; induction xs as [ | x xs IHxs]; simpl.
    (* The case that xs = nil is impossible *)
    intros ys Incl Len; exfalso; destruct ys as [ | y ys]. 
      simpl in Len; omega.
      unfold incl in *; simpl in *; apply (Incl y); intuition.
    (* The case for xs = x :: xs *)
    intros ys Incl Len; destruct ys as [ | y ys].
      (* The case for ys = nil is impossible *)
      exfalso; simpl in *; omega.
      (* The case for ys = y :: ys we decide if y is in ys or not *)
      destruct (In_dec eq_dec y ys) as [Elem | Nelem].
        (* When y is in ys *)
        assert (H1 : occur y ys > 0) by apply (in_occur _ _ Elem).
        exists y.
        simpl; destruct (eq_dec y y) as [Same | Diff]; 
          [omega | exfalso; apply Diff; reflexivity].
       (* When y is not in ys *)
       case (le_lt_dec (occur x ys) 1).
         (* If x occurs less than once in ys *)
         intro Occurs.
         destruct (incl_cons_l _ _ _ Incl) as [Elem Incl'].
         assert (H : In x ys \/ incl ys xs) by apply (incl_cons_r _ _ _ Incl');
           destruct H as [Elem' | Incl''].
           (* When In x ys *)
           destruct Elem as [Now | Later]. 
             (* when x = y *)
             subst x; contradiction.         
             (* when Later : In x ys *)
             assert (Split : exists init, exists tail, ys = init ++ x :: tail /\ ~In x init) by 
               (apply (in_elim_dec _ _ Elem'));
               destruct Split as [init [tail [Split NelemInit]]].
             assert (Nelem' : ~In x tail). 
               apply (occur_notin); rewrite Split, occur_app in Occurs; simpl in Occurs.
               destruct (eq_dec x x) as [Same | Diff]; [omega | now (exfalso; apply Diff)].
             rewrite Split in Incl'.
             assert (InclSplit : incl init (x :: xs) /\ incl (x :: tail) (x :: xs)) 
               by (apply (incl_app_elim _ _ _ Incl'));
               destruct InclSplit as [InclInit InclTail].
             assert (H : In x init \/ incl init xs) by apply (incl_cons_r _ _ _ InclInit);
               destruct H as [InInit | Inclxs]. 
               (* If In x init we have an immediate contradiction *)
               now (contradiction).
               (* Otherwise incl init xs ... *)
               assert (H : In x (x :: xs) /\ incl tail (x :: xs)) 
                 by apply (incl_cons_l _ _ _ InclTail).
               destruct H as [H InclTail']; clear H.
               assert (H : In x tail \/ incl tail xs) by apply (incl_cons_r _ _ _ InclTail');
                 destruct H as [F | InclInit']. 
                   (* If In x tail, we have another contradiction *)
                   now contradiction.
                   (* Otherwise incl tail xs *)
                   set (zs := init ++ y :: tail).
                   assert (InclZsXs : incl zs xs) by
                     now (unfold zs; apply incl_app; [ assumption | apply incl_cons]).
                   assert (Len' : length zs > length xs) by
                     (unfold zs; rewrite app_length; simpl in *;
                     rewrite Split, app_length in Len; simpl in *;
                     omega).
                   destruct (IHxs zs InclZsXs Len') as [z H].
                     exists z; subst zs.
                     rewrite Split, occur_delta, occur_app, occur_delta.
                     rewrite occur_app, occur_delta in H.
                     omega.
           (* When incl ys xs *)
           assert (Len' : length ys > length xs) by (simpl in Len; omega).
           destruct (IHxs ys Incl'' Len') as [z H];
             now (exists z; simpl; destruct (eq_dec z y); omega).
         (* If x happens to occur twice, we're done *)
         now (exists x; simpl; destruct (eq_dec x y); omega).
Qed.

End Pigeonhole.