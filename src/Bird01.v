Require Import List.
Require Import Peano_dec.
Require Import Div2.
Require Import Arith.
Require Import Program.
Require Import Recdef.
Require Import Omega.

Require Import Lib.Prelude.
Require Import Lib.Pigeonhole.
Require Import Lib.Unique.
Require Import Lib.Partition.
Require Import Lib.Remove.

Lemma necessarily_in (a k : nat) (us : list nat)
   (ListBounds : Forall (fun u => a <= u < k + a) us)
   (L : length us = k) (U : unique_list nat us) : forall y, a <= y < k + a -> In y us.
  Proof.
    intros y Bounds; case (in_dec eq_nat_dec y us).
      now intuition.
      (* If ~ In y us ... *)
      intros Nelem; set (vs := remove eq_nat_dec y (seq a k)).
      (* Derive a contradition using the pigeon hole principle *)
      assert (PH : exists x, occur _ eq_nat_dec x us >= 2). 
        apply (pigeon_hole _ eq_nat_dec vs us).
        (* We must show incl us vs ... *)
        assert (incl us (seq a k)) by
          now (intros x V; apply in_seq; apply (Forall_forall (fun u => a <= u < k + a) us)).
        now (apply incl_remove).
        (* And we must show that length us > length vs *)
        assert (Lengths : length vs < length (seq a k)) by
            (subst vs; apply length_remove_element; apply in_seq; omega).
        now (rewrite L; rewrite seq_length in Lengths; omega).
    (* Now derive a contradiction *)
    destruct PH as [x Occurs].
    rewrite unique_in in Occurs;
      [exfalso; omega | assumption | apply (occur_in _ eq_nat_dec)].
      omega.
  Qed.

Lemma missing_element (b : nat) (n : nat) : forall us a,
    length us = n ->
    unique_list nat us ->
    Forall (fun u => a <= u < b) us ->
    length us < b - a ->
    exists x, a <= x < b /\ ~ In x us.
  Proof.
    induction n.
    (* Base case *)
    intros us a L; rewrite (length_zero nat us); [ | assumption].
      now (intros _ _ H; exists a; split; [omega | intros F; exfalso; apply F]).
    (* Cons branch *)
    intros us a L U Bounds L'; case (in_dec eq_nat_dec a us).
      (* If In a us *)
      intros H.
      assert (LR : length (remove eq_nat_dec a us) = n) by
        now (apply eq_add_S; rewrite <- L, (length_remove_unique _ eq_nat_dec a us)).
      destruct (IHn (remove eq_nat_dec a us) (S a)) as [m [B N]].
        now trivial. 
        now (apply unique_remove).
        now (apply remove_least).
        now omega.
      destruct (IHn (remove eq_nat_dec a us) (S a)) as [y [Bs Nelem]].
        now trivial.
        now apply (unique_remove _ eq_nat_dec a us).
        now apply (remove_least a b us).
        now omega.
      exists y; split.
        now omega.
        now (intros Elem; apply Nelem; apply remove_distinct; try omega).
      (* If ~ In a us *)
      intros Nelem; exists a; split; [omega | assumption].
  Qed.

Program Fixpoint minfrom (a : nat)
 (xs : {xs' : list nat | unique_list nat xs' /\ Forall (fun x => a <= x) xs'})
 (n : {n' : nat | length xs = n'}) {measure (length xs)} :
 {m : nat | a <= m /\ ~In m xs /\ forall y, a <= y < m -> In y xs}
  := match n with
       | O => a
       | n =>
         let b := S (a + div2 n) in
         match partition _ _ (fun x => lt_dec x b) xs with
           | (us , vs) =>
             let m := length us in
               match lt_eq_lt_dec m (b - a) with
                 | inleft (right eq) => minfrom b vs (n - m)
                 | inleft (left neq) => minfrom a us m
                 | inright neq => !
               end
         end
     end.

  Next Obligation.
    split; constructor.
      now (rewrite (length_zero nat xs)).
      now (intros y H; exfalso; omega).
  Qed.

  Next Obligation.
    change vs with (snd (us,vs)); rewrite Heq_anonymous; split.
      now (apply partition_unique_right).
      now (apply (Forall_impl (P := fun x => ~ x < S (a + div2 (length xs))));
        [intros; omega | apply partition_prop]).
  Defined.

  Next Obligation.
    apply plus_minus.
    change us with (fst (us,vs)); change vs at 2 with (snd (us,vs)).
    now (rewrite Heq_anonymous, partition_length).
  Defined.

  Next Obligation.    
    change (match a with 0 => S (a + div2 (length xs))
               | S l => a + div2 (length xs) - l end)
      with (S (a + div2 (length xs)) - a) in eq.
    rewrite <- (partition_length _ _ (fun x => lt_dec x (S (a + div2 (length xs)))) xs),
            <- Heq_anonymous; simpl; rewrite eq; omega.
  Defined.

  Local Obligation Tactic := idtac.

  Next Obligation.
    intros a [xs [U LeA]] [n L] minfrom filtered_var k NonZero.
    intros Heq_n b filtered_var0 us vs Heq_anonymous m filtered_var1 eq Heq_anonymous0.
    subst filtered_var filtered_var0 filtered_var1 m.
    destruct_call minfrom as [x [Lower [Nelem Least]]].
    simpl; simpl in Lower, Nelem, Least; split; [ | split].
      (* Now we need to show a <= x *) 
      now (subst b; omega).
      (* ... and ~In x xs *)
      intro F; apply Nelem; change vs with (snd (us,vs)); rewrite Heq_anonymous.
      now (apply in_right_partition; try omega).
      (* ... and forall y, a <= y < x -> In y xs *)
      intros y Bounds; destruct (le_dec b y) as [Le | Gt ].
        (* b <= y *)
        assert (AlsoIn : In y vs -> In y xs) by
          (change vs with (snd (us,vs)); rewrite Heq_anonymous; apply partition_in_right).
        now (apply AlsoIn, Least; omega).
        (* b > y *)
        assert (InUs : In y us).
          (* Assemble the required arguments for necessarily_in ... *)
          assert (H :  Forall (fun u : nat => a <= u < b - a + a) us).
            apply forall_cong; change us with (fst (us,vs)); rewrite Heq_anonymous; split.
              now (apply (forall_partition_left); refine (Forall_impl _ _ LeA)).
              now (apply (Forall_impl (P := fun x => x < S (a + div2 k)));
                [intros; subst b; omega |
                apply (proj1 (partition_prop _ _ (fun x => lt_dec x (S (a + div2 k))) xs))]).
            assert (Uus : unique_list nat us) by
              (change us with (fst (us,vs)); rewrite Heq_anonymous; 
                apply (partition_unique_left); assumption).
            assert (B : a <= y < b - a + a) by omega.
            now (apply (necessarily_in a (b - a) us)).
        (* Now we only need to show that In y us -> In y xs *)    
        apply (partition_in_left _ _ (fun x => lt_dec x (S (a + div2 k)))).
        now (subst b; simpl in Heq_anonymous; rewrite <- Heq_anonymous).
    Qed.

  Local Obligation Tactic := program_simpl.

  Next Obligation.
    change us with (fst (us,vs)); rewrite Heq_anonymous.
    split; [ apply partition_unique_left | apply forall_partition_left]; assumption.
  Qed.

  Next Obligation.
    change (match a with 0 => S (a + div2 (length xs))
               | S l => a + div2 (length xs) - l end)
      with (S (a + div2 (length xs)) - a) in neq.
    destruct xs as [ | x xs].
      now (exfalso; apply H).
      assert (LT : div2 (length (x :: xs)) < length (x :: xs)) by
        (apply lt_div2; omega).
      now (apply (lt_le_trans _ _ _ neq); omega).
  Defined.

  Local Obligation Tactic := idtac.

  Next Obligation.    
    intros a [xs [U LeA]] [n L] minfrom filtered_var k NonZero.
    intros Heq_n b filtered_var0 us vs Heq_anonymous m filtered_var1 eq Heq_anonymous0.
    subst filtered_var filtered_var0 filtered_var1 m.
    destruct_call minfrom as [x [Lower [Nelem Least]]].
    simpl; simpl in Lower, Nelem, Least; split; [ | split].
    (* We need to show a <= x *)
    now assumption.
    (* ... and ~ In x xs *)
    intro Elem; clear minfrom; clear Heq_n.
    destruct (missing_element b (length us) us a) as [z [zBounds zNelem]]. 
      now (reflexivity).
      now (change us with (fst (us,vs)); rewrite Heq_anonymous; apply partition_unique_left).
      apply forall_cong; split; change us with (fst (us,vs)); 
        rewrite Heq_anonymous; simpl.
        now (apply forall_partition_left; refine (Forall_impl _ _ LeA)).
      now (apply (proj1 (partition_prop _ _ _ _))).
      now omega.
    assert (B : ~ (x < b)).
      intros F; apply Nelem.
      now (change us with (fst (us,vs)); rewrite Heq_anonymous; apply (in_left_partition)).
      now (apply zNelem, Least; omega).
  (* ... and forall y, a <= y < x -> In y xs *)
  intros y Bounds; cut (In y us); [ idtac | apply Least; assumption].
    now (change us with (fst (us,vs)); rewrite Heq_anonymous; apply partition_in_left).
  Qed.

  Local Obligation Tactic := program_simpl.

  Next Obligation.
    change (match a with 0 => S (a + div2 (length xs))
               | S l => a + div2 (length xs) - l end)
      with (S (a + div2 (length xs)) - a) in neq.
    (* There must be an element of the list that occurs more than once ... *)
    assert (PH : exists x, occur _ eq_nat_dec x us >= 2).
    apply (pigeon_hole _ eq_nat_dec (seq a (S (a + div2 (length xs)) - a))).
      (* Proof that us is included in the sequence [a ... a + b] *)
      intros x Elem.
      (* by proving that any inhabitant of us lies between a and a + b *)
      apply in_seq; split.
        (* a <= x for all x in us *)
        apply (proj1 (Forall_forall (fun x => a <= x) us)); try assumption.
          change us with (fst (us,vs)); rewrite Heq_anonymous.
          now (apply forall_partition_left).
        (* x < S (a + b) for x in us *)
        assert (Lt : Forall (fun x => x < (S (a + div2 (length xs)))) us).
          now (change us with (fst (us,vs)); rewrite Heq_anonymous; apply partition_prop).
        replace (S (a + div2 (length xs)) - a + a) with
          (S (a + div2 (length xs))) by omega.
        now (apply (proj1 (Forall_forall (fun x => x < S (a + div2 (length xs))) us))).
    (* Proof that length us > legnth [a .. a + b] *)
    now (rewrite seq_length; omega).
    (* Derive a contradiction from the assumption that x contains unique values *)
    assert (U : unique_list nat us) by
      now (change us with (fst (us,vs)); rewrite Heq_anonymous; apply partition_unique_left).
    destruct PH as [x OccursTwice].
    rewrite unique_in in OccursTwice.
      now omega.
      now assumption.
      now (apply (occur_in _ eq_nat_dec); omega).
  Defined.

Program Definition minfree (xs : {xs' : list nat | unique_list nat xs'}) : 
  {m : nat | ~In m xs /\ forall y, y < m -> In y xs} 
  := minfrom 0 xs (length xs).

Local Obligation Tactic := idtac.

Next Obligation.
  intros [xs U]; split; [assumption | ].
  induction xs. 
    now (constructor).
    now (simpl in *; destruct U as [Hd Tl]; constructor; [omega | apply IHxs]).
  Defined.


Next Obligation.
  trivial.
  Defined.

Next Obligation.
  intros [xs U]; destruct_call minfrom as [m [A [B C]]]; simpl in *.
  split; [assumption | intros; apply C; split; omega].
  Defined.    

