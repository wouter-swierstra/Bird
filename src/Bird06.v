Require Import List.
Require Import Bool.
Require Import Recdef.
Require Import Omega.

Section a_little_theory.

  Variable datum : Set.
  Definition data : Set := list datum.
  Variable candidate : Set.
  Variable value : Set.

  Variable candidates : data -> list candidate.
  Variable eval : candidate -> value.
  Variable good : value -> bool.

  Definition solution_spec : data -> list candidate := 
    fun d => filter (fun c => good (eval c)) (candidates d).

  (* First assumption *)
  Variable extend : datum -> list candidate -> list candidate.
  Variable candidates_assumption : forall ds, candidates ds = fold_right extend nil ds.
  
  (* Second assumption *)
  Variable ok : value -> bool.
  Variable necessarily_ok : forall v, Is_true (good v) -> Is_true (ok v).
  
  Lemma filter_prop (xs : list candidate) : 
    filter (fun c => good (eval c)) xs = filter (fun c => good (eval c)) (filter (fun c => ok (eval c)) xs).
    Proof.
      induction xs as [ | x xs IHxs].
        now trivial.
        (* Cons branch *)
        case_eq (good (eval x)).
          intro isGood; assert (isOk : Is_true (ok (eval x))) by intuition.
            now (simpl; rewrite (Is_true_eq_true (ok (eval x)) isOk); simpl; rewrite isGood, IHxs).
          now (intros isNoGood; simpl; case (ok (eval x)); simpl; rewrite IHxs, isNoGood).
    Qed.

  Variable ok_search : forall d cs, 
    filter (fun c => ok (eval c)) (extend d cs)
    = filter (fun c => ok (eval c)) (extend d (filter (fun c => ok (eval c)) cs)).

  Definition extend' (x : datum) (cs : list candidate) :=
    filter (fun c => ok (eval c)) (extend x cs).

  Lemma fold_fusion {A B C: Type} (b : B) (h : C -> B -> B)
    (a : A)  (f : A -> B) (g : C -> A -> A) :
    forall xs, f a = b -> (forall x y, f (g x y) = h x (f y)) ->
    f (fold_right g a xs) = fold_right h b xs.
    Proof.
      intros xs Base Step; induction xs as [ | x xs IHxs].
        now trivial.
        now (simpl; rewrite Step, IHxs).
    Qed.

  

  Lemma search_ok : forall ds,
    solution_spec ds = filter (fun c => good (eval c)) (fold_right extend' nil ds).
    Proof.
      intros ds; unfold solution_spec, extend'.
      rewrite (candidates_assumption ds).
      rewrite filter_prop.
      rewrite (fold_fusion nil extend').
        now trivial.
        now trivial.
        now (intros; unfold extend'; rewrite ok_search).
    Qed.

  Variable modify : datum -> list value -> list value.

  Variable modify_prop : forall x cs, map eval (extend x cs) = modify x (map eval cs).

  Definition fork {A B C : Type} (fg : (A -> B) * (A -> C)) : A -> B * C := 
    match fg with
      (f , g) => fun x => (f x , g x)
    end.

  Definition cross {A B C D : Type} : (A -> B) * (C -> D) -> A * C -> B * D :=
    fun fg xy => match fg, xy with
                | (f , g) , (x , y) => (f x, g y)
              end.

  Definition candidates' (ds : data) : list (candidate * value) := 
    map (fun x => fork ((fun x => x),eval) x) (fold_right extend' nil ds).

  Definition uncurry (A B C : Type) (f : A -> B -> C) (xy : A * B) : C :=
    match xy with
      | (x , y) => f x y
    end.

  Definition zip (A B : Type) (xsys : list A * list B) : list (A * B) :=
    uncurry (list A) (list B) (list (A * B)) (fun xs ys => combine xs ys) xsys.

  Implicit Arguments zip.

  Definition expand (x : datum) (cvs : list (candidate * value)) : list (candidate * value) :=
    filter (fun cv => ok (snd cv)) (zip (cross (extend x, modify x) (split cvs))).

  Definition candidates'' (ds : data) : list (candidate * value) := fold_right expand nil ds.

  Lemma (* 6.9 *) map_fork_zip {A B C : Type} 
    (f : A -> B) (g : A -> C) (xs : list A) :
    map (fun x => fork (f,g) x) xs = zip (fork (fun xs => map f xs, fun xs => map g xs) xs).
    Proof.
      induction xs as [ | x xs IHxs].
        now (reflexivity).
        simpl in *.
        rewrite IHxs.
        reflexivity.
    Qed.

  Lemma (* 6.10 *) map_fork_filter {A B C : Type}
    (f : A -> B) (g : A -> C) (p : C -> bool) : forall xs,
    map (fun xy => fork (f,g) xy) (filter (fun x => p (g x)) xs)
    = filter (fun xy => p (snd xy)) (map (fun x => fork (f,g) x) xs).
    Proof.
      induction xs as [ | x xs IHxs].
        reflexivity.
        simpl in *; case (p (g x)).
        simpl.
        rewrite IHxs.
        reflexivity.
        simpl; rewrite IHxs.
        reflexivity.
     Qed.

  Lemma map_id {A : Type} (xs : list A) : map (fun x => x) xs = xs.
    induction xs as [ | x xs IHxs];
      [trivial | simpl; rewrite IHxs; reflexivity].
  Qed.
    
  Lemma fork_split (* 6.6 *) {A B C D : Type} (f : A -> B) (g : A -> C) (h : D -> A) :
    forall d, fork (fun x => f x, fun x => g x) (h d) = fork (fun x => f (h x), fun x => g (h x)) d.
    Proof. trivial. Qed.

  Lemma fork_cross (* 6.7 *) {A B C D B' C' D' : Type} 
    (f : B -> C) (h : A -> B) (g : B' -> C') (k : A -> B') :
    (fun xy => fork ((fun x => f (h x)), fun x => (g (k x))) xy)
      = (fun xy => cross (f,g) (fork (h,k) xy)).
    Proof. reflexivity. Qed.

  Lemma fork_map (* 6.8 *) {A B C : Type} (f : A -> B) (g : A -> C) : forall xs,
    fork ((fun xs => map f xs), (fun ys => map g ys)) xs = split (map (fun xy => fork (f,g) xy) xs).
    Proof.
      induction xs as [ | x xs IHxs].
      reflexivity.
      simpl in *.
      rewrite <- IHxs.
      reflexivity.
    Qed.

  Lemma candidates_correct (ds : data) :
    candidates' ds = candidates'' ds.
    Proof.
      unfold candidates', candidates''.
      rewrite (fold_fusion nil expand).
        now trivial.
        now trivial.
        intros d cs; unfold extend'.
        rewrite map_fork_filter, map_fork_zip, fork_split; simpl.
        rewrite modify_prop, map_id.
        change (combine (extend d cs) (modify d (map eval cs))) with
          (zip (fork (extend d, fun cs => modify d (map eval cs)) cs)).
        unfold expand.
        change (fork (extend d, fun cs => modify d (map eval cs)) cs) with
          (cross (extend d, modify d) (fork (fun x => x, map eval) cs)).
        cutrewrite ((fork (fun x => x, map eval) cs) = split (map (fork (fun x => x, eval)) cs)).
        reflexivity.
        simpl.
        induction cs as [ | x xs IHxs].
          reflexivity.
          simpl.
          rewrite <- IHxs.
          reflexivity.
    Qed.

  Definition solutions : data -> list candidate := 
    fun ds => map (fun cv => fst cv) (filter (fun cv => good (snd cv)) (candidates'' ds)).

  Lemma map_filter {A B : Type} (f : A -> B) (p : B -> bool) : forall xs,
    filter p (map f xs) = map f (filter (fun x => p (f x)) xs).
  Proof.
    induction xs as [ | x xs IHxs].
      reflexivity.
       simpl.
       case (p (f x)).
       simpl.
       rewrite IHxs.
       reflexivity.
       rewrite IHxs.
       reflexivity.
   Qed.

  Lemma solutions'_satisfies_spec : forall ds, solution_spec ds = solutions ds.
    intros ds.
    rewrite search_ok.
    unfold solutions.
    rewrite <- candidates_correct.
    unfold candidates'.
    rewrite map_filter.
    rewrite map_map.
    simpl.
    rewrite map_id.
    reflexivity.
  Qed.

End a_little_theory.

Definition digit : Set := nat.

Definition factor : Set := list digit.

Definition term := list factor.

Definition expression := list term.

Fixpoint sum (xs : list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.
   
Fixpoint product (xs : list nat) : nat :=
  match xs with
    | nil => 1
    | x :: xs => x * sum xs
  end.

Fixpoint eval_factor (f : factor) : nat := 
  match f with
    | nil => 0
    | x :: xs => fold_left (fun n d => 10 * n + d) xs x
  end.

Definition eval_term : term -> nat := fun t => product (map eval_factor t).

Definition eval_expression : expression -> nat := fun e => sum (map eval_term e).

Definition good (n : nat) : Prop := n = 100.
