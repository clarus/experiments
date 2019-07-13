Require Coq.Logic.ClassicalChoice.
Require Coq.Logic.ChoiceFacts.

Parameter T: Type.
Parameter R: T -> T -> Prop.

Hypothesis exists_all: forall a, exists a', R a a'.

CoInductive stream : Type :=
| sintro: forall a: T, stream -> stream.

CoInductive smatch : stream -> stream -> Prop :=
| smatch_intro:
    forall a1 a2 s1' s2',
    R a1 a2 ->
    smatch s1' s2'  ->
    smatch (sintro a1 s1') (sintro a2 s2').

Lemma stream_eta (s: stream): s = match s with sintro a s' => sintro a s' end.
Proof.
  destruct s; reflexivity.
Qed.

Theorem stream_ex:
  forall s, exists s', smatch s s'.
Proof.
Abort.

Module WithConstructiveExists.
  CoFixpoint matching_stream
    (exists_all: forall a, {a': T | R a a'})
    (s: stream)
    : stream.
    destruct s as [a s'].
    destruct (exists_all a) as [a'].
    exact (sintro a' (matching_stream exists_all s')).
  Defined.

  CoFixpoint matching_stream_is_matching
    (exists_all: forall a, {a': T | R a a'})
    (s: stream)
    : smatch s (matching_stream exists_all s).
  Proof.
    destruct s as [a s'].
    rewrite stream_eta.
    simpl.
    destruct (exists_all a) as [a' R_a_a'].
    apply smatch_intro.
    - exact R_a_a'.
    - apply matching_stream_is_matching.
  Qed.

  Theorem stream_ex
    (exists_all: forall a, {a': T | R a a'})
    : forall s, exists s', smatch s s'.
  Proof.
    intro s.
    exists (matching_stream exists_all s).
    apply matching_stream_is_matching.
  Qed.
End WithConstructiveExists.

Module WithChoiceAxiom.
  Definition choice_axiom_instance :=
    ClassicalChoice.choice (A := T) (B := T) R.

  CoFixpoint matching_stream (f: T -> T) (s: stream): stream :=
    match s with
    | sintro a s' => sintro (f a) (matching_stream f s')
    end.

  CoFixpoint matching_stream_is_matching
    (f: T -> T)
    (f_is_sound: forall a, R a (f a))
    (s: stream)
    : smatch s (matching_stream f s).
  Proof.
    destruct s as [a s'].
    rewrite stream_eta.
    simpl in *.
    apply smatch_intro.
    - apply f_is_sound.
    - apply matching_stream_is_matching; trivial.
  Qed.

  Theorem stream_ex:
    forall s, exists s', smatch s s'.
  Proof.
    intro s.
    destruct choice_axiom_instance as [f f_is_sound].
    - exact exists_all.
    - exists (matching_stream f s).
      apply (matching_stream_is_matching f f_is_sound).
  Qed.
End WithChoiceAxiom.

Module WithChoiceAxiomAndConstructiveExists.
  Theorem stream_ex:
    forall s, exists s', smatch s s'.
  Proof.
    apply ChoiceFacts.relative_non_contradiction_of_indefinite_descr.
    - intros H s.
      apply WithConstructiveExists.stream_ex.
      intro a.
      unfold ChoiceFacts.ConstructiveIndefiniteDescription_on in H.
      apply H with (P := fun a' => R a a').
      apply exists_all.
    - unfold ChoiceFacts.FunctionalChoice_on.
      apply ClassicalChoice.choice.
  Qed.
End WithChoiceAxiomAndConstructiveExists.

(* Asked by Christian Doczkal. *)
Module SupplementaryExercise.
  CoInductive stream (T: Type) : Type :=
  | sintro: forall a: T, stream T -> stream T.

  Lemma stream_eta {T: Type} (s: stream T): s = match s with sintro _ a s' => sintro _ a s' end.
  Proof.
    destruct s; reflexivity.
  Qed.

  CoInductive smatch {T: Type} (R: T -> T -> Prop) : stream T -> stream T -> Prop :=
  | smatch_intro:
    forall (a1 a2: T) (s1' s2': stream T),
    R a1 a2 ->
    smatch R s1' s2'  ->
    smatch R (sintro T a1 s1') (sintro T a2 s2').

  Definition stream_ex :=
    forall T (R : T -> T -> Prop),
      (forall a, exists a', R a a') -> forall s, exists s', smatch R s s'.

  CoFixpoint counting_stream {X: Type} (x: X) (n: nat): stream (nat * X) :=
    sintro _ (n, x) (counting_stream x (S n)).

  Fixpoint nth {T: Type} (s: stream T) (n: nat): T :=
    let (a, s') := s in
    match n with
    | O => a
    | S n' => nth s' n'
    end.

  Fixpoint nth_counting_stream {X: Type} (x: X) (n m: nat): nth (counting_stream x m) n = (n + m, x).
    destruct n as [| n']; simpl.
    - reflexivity.
    - rewrite plus_n_Sm.
      apply (nth_counting_stream _ x n' (S m)).
  Qed.

  Fixpoint nth_smatch_streams
    {T: Type}
    {R: T -> T -> Prop}
    (s1 s2: stream T)
    (H_smatch: smatch R s1 s2)
    (n: nat)
    : R (nth s1 n) (nth s2 n).
    destruct n as [| n'].
    - destruct H_smatch.
      simpl.
      assumption.
    - destruct H_smatch.
      simpl.
      apply nth_smatch_streams.
      assumption.
  Qed.

  Theorem stream_ex_implies_countable_choice X (P : nat -> X -> Prop) :
    stream_ex -> (forall n, exists x, P n x) -> exists f, forall n, P n (f n).
  Proof.
    intros H_stream_ex H_exists.
    pose (T := (nat* X)%type).
    pose (R := fun (x y: T) => P (fst x) (snd y)).
    destruct (H_exists O) as [x].
    assert (H_exists_R: forall ny, exists n'y', R ny n'y').
    - intro ny; destruct ny as [n y].
      destruct (H_exists n) as [y' Hy'].
      exists (n, y').
      apply Hy'.
    - destruct (H_stream_ex _ R H_exists_R (counting_stream x O)) as [s Hs].
      exists (fun n => snd (nth s n)).
      intro n.
      replace n with (fst (n, x)) at 1; trivial.
      rewrite (plus_n_O n) at 1.
      rewrite <- nth_counting_stream.
      apply (nth_smatch_streams (counting_stream x 0) s Hs).
  Qed.
End SupplementaryExercise.
