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
  Parameter exists_all_bis: forall a, {a': T | R a a'}.

  CoFixpoint matching_stream (s: stream): stream.
    destruct s as [a s'].
    destruct (exists_all_bis a) as [a'].
    exact (sintro a' (matching_stream s')).
  Defined.

  CoFixpoint matching_stream_is_matching (s: stream): smatch s (matching_stream s).
  Proof.
    destruct s as [a s'].
    rewrite stream_eta.
    simpl.
    destruct (exists_all_bis a) as [a' R_a_a'].
    apply smatch_intro.
    - exact R_a_a'.
    - apply matching_stream_is_matching.
  Qed.

  Theorem stream_ex:
    forall s, exists s', smatch s s'.
  Proof.
    intro s.
    exists (matching_stream s).
    apply matching_stream_is_matching.
  Qed.
End WithConstructiveExists.

Module WithChoiceAxiom.
  Require Coq.Logic.ClassicalChoice.

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
