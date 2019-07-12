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

  Theorem stream_ex_bis:
    forall s, exists s', smatch s s'.
  Proof.
    intro s.
    exists (matching_stream s).
    apply matching_stream_is_matching.
  Qed.
End WithConstructiveExists.
