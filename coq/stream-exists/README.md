# Stream Exists

Experiments around a problem of Igor Jirkov in an email on Coq-Club entitled `[Coq-Club] Prove the existence of pairwise matched stream`, where the goal is finding a proof of:
```
Parameter T: Type.
Parameter R: T -> T -> Prop.

Hypothesis exists_all :forall a, exists a', R a a'.

CoInductive stream : Type :=
| sintro: forall a: T, stream -> stream.

CoInductive smatch : stream -> stream -> Prop :=
| smatch_intro:
    forall a1 a2 s1' s2',
    R a1 a2 ->
    smatch s1' s2'  ->
    smatch (sintro a1 s1') (sintro a2 s2')
.

Theorem stream_ex:
  forall s, exists s', smatch s s'.
Proof.
Abort.
```
