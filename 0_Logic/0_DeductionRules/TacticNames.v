


Ltac intro_True := exact I.
Ltac elim_False h := destruct h.
Ltac intro_And := split.
Ltac elim_And h h1 h2:= destruct h as [h1 h2].
Ltac elim_Or h h1 h2:= destruct h as [h1 | h2].
Ltac intro_Iff := split.
Ltac elim_Iff h h1 h2 := destruct h as [h1 h2].
Ltac intro_Neg h := exact h.
Ltac elim_Neg h1 h2 := exact (h2 h1).


Module classical.

Axiom neg_neg_elim : forall {p : Prop}, ((p -> False) -> False) -> p.

Ltac by_contra h := apply (neg_neg_elim h).

End classical.