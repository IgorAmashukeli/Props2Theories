Require Import Top.TacticNames.
Require Import Unicode.Utf8.

(*Universal Quantifier rules*)
Theorem universal_elim (T : Type) (P : T → Prop) (h : ∀ x, P x) (a : T) : P a.
Proof.
    apply h.
Qed.

Theorem universal_elim_2 (T : Type) (P : T → Prop) (h : ∀ x, P x) (a : T) : P a.
Proof.
    specialize (h a).
    assumption.
Qed.

Theorem universal_elim_4 (T : Type) (P : T → Prop) (h : ∀ x, P x) (a : T) : P a.
Proof.
    pose (ha := h a).
    assumption.
Qed.

Theorem universal_elim_3 (T : Type) (P : T → Prop) (h : ∀ x, P x) (a : T) : P a.
Proof.
    exact (h a).
Qed.

Theorem universal_intro (T : Type) (P : T → Prop) (h : ∀ x, P x) : ∀ x, P x.
Proof.
    intro x.
    apply h.
Qed.

Theorem universal_intro_2 (T : Type) (P : T → Prop) (h : ∀ x, P x) : ∀ x, P x.
Proof.
    assert (h₂ : ∀ x, P x) by (exact h).
    assumption.
Qed.

Theorem universal_intros (T : Type) (P : T → T → Prop) (h : ∀ x y, P x y) : ∀ x y, P x y.
Proof.
    intros x y.
    apply h.
Qed.


(*Existential Quantifier rules**)
Theorem exists_intro (T : Type) (P : T → Prop) (a : T) (h : P a) : ∃ x, P x.
Proof.
    exists a.
    assumption.
Qed.

Theorem exists_intro_2 (T : Type) (P : T → Prop) (a : T) (h : P a) : ∃ x, P x.
Proof.
    exists_ a h.
Qed.

Theorem exists_intro_3 (T : Type) (P : T → Prop) (a : T) (h : P a) : ∃ x, P x.
    _exists a h he.
    assumption.
Qed.

Theorem exists_elim (T : Type) (P : T → Prop) (Q : Prop) (h : ∃ x, P x) (hq : ∀ x, (P x → Q)) : Q.
Proof.
    exists_elim h a ha.
    specialize (hq a).
    apply hq.
    assumption.
Qed.

Theorem exists_elim_2 (T : Type) (P : T → Prop) (Q : Prop) (h : ∃ x, P x) (hq : ∀ x, (P x → Q)) : Q.
Proof.
    exists_elim_ h hq.
Qed.

Theorem exists_elim_3 (T : Type) (P : T → Prop) (Q : Prop) (h : ∃ x, P x) (hq : ∀ x, (P x → Q)) : Q.
Proof.
    _exists_elim h Q hfoll.
    apply hfoll.
    assumption.
Qed.

Theorem exists_elim_4 (T : Type) (P : T → Prop) (Q : Prop) (h : ∃ x, P x) (hq : ∀ x, (P x → Q)) : Q.
Proof.
    _exists_elim_app h Q hfoll hq.
    assumption.
Qed.






    







