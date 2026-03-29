Require Import Top.TacticNames.
Require Import Setoid.
Require Import Unicode.Utf8.

(* Equality Introduction*)
Theorem eq_intro (T : Type) (x : T) : x = x.
Proof.
    reflexivity.
Qed.

Theorem eq_intro_2 (T : Type) (x : T) : x = x.
Proof.
    _reflexivity x h.
    assumption.
Qed.



(* Eqiality Elimination*)
(* Here we changed elimnation rule that in natural deduction*)
(* The rule is not just does (a = b) → P a → P b only for predicates*)
(* We say that our default rule is rewriting any equal term in any expression*)
Theorem eq_elim (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpb : P b) : P a.
Proof.
    rewrite -> heq.
    assumption.
Qed.

Theorem eq_elim_2 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpb : P b) : P a.
Proof.
    rewrite heq.
    assumption.
Qed.

Theorem eq_elim_3 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpa : P a) : P b.
Proof.
    rewrite <- heq.
    assumption.
Qed.

Theorem eq_elim_4 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpa : P a) : P b.
Proof.
    rewrite heq in hpa.
    assumption.
Qed.

Theorem eq_elim_5 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpb : P b) : P a.
Proof.
    rewrite <- heq in hpb.
    assumption.
Qed.

Theorem eq_elim_6 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpa : P a) (hqa : Q a) : P b ∧ Q b.
Proof.
    rewrite heq in hqa.
    rewrite heq in hpa.
    intro_and_ hpa hqa.
Qed.

Theorem eq_elim_7 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpa : P a) (hqa : Q a) : P b ∧ Q b.
Proof.
    rewrite heq in *.
    intro_and_ hpa hqa.
Qed.

Theorem eq_elim_8 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpb : P b) (hqb : Q b) : P a ∧ Q a.
Proof.
    rewrite <- heq in *.
    intro_and_ hpb hqb.
Qed.

Theorem eq_elim_9 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpa : P a) (hqa : Q a) : P b ∧ Q b.
Proof.
    rewrite heq in * |- *.
    intro_and_ hpa hqa.
Qed.

Theorem eq_elim_10 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpb : P b) (hqb : Q b) : P a ∧ Q a.
Proof.
    rewrite <- heq in * |- *.
    intro_and_ hpb hqb.
Qed.

Theorem eq_elim_11 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpb : P b) (hqb : Q b) : P a ∧ Q a.
Proof.
    rewrite heq at 1.
    rewrite heq at 1.
    intro_and_ hpb hqb.
Qed.

Theorem eq_elim_12 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpa : P a) (hqa : Q a) : P b ∧ Q b.
Proof.
    rewrite <- heq at 1.
    rewrite <- heq at 1.
    intro_and_ hpa hqa.
Qed.

Theorem eq_elim_13 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpqa : P a ∧ Q a) : P a ∧ Q b.
Proof.
    rewrite heq in hpqa at 2.
    assumption.
Qed.

Theorem eq_elim_14 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpqb : P b ∧ Q b) : P a ∧ Q b.
Proof.
    rewrite <- heq in hpqb at 1.
    assumption.
Qed.


Theorem eq_elim_15 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpb : P b) (hqb : Q b) : P a ∧ Q a.
Proof.
    rewrite heq at 1 2.
    intro_and_ hpb hqb.
Qed.

Theorem eq_elim_16 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpa : P a) (hqa : Q a) : P b ∧ Q b.
Proof.
    rewrite <- heq at 1 2.
    intro_and_ hpa hqa.
Qed.

Theorem eq_elim_17 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpa : P a) : P b.
Proof.
    replace b with a.
    assumption.
Qed.

Theorem eq_elim_18 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpa : P a) : P b.
Proof.
    replace a with b in hpa.
    assumption.
Qed.

Theorem eq_elim_19 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpa : P a) : P b.
Proof.
    replace b with a by (apply heq).
    assumption.
Qed.

Theorem eq_elim_20 (T : Type) (P : T → Prop) (a b : T) (heq : a = b) (hpb : P b) : P a.
Proof.
    replace <- b with a in hpb by (apply heq).
    assumption.
Qed.

Theorem eq_elim_21 (T : Type) (P Q : T → Prop) (a b : T) (heq : a = b) (hpa : P a ∧ Q a) : P a ∧ Q b.
Proof.
    replace -> a with b in hpa at 2 by (apply heq).
    assumption.
Qed.


Theorem eq_elim_22 (T : Type) (P : T → Prop) (a : T) (h : P a) : P a.
Proof.
    remember a as b.
    assert (hpa : P a) by (rewrite Heqb in h; assumption).
    assumption.
Qed.



(*Classical Prop introduction*)
Theorem intro_prop_cl (P Q : Prop) (h : P ↔ Q) : P = Q.
Proof.
    classical.intro_prop_eq h.
Qed.

Theorem intro_prop_cl_2 (P Q : Prop) (h : P ↔ Q) : P = Q.
Proof.
    classical.intro_prop_eq_ h h_new.
    assumption.
Qed.










