Require Import Top.TacticNames.
Require Import Unicode.Utf8.

(* True and False laws *)
Theorem neg_true : ¬ True ↔ False.
Proof.
Admitted.
Theorem neg_false : ¬ False ↔ True.
Proof.
Admitted.
Theorem conj_true (p : Prop) : p ∧ True ↔ p.
Proof.
Admitted.
Theorem conj_false (p : Prop) : p ∧ False ↔ False.
Proof.
Admitted.
Theorem disj_true (p : Prop) : p ∨ True ↔ True.
Proof.
Admitted.
Theorem disj_false (p : Prop) : p ∨ False ↔ p.
Proof.
Admitted.
Theorem impl_true (p : Prop) : (p → True) ↔ True.
Proof.
Admitted.
Theorem true_impl (p : Prop) : (True → p) ↔ p.
Proof.
Admitted.
Theorem impl_false (p : Prop) : (p → False) ↔ ¬ p.
Proof.
Admitted.
Theorem false_impl (p : Prop) : (False → p) ↔ True.
Proof.
Admitted.



(*Impodent laws*)
Theorem axiomatic_rule (p : Prop) : p → p.
Proof.
Admitted.
Theorem trivial_equivalence (p : Prop) : p ↔ p.
Proof.
Admitted.
Theorem conj_idemp (p : Prop) : p ↔ (p ∧ p).
Proof.
Admitted.
Theorem disj_idemp (p : Prop) : p ↔ (p ∨ p).
Proof.
Admitted.

(*Absorbtion laws*)
Theorem absorbtion_disj (p q : Prop) : p ∨ (p ∧ q) ↔ p.
Proof.
Admitted.
Theorem absorbtion_conj (p q : Prop) : p ∧ (p ∨ q) ↔ p.
Proof.
Admitted.

(*Commutativity laws*)
Theorem conj_comm (p q : Prop) : (p ∧ q) ↔ (q ∧ p).
Proof.
Admitted.
Theorem disj_comm (p q : Prop) : (p ∨ q) ↔ (q ∨ p).
Proof.
Admitted.
Theorem iff_comm (p q : Prop) : (p ↔ q) ↔ (q ↔ p).
Proof.
Admitted.


(*Associativity laws*)
Theorem conj_assoc (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r).
Admitted.
Theorem disj_assoc (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r).
Proof.
Admitted.


(*Distributivity laws*)
Theorem conj_disj_distrib (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r).
Proof.
Admitted.
Theorem disj_conj_distrib (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r).
Proof.
Admitted.

(*Weak pierce law*)
(*Dont' use classical rules*)
Theorem weak_pierce_law (p q : Prop) : ((((p → q) → p) → p) → q) → q.
Proof.
Admitted.

(*3 De Morgan Intuitionistic implications*)
(*Don't use classic rules*)
Theorem morgan_disj (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q.
Proof.
Admitted.
Theorem morgan_conj_mpr (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q).
Proof.
Admitted.


(*Implication and negative implication sufficiencies*)
Theorem neg_to_impl (p q : Prop) : ¬p → (p → q) .
Proof.
Admitted.
Theorem impl_def_lr (p q : Prop) : (¬p ∨ q) → (p → q) .
Proof.
Admitted.
Theorem neg_imp_def_rl (p q : Prop) : p ∧ ¬q → ¬(p → q) .
Proof.
Admitted.

(* Direct contraposition*)
Theorem contraposition_lr (p q : Prop) : (p → q) → (¬q → ¬p).
Proof.
Admitted.


(* Exportation (currying) law*)
Theorem exportation_law (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r).
Proof.
Admitted.


(** Disjunction in implication antecedent*)
Theorem cases_impl_left (p q r : Prop) : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r).
Proof.
Admitted.


(* Syllogism *)
Theorem syllogism (p q r : Prop) : (p → q) → (q → r) → (p → r).
Proof.
Admitted.


(*Transitivity of equivalence*)
Theorem iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r).
Proof.
Admitted.


(*Congruence laws*)
Theorem neg_congr (p q : Prop) : (p ↔ q) → (¬p ↔ ¬q).
Proof.
Admitted.
Theorem disj_congr (p q r : Prop) : (p ↔ q) → ((p ∨ r) ↔ (q ∨ r)).
Proof.
Admitted.
Theorem conj_congr (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r)).
Proof.
Admitted.
Theorem impl_congr_right (p q r : Prop) : (p ↔ q) → ((p → r) ↔ (q → r)).
Proof.
Admitted.
Theorem impl_congr_left (p q r : Prop) : (p ↔ q) → ((r → p) ↔ (r → q)).
Proof.
Admitted.
Theorem iff_congr_ (p q r : Prop) : (p ↔ q) → ((p ↔ r) ↔ (q ↔ r)).
Proof.
Admitted.


(*Equivalence to both conditions*)
Theorem iff_conj_intro(p q r : Prop) : (p ↔ q) → (p ↔ r) → (p ↔ (q ∧ r)).
Proof.
Admitted.

(*Noncontradiction law*)
Theorem no_contradiction (p : Prop) : ¬(p ∧ ¬ p).
Proof.
Admitted.

(*Direct double negation*)
Theorem double_negation_lr (p : Prop) : p → ¬¬ p.
Proof.
Admitted.

(*Nonequivalence of opposites*)
(*Don't use classical rules*)
Theorem negation_not_equiv (p : Prop) : ¬(p ↔ ¬p).
Proof.
Admitted.


(*Classical double negation*)
Theorem double_negation_cl (p : Prop) : p ↔ ¬¬p.
Proof.
Admitted.

(*Classical tertsium non datur (law of excluded middle)*)
Theorem tnd_cl (p : Prop) : p ∨ ¬ p.
Proof.
Admitted.

(*Classical cases*)
Theorem cases_analysis_cl (p q : Prop) : (p → q) → (¬p → q) → q.
Proof.
Admitted.
Theorem cases_analysis_l_cl (p q r : Prop) : (p ∨ q) → (p → r) → (q → (¬p → r)) → r.
Proof.  
Admitted.
Theorem cases_analysis_r_cl (p q r : Prop) : (p ∨ q) → (q → r) → (p → (¬q → r)) → r.
Proof.
Admitted.

Theorem cases_impl_right_cl (p q r : Prop) : (p → q ∨ r) → ((p → q) ∨ (p → r)).
Proof.
Admitted.


(*One of the De Morgan classical law*)
Theorem Morgan_conj_cl (p q : Prop) : ¬ (p ∧ q) ↔ ¬p ∨ ¬q.
Proof.
Admitted.

(*Implication and neg implication classical equivalence*)
Theorem imp_def_cl (p q : Prop) : (p → q) ↔ (¬p ∨ q).
Proof.
Admitted.
Theorem neg_imp_def_cl (p q : Prop) :  ¬ (p → q) ↔ p ∧ ¬ q.
Proof.
Admitted.

(*Classical contraposition*)
Theorem contraposition_cl (p q : Prop) : (p → q) ↔ (¬q → ¬p).
Proof.
Admitted.

(*Classical Pierce law*)
Theorem pierce_cl (p q : Prop) : (((p → q) → p) → p).
Proof.      
Admitted.

(*Associativity of Equivalence*)
Theorem impl_assoc_cl (p q r : Prop) : (p ↔ (q ↔ r)) ↔ ((p ↔ q) ↔ r).
Proof.
Admitted.


(*Xor definition and notation*)
Definition xor (p q : Prop) : Prop := (p ∧ ¬q) ∨ (q ∧ ¬p).
Notation "l ⊕ r" := (xor l r) (at level 80, right associativity).

(*Xor properties*)
Theorem xor_equiv_def (p q : Prop) : (p ⊕ q) ↔ ((p ∨ q) ∧ (¬ (p ∧ q))).
Proof.
Admitted.
Theorem xor_not_iff (p q : Prop) : (p ⊕ q) ↔ (¬ (p ↔ q)).
Proof.    
Admitted.
Theorem iff_not_xor (p q : Prop) : (p ↔ q) ↔ (¬ (p ⊕ q)).
Proof.
Admitted.
Theorem xor_equal (p : Prop) : ¬ (p ⊕ p).
Proof.
Admitted.
Theorem xor_neg (p : Prop) : (p ⊕ ¬ p).
Proof.
Admitted.
Theorem xor_comm (p q : Prop) : (p ⊕ q) ↔ (q ⊕ p).
Proof.
Admitted.
Theorem xor_assoc (p q r : Prop) : ((p ⊕ q) ⊕ r) ↔ (p ⊕ (q ⊕ r)).
Proof.
Admitted.
Theorem xor_introl (p q : Prop) : (p ∧ ¬q) → (p ⊕ q).
Proof.
Admitted.
Theorem xor_intror (p q : Prop) : (q ∧ ¬p) → (p ⊕ q).
Proof.
Admitted.
Theorem xor_intro (p q : Prop) : (p ∨ q) → (¬ (p ∧ q)) → (p ⊕ q).
Proof.
Admitted.
Theorem xor_left (p q : Prop) : (p ⊕ q) → (p ∨ q).
Proof.
Admitted.
Theorem xor_right (p q : Prop) : (p ⊕ q) → (¬ (p ∧ q)).
Proof.
Admitted.
Theorem xor_elim (p q r : Prop) : (p ⊕ q) → ((p ∧ ¬q) → r) → ((q ∧ ¬p) → r) → r.
Proof.
Admitted.
