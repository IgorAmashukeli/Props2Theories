Require Import TacticNames.
Require Import Unicode.Utf8.

(*Assumption rules*)

Theorem exact_save (p : Prop) (h : p) : p.
Proof.
    exact h.
Qed.


Theorem assumption_save (p : Prop) (h : p) : p.
Proof.
    assumption.
Qed.





(*True, False rules*)

Theorem true_intro: True.
Proof.
    intro_True.
Qed.

Theorem false_elim (p : Prop) (h : False) : p.
Proof.
    elim_False h.
Qed.



(*Implication rules*)
Theorem implication_intro (p q : Prop) (h_pq : p -> q) : p → q.
Proof.
    intro hp.
    exact (h_pq hp).
Qed.

Theorem implication_elim (p q : Prop) (h_pq : p → q) (h_p : p) : q.
Proof.
    apply h_pq.
    assumption.
Qed.

Theorem implication_elim_2 (p q : Prop) (h_pq : p → q) (h_p : p) : q.
Proof.
    apply h_pq in h_p.
    assumption.
Qed.
  




(*Conjunction rules*)

Theorem and_intro (p q : Prop) (h_p : p) (h_q : q) : p ∧ q.
Proof.
    intro_And.
    - assumption.
    - assumption.
Qed.

Theorem and_left (p q : Prop) (h_pq : p ∧ q) : p.
Proof.
    elim_And h_pq h_p h_q.
    assumption.
Qed.

Theorem and_right (p q : Prop) (h_pq : p ∧ q) : p.
Proof.
    elim_And h_pq h_p h_q.
    assumption.
Qed.



(*Disjunction rules*)

Theorem or_intro_left (p q : Prop) (h_p : p) : p ∨ q.
Proof.
    left.
    assumption.
Qed.

Theorem or_intro_right (p q : Prop) (h_q : q) : p ∨ q.
Proof.
    right.
    assumption.
Qed.

Theorem or_elim (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r.
Proof.
    elim_Or h_pq h_p h_q.
    - apply h_pr in h_p.
      assumption.
    - apply h_qr in h_q.
      assumption.
Qed.



(**Equivalence rules*)
Theorem iff_intro (p q : Prop) (h_pq : p → q) (h_qp : q → p) : p ↔ q.
Proof.
    intro_Iff.
    - assumption.
    - assumption.
Qed.

Theorem iff_lr (p q : Prop) (h_pq : p ↔ q) : p → q.
Proof.
    elim_Iff h_pq h_lpq h_rpq.
    assumption.
Qed.


Theorem iff_rl (p q : Prop) (h_pq : p ↔ q) : q → p.
Proof.
    elim_Iff h_pq h_lpq h_rpq.
    assumption.
Qed.



(**Negation*)
Theorem neg_intro (p : Prop) (h_pF : p → False) : ¬p.
Proof.
    intro_Neg h_pF.
Qed.

Theorem neg_elim (p : Prop) (h_p : p) (h_np : ¬p) : False.
Proof.
    elim_Neg h_p h_np.
Qed.


Theorem by_contradiction (p : Prop) (h_p : ¬p → False) : p.
Proof.
    classical.by_contra h_p.
Qed.

    
    
    









