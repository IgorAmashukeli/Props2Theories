Require Import Top.TacticNames.
Require Import Unicode.Utf8.


(*Proof Context rules*)

Theorem exact_save (p : Prop) (h : p) : p.
Proof.
    exact h.
Qed.

Theorem assumption_save (p q : Prop) (h : p) (s : q) : p.
Proof.
    assumption.
Qed.

Theorem assert_hypothesis (p q : Prop) (h : p) (s : q) : p.
Proof.
    assert (s₂ : q).
     - assumption.
     - assumption.
Qed.

Theorem assert_by (p q : Prop) (h : p) (s : q) : p.
Proof.
    assert (s₂ : q) by assumption.
    assumption.
Qed.

Theorem enough_hypotheisi(p q : Prop) (h : p) (s : q) : p.
Proof.
    enough (s₂ : q).
    - assumption.
    - assumption.
Qed.

Theorem pose_term (p q : Prop) (h : p) (s : q) : p.
Proof.
    pose (s₂ := s).
    assumption.
Qed.

Theorem clear_hypothesis (p :  Prop) (h : p) (h₂ : p) : p.
Proof.
    clear h₂.
    assumption.
Qed.

Theorem repeat_hypothesis (p : Prop) (h : p) : p.
Proof.
    pose proof h as h₂.
    assumption.
Qed.



(*True, False rules*)

Theorem true_intro: True.
Proof.
    intro_true.
Qed.

Theorem true_intro_2 : True.
Proof.
    _intro_true h.
    assumption.
Qed.

Theorem false_elim (p : Prop) (h : False) : p.
Proof.
    elim_false.
    assumption.
Qed.

Theorem false_elim_2 (p : Prop) (h : False) : p.
Proof.
    elim_false_.
Qed.



(*Implication rules*)
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

Theorem implication_elim_3 (p q : Prop) (h_pq : p → q) (h_p : p) : q.
Proof.
    exact (h_pq h_p).
Qed.

Theorem implication_intro (p q : Prop) (h_pq : p -> q) : p → q.
Proof.
    intro hp.
    apply h_pq in hp.
    assumption.
Qed.

Theorem implication_intro_2 (p q : Prop) (h_pq : p -> q) : p → q.
Proof.
    intro hp.
    pose (hq := h_pq hp).
    assumption.
Qed.

Theorem implication_intro_3 (p q : Prop) (h_pq : p -> q) : p → q.
Proof.
    apply (implication_intro_2 p q h_pq).
Qed.

Theorem implication_intro_4 (p q : Prop) (h_pq : q) : p → q.
Proof.
    assert (h_pq₂ : p → q) by (intro h_p; assumption).
    assumption.
Qed.

Theorem implication_intros (p q t : Prop) (h_pqt : p → q → t) : p → q → t.
Proof.
    intros hp hq.
    apply h_pqt.
    - assumption.
    - assumption.
Qed.

(*Some additional Proof Context rules*)
Theorem repeat_tactic (p q t : Prop) (h_pqt : p → q → t) : p → q → t.
Proof.
    repeat (intro).
    apply h_pqt.
    - assumption.
    - assumption.
Qed.

Theorem comma_sep (p q t : Prop) (h_pqt : p → q → t) : p → q → t.
Proof.
    repeat (intro).
    apply h_pqt; assumption.
Qed.

Theorem bar_sep (p q t : Prop) (h_pqt : p → q → t) : p → q → t.
Proof.
    repeat (intro).
    apply h_pqt;
    [assumption| assumption].
Qed.



(*Conjunction rules*)

Theorem and_intro (p q : Prop) (h_p : p) (h_q : q) : p ∧ q.
Proof.
    intro_and.
    - assumption.
    - assumption.
Qed.


Theorem and_intro_2 (p q : Prop) (h_p : p) (h_q : q) : p ∧ q.
Proof.
    intro_and_ h_p h_q.
Qed.

Theorem add_intro_3 (p q : Prop) (h_p : p) (h_q : q) : p ∧ q.
Proof.
    _intro_and h_p h_q h_pq.
    assumption.
Qed.
    
Theorem and_left (p q : Prop) (h_pq : p ∧ q) : p.
Proof.
    elim_and h_pq h_p h_q.
    assumption.
Qed.

Theorem and_left_2 (p q : Prop) (h_pq : p ∧ q) : p.
Proof.
    elim_and_ h_pq.
Qed.

Theorem and_right (p q : Prop) (h_pq : p ∧ q) : p.
Proof.
    elim_and h_pq h_p h_q.
    assumption.
Qed.

Theorem and_right_2 (p q : Prop) (h_pq : p ∧ q) : p.
Proof.
    elim_and_ h_pq.
Qed.





(*Disjunction rules*)

Theorem or_intro_left (p q : Prop) (h_p : p) : p ∨ q.
Proof.
    left.
    assumption.
Qed.

Theorem or_intro_left_2 (p q : Prop) (h_p : p) : p ∨ q.
Proof.
    left_.
Qed.

Theorem or_intro_left_3 (p q : Prop) (h_p : p) : p ∨ q.
Proof.
    _left h_p q h_pt.
    assumption.
Qed.

Theorem or_intro_right (p q : Prop) (h_q : q) : p ∨ q.
Proof.
    right.
    assumption.
Qed.

Theorem or_intro_right_2 (p q : Prop) (h_q : q) : p ∨ q.
Proof.
    right_.
Qed.

Theorem or_intro_right_3 (p q : Prop) (h_q : q) : p ∨ q.
Proof.
    _right h_q p hpq.
    assumption.
Qed.




Theorem or_elim (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r.
Proof.
    elim_or h_pq h_p h_q.
    - apply h_pr in h_p.
      assumption.
    - apply h_qr in h_q.
      assumption.
Qed.

Theorem or_elim_2 (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r.
Proof.
    elim_or h_pq h_p h_q;
    [ (apply h_pr in h_p) | (apply h_qr in h_q) ];
    assumption.
Qed.

Theorem or_elim_3 (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r.
Proof.
    elim_or_ h_pq h_pr h_qr.
Qed.

Theorem or_elim_4 (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r.
Proof.
    _elim_or h_pq r h_pqr.
    apply h_pqr.
    - assumption.
    - assumption.
Qed.

Theorem or_elim_5 (p q r : Prop) (h_pq : p ∨ q) (h_pr : p → r) (h_qr : q → r) : r.
Proof.
    _elim_or_app h_pq h_pr h_qr hr.
    assumption.
Qed.



(**Biconditional rules*)
Theorem iff_intro (p q : Prop) (h_pq : p → q) (h_qp : q → p) : p ↔ q.
Proof.
    intro_iff.
    - assumption.
    - assumption.
Qed.

Theorem iff_intro_2 (p q : Prop) (h_pq : p → q) (h_qp : q → p) : p ↔ q.
Proof.
    intro_iff_ h_pq h_qp.
Qed.

Theorem iff_intro_3 (p q : Prop) (h_pq : p → q) (h_qp : q → p) : p ↔ q.
Proof.
    _intro_iff h_pq h_qp hifpq.
    assumption.
Qed.

Theorem iff_lr (p q : Prop) (h_pq : p ↔ q) : p → q.
Proof.
    _elim_iff h_pq h_lpq h_rpq.
    assumption.
Qed.

Theorem iff_lr_2 (p q : Prop) (h_pq : p ↔ q) : p → q.
Proof.
    elim_iff_ h_pq.
Qed.

Theorem iff_lrl (p q : Prop) (h_pq : p ↔ q) : p → q.
Proof.
    intro hp.
    _elim_iff_l h_pq hp hq.
    clear hp h_pq.
    assumption.
Qed.

Theorem iff_lrl_2 (p q : Prop) (h_pq : p ↔ q) : p → q.
    intro hp.
    elim_iff_l h_pq hp.
Qed.

Theorem iff_lrl_3 (p q : Prop) (h_pq : p ↔ q) : p → q.
    intro hp.
    elim_iff_l_ h_pq.
    assumption.
Qed.

Theorem iff_rlr (p q : Prop) (h_pq : p ↔ q) : q → p.
Proof.
    intro hq.
    _elim_iff_r h_pq hq hp.
    clear hq h_pq.
    assumption.
Qed.

Theorem iff_rlr_2 (p q : Prop) (h_qp : p ↔ q) : q → p.
Proof.
    intro hq.
    elim_iff_r h_qp hq.
Qed.

Theorem iff_rlr_3 (p q : Prop) (h_qp : p ↔ q) : q → p.
Proof.
    intro hq.
    elim_iff_r_ h_qp.
    assumption.
Qed.

Theorem iff_rl (p q : Prop) (h_pq : p ↔ q) : q → p.
Proof.
    elim_iff_ h_pq.
Qed.








(**Negation*)
Theorem neg_intro (p : Prop) (h_pF : p → False) : ¬p.
Proof.
    intro_neg h_p.
    apply h_pF.
    assumption.
Qed.

Theorem neg_intro_2 (p : Prop) (h_pF : p → False) : ¬p.
Proof.
    intro_neg_.
Qed.

Theorem neg_intro_3 (p : Prop) (h_pF : p → False) : ¬p.
Proof.
    _intro_neg h_pF hpn.
    assumption.
Qed.

Theorem neg_elim (p : Prop) (h_p : p) (h_np : ¬p) : False.
Proof.
    elim_neg h_np.
    assumption.
Qed.

Theorem neg_elim_2 (p : Prop) (h_p : p) (h_np : ¬p) : False.
Proof.
    elim_neg_ h_np.
Qed.


Theorem neg_elim_3 (p : Prop) (h_p : p) (h_np : ¬p) : False.
Proof.
    _elim_neg hpf h_np.
    exact (hpf h_p).
Qed.


Theorem neg_elim_4 (p : Prop) (h_p : p) (h_np : ¬p) : False.
Proof.
    _elim_neg_app h_p h_np hf.
    assumption.
Qed.

Theorem neg_elim_5 (p q : Prop) (h_p : p) (h_np : ¬p) : q.
Proof.
    elim_f_neg h_np.
Qed.

Theorem neg_elim_6 (p q : Prop) (h_p : p) (h_np : ¬ p) : q.
Proof.
    _elim_f_neg h_np q hq.
    assumption.
Qed.




(*Classical logic principle*)
Theorem by_contradiction_cl (p : Prop) (h_p : ¬p → False) : p.
Proof.
    classical.by_contra h_np.
    apply h_p.
    assumption.
Qed.

Theorem by_contradiction_2_cl (p : Prop) (h_p : ¬p → False) : p.
Proof.
    classical.by_contra_.
Qed.

Theorem by_contradiction_3_cl (p : Prop) (h_p : ¬p → False) : p.
Proof.
    classical._by_contra h_p hp.
    assumption.
Qed.

    









