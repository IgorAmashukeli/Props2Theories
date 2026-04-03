import Props2Theories.TacticNames

-- True and False laws
theorem neg_true : ¬ True ↔ False:= by
  intro_iff
  · intro h_nt
    elim_neg h_nt
    intro_true
  · intro h_f
    elim_false_



theorem neg_false : ¬ False ↔ True := by
  intro_iff
  · intro h_nt
    intro_true
  · intro h_t
    intro_neg h_f
    assumption


theorem conj_true (p : Prop) : p ∧ True ↔ p := by
  intro_iff
  · intro h_pt
    elim_and_ h_pt
  · intro h_p
    intro_and
    · assumption
    · intro_true




theorem conj_false (p : Prop) : p ∧ False ↔ False := by
  intro_iff
  · intro h_pf
    elim_and_ h_pf
  · intro h_pf
    elim_false_


theorem disj_true (p : Prop) : p ∨ True ↔ True := by
  intro_iff
  · intro h_pt
    elim_or h_pt, h_p, h_t <;> intro_true
  · intro h_pt
    right_


theorem disj_false (p : Prop) : p ∨ False ↔ p := by
  intro_iff
  · intro h_pf
    elim_or h_pf, h_p, h_f
    · assumption
    · elim_false_
  · intro h_pt
    left_


theorem impl_true (p : Prop) : (p → True) ↔ True := by
  intro_iff
  · intro h_pt
    intro_true
  · intros h_t h_p
    assumption



theorem true_impl (p : Prop) : (True → p) ↔ p := by
  intro_iff
  · intro h_tp
    apply h_tp
    intro_true
  · intros h_p h_t
    assumption


theorem impl_false (p : Prop) : (p → False) ↔ ¬ p := by
  intro_iff
  · intro h_pf
    intro_neg_
  · intros h_np h_p
    elim_neg_ h_np


theorem false_impl (p : Prop) : (False → p) ↔ True := by
  intro_iff
  · intro h_fp
    intro_true
  · intros h_t h_f
    elim_false_







--Impodent laws
theorem axiomatic_rule (p : Prop) : p → p := by
  intro h_p
  assumption


theorem trivial_equivalence (p : Prop) : p ↔ p := by
  intro_iff <;> apply axiomatic_rule


theorem conj_idemp (p : Prop) : p ↔ (p ∧ p) := by
  intro_iff
  · intro h_p
    intro_and_ h_p, h_p
  · intro h_pp
    elim_and_ h_pp


theorem disj_idemp (p : Prop) : p ↔ (p ∨ p) := by
  intro_iff
  · intro h_p
    left_
  · intro h_pp
    elim_or_ h_pp, (axiomatic_rule p), (axiomatic_rule p)



--Absorbtion laws
theorem absorbtion_disj (p q : Prop) : p ∨ (p ∧ q) ↔ p := by
  intro_iff
  · intro h_ppq
    have h_pqp : (p ∧ q) → p := by intro h_pq; elim_and_ h_pq
    elim_or_ h_ppq, (axiomatic_rule p), (h_pqp)
  · intro h_p
    left_


theorem absorbtion_conj (p q : Prop) : p ∧ (p ∨ q) ↔ p := by
  intro_iff
  · intro h_ppq
    elim_and_ h_ppq
  · intro h_p
    intro_and
    · assumption
    · left_



--Commutativity laws
theorem conj_symm (p q : Prop) : (p ∧ q) → (q ∧ p) := by
  intro h_pq
  elim_and h_pq, h_p, h_q
  intro_and <;> assumption

theorem conj_commut (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by
  intro_iff <;> apply conj_symm

theorem disj_symm (p q : Prop) : (p ∨ q) → (q ∨ p) := by
  intro h_pq
  elim_or h_pq, h_p, h_q
  · right_
  · left_

theorem disj_commut (p q : Prop) : (p ∨ q) ↔ (q ∨ p) := by
  intro_iff <;> apply disj_symm

theorem iff_symm (p q : Prop) : (p ↔ q) → (q ↔ p) := by
  intro h_pq
  intro_iff <;> elim_iff_ h_pq

theorem iff_commut (p q : Prop) : (p ↔ q) ↔ (q ↔ p) := by
  intro_iff <;> apply iff_symm


--Associativity laws
theorem conj_assoc (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  intro_iff
  · intro h_pqr
    elim_and h_pqr, h_pq, h_r
    elim_and h_pq, h_p, h_q
    intro_and <;> try assumption
    intro_and <;> assumption
  · intro h_pqr
    elim_and h_pqr, h_p, h_qr
    elim_and h_qr, h_q, h_r
    intro_and <;> try assumption
    intro_and <;> assumption



theorem disj_assoc (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  intro_iff
  · intro h_pqr
    elim_or h_pqr, h_pq, h_r
    · elim_or h_pq, h_p, h_q
      · left_
      · right; left_
    · right
      right_
  · intro h_pqr
    elim_or h_pqr, h_p, h_qr
    · left;
      left_
    · elim_or h_qr, h_q, h_r
      · left
        right_
      · right_


--Distributivity laws
theorem conj_disj_distrib (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  intro_iff
  · intro h_pqr
    elim_and h_pqr, h_p, h_qr
    elim_or h_qr, h_q, h_r
    · left
      intro_and_ h_p, h_q
    · right
      intro_and_ h_p, h_r
  · intro h_pqr
    elim_or h_pqr, h_pq, h_pr
    · elim_and h_pq, h_p, h_q
      intro_and
      · assumption
      · left_
    · elim_and h_pr, h_p, h_r
      intro_and
      · assumption
      · right_



theorem disj_conj_distrib (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  intro_iff
  · intro h_pqr
    elim_or h_pqr, h_p, h_qr
    · intro_and <;> left_
    · elim_and h_qr, h_q, h_r
      intro_and <;> right_
  · intro h_pqr
    elim_and h_pqr, h_pq, h_pr
    elim_or h_pq, h_p, h_q <;>
    elim_or h_pr, h_p, h_r <;>
    try left_
    right
    intro_and_ h_q, h_r




--Weak pierce law
--Dont' use classical rules
theorem weak_pierce_law (p q : Prop) : ((((p → q) → p) → p) → q) → q := by
  intro h_pqppq
  apply h_pqppq
  intro h_pqp
  apply h_pqp
  intro h_p
  apply h_pqppq
  intro h_pqp₂
  assumption



--3 De Morgan Intuitionistic implications
--Don't use classic rules
theorem morgan_disj (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  intro_iff
  · intro h_npq
    intro_and
    · intro_neg h_p
      elim_neg h_npq
      left_
    · intro_neg h_q
      elim_neg h_npq
      right_
  · intro h_np_nq
    intro_neg h_pq
    elim_and h_np_nq, h_np, h_nq
    elim_or h_pq, h_p, h_q
    · elim_neg_ h_np
    · elim_neg_ h_nq


theorem morgan_conj_rl (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h_np_nq
  intro h_pq
  elim_and h_pq, h_p, h_q
  elim_or h_np_nq, h_np, h_nq
  · elim_neg_ h_np
  · elim_neg_ h_nq




--Implication and negative implication sufficiencies
theorem neg_to_impl (p q : Prop) : ¬p → (p → q)  := by
  intros h_np h_p
  elim_f_neg h_np


theorem impl_def_lr (p q : Prop) : (¬p ∨ q) → (p → q)  := by
  intros h_npq h_p
  elim_or h_npq, h_np, h_q
  · elim_f_neg h_np
  · assumption


theorem neg_imp_def_rl (p q : Prop) : p ∧ ¬q → ¬(p → q)  := by
  intro h_p_nq
  intro_neg h_piq
  elim_and h_p_nq, h_p, h_nq
  specialize (h_piq h_p)
  elim_neg_ h_nq



-- Direct contraposition
theorem contraposition_lr (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intro h_pq h_nq
  intro_neg h_p
  elim_neg h_nq
  apply h_pq
  assumption




-- Exportation (currying) law
theorem exportation_law (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r) := by
  intro_iff
  · intros h_pqr h_pq
    elim_and h_pq, h_p, h_q
    apply h_pqr <;> assumption
  · intros h_pqr h_p h_q
    apply h_pqr
    intro_and_ h_p, h_q



--* Disjunction in implication antecedent
theorem cases_impl_left (p q r : Prop) : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  intro_iff
  · intro h_pqr
    intro_and
    · intro h_p
      apply h_pqr
      left_
    · intro h_q
      apply h_pqr
      right_
  · intros h_pr_qr h_pq
    elim_and h_pr_qr, h_pr, h_qr
    elim_or h_pq, h_p, h_q
    · exact (h_pr h_p)
    · exact (h_qr h_q)



-- Syllogism
theorem syllogism (p q r : Prop) : (p → q) → (q → r) → (p → r) := by
  intros h_pq h_qr h_p
  apply h_qr
  apply h_pq
  assumption




--Transitivity of equivalence
theorem iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r) := by
  intro h_pq
  intro h_qr
  intro_iff
  · apply (syllogism p q r)
    · elim_iff_ h_pq
    · elim_iff_ h_qr
  · apply (syllogism r q p)
    · elim_iff_ h_qr
    · elim_iff_ h_pq




--Congruence laws
theorem neg_congr (p q : Prop) : (p ↔ q) → (¬p ↔ ¬q) := by
  intro h_pq
  intro_iff
  · intro h_np
    intro_neg h_q
    elim_neg h_np
    apply_r_ h_pq
  · intro h_nq
    intro_neg h_p
    elim_neg h_nq
    apply_l_ h_pq



theorem disj_congr (p q r : Prop) : (p ↔ q) → ((p ∨ r) ↔ (q ∨ r)) := by
  intro h_pq
  intro_iff
  · intro h_pr
    elim_or h_pr, h_p, h_r
    · left
      apply_l_ h_pq
    · right_
  · intro h_qr
    elim_or h_qr, h_q, h_
    · left
      apply_r_ h_pq
    · right_


theorem conj_congr (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r)) := by
  intro h_pq
  intro_iff
  · intro h_pr
    elim_and h_pr, h_p, h_r
    intro_and <;>
    (try (apply_l_ h_pq)) <;>
    assumption
  · intro h_qr
    elim_and h_qr, h_q, h_r
    intro_and <;>
    (try (apply_r_ h_pq)) <;>
    assumption



theorem impl_congr_right (p q r : Prop) : (p ↔ q) → ((p → r) ↔ (q → r)) := by
  intro h_pq
  intro_iff
  · intros h_pr h_q
    apply h_pr
    apply_r_ h_pq
  · intros h_qr h_p
    apply h_qr
    apply_l_ h_pq


theorem impl_congr_left (p q r : Prop) : (p ↔ q) → ((r → p) ↔ (r → q)) := by
  intro h_pq
  intro_iff
  · intros h_rp h_r
    apply_l h_pq
    exact (h_rp h_r)
  · intros h_rq h_r
    apply_r h_pq
    exact (h_rq h_r)




theorem iff_congr_ (p q r : Prop) : (p ↔ q) → ((p ↔ r) ↔ (q ↔ r)) := by
  intro h_pq
  have h_pr_qr := impl_congr_right p q r h_pq
  have h_rp_rq := impl_congr_left p q r h_pq
  intro_iff
  · intro h_pr
    elim_iff h_pr, h_p_r, h_r_p
    _apply_l h_pr_qr, h_p_r, h_qr
    _apply_l h_rp_rq, h_r_p, h_rq
    intro_iff_ h_qr, h_rq
  · intro h_qr
    elim_iff h_qr, h_q_r, h_r_q
    _apply_r h_pr_qr, h_q_r, h_pr
    _apply_r h_rp_rq, h_r_q, h_rp
    intro_iff_ h_pr, h_rp





--Equivalence to both conditions
theorem iff_conj_intro(p q r : Prop) : (p ↔ q) → (p ↔ r) → (p ↔ (q ∧ r)) := by
  intros h_pq h_pr
  intro_iff
  · intro h_p
    intro_and
    · apply_l_ h_pq
    · apply_l_ h_pr
  · intro h_qr
    elim_and h_qr, h_q, h_r
    apply_r_ h_pq



--Noncontradiction law
theorem no_contradiction (p : Prop) : ¬(p ∧ ¬ p) := by
  intro_neg h_p_np
  elim_and h_p_np, h_p, h_np
  elim_neg_ h_np


--Direct double negation
theorem double_negation_lr (p : Prop) : p → ¬¬ p := by
  intro hp
  intro_neg h_np
  elim_neg_ h_np



--Nonequivalence of opposites
--Don't use classical rules
theorem negation_not_equiv (p : Prop) : ¬(p ↔ ¬p) := by
  intro h_p_np
  have h_np : ¬p := by
    intro_neg h_p
    _apply_l h_p_np, h_p, h_np
    elim_neg_ h_np
  _apply_r h_p_np, h_np, h_p
  elim_neg_ h_np




--Classical double negation
theorem double_negation_cl (p : Prop) : p ↔ ¬¬p := by
  intro_iff
  · exact (double_negation_lr p)
  · intro h_n_np
    by_contra h_np
    elim_neg_ h_n_np



--Classical tertsium non datur (law of excluded middle)
theorem tnd_cl (p : Prop) : p ∨ ¬ p := by
  by_contra h_n_pnp
  _apply_l (morgan_disj p (¬p)), h_n_pnp, h_np_nnp
  elim_and h_np_nnp, h_np, h_nnp
  clear h_np_nnp h_n_pnp
  elim_neg_ h_nnp



--Classical cases
theorem cases_analysis_cl (p q : Prop) : (p → q) → (¬p → q) → q := by
  intros h_pq h_npq
  elim_or (tnd_cl p), h_p, h_np
  · exact (h_pq h_p)
  · exact (h_npq h_np)


theorem cases_analysis_l_cl (p q r : Prop) : (p ∨ q) → (p → r) → (q → (¬p → r)) → r := by
  intros h_pq h_pr h_qnpr
  apply cases_analysis_cl p r
  · assumption
  · elim_or h_pq, h_p, h_q <;> intro h_np
    · elim_f_neg h_np
    · apply h_qnpr <;> assumption



theorem cases_analysis_r_cl (p q r : Prop) : (p ∨ q) → (q → r) → (p → (¬q → r)) → r := by
  intros h_pq h_qr h_pnqr
  apply cases_analysis_cl q r
  · assumption
  · elim_or h_pq, h_p, h_q <;> intro h_nq
    · apply h_pnqr <;> assumption
    · elim_f_neg h_nq



theorem cases_impl_right_cl (p q r : Prop) : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h_pqr
  apply (cases_analysis_cl p)
  · intro h_p
    specialize h_pqr h_p
    elim_or h_pqr, h_q, h_r
    · left; intro h_p₂; assumption
    · right; intro h_p₂; assumption
  · intro h_np
    left
    apply (neg_to_impl)
    assumption



--One of the De Morgan classical law
theorem Morgan_conj_cl (p q : Prop) : ¬ (p ∧ q) ↔ ¬p ∨ ¬q := by
  intro_iff <;> try (apply (morgan_conj_rl p q))
  intro h_npq
  by_contra h_n_np_nq
  _apply_l (morgan_disj (¬p) (¬q)), h_n_np_nq, h_nnp_nnq
  elim_and h_nnp_nnq, h_nnp, h_nnq
  elim_neg h_npq
  intro_and <;> apply_r_ (double_negation_cl _)


--Implication and neg implication classical equivalence
theorem impl_def_cl (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  intro_iff <;> try (apply (impl_def_lr (p) q))
  intro h_pq
  apply (cases_analysis_cl p)
  · intro h_p
    right; exact (h_pq h_p)
  · intro h_np
    left_


theorem neg_imp_def_cl (p q : Prop) :  ¬ (p → q) ↔ p ∧ ¬ q := by
  intro_iff <;> try (apply (neg_imp_def_rl p q))
  intro h_npq
  intro_and
  · by_contra h_np
    elim_neg h_npq
    intro h_p
    elim_f_neg h_np
  · intro h_q
    elim_neg h_npq
    intro h_p; assumption



--Classical contraposition
theorem contraposition_cl (p q : Prop) : (p → q) ↔ (¬q → ¬p) := by
  intro_iff <;> try (apply (contraposition_lr p q))
  intro h_nq_np
  intro h_p
  by_contra h_nq
  specialize (h_nq_np h_nq)
  elim_neg_ h_nq_np



--Classical Pierce law
theorem pierce_cl (p q : Prop) : (((p → q) → p) → p) := by
  intro h_pqp
  by_contra h_np
  specialize (h_pqp (neg_to_impl p q h_np))
  elim_neg_ h_np



--Associativity of Equivalence
theorem impl_assoc_cl (p q r : Prop) : (p ↔ (q ↔ r)) ↔ ((p ↔ q) ↔ r) := by
  intro_iff
  · intro h_pqr
    intro_iff
    · intro h_pq
      apply (cases_analysis_cl p)
      · intro h_p
        _apply_l h_pq, h_p, h_q
        _apply_l h_pqr, h_p, h_qr
        apply_l h_qr; assumption
      · intro h_np
        apply (cases_analysis_cl q)
        · intro h_q
          _apply_r h_pq, h_q, h_p
          elim_f_neg h_np
        · intro h_nq
          by_contra h_nr
          elim_neg h_np
          apply_r h_pqr
          intro_iff
          · intro h_q
            elim_f_neg h_nq
          · intro h_r
            elim_f_neg h_nr
    intro h_r
    intro_iff
    · intro h_p
      _apply_l h_pqr, h_p, h_qr
      apply_r_ h_qr
    · intro h_q
      apply_r h_pqr
      intro_iff
      · intro h_q₂
        assumption
      · intro h_r₂
        assumption
  · intro h_pqr
    intro_iff
    · intro h_p
      intro_iff
      · intro h_q
        apply_l h_pqr
        intro_iff
        · intro h_p₂
          assumption
        · intro h_q₂
          assumption
      · intro h_r
        _apply_r h_pqr, h_r, h_pq
        apply_l_ h_pq
    · intro h_qr










--Xor definition and notation
def xor_pr (p q : Prop) : Prop := (p ∧ ¬q) ∨ (¬p ∧ q)
macro l:term:10 " ⊕ " r:term:11 : term => `(xor_pr $l $r)

--Xor properties
theorem xor_equiv_def (p q : Prop) : (p ⊕ q) ↔ ((p ∨ q) ∧ (¬ (p ∧ q))) := by
admit


theorem xor_not_iff (p q : Prop) : (p ⊕ q) ↔ (¬ (p ↔ q)) := by
admit


theorem iff_not_xor (p q : Prop) : (p ↔ q) ↔ (¬ (p ⊕ q)) := by
admit


theorem xor_equal (p : Prop) : ¬ (p ⊕ p) := by
admit


theorem xor_neg (p : Prop) : (p ⊕ ¬ p) := by
admit


theorem xor_commut (p q : Prop) : (p ⊕ q) ↔ (q ⊕ p) := by
admit


theorem xor_assoc (p q r : Prop) : ((p ⊕ q) ⊕ r) ↔ (p ⊕ (q ⊕ r)) := by
admit


theorem xor_introl (p q : Prop) : (p ∧ ¬q) → (p ⊕ q) := by
admit


theorem xor_intror (p q : Prop) : (q ∧ ¬p) → (p ⊕ q) := by
admit


theorem xor_intro (p q : Prop) : (p ∨ q) → (¬ (p ∧ q)) → (p ⊕ q) := by
admit


theorem xor_left (p q : Prop) : (p ⊕ q) → (p ∨ q) := by
admit


theorem xor_right (p q : Prop) : (p ⊕ q) → (¬ (p ∧ q)) := by
admit


theorem xor_elim (p q r : Prop) : (p ⊕ q) → ((p ∧ ¬q) → r) → ((q ∧ ¬p) → r) → r := by
admit
