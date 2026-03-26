Require Import Top.TacticNames.
Require Import Unicode.Utf8.

(* True and False properties *)
Theorem neg_true : ¬ True ↔ False.
Proof.
    intro_iff.
    -   intro hn. 
        _intro_true h.
        elim_neg hn.
        assumption.
    -   intro fl.
        elim_false_.
Qed.

Theorem neg_false : ¬ False ↔ True.
Proof.
    intro_iff.
    -   intro nh. 
        intro_true.
    -   intro ht. 
        intro_neg f. 
        assumption.
Qed.

Theorem conj_true (p : Prop) : p ∧ True ↔ p.
Proof.
    intro_iff.
    -   intro hpt.
        elim_and hpt hp ht.
        assumption.
    -   intro hp.
        _intro_true hI.
        intro_and_ hp hI.
Qed.

Theorem conj_false (p : Prop) : p ∧ False ↔ False.
Proof.
    intro_iff.
    -   intro hpf.
        elim_and hpf hp hf.
        assumption.
    -   intro hf.
        elim_false.
        assumption.   

Qed.
Theorem disj_true (p : Prop) : p ∨ True ↔ True.
Proof.
    intro_iff.
    -   intro hpt.
        intro_true.
    -   intro hpt.
        right.
        intro_true. 

Qed.
Theorem disj_false (p : Prop) : p ∨ False ↔ p.
Proof.
    intro_iff.
    -   intro hpf.
        elim_or hpf hp hf.
        + assumption.
        + elim_false_.
    -   intro hp.
        left_.
Qed. 

Theorem impl_true (p : Prop) : (p → True) ↔ True.
Proof.
    intro_iff.
    -   intro hpt.
        intro_true.
    -   intros tr hp.
        intro_true.      
Qed.

Theorem true_impl (p : Prop) : (True → p) ↔ p.
Proof.
    intro_iff.
    -   intro htp.
        apply htp.
        intro_true.
    -   intros hpt tr.
        assumption.
Qed.

Theorem impl_false (p : Prop) : (p → False) ↔ ¬ p.
Proof.
    intro_iff.
    -   intro hpf.
        intro_neg_.
    -   intros hnp hp.
        elim_neg_ hnp.
Qed.

Theorem false_impl (p : Prop) : (False → p) ↔ True.
Proof.
    intro_iff.
    -   intro hfp.
        intro_true.
    -   intros ht hf.
        elim_false_.   
Qed.



(*Impodent properties*)
Theorem axiomatic_rule (p : Prop) : p → p.
Proof.
    intro hp.
    assumption.
Qed.

Theorem trivial_equivalence (p : Prop) : p ↔ p.
Proof.
    pose (hp := axiomatic_rule p).
    intro_iff_ hp hp.
Qed.

Theorem conj_idemp (p : Prop) : p ↔ (p ∧ p).
Proof.
    intro_iff.
    -   intro hp.
        intro_and_ hp hp.
    -   intro hpp.
        elim_and_ hpp.
Qed.

Theorem disj_idemp (p : Prop) : p ↔ (p ∨ p).
Proof.
    intro_iff.
    -   intro hp.
        left_.
    -   intro hpl.
        pose (hp := axiomatic_rule p).
        elim_or_ hpl hp hp.
Qed.



(*Absorbtion laws*)
Theorem absorbtion_disj (p q : Prop) : p ∨ (p ∧ q) ↔ p.
Proof.
    intro_iff.
    -   intro hppp.
        pose (hp := axiomatic_rule p).
        assert (hpqp : (p ∧ q) → p) by (intro hpq; elim_and_ hpq).
        elim_or_ hppp hp hpqp.
    -   intro hp.
        left_.   
Qed.

Theorem absorbtion_conj (p q : Prop) : p ∧ (p ∨ q) ↔ p.
Proof.
    intro_iff.
    -   intro hppq.
        elim_and_ hppq.
    -   intro hp.
        assert (hpq : p ∨ q) by left_.
        intro_and_ hp hpq.
Qed.



(*Commutativity laws*)
Lemma conj_comm_if (p q : Prop) : (p ∧ q) → (q ∧ p).
Proof.
    intro hpq.
    elim_and hpq hp hq.
    intro_and_ hq hp.
Qed.
Theorem conj_comm (p q : Prop) : (p ∧ q) ↔ (q ∧ p).
Proof.
    pose (hpq := conj_comm_if p q).
    pose (hqp := conj_comm_if q p).
    intro_iff_ hpq hqp.
Qed.

Lemma disj_comm_if (p q : Prop) : (p ∨ q) → (q ∨ p).
Proof.
    intro hpq.
    assert (hppq : p → (q ∨ p)) by (intro hp; right_).
    assert (hqpq : q → (q ∨ p)) by (intro hq; left_). 
    elim_or_ hpq hppq hqpq.
Qed.
Theorem disj_comm (p q : Prop) : (p ∨ q) ↔ (q ∨ p).
Proof.
    pose (hpq := disj_comm_if p q).
    pose (hqp := disj_comm_if q p).
    intro_iff_ hpq hqp.
Qed.

Lemma iff_comm_if (p q : Prop) : (p ↔ q) → (q ↔ p).
Proof.
    intro hpq.
    _elim_iff hpq hpql hqpr.
    intro_iff_ hqpr hpql.
Qed.
Theorem iff_comm (p q : Prop) : (p ↔ q) ↔ (q ↔ p).
Proof.
    pose (hpq := iff_comm_if p q).
    pose (hqp := iff_comm_if q p).
    intro_iff_ hpq hqp.
Qed.


(*Associativity laws*)
Theorem conj_assoc (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r).
Proof.
    intro_iff.
    -   intro hpqr.
        elim_and hpqr hpq hr; elim_and hpq hp hq.
        repeat intro_and; assumption.
    -   intro hpqr.
        elim_and hpqr hp hqr; elim_and hqr hq hr.
        repeat intro_and; assumption.
Qed.

Theorem disj_assoc (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r).
Proof.
    intro_iff.
    -   intro hpqr.
        elim_or hpqr hpq hr; repeat elim_or hpq hp hq;
        [left_ | right; left_ | right; right_].
    -   intro hpqr.
        elim_or hpqr hp hqr; repeat elim_or hqr hq hr;
        [left; left_ | left; right_ | right_].
Qed.


(*Distributivity laws*)
Theorem conj_disj_distrib (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r).
Proof.
    intro_iff.
    -   intro hpqr.
        elim_and hpqr hp hqr.
        elim_or hqr hq hr.
        + left. intro_and_ hp hq.
        + right. intro_and_ hp hr.
    -   intro hpqpr.
        assert (hpqfol : (p ∧ q) → (p ∧ (q ∨ r))) by (intro hpq; intro_and; [ elim_and_ hpq | left; elim_and_ hpq]).
        assert (hprfol : (p ∧ r) → (p ∧ (q ∨ r))) by (intro hpq; intro_and; [ elim_and_ hpq | right; elim_and_ hpq]).
        elim_or_ hpqpr hpqfol hprfol.
Qed.

Theorem disj_conj_distrib (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r).
Proof.
    intro_iff.
    -   intro hpqr.
        assert (hpfol : p → (p ∨ q) ∧ (p ∨ r)) by (intro hp; intro_and; [left_ | left_]).
        assert (hqrfol : (q ∧ r) → (p ∨ q) ∧ (p ∨ r)) by (intro hqr; elim_and hqr hq hr; intro_and; [right_ | right_]).
        elim_or_ hpqr hpfol hqrfol.
    -   intro hpqpr.
        elim_and hpqpr hpq hpr.
        assert (hpfol : p → ( p ∨ (q ∧ r))) by (intro hp; left_).
        elim_or hpr hp hr.
        + apply hpfol. assumption.
        + elim_or hpq hp hq; 
        [apply hpfol; assumption | right; intro_and; assumption].
Qed.


(*Weak pierce law*)
(*Dont' use classical rules*)
Theorem weak_pierce_law (p q : Prop) : ((((p → q) → p) → p) → q) → q.
Proof.
    intro hpqppq.
    apply hpqppq.
    intro hpqp.
    apply hpqp.
    intro hp.
    apply hpqppq.
    intro hpqp₂.
    assumption.
Qed.


(*3 De Morgan Intuitionistic implications*)
(*Don't use classic rules*)
Theorem morgan_disj (p q : Prop) :  ¬(p ∨ q) ↔ ¬p ∧ ¬q.
Proof.
    intro_iff.
    -   intro hpq. intro_and;
        [intro_neg hp; elim_neg hpq; left_ | intro_neg hq; elim_neg hpq; right_].
    -   intros hnpnq. intro_neg hpq. elim_and hnpnq hnp hnq.
        elim_or hpq hp hq;
        [elim_neg_ hnp | elim_neg_ hnq].
Qed.

Theorem morgan_conj_rl (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q).
Proof.
    intro hnpnq. intro_neg hpq. elim_and hpq hp hq.
    elim_or hnpnq hnp hnq;
    [elim_neg_ hnp | elim_neg_ hnq].
Qed.

(*Implication and negative implication sufficiencies*)
Theorem neg_to_impl (p q : Prop) : ¬p → (p → q) .
Proof.
    intros hnp hp.
    elim_false.
    elim_neg_ hnp.
Qed.
Theorem impl_def_lr (p q : Prop) : (¬p ∨ q) → (p → q) .
Proof.
    intros hnpq hp.
    elim_or hnpq hnp hq;
    [apply (neg_to_impl p q); repeat assumption| assumption].

Qed.
Theorem neg_imp_def_rl (p q : Prop) : p ∧ ¬q → ¬(p → q) .
Proof.
    intro hpnq. intro_neg hpq. elim_and hpnq hp hnq.
    elim_neg hnq. exact (hpq hp).
Qed.


(* Direct contraposition*)
Theorem contraposition_lr (p q : Prop) : (p → q) → (¬q → ¬p).
Proof.
    intros hpq hnq. intro_neg hp.
    apply hpq in hp.
    elim_neg_ hnq. 
Qed.


(* Exportation (currying) law*)
Theorem exportation_law (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r).
Proof.
    intro_iff.
    -   intros hpqr hpq. elim_and hpq hp hq.
        apply hpqr; assumption.
    -   intros hpqr hp hq. apply hpqr. 
        intro_and; assumption.
Qed.


(** Disjunction in implication antecedent*)
Theorem cases_impl_left (p q r : Prop) : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r).
Proof.
    intro_iff.
    -   intro hpqr. intro_and;
        [intro hp; apply hpqr; left_ | intro hq; apply hpqr; right_].
    -   intros hprqr hpq. elim_and hprqr hpr hqr.
        elim_or_ hpq hpr hqr.
Qed.


(* Syllogism *)
Theorem syllogism (p q r : Prop) : (p → q) → (q → r) → (p → r).
Proof.
    intros hpq hqr hp.
    apply hqr. apply hpq.
    assumption.
Qed.


(*Transitivity of equivalence*)
Theorem iff_transitivity (p q r : Prop) : (p ↔ q) → (q ↔ r) → (p ↔ r).
Proof.
    intros hpq hqr. _elim_iff hpq hpql hqpr. _elim_iff hqr hqrl hrqr.
    pose (hpr := syllogism p q r hpql hqrl).
    pose (hrp := syllogism r q p hrqr hqpr).
    intro_iff_ hpr hrp. 
Qed.


(*Congruence laws*)
Theorem neg_congr (p q : Prop) : (p ↔ q) → (¬p ↔ ¬q).
Proof.
    intro hpq. _elim_iff hpq hpql hqpr.
    intro_iff.
    -   intro hnp. intro_neg hq.
        apply hqpr in hq. elim_neg_ hnp.
    -   intro hnq. intro_neg hp.
        apply hpql in hp. elim_neg_ hnq.   
Qed.
Theorem disj_congr (p q r : Prop) : (p ↔ q) → ((p ∨ r) ↔ (q ∨ r)).
Proof.
    intro hpq. _elim_iff hpq hpql hqpr.
    intro_iff.
    -   intro hpr.
        elim_or hpr hp hr;
        [left; apply hpql; assumption | right_].
    -   intro hqr.
        elim_or hqr hq hr;
        [left; apply hqpr; assumption | right_].
Qed.
Theorem conj_congr (p q r : Prop) : (p ↔ q) → ((p ∧ r) ↔ (q ∧ r)).
Proof.
    intro hpq. _elim_iff hpq hpql hqpr.
    intro_iff.
    -   intro hpr. elim_and hpr hp hr. apply hpql in hp. intro_and_ hp hr.
    -   intro hqr. elim_and hqr hq hr. apply hqpr in hq. intro_and_ hq hr.
Qed.
Theorem impl_congr_right (p q r : Prop) : (p ↔ q) → ((p → r) ↔ (q → r)).
Proof.
    intro hpq. _elim_iff hpq hpql hqpr.
    intro_iff.
    -   intros hpr hq. exact (hpr (hqpr hq)).
    -   intros hqr hp. exact (hqr (hpql hp)). 
Qed.
Theorem impl_congr_left (p q r : Prop) : (p ↔ q) → ((r → p) ↔ (r → q)).
Proof.
    intro hpq. _elim_iff hpq hpql hqpr.
    intro_iff.
    -   intros hrp hr. exact (hpql (hrp hr)).
    -   intros hrq hr. exact (hqpr (hrq hr)).   
Qed.
Theorem iff_congr_ (p q r : Prop) : (p ↔ q) → ((p ↔ r) ↔ (q ↔ r)).
Proof.
    pose (hpqr := iff_transitivity p q r).
    pose (hqrp := iff_transitivity q p r).
    pose (hpqqp := iff_comm p q). _elim_iff hpqqp hpqqp_l hpqqp_r.
    intro hpq.
    intro_iff.
    -   intro hpr. apply hqrp; repeat assumption. apply hpqqp_l. assumption.
    -   intro hqr. apply hpqr; assumption.
Qed.


(*Equivalence to both conditions*)
Theorem iff_conj_intro(p q r : Prop) : (p ↔ q) → (p ↔ r) → (p ↔ (q ∧ r)).
Proof.
    intros hpq hpr. _elim_iff hpq hpql hqpr. _elim_iff hpr hprl hrpr.
    intro_iff.
    -   intro hp. intro_and;
        [exact (hpql hp)| exact (hprl hp)].
    -   intro hqr. elim_and hqr hq hr.
        exact (hrpr hr).
Qed.

(*Noncontradiction law*)
Theorem no_contradiction (p : Prop) : ¬(p ∧ ¬ p).
Proof.
    intro_neg hpnp. 
    elim_and hpnp hp hnp.
    elim_neg_ hnp.
Qed.


(*Direct double negation*)
Theorem double_negation_lr (p : Prop) : p → ¬¬ p.
Proof.
    intro hp. intro_neg hnp.
    elim_neg_ hnp.
Qed.


(*Nonequivalence of opposites*)
(*Don't use classical rules*)
Theorem negation_not_equiv (p : Prop) : ¬(p ↔ ¬p).
Proof.
    intro_neg hpnp.
    assert (hnp : ¬p).
    -   intro_neg hp.
        _elim_iff_l hpnp hp hnp.
        elim_neg_ hnp.
    -   _elim_iff_r hpnp hnp hp.
        elim_neg_ hnp.
Qed.


(*Classical double negation*)
Theorem double_negation_cl (p : Prop) : p ↔ ¬¬p.
Proof.
    intro_iff.
    -   exact (double_negation_lr p).
    -   intro hnnp. _elim_neg hnpf hnnp. 
        classical.by_contra_.   
Qed.

(*Classical tertsium non datur (law of excluded middle)*)
Theorem tnd_cl (p : Prop) : p ∨ ¬ p.
Proof.
    pose (dneg := double_negation_cl (p ∨ ¬ p)).
    _elim_iff dneg dnl dnr. clear dnl. apply dnr. clear dnr.
    intro_neg hnpnp.
    pose (dmorg := morgan_disj p (¬ p)).
    _elim_iff dmorg dml dmr. clear dmr. apply dml in hnpnp. clear dml.
    pose (dcontr := no_contradiction (¬ p)).
    elim_neg_ dcontr.
Qed.

(*Classical cases*)
Theorem cases_analysis_cl (p q : Prop) : (p → q) → (¬p → q) → q.
Proof.
    intros hpq hnpq.
    pose (tndp := tnd_cl p).
    elim_or_ tndp hpq hnpq.
Qed.
Theorem cases_analysis_l_cl (p q r : Prop) : (p ∨ q) → (p → r) → (q → (¬p → r)) → r.
Proof.
    intros hpq hpr hqnpr.
    pose (tndp := tnd_cl p).
    elim_or tndp hp hnp.
    -   exact (hpr hp).
    -   _elim_or hpq r hpqr.
        apply hpqr;
        [assumption | intro hq; exact (hqnpr hq hnp)].   
Qed.
Theorem cases_analysis_r_cl (p q r : Prop) : (p ∨ q) → (q → r) → (p → (¬q → r)) → r.
Proof.
    intros hpq hqr hpnqr.
    pose (tndq := tnd_cl q).
    elim_or tndq hq hnq.
    -   exact (hqr hq).
    -   _elim_or hpq r hpqr.
        apply hpqr;
        [intro hp; exact (hpnqr hp hnq) | assumption].
Qed.

Theorem cases_impl_right_cl (p q r : Prop) : (p → (q ∨ r)) → ((p → q) ∨ (p → r)).
Proof.
    intro hpqr.
    pose (tndp := tnd_cl p).
    elim_or tndp hp hnp.
    -   apply hpqr in hp.
        elim_or hp hq hr;
        [left | right]; intro; assumption.
    -   left. intro hp. elim_false. elim_neg_ hnp.
Qed.

(*One of the De Morgan classical law*)
Theorem Morgan_conj_cl (p q : Prop) : ¬ (p ∧ q) ↔ ¬p ∨ ¬q.
Proof.
    intro_iff.
    -   intro hpq.
        pose (hcs := cases_analysis_cl p (¬ p ∨ ¬ q)). apply hcs.
        +   intro hp.
            pose (hcs₂ := cases_analysis_cl q (¬ p ∨ ¬ q)). apply hcs₂.
            *   intro hq.
                elim_false.
                elim_neg hpq. intro_and_ hp hq.
            *   intro hnq.
                right_.
        +   intro hnp.
            left_.
    - exact (morgan_conj_rl p q).
Qed.

(*Implication and neg implication classical equivalence*)
Theorem imp_def_cl (p q : Prop) : (p → q) ↔ (¬p ∨ q).
Proof.
    intro_iff.
    -   intro hpq.
        pose (hcs := cases_analysis_cl p (¬ p ∨ q)). apply hcs.
        +   intro hp. right. exact (hpq hp).
        +   intro hnp. left_.
    -  exact (impl_def_lr p q).
Qed.
Theorem neg_imp_def_cl (p q : Prop) :  ¬ (p → q) ↔ p ∧ ¬ q.
Proof.
    intro_iff.
    -   intro hnpq.
        pose (hcs := cases_analysis_cl p (p ∧ ¬ q)). apply hcs.
        + intro hp. intro_and;
        [| intro_neg hq; elim_neg hnpq; intro hp₂]; assumption.
        + intro hnp. elim_false. elim_neg hnpq. 
        intro hp. elim_false. elim_neg_ hnp.
    -   exact (neg_imp_def_rl p q).
Qed.

(*Classical contraposition*)
Theorem contraposition_cl (p q : Prop) : (p → q) ↔ (¬q → ¬p).
Proof.
    intro_iff.
    -   exact (contraposition_lr p q).
    -   intros hnqnp hp.
        pose (tndq := tnd_cl q). elim_or tndq hq hnq;
        [assumption | apply hnqnp in hnq; elim_false; elim_neg_ hnq].
Qed.

(*Classical Pierce law*)
Theorem pierce_cl (p q : Prop) : (((p → q) → p) → p).
Proof.
    intro hpqp.
    pose (tndp := tnd_cl p). 
    elim_or tndp hp hnp.
    -   assumption.
    -   apply hpqp. intro hp. elim_false. elim_neg_ hnp.      
Qed.

(*Associativity of Equivalence*)
Theorem impl_assoc_cl (p q r : Prop) : ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r)).
Proof.
    intro_iff.
    -   intro hpqr.
        intro_iff.
        +   intro hp.
            intro_iff.
            *   intro hq.
                assert (hpq : (p ↔ q)) 
                    by (intro_iff; [intro hp₂; assumption | intro hq₂; assumption]).
                _elim_iff_l hpqr hpq hr. assumption.
            *   intro hr.
                _elim_iff_r hpqr hr hpq. elim_iff_l hpq hp.
        +   intro hqr.
            pose (tndp := tnd_cl p). elim_or tndp hp hnp.
            *   assumption.
            *   pose (tndq := tnd_cl q). elim_or tndq hq hnq.
                --  assert (hr : r) by (elim_iff_l hqr hq).
                    assert (hpq : (p ↔ q)) by (elim_iff_r hpqr hr).
                    elim_iff_r hpq hq.
                --  assert (hpq : (p ↔ q)).
                    ++  intro_iff.
                        ** intro hp. elim_f_neg hnp.
                        ** intro hq. elim_f_neg hnq.
                    ++  assert (hr : r) by (elim_iff_l hpqr hpq).
                        assert (hq : q) by (elim_iff_r hqr hr).
                        elim_f_neg hnq.
    -   intro hpqr.
        intro_iff.
        +   intro hpq.
            pose (tndp := tnd_cl p). elim_or tndp hp hnp.
            *   assert (hq : q) by (elim_iff_l hpq hp).
                assert (hqr : (q ↔ r)) by (elim_iff_l hpqr hp).
                elim_iff_l hqr hq.
            *   pose (tndq := tnd_cl q). elim_or tndq hq hnq.
                --  assert (hp : p) by (elim_iff_r hpq hq).
                    elim_f_neg hnp.
                --  pose (tndr := tnd_cl r). elim_or tndr hr hnqr.
                    ++  assumption.
                    ++  assert (hqr : (q ↔ r)) by 
                            (intro_iff; [intro hq; elim_f_neg hnq| intro hr; elim_f_neg hnqr]).
                        assert (hp : p) by (elim_iff_r hpqr hqr).
                        elim_f_neg hnp.
        +   intro hr.
            intro_iff.
            *   intro hp.
                assert (hqr : (q ↔ r)) by (elim_iff_l hpqr hp).
                elim_iff_r hqr hr.
            *   intro hq.
                assert (hqr : (q ↔ r)) by 
                    (intro_iff; [intro hq₂ | intro hr₂]; assumption).
                elim_iff_r hpqr hqr.
Qed.

(*Xor definition and notation*)
Definition xor (p q : Prop) : Prop := (p ∧ ¬q) ∨ (q ∧ ¬p).
Notation "l ⊕ r" := (xor l r) (at level 80, right associativity).

(*Xor properties*)
Theorem xor_equiv_def (p q : Prop) : (p ⊕ q) ↔ ((p ∨ q) ∧ (¬ (p ∧ q))).
Proof.
    intro_iff.
    -   intro hpq.
        elim_or hpq hpnq hqnp.
        +   elim_and hpnq hp hnq.
            intro_and; [left_ | intro_neg hpaq; elim_and hpaq hp₂ hq; elim_f_neg hnq].
        +   elim_and hqnp hq hnp.
            intro_and; [right_ | intro_neg hpaq; elim_and hpaq hp hq₂; elim_f_neg hnp].
    -   intro hpqnpq. elim_and hpqnpq hpq hnpq.
        elim_or hpq hp hq.
        +   left.
            intro_and; [assumption | intro_neg hq; elim_neg hnpq; intro_and; assumption].
        +   right.
            intro_and; [assumption | intro_neg hp; elim_neg hnpq; intro_and; assumption].
Qed.

Theorem xor_not_iff (p q : Prop) : (p ⊕ q) ↔ (¬ (p ↔ q)).
Proof.
    intro_iff.
    -   intro hpq.
        intro_neg hpiq.
        elim_or hpq hnpq hpnq.
        +   elim_and hnpq hp hnq.
            _elim_iff hpiq hpql hqpr.
            elim_neg hnq.
            exact (hpql hp).
        +   elim_and hpnq hq hnp.
            _elim_iff hpiq hpql hpqr.
            elim_neg hnp.
            exact (hpqr hq).
    -   intro hnpq.
        pose (tndp := tnd_cl p). elim_or tndp hp hnp.
        +   left.
            intro_and.
            *   assumption.
            *   intro_neg hq.
                elim_neg hnpq.
                intro_iff; intro h; assumption.
        +   right.
            intro_and.
            *   classical.by_contra hnq.
                elim_neg hnpq.
                intro_iff.
                ++  intro h. elim_f_neg hnp.
                ++  intro h. elim_f_neg hnq.
            *   assumption.
Qed.

Theorem iff_not_xor (p q : Prop) : (p ↔ q) ↔ (¬ (p ⊕ q)).
Proof.
    intro_iff.
    -   intro hpq.
        intro_neg hpxq.
        pose (xi := xor_not_iff p q).
        _elim_iff_l xi hpxq hnpq.
        elim_neg_ hnpq.
    -   intro hnpq.
        classical.by_contra hnipq.
        pose (xi := xor_not_iff p q).
        _elim_iff_r xi hnipq hpq.
        elim_neg_ hnpq.
Qed.

Theorem xor_equal (p : Prop) : ¬ (p ⊕ p) .
Proof.
    intro_neg hpp.
    pose (hcontr := no_contradiction p).
    elim_or hpp hp hp; elim_neg_ hcontr.
Qed.

Theorem xor_neg (p : Prop) : (p ⊕ ¬ p) .
Proof.
    pose (tndp := tnd_cl p). elim_or tndp hp hp.
    - left. intro_and; [| apply (double_negation_lr p)]; assumption.
    - right. intro_and; assumption.
Qed.

Theorem xor_comm (p q : Prop) : (p ⊕ q) ↔ (q ⊕ p) .
Proof.
    exact (disj_comm (p ∧ ¬q) (q ∧ ¬ p)).
Qed.


Theorem xor_assoc (p q r : Prop) : ((p ⊕ q) ⊕ r) ↔ (p ⊕ (q ⊕ r)) .
Proof.
    intro_iff.
    -   intro hpqr.
        elim_or hpqr hpq hrnpq.
        +   elim_and hpq hpxq hnr.
            pose (tndp := tnd_cl p).
            elim_or tndp hp hnp.
            *   left. intro_and.
                ++  assumption.
                ++  intro_neg hqr.
                    elim_or hpxq hpnq hnpq.
                    **  elim_and hpnq hp₂ hnq.
                        elim_or hqr hqnr hrnq.
                        --  elim_and hqnr hq hnr₂.
                            elim_neg_ hnq.
                        -- elim_and hrnq hr hnq₂.
                            elim_neg_ hnr.
                    **  elim_and hnpq hq hnp.
                        elim_neg_ hnp.
            *   right.
                intro_and.
                ++ elim_or hpxq hpnq hqnp.
                    **  elim_and hpnq hp hnq.
                        elim_f_neg hnp. 
                    **  elim_and hqnp hq hnp₂.
                        left.
                        intro_and; assumption.
                ++ assumption.
        +   elim_and hrnpq hr hnpq.
            pose (tndp := tnd_cl p).
            elim_or tndp hp hnp.
            *   left. intro_and.
                ++  assumption.
                ++  intro_neg hqr.
                    elim_or hqr hqnr hnqr.
                    ** elim_and hqnr hq hnr.
                       elim_neg_ hnr.
                    ** elim_and hnqr hr₂ hnq.
                       elim_neg hnpq.
                       left.
                       intro_and; assumption.
            *   right. intro_and.
                ++  right.
                    intro_and.
                    **  assumption.
                    **  intro_neg hq.
                        elim_neg hnpq.
                        right. intro_and; assumption.
                ++ assumption.
    -   intro hpqr.
        elim_or hpqr hpnqr hnpqr.
        +   elim_and hpnqr hp hnqr.
            pose (tndq := tnd_cl q).
            elim_or tndq hq hnq.
            *   right.
                intro_and.
                ++ classical.by_contra hnr.
                   elim_neg hnqr.
                   left. intro_and; assumption.
                ++ intro_neg hpq.
                    elim_or hpq hpnq hqnp.
                    ** elim_and hpnq hp₂ hnq.
                       elim_neg_ hnq.
                    ** elim_and hqnp hq₂ hnp.
                       elim_neg_ hnp.
            *   left.
                intro_and.
                ++  left. intro_and; assumption.
                ++  intro_neg hr.
                    elim_neg hnqr.
                    right.
                    intro_and; assumption.
        +   elim_and hnpqr hqr hnp.
            pose (tndq := tnd_cl q).
            elim_or tndq hq hnq.
            *   left.
                intro_and.
                ++ right. intro_and; assumption.
                ++ intro_neg hr. 
                    pose (xoreq := xor_equiv_def q r).
                    _elim_iff_l xoreq hqr hqrnqr.
                    elim_and hqrnqr hqorr hnqandr.
                    elim_neg hnqandr.
                    intro_and; assumption.
            *   right.
                intro_and.
                ++ elim_or hqr hqnr hnqr.
                    ** elim_and hqnr hq hnr.
                        elim_f_neg hnq.
                    **  elim_and hnqr hr hnq₂.
                        assumption.
                ++ intro_neg hpq.
                    elim_or hpq hpnq hnpq.
                    ** elim_and hpnq hp hnq₂.
                       elim_neg_ hnp.
                    ** elim_and hnpq hq hnp₂.
                       elim_neg_ hnq.        
Qed.

Theorem xor_introl (p q : Prop) : (p ∧ ¬q) → (p ⊕ q).
Proof.
    intro hpnq.
    left_.
Qed.
Theorem xor_intror (p q : Prop) : (q ∧ ¬p) → (p ⊕ q).
Proof.
    intro hnpq.
    right_.

Qed.
Theorem xor_intro (p q : Prop) : (p ∨ q) → (¬ (p ∧ q)) → (p ⊕ q).
Proof.
    intros hpq hnpq.
    pose (xed := xor_equiv_def p q).
    elim_iff_r_ xed.
    intro_and_ hpq hnpq.
Qed.
Theorem xor_left (p q : Prop) : (p ⊕ q) → (p ∨ q).
Proof.
    intros hpq.
    pose (xed := xor_equiv_def p q).
    _elim_iff_l xed hpq hporq.
    elim_and_ hporq.
Qed.
Theorem xor_right (p q : Prop) : (p ⊕ q) → (¬ (p ∧ q)).
Proof.
    intros hpq.
    pose (xed := xor_equiv_def p q).
    _elim_iff_l xed hpq hporq.
    elim_and_ hporq.
Qed.
Theorem xor_elim (p q r : Prop) : (p ⊕ q) → ((p ∧ ¬q) → r) → ((q ∧ ¬p) → r) → r.
Proof.
    intros hpq.
    intros hpnqr.
    intros hnpqr.
    elim_or_ hpq hpnqr hnpqr.
Qed.

