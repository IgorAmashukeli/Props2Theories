Require Import Top.TacticNames.
Require Import Setoid.
Require Import Unicode.Utf8.

(*Reflexivity, symmetry, commutativity and transitivity of equality*)
Theorem equal_refl (T : Type) : (∀ x : T, x = x) .
Proof.
    intro x.
    reflexivity.
Qed.
Theorem equal_symm (T : Type) : (∀ (x y : T), x = y → y = x) .
Proof.
    intros x y xy.
    rewrite <- xy.
    reflexivity.
Qed.
Theorem equal_commut (T : Type) : (∀ x : T, ∀ y : T, x = y ↔ y = x) .
Proof.
    intros x y.
    intro_iff; apply (equal_symm).
Qed.
Theorem equal_trans (T : Type) : (∀ (x y z : T), x = y → y = z → x = z) .
Proof.
    intros x y z xy yz.
    rewrite xy.
    assumption.
Qed.

(*Congruence of equality*)
Theorem eq_subst (T : Type) (P : T → Prop) : (∀ (a b : T), a = b → P a → P b).
Proof.
    intros a b heq pa.
    rewrite <- heq.
    assumption.
Qed.
Theorem eq_substr (T : Type) (P : T → Prop) : (∀ (a b : T), a = b → P b → P a).
Proof.
    intros a b heq pb.
    rewrite heq.
    assumption.
Qed.
Theorem eq_congr_func_arg (T : Type) (S : Type) (f : T → S) : (∀ (x y : T), x = y → f x = f y).
Proof.
    intros x y heq.
    rewrite <- heq.
    reflexivity.
Qed.
Theorem eq_congr_pred_arg (T : Type) (P : T → Prop) : (∀ (x y : T), x = y → (P x ↔ P y)).
Proof.
    intros x y heq.
    intro_iff.
    -   exact (eq_subst T P x y heq).
    -   pose (heqs := equal_symm T x y heq). 
        exact (eq_subst T P y x heqs).
Qed.
Theorem iff_congr_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x ↔ P y)).
Proof.
    intros x y hxy.
Qed.
Theorem iff_subst_pred_arg (P : Prop → Prop) : (∀ (x y : Prop), (x ↔ y) → (P x → P y)).
Proof.
Qed.
Theorem eq_congr_func_symb (T : Type) (S : Type) (f g : T → S) (h : f = g) : (∀ x : T, f x = g x).
Proof.
Qed.
Theorem eq_congr_pred_symb (T : Type) (P Q : T → Prop) (h : P = Q) : (∀ x : T, P x ↔ Q x).
Proof.
Qed.
Theorem eq_congr_func_arg_symb (T : Type) (S : Type) (f₁ f₂ : T → S) : ∀ (a₁ a₂ : T), (f₁ = f₂) → (a₁ = a₂) → (f₁ a₁ = f₂ a₂).
Proof.
Qed.
Theorem eq_congr_pred_arg_symb (T : Type) (P₁ P₂ : T → Prop) : ∀ (a₁ a₂ : T), (P₁ = P₂) → (a₁ = a₂) → (P₁ a₁ ↔ P₂ a₂).
Proof.
Qed.



