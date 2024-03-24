import Logic.Propositional.Intuitionistic.Kripke.Semantics
import Logic.Propositional.Intuitionistic.Deduction

namespace LO.Propositional.Intuitionistic

open Formula Kripke KripkeSatisfies

variable {α : Type u} [Inhabited α]

lemma Kripke.soundsAux (Γ : Theory α) (p : Formula α) (h : Γ ⊢ⁱ! p) : Γ ⊨ⁱ p := by
  induction h.some with
  | axm => simp_all only [KripkeConsequence, Theory.KripkeSatisfies, implies_true, forall_const];
  | @modusPonens p q hpq hp ihpq ihp =>
    simp [KripkeConsequence];
    intro _ M w a;
    exact ihpq ⟨hpq⟩ M w (by intro q hq; exact a q (by simpa))
      |>.modus_ponens $ ihp ⟨hp⟩ M w (by intro q hq; exact a q (by simpa));
  | eaxm ih =>
    obtain ⟨q, hq⟩ := by simpa [AxiomEFQ.set, AxiomEFQ] using ih;
    subst hq;
    simp [KripkeConsequence];
  | imply₁ =>
    simp [KripkeConsequence];
    intro _ _ _ _ _ _ hp _ hw _;
    exact herditary_formula hw hp;
  | imply₂ =>
    simp [KripkeConsequence];
    intro _ M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
    exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃ w₄ (M.frame_refl) (h₂ w₄ hw₃w₄ h₃);
  | conj₁ => simp only [KripkeConsequence, imp_def', and_def, and_imp]; intros; assumption;
  | conj₃ =>
    simp [KripkeConsequence];
    intro _ _ _ _ _ _ hp _ _ _;
    exact ⟨(herditary_formula (by simpa) hp), (by simpa)⟩;
  | disj₁ => simp only [KripkeConsequence, imp_def', or_def]; intros; left; assumption;
  | disj₂ => simp only [KripkeConsequence, imp_def', or_def]; intros; right; assumption;
  | disj₃ =>
    simp [KripkeConsequence];
    intro _ M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
    cases h₃ with
    | inl h₃ => exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃;
    | inr h₃ => exact h₂ w₄ hw₃w₄ h₃;
  | _ => simp_all [KripkeConsequence];

theorem Kripke.sounds {Γ : Theory α} {p : Formula α} : (Γ ⊢ⁱ! p) → (Γ ⊨ⁱ p) := Kripke.soundsAux Γ p

variable {β} [Inhabited β]

/-
theorem Deduction.consistent : ∅ ⊬ⁱ! (⊥ : Formula α) := by
  by_contra hC;
  have : ∅ ⊨ⁱ (⊥ : Formula α) := Kripke.sounds (by simpa [System.unprovable_iff_not_provable] using hC);
  have : ∅ ⊭ⁱ (⊥ : Formula α) := by
    simp [KripkeInconsequence, KripkeConsequence, Theory.KripkeSatisfies];
    existsi β;
    existsi default;
    trivial;
  contradiction
-/

end LO.Propositional.Intuitionistic
