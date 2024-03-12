import Logic.Propositional.Intuitionistic.Kripke.Semantics
import Logic.Propositional.Intuitionistic.Deduction

namespace LO.Propositional.Intuitionistic

open Formula Kripke

variable {α : Type (u + 1)}

lemma Kripke.soundsAux (Γ : Theory α) (p : Formula α) (h : Γ ⊢ᴵ! p) : (Γ ⊨ᴵ p) := by
  induction h.some <;> simp [KripkeConsequence, KripkeValid, KripkeModels, Theory.KripkeSatisfies];
  case axm => aesop;
  case modus_ponens Γ₁ Γ₂ p q hpq hp ihpq ihp =>
    intro M w a;
    exact ihpq ⟨hpq⟩ M w (by intro q hq; exact a q (by left; simpa))
      |>.modus_ponens $ ihp ⟨hp⟩ M w (by intro q hq; exact a q (by right; simpa));
  case imply₁ =>
    intro _ _ _ _ _ hp _ hw _;
    exact herditary_formula hw hp;
  case imply₂ =>
    intro M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
    exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃ w₄ (M.frame_refl) (h₂ w₄ hw₃w₄ h₃);
  case conj₁ => intros; simpa;
  case conj₃ =>
    intro _ _ _ _ _ hp _ _ _;
    exact ⟨(herditary_formula (by simpa) hp), (by simpa)⟩;
  case disj₁ => intros; left; simpa;
  case disj₂ => intros; right; simpa;
  case disj₃ =>
    intro M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
    cases h₃ with
    | inl h₃ => exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃;
    | inr h₃ => exact h₂ w₄ hw₃w₄ h₃;

theorem Kripke.sounds {Γ : Theory α} {p} : (Γ ⊢ᴵ! p) → (Γ ⊨ᴵ p) := Kripke.soundsAux Γ p

theorem Provable.consistent : ⊬ᴵ! (⊥ : Formula α) := by
  by_contra hC; simp at hC;
  have h := Kripke.soundsAux ∅ (⊥ : Formula α) hC default;
  simp [Formula.KripkeConsequence, Theory.KripkeSatisfies] at h;

end LO.Propositional.Intuitionistic
