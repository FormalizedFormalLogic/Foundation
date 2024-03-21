import Logic.Propositional.Intuitionistic.Kripke.Semantics
import Logic.Propositional.Intuitionistic.Deduction

namespace LO.Propositional.Intuitionistic

open Formula Kripke KripkeSatisfies

variable {α : Type u} [Inhabited α]

lemma Kripke.soundsAux (Γ : Theory α) (p : Formula α) (h : Γ ⊢! p) : Γ ⊨ᴵ p := by
  induction h.some <;> simp [KripkeConsequence];
  case axm => simp_all [Theory.KripkeSatisfies];
  case modusPonens _ p q hpq hp ihpq ihp =>
    intro _ M w a;
    exact ihpq ⟨hpq⟩ M w (by intro q hq; exact a q (by simpa))
      |>.modus_ponens $ ihp ⟨hp⟩ M w (by intro q hq; exact a q (by simpa));
  case imply₁ =>
    intro _ _ _ _ _ _ hp _ hw _;
    exact herditary_formula hw hp;
  case imply₂ =>
    intro _ M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
    exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃ w₄ (M.frame_refl) (h₂ w₄ hw₃w₄ h₃);
  case conj₁ => intros; simpa;
  case conj₃ =>
    intro _ _ _ _ _ _ hp _ _ _;
    exact ⟨(herditary_formula (by simpa) hp), (by simpa)⟩;
  case disj₁ => intros; left; simpa;
  case disj₂ => intros; right; simpa;
  case disj₃ =>
    intro _ M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
    cases h₃ with
    | inl h₃ => exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃;
    | inr h₃ => exact h₂ w₄ hw₃w₄ h₃;

theorem Kripke.sounds {Γ : Theory α} {p} : Γ ⊢! p → Γ ⊨ᴵ p := Kripke.soundsAux Γ p

variable {β} [Inhabited β]

theorem Deduction.consistent : ∅ ⊬ (⊥ : Formula α) := by
  by_contra hC;
  have : ∅ ⊨ᴵ (⊥ : Formula α) := Kripke.sounds (by simpa [System.unprovable_iff_not_provable] using hC);
  have : ∅ ⊭ᴵ (⊥ : Formula α) := by
    simp [KripkeInconsequence, KripkeConsequence, Theory.KripkeSatisfies];
    existsi β;
    existsi default;
    trivial;
  contradiction

end LO.Propositional.Intuitionistic
