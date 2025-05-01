import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Entailment.Cl

section

variable {α : Sort*} (R : α → α → Prop)

def KrieselPutnamCondition :=
  ∀ x y z,
  (R x y ∧ R x z ∧ ¬R y z ∧ ¬R z y) →
  (∃ u, R x u ∧ R u y ∧ R u z ∧ (∀ v, R u v → ∃ w, R v w ∧ (R y w ∨ R z w)))

end


namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

open Formula (atom)

lemma validate_KrieselPutnam_of_KrieselPutnamCondition : KrieselPutnamCondition F → F ⊧ (Axioms.KrieselPutnam (.atom 0) (.atom 1) (.atom 2)) := by
  intro hKP V x y Rxy h₁;
  by_contra hC;
  replace hC := Satisfies.or_def.not.mp hC;
  push_neg at hC;
  obtain ⟨h₂, h₃⟩ := hC;

  replace h₂ := Satisfies.imp_def.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z₁, Ryz₁, ⟨hz₁₁, hz₁₂⟩⟩ := h₂;

  replace h₃ := Satisfies.imp_def.not.mp h₃;
  push_neg at h₃;
  obtain ⟨z₂, Ryz₂, ⟨hz₂₁, hz₂₂⟩⟩ := h₃;

  obtain ⟨u, Ryu, ⟨Ruz₁, Ruz₂, h⟩⟩ := hKP y z₁ z₂ ⟨
    Ryz₁, Ryz₂,
    by
      rcases Satisfies.or_def.mp $ h₁ Ryz₁ hz₁₁ with (h | h);
      . exfalso; exact hz₁₂ h;
      . by_contra hC; exact hz₂₂ $ Satisfies.formula_hereditary hC h;
    ,
    by
      rcases Satisfies.or_def.mp $ h₁ Ryz₂ hz₂₁ with (h | h);
      . by_contra hC; exact hz₁₂ $ Satisfies.formula_hereditary hC h;
      . exfalso; exact hz₂₂ h;
  ⟩;

  have : ¬Satisfies ⟨F, V⟩ u (∼(.atom 0)) := by
    by_contra hC;
    rcases Satisfies.or_def.mp $ h₁ Ryu hC with (h | h);
    . apply hz₁₂; exact Satisfies.formula_hereditary Ruz₁ h;
    . apply hz₂₂; exact Satisfies.formula_hereditary Ruz₂ h;
  replace this := Satisfies.neg_def.not.mp this;
  push_neg at this;
  obtain ⟨v, Ruv, hv⟩ := this;

  obtain ⟨w, Rvw, (Rz₁w | Rz₂w)⟩ := h v Ruv;
  . exact Satisfies.not_of_neg (Satisfies.formula_hereditary (φ := (∼(.atom 0))) Rz₁w hz₁₁) $ Satisfies.formula_hereditary Rvw hv;
  . exact Satisfies.not_of_neg (Satisfies.formula_hereditary (φ := (∼(.atom 0))) Rz₂w hz₂₁) $ Satisfies.formula_hereditary Rvw hv;

end definability

end Kripke

end LO.Propositional
