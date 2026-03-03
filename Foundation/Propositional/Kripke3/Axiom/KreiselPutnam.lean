module

public import Foundation.Propositional.Kripke3.Basic
public import Foundation.Vorspiel.Rel.Euclidean
public import Foundation.Propositional.Entailment.KreiselPutnam

@[expose] public section

class SatisfiesKreiselPutnamCondition (R : Rel α α) where
  kreisel_putnam :
    ∀ x y z : α,
    (R x y ∧ R x z ∧ ¬R y z ∧ ¬R z y) →
    (∃ u, R x u ∧ R u y ∧ R u z ∧ (∀ v, R u v → ∃ w, R v w ∧ (R y w ∨ R z w)))

namespace LO.Propositional

variable {κ α : Type*} [Nonempty κ]

namespace KripkeModel

variable {M : KripkeModel κ α} [M.Intuitionistic] {φ ψ χ : Formula α}

lemma validates_axiomKreiselPutnam_of_satisfiesKreiselPutnamCondition
  [SatisfiesKreiselPutnamCondition M.rel] : M ⊧ (Axioms.KreiselPutnam φ ψ χ) := by
  intro x y Rxy h₁;
  apply forces_or.mpr;
  by_contra! hC;
  obtain ⟨h₂, h₃⟩ := hC;

  replace h₂ := forces_imp.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z₁, Ryz₁, ⟨hz₁φ, hz₁ψ⟩⟩ := h₂;

  replace h₃ := forces_imp.not.mp h₃;
  push_neg at h₃;
  obtain ⟨z₂, Ryz₂, ⟨hz₂φ, hz₂ψ⟩⟩ := h₃;

  obtain ⟨u, Ryu, ⟨Ruz₁, Ruz₂, h⟩⟩ := SatisfiesKreiselPutnamCondition.kreisel_putnam y z₁ z₂ ⟨
    Ryz₁, Ryz₂,
    by
      rcases forces_or.mp $ h₁ _ Ryz₁ hz₁φ with (h | h);
      . exfalso; exact hz₁ψ h;
      . by_contra hC; exact hz₂ψ $ M.formula_persistency h hC;
    ,
    by
      rcases forces_or.mp $ h₁ _ Ryz₂ hz₂φ with (h | h);
      . by_contra hC; exact hz₁ψ $ M.formula_persistency h hC;
      . exfalso; exact hz₂ψ h;
  ⟩;
  have : ¬u ⊩ (∼φ) := by
    by_contra hC;
    rcases forces_or.mp $ h₁ _ Ryu hC with (h | h);
    . apply hz₁ψ $ M.formula_persistency h Ruz₁;
    . apply hz₂ψ $ M.formula_persistency h Ruz₂;
  replace this := forces_neg.not.mp this;
  push_neg at this;
  obtain ⟨v, Ruv, hv⟩ := this;

  rcases h v Ruv with ⟨w, Rvw, (Rz₁w | Rz₂w)⟩
  . apply (forces_neg.mp $ M.formula_persistency hz₁φ Rz₁w) w $ Std.Refl.refl w;
    exact M.formula_persistency hv Rvw;
  . apply (forces_neg.mp $ M.formula_persistency hz₂φ Rz₂w) w $ Std.Refl.refl w;
    exact M.formula_persistency hv Rvw;

end KripkeModel

end LO.Propositional
end
