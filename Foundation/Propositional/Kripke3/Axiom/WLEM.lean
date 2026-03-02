module

public import Foundation.Propositional.Kripke3.Basic
public import Foundation.Vorspiel.Rel.Convergent

@[expose] public section

namespace LO.Propositional

variable {κ α : Type*} [Nonempty κ]

namespace KripkeModel

variable {M : KripkeModel κ α} [M.Intuitionistic] {φ ψ χ : Formula α}

lemma validates_axiomWLEM [IsPiecewiseStronglyConvergent M.rel] : M ⊧ (Axioms.WLEM φ) := by
  have : PiecewiseStronglyConvergent M.rel := IsPiecewiseStronglyConvergent.ps_convergent;
  contrapose! this;
  obtain ⟨x, h⟩ := exists_world_notForces_of_notValidates this;

  replace h := forces_or.not.mp h;
  push_neg at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₁ := forces_neg.not.mp h₁;
  push_neg at h₁;
  obtain ⟨y, Rxy, hy⟩ := h₁;

  replace h₂ := forces_neg.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z, Rxz, hz⟩ := h₂;

  dsimp [PiecewiseStronglyConvergent]
  push_neg;
  use x, y, z;
  refine ⟨Rxy, Rxz, ?_⟩;
  . intro u Ryu;
    by_contra Rzu;
    exact hz u Rzu $ M.formula_persistency hy Ryu;

lemma isPiecewiseStronglyConvergent_of_validates_axiomWLEM [Std.Refl K]
  (h : ∀ V, letI M : KripkeModel κ α := ⟨K, V⟩; M ⊧ (Axioms.WLEM #a))
  : IsPiecewiseStronglyConvergent K := by
  constructor;
  rintro x y z Rxy Rxz;
  have := (h $ (λ {p v} => K y v)) x;
  rw [forces_or] at this;
  rcases this with (hi | hi);
  . exfalso;
    simp only [forces_neg, ForcingRelation.NotForces, forces_atom] at hi;
    apply hi y Rxy $ Std.Refl.refl y;
  . simp only [forces_neg, ForcingRelation.NotForces, forces_atom] at hi;
    push_neg at hi;
    obtain ⟨w, Rzw, Ryw⟩ := hi z Rxz;
    use w;

end KripkeModel

end LO.Propositional
end
