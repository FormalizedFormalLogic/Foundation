module

public import Foundation.Propositional.Kripke3.Basic
public import Foundation.Vorspiel.Rel.Euclidean
public import Foundation.Propositional.Kripke3.Logic.Int.Completeness

@[expose] public section

namespace LO.Propositional

variable {κ α : Type*} [Nonempty κ]

namespace KripkeModel

variable {M : KripkeModel κ α} [M.Intuitionistic] {φ ψ χ : Formula α}

lemma validates_axiomLEM_of_isSymmetric [Std.Symm M.rel] : M ⊧ (Axioms.LEM φ) := by
  have : Symmetric M.rel := Std.Symm.symm;
  contrapose! this;
  obtain ⟨x, h⟩ := exists_world_notForces_of_notValidates this;

  replace h := forces_or.not.mp h;
  push_neg at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₂ := forces_neg.not.mp h₂;
  push_neg at h₂;
  obtain ⟨y, Rxy, hy⟩ := h₂;

  dsimp [Symmetric]
  push_neg;
  use x, y;
  constructor;
  . assumption;
  . contrapose! h₁;
    apply M.formula_persistency hy h₁;

lemma validates_axiomLEM_of_isRightEuclidean [IsRightEuclidean M.rel] : M ⊧ (Axioms.LEM φ) := validates_axiomLEM_of_isSymmetric

lemma isRightEuclidean_of_validates_axiomLEM [Std.Refl K] [IsTrans _ K]
  (h : ∀ V, letI M : KripkeModel κ α := ⟨K, V⟩; M ⊧ (Axioms.LEM #a))
  : IsRightEuclidean K := by
  constructor;
  rintro x y z Rxy Rxz;
  have := h (λ {p v} => K y v) x;
  rcases this with (hi | hi);
  . apply IsTrans.trans y x z hi Rxz;
  . exfalso;
    apply forces_neg.mp hi y Rxy;
    apply Std.Refl.refl;

end KripkeModel

section

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open Formula.Kripke
open LO.Entailment
     LO.Entailment.FiniteContext
open canonicalKripkeModel
open SaturatedConsistentTableau
open Classical

instance [Entailment.HasAxiomLEM 𝓢] : IsRightEuclidean (canonicalKripkeModel 𝓢).rel := by
  constructor;
  intro x y z Rxy;
  contrapose!;
  rintro nRyz;
  obtain ⟨φ, hφy, hφz⟩ := Set.not_subset.mp nRyz;
  apply Set.not_subset.mpr;
  use φ;
  constructor;
  . rcases (show φ ∈ x.1.1 ∨ ∼φ ∈ x.1.1 by exact iff_mem₁_or.mp $ mem₁_of_provable (by simp)) with h | h;
    . assumption;
    . have : φ ∉ y.1.1 := of_mem₁_neg' $ Rxy h;
      contradiction;
  . assumption;

end

end LO.Propositional
end
