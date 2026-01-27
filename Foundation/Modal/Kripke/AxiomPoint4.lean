module

public import Foundation.Modal.Kripke.AxiomGeach
public import Foundation.Modal.Kripke.AxiomPoint3

@[expose] public section

namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

namespace Frame

class SatisfiesSobocinskiCondition (F : Kripke.Frame) where
  sobocinski : ∀ ⦃x y z : F⦄, x ≠ y → x ≺ y → x ≺ z → z ≺ y

instance [F.SatisfiesSobocinskiCondition] : F.IsPiecewiseStronglyConnected where
  ps_connected := by
    intro x y z Rxy Rxz;
    by_cases exy : x = y;
    . subst exy;
      tauto;
    . right;
      exact SatisfiesSobocinskiCondition.sobocinski (by simpa) Rxy Rxz;

instance [F.IsEuclidean] : F.SatisfiesSobocinskiCondition where
  sobocinski := by
    intro x y z _ Rxy Rxz;
    exact IsRightEuclidean.reucl Rxz Rxy;

end Frame


instance : whitepoint.SatisfiesSobocinskiCondition := ⟨by tauto⟩


section definability

open Formula (atom)
open Formula.Kripke

variable {F : Kripke.Frame}

private lemma validate_axiomPoint4_of_sobocinskiCondition : (∀ ⦃x y z : F⦄, x ≠ y → x ≺ y → x ≺ z → z ≺ y) → F ⊧ (Axioms.Point4 (.atom 0)) := by
  contrapose!;
  intro h;
  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;

  replace h := Satisfies.not_imp_def.mp h;
  have ⟨h₁, h₂⟩ := h;
  replace h₂ := Satisfies.not_imp_def.mp h₂;
  replace ⟨h₂, h₃⟩ := h₂;

  replace h₁ := Satisfies.dia_def.mp h₁;
  obtain ⟨z, Rxz, hz⟩ := h₁;

  replace h₃ := Satisfies.not_box_def.mp h₃;
  obtain ⟨y, Rxy, hy⟩ := h₃;

  use x, y, z;
  refine ⟨?_, Rxy, Rxz, ?_⟩;
  . by_contra hC; subst hC; contradiction;
  . by_contra hC; apply hy; apply hz; assumption;

lemma validate_axiomPoint4_of_satisfiesSobocinskiCondition [F.SatisfiesSobocinskiCondition] : F ⊧ (Axioms.Point4 (.atom 0)) :=
  validate_axiomPoint4_of_sobocinskiCondition Frame.SatisfiesSobocinskiCondition.sobocinski

lemma sobocinskiCondition_of_validate_axiomPoint4 (h : F ⊧ (Axioms.Point4 (.atom 0))) : F.SatisfiesSobocinskiCondition where
  sobocinski := by
    revert h;
    contrapose!;
    rintro ⟨x, y, z, nexy, Rxy, Rxz, Rzy⟩;
    apply ValidOnFrame.not_of_exists_valuation_world;
    suffices ∃ V : Valuation F, ∃ x z, x ≺ z ∧ (∀ w, z ≺ w → V w 0) ∧ V x 0 ∧ ∃ y, x ≺ y ∧ ¬V y 0 by
      simpa [Axioms.Point4, Satisfies];
    use (λ w _ => w = x ∨ z ≺ w), x, z;
    refine ⟨?_, ?_, ?_, ?_⟩;
    . assumption;
    . tauto;
    . tauto;
    . use y;
      tauto;

end definability


section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢]

open Formula.Kripke
open LO.Entailment
     LO.Entailment.FiniteContext
     Modal.Entailment
open canonicalModel
open MaximalConsistentTableau

instance [Entailment.K 𝓢] [Entailment.HasAxiomPoint4 𝓢] : (canonicalFrame 𝓢).SatisfiesSobocinskiCondition := ⟨by
  intro x y z nexy Rxy Rxz;
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists₁₂_of_ne nexy;
  apply def_rel_box_mem₁.mpr;
  intro ψ hψ;
  have : (φ ⋎ ψ) ➝ □(φ ⋎ ψ) ∈ x.1.1 := mdp_mem₁_provable axiomPoint4! $ def_rel_dia_mem₁.mp Rxz $ mdp_mem₁_provable (by
    apply imply_box_distribute'!;
    simp;
  ) hψ;
  have : □(φ ⋎ ψ) ∈ x.1.1 := iff_mem₁_imp'.mp this $ by
    apply iff_mem₁_or.mpr;
    left;
    tauto;
  rcases iff_mem₁_or.mp $ (iff_mem₁_box.mp this) Rxy with (_ | _);
  . exfalso;
    apply y.neither (φ := φ);
    constructor <;> assumption;
  . assumption;
⟩

end canonicality

end Kripke

end LO.Modal
end
