module

public import Foundation.Modal.Kripke.Completeness

@[expose] public section

namespace LO.Modal

open Formula.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.SatisfiesMakinsonCondition (F : Frame) where
  makinson : ∀ x : F, ∃ y, x ≺ y ∧ y ≺ x ∧ (∀ z, y ≺^[2] z → x ≺ z)

lemma Frame.makinson [F.SatisfiesMakinsonCondition] : ∀ x : F, ∃ y, x ≺ y ∧ y ≺ x ∧ (∀ z, y ≺^[2] z → x ≺ z) := SatisfiesMakinsonCondition.makinson

instance : whitepoint.SatisfiesMakinsonCondition := ⟨by
  intro x;
  use x;
  tauto;
⟩

section definability

lemma validate_axiomMk_of_satisfiesMakinsonCondition [F.SatisfiesMakinsonCondition] : F ⊧ (Axioms.Mk (.atom 0) (.atom 1)) := by
  intro V x hx;
  replace ⟨hx₁, hx₂⟩ := Satisfies.and_def.mp hx;
  obtain ⟨y, Rxy, Ryx, hz⟩ := Frame.makinson x;
  apply Satisfies.dia_def.mpr;
  use y;
  constructor;
  . assumption;
  . apply Satisfies.and_def.mpr;
    constructor;
    . suffices Satisfies ⟨F, V⟩ y (□^[2](.atom 0)) by simpa using this;
      apply Satisfies.boxItr_def.mpr
      intro z Ryz;
      apply hx₁;
      apply hz;
      exact Ryz;
    . apply Satisfies.dia_def.mpr;
      use x;

end definability

section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open LO.Entailment Entailment.FiniteContext LO.Modal.Entailment
open canonicalModel
open MaximalConsistentTableau

namespace Canonical

open Classical in
instance [Entailment.HasAxiomT 𝓢] [Entailment.HasAxiomMk 𝓢] : (canonicalFrame 𝓢).SatisfiesMakinsonCondition := ⟨by
  sorry;
  /-
  rintro x;
  obtain ⟨y, hy⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□⁻¹'x.1.1, x.1.2.box ∪ x.1.2.dia⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra! hC;
    let Δ₁ := { φ ∈ Δ | φ ∈ x.1.2.box };
    let Δ₂ := { φ ∈ Δ | φ ∈ x.1.2.dia };
    have eΔ : Δ = Δ₁ ∪ Δ₂ := by
      ext φ;
      simp only [Set.mem_image, Function.iterate_one, Finset.mem_union, Finset.mem_filter, Δ₁, Δ₂];
      constructor;
      . rintro h;
        rcases hΔ h with h₁ | h₂ <;> tauto;
      . tauto;
    rw [eΔ] at hC;
    have : 𝓢 ⊢ Γ.conj 🡒 Δ₁.disj ⋎ Δ₂.disj := C!_trans hC CFdisjUnionAFdisj;
    have : 𝓢 ⊢ □Γ.prebox.conj 🡒 Δ₁.disj ⋎ Δ₂.disj := C!_trans (by
      apply right_Fconj!_intro;
      intro φ hφ;
      have := hΓ hφ;
      simp at this;
      sorry
    ) this;
    sorry;
  use y;
  refine ⟨?_, ?_, ?_⟩;
  . exact hy.1;
  . apply def_rel_box_mem₂.mpr;
    intro φ hφ;
    exact @hy.2 (□φ) (by left; simpa);
  . rintro z Ryz;
    apply def_rel_dia_mem₂.mpr;
    intro φ hφ;
    apply def_multirel_diaItr_mem₂.mp Ryz;
    exact @hy.2 (◇◇φ) (by simpa);
  -/
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
end
