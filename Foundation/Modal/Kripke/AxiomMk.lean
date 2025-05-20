import Foundation.Modal.Kripke.Completeness



section

variable {α : Type u} (rel : α → α → Prop)

def MakinsonCondition := ∀ x, ∃ y, rel x y ∧ rel y x ∧ (∀ z, Rel.iterate rel 2 y z → rel x z)

class SatisfiesMakinsonCondition (α) (rel : α → α → Prop) : Prop where
  mkCondition : MakinsonCondition rel

end




namespace LO.Modal

open Formula.Kripke

namespace Kripke

section definability

variable {F : Kripke.Frame}

lemma validate_axiomMk_of_makinsonCondition (h : MakinsonCondition F.Rel) : F ⊧ (Axioms.Modal.Mk (.atom 0) (.atom 1)) := by
  intro V x hx;
  replace ⟨hx₁, hx₂⟩ := Satisfies.and_def.mp hx;
  obtain ⟨y, Rxy, Ryx, hz⟩ := @h x;
  apply Satisfies.dia_def.mpr;
  use y;
  constructor;
  . assumption;
  . apply Satisfies.and_def.mpr;
    constructor;
    . suffices Satisfies ⟨F, V⟩ y (□^[2](.atom 0)) by simpa using this;
      apply Satisfies.multibox_def.mpr
      intro z Ryz;
      apply hx₁;
      apply hz;
      exact Ryz;
    . apply Satisfies.dia_def.mpr;
      use x;

lemma validate_axiomMk_of_satisfiesMakinsonCondition [SatisfiesMakinsonCondition _ F.Rel] : F ⊧ (Axioms.Modal.Mk (.atom 0) (.atom 1)) :=
  validate_axiomMk_of_makinsonCondition SatisfiesMakinsonCondition.mkCondition

instance : SatisfiesMakinsonCondition _ whitepoint := ⟨by
  intro x;
  use x;
  tauto;
⟩

end definability

section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Modal.K 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open Entailment.Modal
open canonicalModel
open MaximalConsistentTableau

namespace Canonical

open Classical in
instance [Entailment.HasAxiomT 𝓢] [Entailment.Modal.HasAxiomMk 𝓢] : SatisfiesMakinsonCondition _ (canonicalFrame 𝓢).Rel := ⟨by
  sorry;
  /-
  rintro x;
  obtain ⟨y, hy⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨x.1.1.prebox, x.1.2.box ∪ x.1.2.dia⟩) $ by
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
    have : 𝓢 ⊢! Γ.conj ➝ Δ₁.disj ⋎ Δ₂.disj := C!_trans hC CFdisjUnionAFdisj;
    have : 𝓢 ⊢! □Γ.prebox.conj ➝ Δ₁.disj ⋎ Δ₂.disj := C!_trans (by
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
    apply def_multirel_multidia_mem₂.mp Ryz;
    exact @hy.2 (◇◇φ) (by simpa);
  -/
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
