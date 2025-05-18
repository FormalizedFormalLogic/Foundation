import Foundation.Modal.LogicSymbol
import Foundation.Logic.Disjunctive
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Propositional.Entailment.Cl
import Foundation.Modal.Axioms
import Foundation.Modal.Entailment.Basic
import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Entailment.K4
import Foundation.Modal.Kripke.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.K4
import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Iterate

namespace LO.Axioms.Modal

variable {F : Type*} [BasicModalLogicalConnective F]
variable (φ ψ χ : F)

protected abbrev Mk := □(□□φ ➝ □ψ) ➝ (□φ ➝ ψ)

end LO.Axioms.Modal


namespace LO.Entailment.Modal

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ : F}

protected class HasAxiomMk [LogicalConnective F] [Box F](𝓢 : S) where
  Mk (φ ψ : F) : 𝓢 ⊢ Axioms.Modal.Mk φ ψ

section

variable [Modal.HasAxiomMk 𝓢]

def axiomMk : 𝓢 ⊢ □(□□φ ➝ □ψ) ➝ (□φ ➝ ψ) := Modal.HasAxiomMk.Mk _ _
@[simp] lemma axiomMk! : 𝓢 ⊢! □(□□φ ➝ □ψ) ➝ (□φ ➝ ψ) := ⟨axiomMk⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : Modal.HasAxiomMk Γ := ⟨fun _ _ ↦ FiniteContext.of axiomMk⟩
instance (Γ : Context F 𝓢) : Modal.HasAxiomMk Γ := ⟨fun _ _ ↦ Context.of axiomMk⟩

end

end LO.Entailment.Modal


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
  intro V x h₁ h₂;
  obtain ⟨y, Rxy, Ryx, hz⟩ := @h x;
  apply @h₁ y ?_ ?_;
  . assumption;
  . assumption;
  . intro z Rxz u Rzu;
    apply h₂;
    apply hz u;
    use z;
    tauto;

lemma validate_axiomM_of_satisfiesMakinsonCondition [SatisfiesMakinsonCondition _ F.Rel] : F ⊧ (Axioms.Modal.Mk (.atom 0) (.atom 1)) :=
  validate_axiomMk_of_makinsonCondition SatisfiesMakinsonCondition.mkCondition

/-
lemma validate_M_of_mckinseyan_trans (hTrans : Transitive F) : F ⊧ (Axioms.M (.atom 0)) → McKinseyCondition F := by
  contrapose;
  intro hMc;
  unfold McKinseyCondition at hMc;
  push_neg at hMc;
  obtain ⟨x, h⟩ := hMc;
  by_cases hDead : ∀ y, ¬x ≺ y;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ _ _ => True), x;
    suffices (∀ y, x ≺ y → ∃ x, y ≺ x) ∧ ∀ y, ¬x ≺ y by
      simpa [Satisfies];
    constructor;
    . intro y Rxy;
      have := hDead y Rxy;
      contradiction;
    . assumption;
  . push_neg at hDead;
    obtain ⟨y, Rxy⟩ := hDead;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ z _ =>
      x ≺ z ∧ ∀ u, x ≺ u → ∃ v, (v ≠ z ∧ u ≺ z ∧ u ≺ v)
    ), x;
    apply Satisfies.imp_def₂.not.mpr;
    push_neg;

    constructor;
    . apply Satisfies.box_def.mpr;
      intro w Rxw;
      apply Satisfies.dia_def.mpr;
      obtain ⟨z, Rwz, hwz⟩ := h w Rxw;
      use z;
      constructor;
      . assumption;
      . simp [Semantics.Realize, Satisfies];
        constructor;
        . exact hTrans Rxw Rwz;
        . intro u Rxu;
          use w;
          refine ⟨?_, ?_, ?_⟩;
          . tauto;
          . sorry
          . sorry;
    . apply Satisfies.dia_def.not.mpr
      push_neg;
      intro z Rxz;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      obtain ⟨w, Rzw, hzw⟩ := h z Rxz;
      use w;
      constructor;
      . assumption;
      . simp [Semantics.Realize, Satisfies];
        intro Rxw;
        use z;
        constructor;
        . assumption;
        . intro v hvw _;
          sorry;

-/

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

  /-
  by_contra! hC;

  obtain ⟨z, ⟨u, Rxu, Ruz⟩, nRxz⟩ := hC x (_root_.refl x) (_root_.refl x);
  replace Ruz : u ≺ z := by simpa using Ruz;

  obtain ⟨φ, hφx, hφz⟩ := Set.not_subset.mp nRxz;
  replace hφx : □φ ∈ x.1.1 := by simpa using hφx;

  have : z ≠ u := by by_contra hC; subst hC; contradiction;
  obtain ⟨ψ, hψz, hψu⟩ := exists₁₂_of_ne this;

  apply x.neither (φ := Axioms.Modal.Mk φ (□ψ));
  constructor;
  . exact iff_provable_mem₁.mp axiomMk! x;
  . apply iff_mem₂_imp.mpr;
    constructor;
    . apply iff_mem₁_box.mpr;
      intro y hy;
      sorry;
    . apply iff_mem₂_imp.mpr;
      constructor;
      . assumption;
      . apply iff_mem₂_box.mpr;
        use u;
  -/

  /-
  have ⟨y, hy⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨x.1.1.prebox, x.1.2.predia⟩) $ by sorry;
  use y;
  refine ⟨?_, ?_, ?_⟩;
  . exact hy.1;
  . sorry;
  . rintro z Ryz;
    replace Ryz : ∀ {φ}, □^[2]φ ∈ y.1.1 → φ ∈ z.1.1 := def_multirel_multibox_mem₁ (n := 2) |>.mp Ryz;
    intro ψ hψ;
    have := hy.1 hψ;
    sorry;
  -/
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
