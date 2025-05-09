import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental
import Foundation.Modal.Kripke.AxiomGeach

namespace LO.Modal

namespace Kripke

open Formula.Kripke

instance : IsWeakConfluent _ whitepoint.Rel := ⟨by tauto⟩

section definability

variable {F : Kripke.Frame}

lemma validate_WeakPoint2_of_weakConfluent [IsWeakConfluent _ F] : F ⊧ (Axioms.WeakPoint2 (.atom 0) (.atom 1)) := by
  rintro V x;
  apply Satisfies.imp_def.mpr;
  suffices
    ∀ y, x ≺ y → (∀ u, y ≺ u → V u 0) → V y 1 →
    ∀ z, x ≺ z → (∀ u, z ≺ u → ¬V u 0) → V z 1
    by simpa [Semantics.Realize, Satisfies];
  intro y Rxy h₁ hy₁ z Rxz h₂;
  by_contra hC;
  have nyz : y ≠ z := by
    by_contra hC;
    subst hC;
    contradiction;
  obtain ⟨u, Ryu, Rzu⟩ := IsWeakConfluent.weak_confluent ⟨Rxy, Rxz, nyz⟩;
  have : V u 0 := h₁ _ Ryu;
  have : ¬V u 0 := h₂ _ Rzu;
  contradiction;

lemma weakConfluent_of_validate_WeakPoint2 : F ⊧ (Axioms.WeakPoint2 (.atom 0) (.atom 1)) → WeakConfluent F := by
  contrapose;
  intro hCon;
  obtain ⟨x, y, Rxy, z, Rxz, nyz, hu⟩ := by simpa [WeakConfluent] using hCon;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ w a => match a with | 0 => y ≺ w | 1 => w = y | _ => False), x;
  suffices x ≺ y ∧ ∃ z, x ≺ z ∧ (∀ u, z ≺ u → ¬y ≺ u) ∧ ¬z = y by
    simpa [Satisfies, Semantics.Realize];
  refine ⟨Rxy, z, Rxz, ?_, by tauto⟩;
  . intro u;
    contrapose;
    push_neg;
    intro Ryu;
    exact hu u Ryu;

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Modal.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

namespace Canonical

instance [Entailment.HasAxiomWeakPoint2 𝓢] : IsWeakConfluent _ (canonicalFrame 𝓢).Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz, eyz⟩;
  have ⟨u, hu⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨y.1.1.prebox, z.1.2.predia⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra hC;
    have hγ : □(Γ.conj) ∈ y.1.1 := y.mdp_mem₁_provable collect_box_fconj! $ iff_mem₁_fconj.mpr (by simpa using hΓ);
    have hδ : ◇(Δ.disj) ∈ z.1.2 := mdp_mem₂_provable distribute_dia_fdisj! $ iff_mem₂_fdisj.mpr (by simpa using hΔ);
    generalize Γ.conj = γ₁ at hγ hC;
    generalize Δ.disj = δ₁ at hδ hC;
    obtain ⟨δ₂, hδ₂₁, hδ₂₂⟩ := exists₁₂_of_ne eyz;

    have : 𝓢 ⊢! □γ₁ ➝ □δ₁ := imply_box_distribute'! hC;
    have : 𝓢 ⊢! □γ₁ ⋏ δ₂ ➝ □δ₁ ⋏ δ₂ := CKK!_of_C! this;
    have : □δ₁ ⋏ δ₂ ∈ y.1.1 := mdp_mem₁_provable this $ by
      apply iff_mem₁_and.mpr; constructor <;> assumption;
    have : ◇(□δ₁ ⋏ δ₂) ∈ x.1.1 := def_rel_dia_mem₁.mp Rxy this;
    have : □(◇δ₁ ⋎ δ₂) ∈ x.1.1 := mdp_mem₁_provable axiomWeakPoint2! this;
    have : ◇δ₁ ⋎ δ₂ ∈ z.1.1 := def_rel_box_mem₁.mp Rxz this;
    rcases iff_mem₁_or.mp this with (hδ₁ | hδ₂);
    . have : ◇δ₁ ∉ z.1.2 := iff_not_mem₂_mem₁.mpr hδ₁;
      contradiction;
    . have : δ₂ ∉ z.1.2 := iff_not_mem₂_mem₁.mpr hδ₂;
      contradiction;
  use u;
  constructor;
  . apply def_rel_box_mem₁.mpr;
    intro φ hφ;
    apply hu.1 hφ;
  . apply def_rel_dia_mem₂.mpr;
    intro φ hφ;
    apply hu.2 hφ;
⟩

end Canonical

end canonicality


end Kripke

end LO.Modal
