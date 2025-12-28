import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Rel.Convergent


namespace LO.Modal

namespace Kripke


variable {F : Kripke.Frame}

namespace Frame

abbrev IsPiecewiseConvergent (F : Frame) := _root_.IsPiecewiseConvergent F.Rel

lemma p_convergent [F.IsPiecewiseConvergent] {x y z : F.World} : x ≺ y → x ≺ z → y ≠ z → ∃ u, y ≺ u ∧ z ≺ u := by
  apply IsPiecewiseConvergent.p_convergent

end Frame


instance : whitepoint.IsPiecewiseConvergent where
  p_convergent := by tauto


section definability

open Formula (atom)
open Formula.Kripke

lemma validate_WeakPoint2_of_weakConfluent [F.IsPiecewiseConvergent] : F ⊧ (Axioms.WeakPoint2 (.atom 0) (.atom 1)) := by
  rintro V x;
  apply Satisfies.imp_def.mpr;
  suffices
    ∀ y, x ≺ y → (∀ u, y ≺ u → V u 0) → V y 1 →
    ∀ z, x ≺ z → (∀ u, z ≺ u → ¬V u 0) → V z 1
    by simpa [Semantics.Models, Satisfies];
  intro y Rxy h₁ hy₁ z Rxz h₂;
  by_contra hC;
  have nyz : y ≠ z := by
    by_contra hC;
    subst hC;
    contradiction;
  obtain ⟨u, Ryu, Rzu⟩ := IsPiecewiseConvergent.p_convergent Rxy Rxz nyz;
  have : V u 0 := h₁ _ Ryu;
  have : ¬V u 0 := h₂ _ Rzu;
  contradiction;

lemma isPiecewiseConvergent_of_validate_axiomWeakPoint2 (h : F ⊧ (Axioms.WeakPoint2 (.atom 0) (.atom 1))) : F.IsPiecewiseConvergent where
  p_convergent := by
    dsimp [PiecewiseConvergent];
    revert h;
    contrapose!;
    rintro ⟨x, y, z, Rxy, Rxz, nyz, hu⟩;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ w a => match a with | 0 => y ≺ w | 1 => w = y | _ => False), x;
    suffices x ≺ y ∧ ∃ z, x ≺ z ∧ (∀ u, z ≺ u → ¬y ≺ u) ∧ ¬z = y by
      simpa [Satisfies, Semantics.Models];
    refine ⟨Rxy, z, Rxz, ?_, by tauto⟩;
    . intro u;
      contrapose;
      push_neg;
      intro Ryu;
      exact hu u Ryu;

end definability


section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open LO.Entailment LO.Modal.Entailment
open Formula.Kripke
open MaximalConsistentTableau
open canonicalModel

instance [Entailment.HasAxiomWeakPoint2 𝓢] : (canonicalFrame 𝓢).IsPiecewiseConvergent where
  p_convergent := by
    rintro x y z Rxy Rxz eyz;
    have ⟨u, hu⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨y.1.1.prebox, z.1.2.predia⟩) $ by
      rintro Γ Δ hΓ hΔ;
      by_contra hC;
      have hγ : □(Γ.conj) ∈ y.1.1 := y.mdp_mem₁_provable collect_box_fconj! $ iff_mem₁_fconj.mpr (by simpa using hΓ);
      have hδ : ◇(Δ.disj) ∈ z.1.2 := mdp_mem₂_provable distribute_dia_fdisj! $ iff_mem₂_fdisj.mpr (by simpa using hΔ);
      generalize Γ.conj = γ₁ at hγ hC;
      generalize Δ.disj = δ₁ at hδ hC;
      obtain ⟨δ₂, hδ₂₁, hδ₂₂⟩ := exists₁₂_of_ne eyz;

      have : 𝓢 ⊢ □γ₁ ➝ □δ₁ := imply_box_distribute'! hC;
      have : 𝓢 ⊢ □γ₁ ⋏ δ₂ ➝ □δ₁ ⋏ δ₂ := CKK!_of_C! this;
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

end canonicality

end Kripke

end LO.Modal
