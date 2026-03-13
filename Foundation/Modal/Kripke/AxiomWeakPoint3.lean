module

public import Foundation.Modal.Kripke.Completeness

@[expose] public section

namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

namespace Frame

variable {F : Frame}

abbrev IsPiecewiseConnected (F : Frame) := _root_.IsPiecewiseConnected F.Rel

lemma IsPiecewiseConnected.mk' (p_connected' : ∀ {x y z : F.World}, x ≺ y → x ≺ z → y ≠ z → y ≺ z ∨ z ≺ y) : F.IsPiecewiseConnected where
  p_connected := by
    intro x y z Rxy Rxz;
    suffices y ≠ z → y ≺ z ∨ z ≺ y by tauto;
    apply p_connected' <;> tauto;

lemma p_connected [F.IsPiecewiseConnected] {x y z : F.World} : x ≺ y → x ≺ z → y ≺ z ∨ y = z ∨ z ≺ y := by apply IsPiecewiseConnected.p_connected
lemma p_connected' [F.IsPiecewiseConnected] {x y z : F.World} : x ≺ y → x ≺ z → y ≠ z → y ≺ z ∨ z ≺ y := IsPiecewiseConnected.p_connected'

end Frame

instance : whitepoint.IsPiecewiseConnected where
  p_connected := by tauto

section definability

open Formula (atom)
open Formula.Kripke

lemma validate_WeakPoint3_of_weakConnected [F.IsPiecewiseConnected] : F ⊧ (Axioms.WeakPoint3 (.atom 0) (.atom 1)) := by
  rintro V x;
  apply Satisfies.or_def.mpr;
  suffices
    (∀ (y : F.World), x ≺ y → V 0 y → (∀ (x : F.World), y ≺ x → V 0 x) → V 1 y) ∨
    (∀ (y : F.World), x ≺ y → V 1 y → (∀ (x : F.World), y ≺ x → V 1 x) → V 0 y)
    by simpa [Semantics.Models, Satisfies];
  by_contra hC;
  push_neg at hC;
  obtain ⟨⟨y, Rxy, hy0, hz, nhy1⟩, ⟨z, Rxz, hz1, hy, nhz0⟩⟩ := hC;
  have nyz : y ≠ z := by
    by_contra hC;
    subst hC;
    contradiction;
  rcases IsPiecewiseConnected.p_connected' Rxy Rxz nyz with (Ryz | Rzy);
  . apply nhz0; exact hz _ Ryz;
  . apply nhy1; exact hy _ Rzy;

lemma isPiecewiseConnected_of_validate_axiomWeakPoint3 (h : F ⊧ (Axioms.WeakPoint3 (.atom 0) (.atom 1))) : F.IsPiecewiseConnected where
  p_connected := by
    dsimp [PiecewiseConnected];
    revert h;
    contrapose!;
    rintro ⟨x, y, z, Rxy, Rxz, nRyz, nyz, nRzy⟩;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ a w => match a with | 0 => w = y ∨ y ≺ w | 1 => w = z ∨ z ≺ w | _ => True), x;
    suffices
      ∃ w, x ≺ w ∧ (w = y ∨ y ≺ w) ∧ (∀ (v : F.World), w ≺ v → ¬v = y → y ≺ v) ∧ ¬w = z ∧ ¬z ≺ w ∧
      ∃ w, x ≺ w ∧ (w = z ∨ z ≺ w) ∧ (∀ (v : F.World), w ≺ v → ¬v = z → z ≺ v) ∧ ¬w = y ∧ ¬y ≺ w by
      simpa [Semantics.Models, Satisfies];
    refine ⟨y, Rxy, ?_, ?_, ?_, ?_, z, Rxz, ?_, ?_, ?_, ?_⟩;
    all_goals tauto;

end definability

section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance [Entailment.HasAxiomWeakPoint3 𝓢] : (canonicalFrame 𝓢).IsPiecewiseConnected where
  p_connected := by
    rintro x y z Rxy Rxz;
    by_contra! hC;
    rcases hC with ⟨nRyz, neyz, nRzy⟩;

    obtain ⟨φ₁, hφ₁y, hφ₁z⟩ := Set.not_subset.mp nRyz;
    replace hφ₁y : □φ₁ ∈ y.1.1 := by simpa using hφ₁y;
    replace hφ₁z : φ₁ ∈ z.1.2 := iff_not_mem₁_mem₂.mp hφ₁z;
    obtain ⟨φ₂, hφ₂y, hφ₂z⟩ := exists₁₂_of_ne neyz;
    let φ := φ₁ ⋎ φ₂;

    obtain ⟨ψ₁, hψz, hψy⟩ := Set.not_subset.mp nRzy;
    replace hψ₁z : □ψ₁ ∈ z.1.1 := by simpa using hψz;
    replace hψ₁y : ψ₁ ∈ y.1.2 := iff_not_mem₁_mem₂.mp hψy;
    obtain ⟨ψ₂, hψ₂z, hψ₂y⟩ := exists₂₁_of_ne neyz;
    let ψ := ψ₁ ⋎ ψ₂;

    apply x.neither (φ := □(⊡φ 🡒 ψ) ⋎ □(⊡ψ 🡒 φ));
    constructor;
    . exact iff_provable_mem₁.mp axiomWeakPoint3! x;
    . apply iff_mem₂_or.mpr;
      constructor;
      . apply iff_mem₂_box.mpr;
        use y;
        constructor;
        . assumption;
        . apply iff_mem₂_imp.mpr;
          constructor;
          . apply iff_mem₁_and.mpr;
            constructor;
            . apply iff_mem₁_or.mpr; tauto;
            . apply iff_mem₁_box.mpr
              intro u Ryu;
              apply iff_mem₁_or.mpr;
              left;
              exact Ryu hφ₁y;
          . apply iff_mem₂_or.mpr;
            constructor;
            . assumption;
            . assumption;
      . apply iff_mem₂_box.mpr;
        use z;
        constructor;
        . assumption;
        . apply iff_mem₂_imp.mpr;
          constructor;
          . apply iff_mem₁_and.mpr;
            constructor;
            . apply iff_mem₁_or.mpr; tauto;
            . apply iff_mem₁_box.mpr
              intro u Rzu;
              apply iff_mem₁_or.mpr;
              left;
              exact Rzu hψ₁z;
          . apply iff_mem₂_or.mpr;
            constructor;
            . assumption;
            . assumption;

end canonicality

end Kripke

end LO.Modal
end
