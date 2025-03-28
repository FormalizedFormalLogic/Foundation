import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental

namespace LO.Modal

namespace Kripke

open Formula.Kripke

instance : IsWeakConnected _ whitepoint.Rel := ⟨by tauto⟩


section definability

variable {F : Kripke.Frame}

lemma validate_WeakPoint3_of_weakConnected [IsWeakConnected _ F] : F ⊧ (Axioms.WeakPoint3 (.atom 0) (.atom 1)) := by
  rintro V x;
  apply Satisfies.or_def.mpr;
  suffices
    (∀ (y : F.World), x ≺ y → V y 0 → (∀ (x : F.World), y ≺ x → V x 0) → V y 1) ∨
    (∀ (y : F.World), x ≺ y → V y 1 → (∀ (x : F.World), y ≺ x → V x 1) → V y 0)
    by simpa [Semantics.Realize, Satisfies];
  by_contra hC;
  push_neg at hC;
  obtain ⟨⟨y, Rxy, hy0, hz, nhy1⟩, ⟨z, Rxz, hz1, hy, nhz0⟩⟩ := hC;
  have nyz : y ≠ z := by
    by_contra hC;
    subst hC;
    contradiction;
  rcases IsWeakConnected.weak_connected ⟨Rxy, Rxz, nyz⟩ with (Ryz | Rzy);
  . have := hz _ Ryz; contradiction;
  . have := hy _ Rzy; contradiction;

lemma weakConnected_of_validate_WeakPoint3 : F ⊧ (Axioms.WeakPoint3 (.atom 0) (.atom 1)) → WeakConnected F := by
  contrapose;
  intro hCon;
  obtain ⟨x, y, Rxy, z, Rxz, nyz, nRyz, nRzy⟩ := by simpa [WeakConnected] using hCon;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ w a => match a with | 0 => w = y ∨ y ≺ w | 1 => w = z ∨ z ≺ w | _ => True), x;
  suffices
    ∃ w, x ≺ w ∧ (w = y ∨ y ≺ w) ∧ (∀ (v : F.World), w ≺ v → ¬v = y → y ≺ v) ∧ ¬w = z ∧ ¬z ≺ w ∧
    ∃ w, x ≺ w ∧ (w = z ∨ z ≺ w) ∧ (∀ (v : F.World), w ≺ v → ¬v = z → z ≺ v) ∧ ¬w = y ∧ ¬y ≺ w by
    simpa [Semantics.Realize, Satisfies];
  refine ⟨
    _,
    Rxy,
    by tauto,
    by tauto,
    by tauto,
    nRzy,
    _,
    Rxz,
    by tauto,
    by tauto,
    by tauto,
    nRyz
  ⟩;

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Modal.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

namespace Canonical

instance [Entailment.HasAxiomWeakPoint3 𝓢] : IsWeakConnected _ (canonicalFrame 𝓢).Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz, eyz⟩;
  by_contra hC;
  push_neg at hC;
  rcases hC with ⟨nRyz, nRzy⟩;

  obtain ⟨φ₁, hφ₁y, hφ₁z⟩ := Set.not_subset.mp nRyz;
  replace hφ₁y : □φ₁ ∈ y.1.1 := by simpa using hφ₁y;
  replace hφ₁z : φ₁ ∈ z.1.2 := iff_not_mem₁_mem₂.mp hφ₁z;
  obtain ⟨φ₂, hφ₂y, hφ₂z⟩ := exists₁₂_of_ne eyz;
  let φ := φ₁ ⋎ φ₂;

  obtain ⟨ψ₁, hψz, hψy⟩ := Set.not_subset.mp nRzy;
  replace hψ₁z : □ψ₁ ∈ z.1.1 := by simpa using hψz;
  replace hψ₁y : ψ₁ ∈ y.1.2 := iff_not_mem₁_mem₂.mp hψy;
  obtain ⟨ψ₂, hψ₂z, hψ₂y⟩ := exists₂₁_of_ne eyz;
  let ψ := ψ₁ ⋎ ψ₂;

  apply x.neither (φ := □(⊡φ ➝ ψ) ⋎ □(⊡ψ ➝ φ));
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
⟩

end Canonical

end canonicality


end Kripke

end LO.Modal
