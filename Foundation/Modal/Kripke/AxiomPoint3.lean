import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

namespace Kripke


section definability

open Formula.Kripke

variable {F : Kripke.Frame}

lemma validate_Point3_of_connected (hCon : Connected F) : F ⊧ (Axioms.Point3 (.atom 0) (.atom 1)) := by
  rintro V x;
  apply Satisfies.or_def.mpr;
  suffices
    (∀ y, x ≺ y → (∀ z, y ≺ z → V z 0) → V y 1) ∨
    (∀ y, x ≺ y → (∀ z, y ≺ z → V z 1) → V y 0)
    by simpa [Semantics.Realize, Satisfies];
  by_contra hC;
  push_neg at hC;
  obtain ⟨⟨y, Rxy, hp, hnq⟩, ⟨z, Rxz, hq, hnp⟩⟩ := hC;
  cases hCon ⟨Rxy, Rxz⟩ with
  | inl Ryz => have := hp z Ryz; contradiction;
  | inr Rzy => have := hq y Rzy; contradiction;

lemma connected_of_validate_Point3 : F ⊧ (Axioms.Point3 (.atom 0) (.atom 1)) → Connected F := by
  contrapose;
  intro hCon;
  obtain ⟨x, y, Rxy, z, Ryz, nRyz, nRzy⟩ := by simpa [Connected] using hCon;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ w a => match a with | 0 => y ≺ w | 1 => z ≺ w | _ => False), x;
  suffices ∃ y', x ≺ y' ∧ (∀ z', y' ≺ z' → y ≺ z') ∧ ¬z ≺ y' ∧ (∃ z', x ≺ z' ∧ (∀ y, z' ≺ y → z ≺ y) ∧ ¬y ≺ z') by
    simpa [Semantics.Realize, Satisfies];
  refine ⟨y, Rxy, by tauto, nRzy, z, Ryz, by tauto, nRyz⟩;

abbrev FrameClass.connected : FrameClass := { F | Connected F }

namespace FrameClass.connected

@[simp]
lemma FrameClass.connected.nonempty : FrameClass.connected.Nonempty := by
  use whitepoint.toFrame;
  simp [Connected];

instance FrameClass.connected.definability : FrameClass.connected.DefinedBy {Axioms.Point3 (.atom 0) (.atom 1)} := ⟨by
  intro F;
  constructor;
  . simpa using validate_Point3_of_connected;
  . simpa using connected_of_validate_Point3;
⟩

end FrameClass.connected

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

namespace Canonical

protected lemma connected [Entailment.HasAxiomPoint3 𝓢] : Connected (canonicalFrame 𝓢).Rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  by_contra hC;
  push_neg at hC;
  rcases hC with ⟨nRyz, nRzy⟩;
  obtain ⟨φ, hφy, hφz⟩ := Set.not_subset.mp nRyz;
  obtain ⟨ψ, hψz, hψy⟩ := Set.not_subset.mp nRzy;
  apply x.neither (φ := □(□φ ➝ ψ) ⋎ □(□ψ ➝ φ));
  constructor;
  . exact iff_provable_mem₁.mp axiomPoint3! x;
  . apply iff_mem₂_or.mpr;
    constructor;
    . apply iff_mem₂_box.mpr;
      use y;
      constructor;
      . exact Rxy;
      . apply iff_mem₂_imp.mpr;
        constructor;
        . simpa using hφy;
        . exact iff_not_mem₁_mem₂.mp hψy;
    . apply iff_mem₂_box.mpr;
      use z;
      constructor;
      . exact Rxz;
      . apply iff_mem₂_imp.mpr;
        constructor;
        . simpa using hψz;
        . exact iff_not_mem₁_mem₂.mp hφz;

end Canonical

end canonicality


end Kripke

end LO.Modal
