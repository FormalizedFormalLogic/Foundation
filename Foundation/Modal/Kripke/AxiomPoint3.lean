import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.HRel.Connected

namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

namespace Frame

abbrev IsPiecewiseStronglyConnected (F : Frame) := _root_.IsPiecewiseStronglyConnected F.Rel

lemma ps_connected [F.IsPiecewiseStronglyConnected] : ∀ {x y z : F.World}, x ≺ y → x ≺ z →  y ≺ z ∨ z ≺ y := by
  apply IsPiecewiseStronglyConnected.ps_connected

end Frame


instance : whitepoint.IsPiecewiseStronglyConnected where
  ps_connected := by tauto;


section definability

open Formula (atom)
open Formula.Kripke

lemma validate_axiomPoint3_of_isPiecewiseStronglyConnected [F.IsPiecewiseStronglyConnected] : F ⊧ (Axioms.Point3 (.atom 0) (.atom 1)) := by
  rintro V x;
  apply Satisfies.or_def.mpr;
  suffices
    (∀ y, x ≺ y → (∀ z, y ≺ z → V z 0) → V y 1) ∨
    (∀ y, x ≺ y → (∀ z, y ≺ z → V z 1) → V y 0)
    by simpa [Semantics.Realize, Satisfies];
  by_contra hC;
  push_neg at hC;
  obtain ⟨⟨y, Rxy, hp, hnq⟩, ⟨z, Rxz, hq, hnp⟩⟩ := hC;
  rcases IsPiecewiseStronglyConnected.ps_connected Rxy Rxz with (Ryz | Rzy);
  . have := hp z Ryz; contradiction;
  . have := hq y Rzy; contradiction;

lemma isPiecewiseStronglyConnected_of_validate_axiomPoint3 (h : F ⊧ (Axioms.Point3 (.atom 0) (.atom 1))) : F.IsPiecewiseStronglyConnected where
  ps_connected := by
    dsimp [PiecewiseStronglyConnected];
    revert h;
    contrapose!;
    rintro ⟨x, y, z, Rxy, Rxz, nRyz, nRzy⟩;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ w a => match a with | 0 => y ≺ w | 1 => z ≺ w | _ => False), x;
    suffices ∃ y', x ≺ y' ∧ (∀ z', y' ≺ z' → y ≺ z') ∧ ¬z ≺ y' ∧ (∃ z', x ≺ z' ∧ (∀ y, z' ≺ y → z ≺ y) ∧ ¬y ≺ z') by
      simpa [Semantics.Realize, Satisfies];
    refine ⟨y, Rxy, by tauto, nRzy, z, Rxz, by tauto, nRyz⟩;

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance [Entailment.HasAxiomPoint3 𝓢] : (canonicalFrame 𝓢).IsPiecewiseStronglyConnected where
  ps_connected := by
    rintro x y z Rxy Rxz;
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

end canonicality

open Formula.Kripke

end Kripke

end LO.Modal
