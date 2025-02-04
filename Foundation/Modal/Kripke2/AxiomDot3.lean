import Foundation.Modal.Kripke2.Basic

namespace LO.Modal

open Formula.Kripke

namespace Kripke

variable {F : Kripke.Frame}

lemma connected_of_validate_dot3 (hCon : Connected F) : F ⊧ (Axioms.Dot3 (.atom 0) (.atom 1)) := by
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

lemma validate_dot3_of_connected : F ⊧ (Axioms.Dot3 (.atom 0) (.atom 1)) → Connected F := by
  contrapose;
  intro hCon;
  obtain ⟨x, y, Rxy, z, Ryz, nRyz, nRzy⟩ := by simpa [Connected] using hCon;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ w a => match a with | 0 => y ≺ w | 1 => z ≺ w | _ => False), x;
  suffices ∃ y', x ≺ y' ∧ (∀ z', y' ≺ z' → y ≺ z') ∧ ¬z ≺ y' ∧ (∃ z', x ≺ z' ∧ (∀ y, z' ≺ y → z ≺ y) ∧ ¬y ≺ z') by
    simpa [Semantics.Realize, Satisfies];
  refine ⟨y, Rxy, by tauto, nRzy, z, Ryz, by tauto, nRyz⟩;

abbrev ConnectedFrameClass : FrameClass := { F | Connected F }

instance ConnectedFrameClass.DefinedByDot3 : ConnectedFrameClass.DefinedBy {Axioms.Dot3 (.atom 0) (.atom 1)} := ⟨by
  intro F;
  constructor;
  . simpa using connected_of_validate_dot3;
  . simpa using validate_dot3_of_connected;
⟩

end Kripke

end LO.Modal
