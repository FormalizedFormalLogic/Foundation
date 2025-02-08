import Foundation.IntProp.Hilbert2.WellKnown
import Foundation.IntProp.Kripke2.Hilbert.Soundness

namespace LO.IntProp

open Kripke
open Formula.Kripke

abbrev Kripke.ConfluentFrameClass : FrameClass := { F | Confluent F }

instance : Kripke.ConfluentFrameClass.DefinedByFormula (Axioms.WeakLEM (.atom 0)) := ⟨by
  rintro F;
  constructor;
  . rintro h φ ⟨_, rfl⟩;
    apply ValidOnFrame.wlem;
    exact h;
  . rintro h x y z ⟨Rxy, Ryz⟩;
    let V : Kripke.Valuation F := ⟨λ {v a} => y ≺ v, by
      intro w v Rwv a Ryw;
      exact F.rel_trans Ryw Rwv;
    ⟩;
    replace h : F ⊧ (Axioms.WeakLEM (.atom 0)) := by simpa using h;
    have : ¬Satisfies ⟨F, V⟩ x (∼(.atom 0)) := by
      simp [Satisfies];
      use y;
      constructor;
      . exact Rxy;
      . apply F.rel_refl;
    have : Satisfies ⟨F, V⟩ x (∼∼(.atom 0)) := by
      apply or_iff_not_imp_left.mp $ Satisfies.or_def.mp $ @h V x;
      assumption;
    obtain ⟨w, Rzw, hw⟩ := by simpa [Satisfies] using @this z Ryz;
    use w;
⟩

instance : Kripke.ConfluentFrameClass.IsNonempty := ⟨by
  use ⟨Unit, λ _ _ => True, by simp [Reflexive], by simp [Transitive]⟩;
  simp [Confluent];
⟩



namespace Hilbert.KC.Kripke

instance : ConfluentFrameClass.DefinedBy (Hilbert.KC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.KC ConfluentFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.KC := Kripke.Hilbert.consistent_of_FrameClass ConfluentFrameClass

end Hilbert.KC.Kripke


end LO.IntProp
