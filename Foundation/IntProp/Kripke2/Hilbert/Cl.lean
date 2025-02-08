import Foundation.IntProp.Hilbert2.WellKnown
import Foundation.IntProp.Kripke2.Hilbert.Soundness

namespace LO.IntProp

open Kripke
open Formula.Kripke


abbrev Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }

instance : Kripke.EuclideanFrameClass.DefinedByFormula (Axioms.LEM (.atom 0)) := ⟨by
  rintro F;
  constructor;
  . rintro hEucl _ ⟨_, rfl⟩;
    apply ValidOnFrame.lem;
    apply symm_of_refl_eucl;
    . exact F.rel_refl;
    . assumption;
  . rintro h x y z Rxy Rxz;
    let V : Kripke.Valuation F := ⟨λ {v a} => z ≺ v, by
      intro w v Rwv a Rzw;
      exact F.rel_trans' Rzw Rwv;
    ⟩;
    suffices Satisfies ⟨F, V⟩ y (.atom 0) by simpa [Satisfies] using this;
    apply V.hereditary Rxy;
    simp at h;
    have := @h V x;
    simp [Semantics.Realize, Satisfies, V, or_iff_not_imp_right] at this;
    apply this z;
    . exact Rxz;
    . apply F.rel_refl;
⟩

instance : Kripke.EuclideanFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Euclidean];
⟩


open Kripke

namespace Hilbert.Cl.Kripke

instance : EuclideanFrameClass.DefinedBy (Hilbert.Cl.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.Cl EuclideanFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.Cl := Kripke.Hilbert.consistent_of_FrameClass EuclideanFrameClass

end Hilbert.Cl.Kripke




namespace Kripke

abbrev ClassicalValuation := ℕ → Prop

end Kripke


namespace Formula.Kripke

open IntProp.Kripke

abbrev ClassicalSatisfies (V : ClassicalValuation) (φ : Formula ℕ) : Prop := Satisfies (⟨pointFrame, ⟨λ _ => V, by tauto⟩⟩) () φ

namespace ClassicalSatisfies

instance : Semantics (Formula ℕ) (ClassicalValuation) := ⟨ClassicalSatisfies⟩

variable {V : ClassicalValuation} {a : ℕ}

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp only [Semantics.Realize, Satisfies]

instance : Semantics.Tarski (ClassicalValuation) where
  realize_top := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_bot := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_or  := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_and := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_imp := by simp [Semantics.Realize, Satisfies]; tauto;
  realize_not := by simp [Semantics.Realize, Satisfies]; tauto;

end ClassicalSatisfies

end Formula.Kripke


namespace Hilbert.Cl

lemma classical_sound : (Hilbert.Cl) ⊢! φ → (∀ V : ClassicalValuation, V ⊧ φ) := by
  intro h V;
  apply Hilbert.Cl.Kripke.sound.sound h Kripke.pointFrame;
  simp [Euclidean];

lemma unprovable_of_exists_classicalValuation : (∃ V : ClassicalValuation, ¬(V ⊧ φ)) → (Hilbert.Cl) ⊬ φ := by
  contrapose;
  simp;
  apply classical_sound;

end Hilbert.Cl


end LO.IntProp
