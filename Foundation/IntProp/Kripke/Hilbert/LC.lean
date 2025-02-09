import Foundation.IntProp.Hilbert.WellKnown
import Foundation.IntProp.Kripke.Hilbert.Soundness
import Foundation.IntProp.Kripke.Completeness

namespace LO.IntProp

open Kripke
open Formula.Kripke

abbrev Kripke.ConnectedFrameClass : FrameClass := { F | Connected F }

instance : Kripke.ConnectedFrameClass.DefinedByFormula (Axioms.Dummett (.atom 0) (.atom 1)) := ⟨by
  rintro F;
  constructor;
  . rintro h φ ⟨_, rfl⟩;
    apply Formula.Kripke.ValidOnFrame.dum;
    exact h;
  . rintro h x y z ⟨Rxy, Ryz⟩;
    let V : Kripke.Valuation F := ⟨λ {v a} => match a with | 0 => y ≺ v | 1 => z ≺ v | _ => True, by
      intro w v Rwv a ha;
      split at ha;
      . exact F.rel_trans ha Rwv;
      . exact F.rel_trans ha Rwv;
      . tauto;
    ⟩;
    replace h : F ⊧ (Axioms.Dummett (.atom 0) (.atom 1)) := by simpa using h;
    rcases Formula.Kripke.Satisfies.or_def.mp $ @h V x with (hi | hi);
    . right;
      simpa [Semantics.Realize, Satisfies, V] using hi Rxy;
    . left;
      simpa [Semantics.Realize, Satisfies, V] using hi Ryz;
⟩


instance : Kripke.ConnectedFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Connected];
⟩


namespace Hilbert.LC.Kripke

instance : ConnectedFrameClass.DefinedBy (Hilbert.LC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.LC ConnectedFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.LC := Kripke.Hilbert.consistent_of_FrameClass ConnectedFrameClass

open
  System
  SaturatedConsistentTableau
in
instance canonical : Canonical Hilbert.LC ConnectedFrameClass := by
  constructor;
  simp [Connected, Kripke.canonicalFrame];
  intro x y z Rxy Ryz;
  apply or_iff_not_imp_left.mpr;
  intro nRyz;
  obtain ⟨φ, hyp, nhzp⟩ := Set.not_subset.mp nRyz;
  intro ψ hqz;
  have : ψ ➝ φ ∉ x.1.1 := by
    by_contra hqpx;
    have hqpz : ψ ➝ φ ∈ z.1.1 := by aesop;
    have : φ ∈ z.1.1 := mdp₁_mem hqz hqpz;
    contradiction;
  have := iff_mem₁_or.mp $ mem₁_of_provable (t := x) (φ := (φ ➝ ψ) ⋎ (ψ ➝ φ)) dummett!;
  have hpqx : φ ➝ ψ ∈ x.1.1 := by aesop;
  have hpqy : φ ➝ ψ ∈ y.1.1 := Rxy hpqx;
  have : ψ ∈ y.1.1 := mdp₁_mem hyp hpqy;
  exact this;

instance complete : Complete Hilbert.LC ConnectedFrameClass := inferInstance

end Hilbert.LC.Kripke


end LO.IntProp
