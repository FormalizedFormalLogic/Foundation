import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Completeness

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

lemma validate_Dummett_of_connected (hCon : Connected F) : F ⊧ (Axioms.Dummett (.atom 0) (.atom 1)) := by
  apply ValidOnFrame.dum hCon;

lemma connected_of_validate_Dummett : F ⊧ (Axioms.Dummett (.atom 0) (.atom 1)) → Connected F := by
  rintro h x y z ⟨Rxy, Ryz⟩;
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

abbrev ConnectedFrameClass : FrameClass := { F | Connected F }

instance ConnectedFrameClass.DefinedByAxiomDummett : ConnectedFrameClass.DefinedBy {Axioms.Dummett (.atom 0) (.atom 1)} := ⟨by
  intro F;
  constructor;
  . simpa using validate_Dummett_of_connected;
  . simpa using connected_of_validate_Dummett;
⟩

instance : ConnectedFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Connected];
⟩

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open SaturatedConsistentTableau
open Classical

namespace Canonical

lemma connected [Entailment.HasAxiomDummett 𝓢] : Connected (canonicalFrame 𝓢).Rel := by
  rintro x y z ⟨Rxy, Ryz⟩;
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

end Canonical

end canonicality

end Kripke

end LO.Propositional
