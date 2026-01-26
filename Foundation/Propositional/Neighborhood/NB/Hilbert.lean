module

public import Foundation.Propositional.Hilbert.WF.Basic
public import Foundation.Propositional.Neighborhood.NB.Basic

@[expose] public section

namespace LO.Propositional

open NBNeighborhood
open Formula
open Formula.NBNeighborhood

namespace Hilbert.WF.NBNeighborhood

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section FrameClass

variable {C C₁ C₂ : NBNeighborhood.FrameClass}

lemma soundness_frameclass (hV : C ⊧* Ax) : (Hilbert.WF Ax) ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind;

instance instFrameClassSound (hV : C ⊧* Ax) : Sound (Hilbert.WF Ax) C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass (C : NBNeighborhood.FrameClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.WF Ax) C] : Entailment.Consistent (Hilbert.WF Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

lemma weakerThan_of_subset_frameClass (C₁ C₂ : NBNeighborhood.FrameClass) (hC : C₂ ⊆ C₁) [Sound (Hilbert.WF Ax₁) C₁] [Complete (Hilbert.WF Ax₂) C₂] : (Hilbert.WF Ax₁) ⪯ (Hilbert.WF Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := (Hilbert.WF Ax₁)) (𝓜 := C₁) hφ;
  apply hC hF;

end FrameClass


section ModelClass

variable {C C₁ C₂ : NBNeighborhood.ModelClass}

lemma soundness_modelclass (hV : C ⊧* Ax) : (Hilbert.WF Ax) ⊢ φ → C ⊧ φ := by
  intro hφ M hM;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind

instance instModelClassSound (hV : C ⊧* Ax) : Sound (Hilbert.WF Ax) C := ⟨fun {_} => soundness_modelclass hV⟩

lemma consistent_of_sound_modelclass (C : NBNeighborhood.ModelClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.WF Ax) C] : Entailment.Consistent (Hilbert.WF Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨M, hM⟩ := hC;
  use M;
  grind;

end ModelClass


end Hilbert.WF.NBNeighborhood


end LO.Propositional
end
