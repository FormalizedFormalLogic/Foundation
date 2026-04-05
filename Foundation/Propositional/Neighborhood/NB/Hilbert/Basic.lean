module

public import Foundation.Propositional.Hilbert.WF.Basic
public import Foundation.Propositional.Neighborhood.NB.Basic

@[expose] public section

namespace LO.Propositional

open NBNeighborhood
open Formula
open Formula.NBNeighborhood

namespace HilbertWF.NBNeighborhood

variable {H H₁ H₂ : HilbertWF ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section FrameClass

variable {C C₁ C₂ : NBNeighborhood.FrameClass}

lemma soundness_frameclass (hV : C ⊧* H) : H ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind;

instance instFrameClassSound (hV : C ⊧* H) : Sound H C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass (C : NBNeighborhood.FrameClass) (hC : Set.Nonempty C) [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push Not;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

lemma weakerThan_of_subset_frameClass (C₁ C₂ : NBNeighborhood.FrameClass) (hC : C₂ ⊆ C₁) [Sound H₁ C₁] [Complete H₂ C₂] : H₁ ⪯ H₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := H₁) (𝓜 := C₁) hφ;
  apply hC hF;

end FrameClass


section ModelClass

variable {C C₁ C₂ : NBNeighborhood.ModelClass}

lemma soundness_modelclass (hV : C ⊧* H) : H ⊢ φ → C ⊧ φ := by
  intro hφ M hM;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind

instance instModelClassSound (hV : C ⊧* H) : Sound H C := ⟨fun {_} => soundness_modelclass hV⟩

lemma consistent_of_sound_modelclass (C : NBNeighborhood.ModelClass) (hC : Set.Nonempty C) [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push Not;
  obtain ⟨M, hM⟩ := hC;
  use M;
  grind;

end ModelClass


end HilbertWF.NBNeighborhood


end LO.Propositional
end
