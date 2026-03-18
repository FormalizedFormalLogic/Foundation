module

public import Foundation.Propositional.Hilbert.F.Basic
public import Foundation.Propositional.Kripke2.Basic

@[expose] public section

namespace LO.Propositional

open Kripke2
open Formula
open Formula.Kripke2

namespace HilbertF.Kripke2

variable {H H₁ H₂ : HilbertF ℕ} {φ : Formula ℕ}


section FrameClass

variable {C C₁ C₂ : Kripke2.FrameClass}

lemma soundness_frameclass (hV : C ⊧* H) : H ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind;

instance instFrameClassSound (hV : C ⊧* H) : Sound H C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass (sound : Sound H C) (hC : Set.Nonempty C) : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

lemma weakerThan_of_subset_frameClass (sound : Sound H₁ C₁) (complete : Complete H₂ C₂) (hC : C₂ ⊆ C₁) : H₁ ⪯ H₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply complete.complete;
  intro F hF;
  apply sound.sound hφ;
  apply hC hF;

end FrameClass


section ModelClass

variable {C C₁ C₂ : Kripke2.ModelClass}

lemma soundness_modelclass (hV : C ⊧* H) : H ⊢ φ → C ⊧ φ := by
  intro hφ M hM;
  induction hφ with
  | axm hi => apply hV.models <;> assumption;
  | _ => grind

instance instModelClassSound (hV : C ⊧* H) : Sound H C := ⟨fun {_} => soundness_modelclass hV⟩

lemma consistent_of_sound_modelclass (sound : Sound H C) (hC : Set.Nonempty C) : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨M, hM⟩ := hC;
  use M;
  grind;

end ModelClass


end HilbertF.Kripke2


end LO.Propositional
end
