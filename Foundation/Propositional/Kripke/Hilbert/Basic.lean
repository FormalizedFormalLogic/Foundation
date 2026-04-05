module

public import Foundation.Propositional.Hilbert.Minimal.Basic
public import Foundation.Propositional.Kripke.Basic

@[expose] public section

namespace LO.Propositional

open Kripke
open Formula
open Formula.Kripke

variable {C : Kripke.FrameClass} {H H₁ H₂ : Hilbert ℕ} {φ : Formula ℕ}

lemma Hilbert.validFrameClass_of_provable {H : Hilbert ℕ} [hCH : C ⊧* H] : H ⊢ φ → C ⊧ φ := by
  rintro ⟨h⟩;
  induction h with
  | axm h => exact hCH.models _ h;
  | mdp _ _ ihφψ ihφ => intro F hF; exact ValidOnFrame.mdp (ihφψ hF) (ihφ hF);
  | _ => intro F; grind;

instance [C ⊧* H] : Sound H C := ⟨Hilbert.validFrameClass_of_provable⟩

lemma consistent_of_nonempty_frameClass (C : FrameClass) (hC : Set.Nonempty C) [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push Not;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

lemma weakerThan_of_subset_frameClass (C₁ C₂ : FrameClass) (hC : C₂ ⊆ C₁) [soundH₁ : Sound H₁ C₁] [completeH₂ : Complete H₂ C₂] : H₁ ⪯ H₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply completeH₂.complete;
  intro F hF;
  apply soundH₁.sound hφ;
  apply hC hF;

end LO.Propositional

end
