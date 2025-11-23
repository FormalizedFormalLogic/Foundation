import Foundation.Propositional.Hilbert.VCorsi.Basic
import Foundation.Propositional.FMT.Basic

namespace LO.Propositional

open FMT
open Formula.FMT

namespace Hilbert.VCorsi.FMT

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section FrameClass

variable {C C₁ C₂ : FMT.FrameClass}

lemma soundness_frameclass (hV : C ⊧* Ax.instances) : (Hilbert.VCorsi Ax) ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | axm s hi =>
    apply hV.models;
    . grind;
    . assumption;
  | _ => grind;

instance instFrameClassSound (hV : C ⊧* Ax.instances) : Sound (Hilbert.VCorsi Ax) C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass (C : FMT.FrameClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.VCorsi Ax) C] : Entailment.Consistent (Hilbert.VCorsi Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  grind;

lemma weakerThan_of_subset_frameClass (C₁ C₂ : FMT.FrameClass) (hC : C₂ ⊆ C₁) [Sound (Hilbert.VCorsi Ax₁) C₁] [Complete (Hilbert.VCorsi Ax₂) C₂] : (Hilbert.VCorsi Ax₁) ⪯ (Hilbert.VCorsi Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := (Hilbert.VCorsi Ax₁)) (𝓜 := C₁) hφ;
  apply hC hF;

end FrameClass

end Hilbert.VCorsi.FMT


end LO.Propositional
