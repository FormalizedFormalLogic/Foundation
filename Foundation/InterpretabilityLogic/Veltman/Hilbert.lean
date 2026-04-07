module

public import Foundation.InterpretabilityLogic.Hilbert.Basic.Basic
public import Foundation.InterpretabilityLogic.Hilbert.Minimal.Basic
public import Foundation.InterpretabilityLogic.Veltman.Basic

@[expose] public section

namespace LO.InterpretabilityLogic

open Formula
open Formula.Veltman

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {φ : Formula ℕ}
variable {F : Veltman.Frame} {C C₁ C₂ : Veltman.FrameClass}

namespace Hilbert.Minimal.Veltman

lemma soundness_frameclass (hV : C ⊧* Ax) : Hilbert.Minimal Ax ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Minimal.rec! with
  | @axm φ s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    . assumption;
    . assumption;
  | _ => grind;

instance instFrameClassSound (hV : C ⊧* Ax) : Sound (Hilbert.Minimal Ax) C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass
  (C : Veltman.FrameClass) (C_nonempty: C.Nonempty)
  [sound : Sound (Hilbert.Minimal Ax) C]
  : Entailment.Consistent (Hilbert.Minimal Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push Not;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma soundness_frame (hV : F ⊧* Ax) : Hilbert.Minimal Ax ⊢ φ → F ⊧ φ := by
  intro hφ;
  induction hφ using Hilbert.Minimal.rec! with
  | axm s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    assumption;
  | _ => grind;

end Hilbert.Minimal.Veltman


namespace Hilbert.Basic.Veltman

lemma soundness_frameclass (hV : C ⊧* Ax) : Hilbert.Basic Ax ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Basic.rec! with
  | @axm φ s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    . assumption;
    . assumption;
  | _ => grind;

instance instFrameClassSound (hV : C ⊧* Ax) : Sound (Hilbert.Basic Ax) C := ⟨fun {_} => soundness_frameclass hV⟩

lemma consistent_of_sound_frameclass
  (C : Veltman.FrameClass) (C_nonempty: C.Nonempty)
  [sound : Sound (Hilbert.Basic Ax) C]
  : Entailment.Consistent (Hilbert.Basic Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push Not;
  obtain ⟨F, hF⟩ := C_nonempty;
  use F;
  constructor;
  . assumption;
  . simp;


lemma soundness_frame [F.IsGL] (hV : F ⊧* Ax) : (Hilbert.Basic Ax) ⊢ φ → F ⊧ φ := by
  intro hφ;
  induction hφ using Hilbert.Basic.rec! with
  | axm s h =>
    apply ValidOnFrame.subst;
    apply hV.models;
    assumption;
  | _ => grind;

instance instFrameSound [F.IsGL] (hV : F ⊧* Ax) : Sound (Hilbert.Basic Ax) F := ⟨fun {_} =>
  soundness_frame hV
⟩

lemma consistent_of_sound_frame (F : Veltman.Frame) [sound : Sound (Hilbert.Basic Ax) F] : Entailment.Consistent (Hilbert.Basic Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  exact Veltman.ValidOnFrame.bot_def;

lemma weakerThan_of_subset_frameClass
  (C₁ C₂ : Veltman.FrameClass) (hC : C₂ ⊆ C₁)
  [Sound (Hilbert.Basic Ax₁) C₁] [Complete (Hilbert.Basic Ax₂) C₂]
  : (Hilbert.Basic Ax₁) ⪯ (Hilbert.Basic Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓜 := C₁) hφ;
  apply hC hF;

end Hilbert.Basic.Veltman


end LO.InterpretabilityLogic
end
