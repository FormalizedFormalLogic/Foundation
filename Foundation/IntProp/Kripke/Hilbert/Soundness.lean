import Foundation.IntProp.Hilbert.Basic
import Foundation.IntProp.Kripke.Basic

namespace LO.IntProp

open Kripke
open Formula
open Formula.Kripke

namespace Kripke.Hilbert

variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section

variable {C : Kripke.FrameClass}

lemma soundness_of_FrameClass_definedBy_axiomInstances [defined : C.DefinedBy H.axiomInstances] : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Deduction.rec! with
  | verum => apply ValidOnFrame.top;
  | implyS => apply ValidOnFrame.imply₁;
  | implyK => apply ValidOnFrame.imply₂;
  | andElimL => apply ValidOnFrame.andElim₁;
  | andElimR => apply ValidOnFrame.andElim₂;
  | andIntro => apply ValidOnFrame.andInst₃;
  | orIntroL => apply ValidOnFrame.orInst₁;
  | orIntroR => apply ValidOnFrame.orInst₂;
  | orElim => apply ValidOnFrame.orElim;
  | mdp => exact ValidOnFrame.mdp (by assumption) (by assumption);
  | maxm hi =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := hi;
    apply defined.defines F |>.mp hF (ψ⟦s⟧);
    use ψ;
    constructor
    . assumption;
    . use s;

instance [defs : C.DefinedBy H.axioms] : C.DefinedBy H.axiomInstances := ⟨by
  intro F;
  constructor;
  . rintro hF φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
    exact ValidOnFrame.subst $ defs.defines F |>.mp hF ψ hψ;
  . intro h;
    apply defs.defines F |>.mpr;
    intro φ hφ;
    apply h;
    use φ;
    constructor;
    . assumption;
    . use .id;
      simp;
⟩

instance [C.DefinedBy H.axioms] : Sound H C := ⟨fun {_} => soundness_of_FrameClass_definedBy_axiomInstances⟩

lemma consistent_of_FrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  use F;
  constructor;
  . assumption;
  . simp;

lemma consistent_of_FrameClass (C : Kripke.FrameClass) [C.IsNonempty] [Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FrameClass_aux (C := C);

end

end Kripke.Hilbert

end LO.IntProp
