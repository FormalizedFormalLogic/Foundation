import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard.Kripke

variable {W α : Type*}
variable {Λ : AxiomSet α}

open Deduction
open Formula Formula.Kripke

lemma sound (d : Λ ⊢ p) : 𝔽(Λ, W) ⊧ p := by
  induction d with
  | maxm h => exact validOnAxiomSetFrameClass_axiom h;
  | mdp _ _ ihpq ihp =>
    intro F hF V w;
    have := ihpq F hF V w;
    have := ihp F hF V w;
    simp_all;
  | nec _ ih =>
    intro F hF V w w' _;
    exact ih F hF V w';
  | disj₃ =>
    intro _ _;
    simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ =>
    intro _ _;
    simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];

lemma sound! : Λ ⊢! p → 𝔽(Λ, W) ⊧ p := λ ⟨d⟩ => sound d

instance : Sound Λ 𝔽(Λ, W) := ⟨sound!⟩


lemma sound_on_model {M : Model W α} [M ⊧* Λ] (d : Λ ⊢ p) : M ⊧ p := by
  induction d with
  | maxm h => exact Semantics.RealizeSet.realize _ h
  | mdp _ _ ihpq ihp =>
    intro w;
    exact (Semantics.Tarski.realize_imp.mp $ ihpq w) (ihp w);
  | nec _ ih =>
    intro w w' _;
    exact ih w';
  | disj₃ =>
    simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];

lemma sound_on_model! {M : Model W α} [M ⊧* Λ] : Λ ⊢! p → M ⊧ p := λ ⟨d⟩ => sound_on_model d

instance {M : Model W α} [M ⊧* Λ] : Sound Λ M := ⟨sound_on_model!⟩


lemma sound_on_frame {F : Frame W α} [F ⊧* Λ] (d : Λ ⊢ p) : F ⊧ p := by
  induction d with
  | maxm h => exact Semantics.realizeSet_iff.mp (by assumption) h;
  | mdp _ _ ihpq ihp =>
    intro V w;
    exact (Semantics.Tarski.realize_imp.mp $ ihpq V w) (ihp V w);
  | nec _ ih =>
    intro V w w' _;
    exact ih V w';
  | disj₃ =>
    simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];

lemma sound_on_frame! {F : Frame W α} [F ⊧* Λ] : Λ ⊢! p → F ⊧ p := λ ⟨d⟩ => sound_on_frame d

instance {F : Frame W α} [F ⊧* Λ] : Sound Λ F := ⟨sound_on_frame!⟩

end LO.Modal.Standard.Kripke
