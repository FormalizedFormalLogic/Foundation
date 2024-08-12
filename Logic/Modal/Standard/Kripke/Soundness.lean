import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Kripke

variable {Ax : AxiomSet α}

open Formula
open Formula.Kripke
open Deduction
open DeductionParameter (Normal)

section

variable {𝔽 : FrameClass}

lemma sound (defines : Ax.DefinesKripkeFrameClass 𝔽) (d : (𝝂Ax) ⊢! p) : 𝔽# ⊧ p := by
  induction d using Deduction.inducition_with_necOnly! with
  | hMaxm h =>
    simp only [Set.mem_setOf_eq] at h;
    rcases h with (⟨p, q, rfl⟩ | hR);
    . exact Kripke.ValidOnFrameClass.axiomK;
    . intro F hF;
      exact Semantics.RealizeSet.setOf_iff.mp (defines.mpr hF) _ hR;
  | hMdp ihpq ihp => exact Kripke.ValidOnFrameClass.mdp ihpq ihp;
  | hNec ih => exact Kripke.ValidOnFrameClass.nec ih;
  | _ => first
    | exact ValidOnFrameClass.imply₁;
    | exact ValidOnFrameClass.imply₂;
    | exact ValidOnFrameClass.elimContra;

lemma sound_of_defines (defines : Ax.DefinesKripkeFrameClass 𝔽) : Sound (𝝂Ax) 𝔽# := ⟨sound defines⟩

lemma unprovable_bot_of_nonempty_frameClass (defines : Ax.DefinesKripkeFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : (𝝂Ax) ⊬! ⊥ := by
  by_contra hC;
  obtain ⟨⟨_, F⟩, hF⟩ := nonempty;
  simpa using sound defines hC hF;

lemma consistent_of_defines (defines : Ax.DefinesKripkeFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : System.Consistent (𝝂Ax) := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot_of_nonempty_frameClass defines nonempty;

instance K_sound : Sound (𝐊 : DeductionParameter α) AllFrameClass# := by simpa [←Normal.isK] using sound_of_defines axiomK_defines;

instance K_consistent' : System.Consistent 𝝂(𝗞 : AxiomSet α) := consistent_of_defines axiomK_defines AllFrameClass.nonempty

instance K_consistent : System.Consistent (𝐊 : DeductionParameter α) := by
  simpa [←Normal.isK] using K_consistent';

end

section

variable {𝔽 : FiniteFrameClass}

lemma finite_sound (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) (d : (𝝂Ax) ⊢! p) : (𝔽 : FrameClass)# ⊧ p := by
  induction d using Deduction.inducition_with_necOnly! with
  | hMaxm h =>
    simp only [Set.mem_setOf_eq] at h;
    rcases h with (⟨p, q, rfl⟩ | hR);
    . exact Kripke.ValidOnFrameClass.axiomK;
    . rintro F ⟨FF, hFF, rfl⟩;
      exact Semantics.RealizeSet.setOf_iff.mp (defines.mpr hFF) _ hR;
  | hMdp ihpq ihp => exact Kripke.ValidOnFrameClass.mdp ihpq ihp;
  | hNec ih => exact Kripke.ValidOnFrameClass.nec ih;
  | _ => first
    | exact ValidOnFrameClass.imply₁;
    | exact ValidOnFrameClass.imply₂;
    | exact ValidOnFrameClass.elimContra;

lemma sound_of_finitely_defines (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) : Sound (𝝂Ax) ↑𝔽# := ⟨finite_sound defines⟩

lemma unprovable_bot_of_nonempty_finite_frameClass (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : (𝝂Ax) ⊬! ⊥ := by
  by_contra hC;
  obtain ⟨F, hF⟩ := nonempty;
  have := @finite_sound α Ax 𝔽 ⊥ defines hC ↑F;
  simp [FiniteFrameClass.toFrameClass] at this;
  have := this F hF;
  contradiction;

lemma consistent_of_finitely_defines (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : System.Consistent (𝝂Ax) := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot_of_nonempty_finite_frameClass defines nonempty;

end

section

variable {𝔽 : FrameClass}

lemma restrict_finite : 𝔽# ⊧ p → 𝔽ꟳ# ⊧ p := by
  intro h F hF;
  obtain ⟨fF, hfF, e⟩ := hF; subst e;
  exact h hfF;

instance instFiniteSound {Λ : DeductionParameter α} [Λ.IsNormal] [sound : Sound Λ 𝔽#] : Sound Λ 𝔽ꟳ# := ⟨by
  intro p h;
  exact restrict_finite $ sound.sound h;
⟩

instance K_fin_sound : Sound (𝐊 : DeductionParameter α) AllFrameClassꟳ# := inferInstance

end

end Kripke

section Reducible

variable [Inhabited α] [DecidableEq α]

open System (weakerThan_iff)
open Kripke
open Formula (atom)
open Formula.Kripke

theorem K_strictlyWeakerThan_KD : (𝐊 : DeductionParameter α) <ₛ 𝐊𝐃 := by
  constructor;
  . apply reducible_K_KD;
  . simp [weakerThan_iff];
    use (□(atom default) ⟶ ◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [FrameClass, ValidOnFrame, ValidOnModel, Satisfies];
      use { World := Fin 1, Rel := λ _ _ => False }, (λ w _ => w = 0), 0;
      simp;

theorem K_strictlyWeakerThan_K4 : (𝐊 : DeductionParameter α) <ₛ 𝐊𝟒 := by
  constructor;
  . apply reducible_K_K4;
  . simp [weakerThan_iff];
    use (□(atom default) ⟶ □□(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [FrameClass, ValidOnFrame, ValidOnModel, Satisfies, Frame.Rel'];
      use { World := Fin 2, Rel := λ x y => x ≠ y }, (λ w _ => w = 1), 0;
      simp;
      constructor;
      . intro y;
        match y with
        | 0 => tauto;
        | 1 => tauto;
      . use 1;
        constructor;
        . simp;
        . use 0; simp;

theorem K_strictlyWeakerThan_KB : (𝐊 : DeductionParameter α) <ₛ 𝐊𝐁 := by
  constructor;
  . apply reducible_K_KB;
  . simp [weakerThan_iff];
    use ((atom default) ⟶ □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [FrameClass, ValidOnFrame, ValidOnModel, Satisfies];
      use { World := Fin 2, Rel := λ x y => x = 0 ∧ y = 1 }, (λ w _ => w = 0), 0;
      simp;
      use 1;

theorem K_strictlyWeakerThan_K5 : (𝐊 : DeductionParameter α) <ₛ 𝐊𝟓 := by
  constructor;
  . apply reducible_K_K5;
  . simp [weakerThan_iff];
    use (◇(atom default) ⟶ □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [FrameClass, ValidOnFrame, ValidOnModel, Satisfies, Frame.Rel'];
      use { World := Fin 2, Rel := λ x _ => x = 0 }, (λ w _ => w = 1), 0;
      simp;
      use 1; tauto;

end Reducible

end LO.Modal.Standard
