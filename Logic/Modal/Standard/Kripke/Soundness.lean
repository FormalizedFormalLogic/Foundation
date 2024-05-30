import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Kripke

variable {W α : Type*} [Inhabited W] [Inhabited α]
variable {L : DeductionParameter α} [L.HasNec]

open Deduction
open Formula Formula.Kripke

lemma sound_on_frameclass (d : L ⊢ p) : 𝔽(Ax(L)) ⊧ p := by
  induction d using Deduction.inducition_with_nec with
  | hMaxm h => exact validOnAxiomSetFrameClass_axiom h;
  | hMdp _ _ ihpq ihp =>
    intro W _ F hF V w;
    exact (Semantics.Tarski.realize_imp.mp $ ihpq W F hF V w) (ihp W F hF V w);
  | hNec _ ih =>
    intro W _ F hF V w w' _;
    exact ih W F hF V w';
  | hDisj₃ =>
    simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];

lemma sound!_on_frameclass : L ⊢! p → 𝔽(Ax(L)) ⊧ p := λ ⟨d⟩ => sound_on_frameclass d

instance : Sound L 𝔽(L.axiomSet) := ⟨sound!_on_frameclass⟩

lemma unprovable_bot [ne : FrameClass.Nonempty 𝔽(Ax(L))] : L ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := ne.existsi;
  have := sound!_on_frameclass h;
  simp [ValidOnFrameClass, ValidOnFrame, ValidOnModel] at this;
  have := @this ne.W ne.W_inhabited F;
  contradiction;

instance [FrameClass.Nonempty 𝔽(Ax(L))] : System.Consistent L := System.Consistent.of_unprovable unprovable_bot

instance : System.Consistent (𝐊 : DeductionParameter α) := inferInstance

lemma unprovable_bot_finite [ne : FiniteFrameClass.Nonempty 𝔽ꟳ(Ax(L))] : L ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := ne.existsi;
  have := sound!_on_frameclass h;
  simp [ValidOnFrameClass, ValidOnFrame, ValidOnModel] at this;
  have := @this ne.W ne.W_inhabited F;
  contradiction;

instance [FiniteFrameClass.Nonempty 𝔽ꟳ(Ax(L))] : System.Consistent L := System.Consistent.of_unprovable unprovable_bot_finite

end LO.Modal.Standard.Kripke
