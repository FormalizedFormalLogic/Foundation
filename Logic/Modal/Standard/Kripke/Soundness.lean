import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Kripke

variable {α : Type u}
         {L : DeductionParameter α} [L.HasNec]

open Deduction
open Formula Formula.Kripke

lemma sound_on_frameclass (d : L ⊢ p) : 𝔽(Ax(L)) ⊧ p := by
  induction d using Deduction.inducition_with_nec with
  | hMaxm h => exact validOnAxiomSetFrameClass_axiom h;
  | hMdp _ _ ihpq ihp =>
    intro F hF V w;
    exact Satisfies.mdp (ihpq F hF V w) (ihp F hF V w);
  | hNec _ ih =>
    intro F hF V w w' _;
    exact ih F hF V w';
  | hDisj₃ =>
    simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];

lemma sound!_on_frameclass : L ⊢! p → 𝔽(Ax(L)) ⊧ p := λ ⟨d⟩ => sound_on_frameclass d

instance : Sound L 𝔽(L.axiomSet) := ⟨sound!_on_frameclass⟩

lemma unprovable_bot [ne : FrameClass.IsNonempty 𝔽(Ax(L))] : L ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := ne;
  simpa using sound!_on_frameclass h F hF;

instance Consistent_of_nonemptyFrameClass [FrameClass.IsNonempty.{u} 𝔽(Ax(L))] : System.Consistent L := System.Consistent.of_unprovable $ unprovable_bot

lemma unprovable_bot_finite [ne : FiniteFrameClass.IsNonempty 𝔽ꟳ(Ax(L))] : L ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := ne;
  simpa using sound!_on_frameclass h F.toFrame hF;

instance Consistent_of_nonemptyFiniteFrameClass [FiniteFrameClass.IsNonempty.{u} 𝔽ꟳ(Ax(L))] : System.Consistent L := System.Consistent.of_unprovable $ unprovable_bot_finite

instance : System.Consistent (𝐊 : DeductionParameter α) := inferInstance

end LO.Modal.Standard.Kripke
