import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Kripke

variable {α : Type u}
         {L : DeductionParameter α} [L.HasNecOnly]

open Deduction
open Formula

lemma sound_on_frameclass (d : L ⊢ p) : 𝔽(Ax(L)) ⊧ p := by
  induction d using Deduction.inducition_with_nec with
  | hMaxm h => exact validOnAxiomSetFrameClass_axiom h;
  | hMdp _ _ ihpq ihp =>
    intro F hF V w;
    exact (ihpq F hF V w) (ihp F hF V w);
  | hNec _ ih =>
    intro F hF V w w' _;
    exact ih F hF V w';
  | hDisj₃ =>
    simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel];

lemma sound!_on_frameclass : L ⊢! p → 𝔽(Ax(L)) ⊧ p := λ ⟨d⟩ => sound_on_frameclass d

instance : Sound L 𝔽(L.axiomSet) := ⟨sound!_on_frameclass⟩

lemma unprovable_bot [ne : 𝔽(Ax(L)).IsNonempty] : L ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := ne.nonempty;
  simpa using sound!_on_frameclass h F hF;

instance Consistent_of_nonemptyFrameClass [𝔽(Ax(L)).IsNonempty] : System.Consistent L := System.Consistent.of_unprovable $ unprovable_bot

lemma unprovable_bot_finite [ne : 𝔽ꟳ(Ax(L)).IsNonempty] : L ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := ne.nonempty;
  simpa using sound!_on_frameclass h F.toFrame hF;

instance Consistent_of_nonemptyFiniteFrameClass [𝔽ꟳ(Ax(L)).IsNonempty] : System.Consistent L := System.Consistent.of_unprovable $ unprovable_bot_finite

instance : System.Consistent (𝐊 : DeductionParameter α) := inferInstance

end LO.Modal.Standard.Kripke
