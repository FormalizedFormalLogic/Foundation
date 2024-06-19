import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Kripke

variable {α : Type u} {Ax : AxiomSet α}

open Deduction
open Formula

open DeductionParameter (Normal)

lemma sound [definability : Ax.DefinesKripkeFrameClass 𝔽] (d : (Normal Ax) ⊢! p) : 𝔽 ⊧ p := by
  induction d using Deduction.inducition_with_nec! with
  | hMaxm h =>
    simp only [Set.mem_setOf_eq] at h;
    rcases h with (hK | hR);
    . exact (Semantics.RealizeSet.setOf_iff.mp valid_on_KripkeFrameClass.axiomK) _ hK;
    . intro F hF;
      exact Semantics.RealizeSet.setOf_iff.mp (definability.defines.mpr hF) _ hR;
  | hMdp ihpq ihp => exact valid_on_KripkeFrameClass.mdp ihpq ihp;
  | hNec ih => exact valid_on_KripkeFrameClass.nec ih;
  | hDisj₃ =>
    simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel];

instance instSound [Ax.DefinesKripkeFrameClass 𝔽] : Sound (DeductionParameter.Normal Ax) 𝔽 := ⟨sound⟩

instance : Sound 𝐊 (AllFrameClass α) := by
  simpa [←Normal.isK] using (instSound (Ax := 𝗞) (𝔽 := AllFrameClass α));

lemma unprovable_bot (𝔽 : FrameClass α) [Ax.DefinesKripkeFrameClass 𝔽] [nonempty : 𝔽.IsNonempty] : (Normal Ax) ⊬! ⊥ := by
  by_contra hC;
  obtain ⟨F, hF⟩ := nonempty.nonempty
  simpa using sound hC F hF;

lemma consistent (𝔽 : FrameClass α) [Ax.DefinesKripkeFrameClass 𝔽] [𝔽.IsNonempty] : System.Consistent (Normal Ax) := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot 𝔽;

instance : System.Consistent (𝐊 : DeductionParameter α) := by
  simpa [←Normal.isK] using consistent (Ax := 𝗞) (𝔽 := AllFrameClass α)

/-
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
-/

end LO.Modal.Standard.Kripke
