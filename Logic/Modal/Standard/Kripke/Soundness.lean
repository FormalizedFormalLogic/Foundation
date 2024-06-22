import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Kripke

variable {α : Type u} {Ax : AxiomSet α}

open Deduction
open Formula

open DeductionParameter (Normal)

lemma sound (defines : Ax.DefinesKripkeFrameClass 𝔽) (d : Axᴺ ⊢! p) : 𝔽 ⊧ p := by
  induction d using Deduction.inducition_with_necOnly! with
  | hMaxm h =>
    simp only [Set.mem_setOf_eq] at h;
    rcases h with (hK | hR);
    . exact (Semantics.RealizeSet.setOf_iff.mp valid_on_KripkeFrameClass.axiomK) _ hK;
    . intro F hF;
      exact Semantics.RealizeSet.setOf_iff.mp (defines.mpr hF) _ hR;
  | hMdp ihpq ihp => exact valid_on_KripkeFrameClass.mdp ihpq ihp;
  | hNec ih => exact valid_on_KripkeFrameClass.nec ih;
  | hDisj₃ =>
    simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];

lemma sound_of_defines (defines : Ax.DefinesKripkeFrameClass 𝔽) : Sound Axᴺ 𝔽 := ⟨sound defines⟩

instance : Sound 𝐊 (AllFrameClass α) := by simpa [←Normal.isK] using (sound_of_defines (Ax := 𝗞) (𝔽 := AllFrameClass α) axiomK_defines);


lemma unprovable_bot_of_nonempty_frameClass (defines : Ax.DefinesKripkeFrameClass 𝔽) [nonempty : 𝔽.IsNonempty] : Axᴺ ⊬! ⊥ := by
  by_contra hC;
  obtain ⟨F, hF⟩ := nonempty.nonempty
  simpa using sound defines hC F hF;

lemma consistent_of_defines (defines : Ax.DefinesKripkeFrameClass 𝔽) [𝔽.IsNonempty] : System.Consistent Axᴺ := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot_of_nonempty_frameClass defines;

instance K_consistent' : System.Consistent (𝗞 : AxiomSet α)ᴺ := consistent_of_defines axiomK_defines

instance K_consistent : System.Consistent (𝐊 : DeductionParameter α) := by
  simpa [←Normal.isK] using K_consistent';



lemma finite_sound (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) (d : Axᴺ ⊢! p) : 𝔽ᶠ ⊧ p := by
  induction d using Deduction.inducition_with_necOnly! with
  | hMaxm h =>
    simp only [Set.mem_setOf_eq] at h;
    rcases h with (hK | hR);
    . exact (Semantics.RealizeSet.setOf_iff.mp valid_on_KripkeFrameClass.axiomK) _ hK;
    . intro F hF;
      simp [FrameClass.toFinite] at hF;
      apply Semantics.RealizeSet.setOf_iff.mp (defines hF.2 |>.mpr hF.1) _ hR;
  | hMdp ihpq ihp => exact valid_on_KripkeFrameClass.mdp ihpq ihp;
  | hNec ih => exact valid_on_KripkeFrameClass.nec ih;
  | hDisj₃ =>
    simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];

lemma sound_of_finitely_defines (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) : Sound Axᴺ 𝔽ᶠ := ⟨finite_sound defines⟩

lemma unprovable_bot_of_nonempty_finite_frameClass (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) [nonempty : 𝔽ᶠ.IsNonempty] : Axᴺ ⊬! ⊥ := by
  by_contra hC;
  obtain ⟨F, hF⟩ := nonempty.nonempty;
  simpa using finite_sound defines hC F hF;

lemma consistent_of_finitely_defines (defines : Ax.FinitelyDefinesKripkeFrameClass 𝔽) [𝔽ᶠ.IsNonempty] : System.Consistent Axᴺ := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot_of_nonempty_finite_frameClass defines;

end LO.Modal.Standard.Kripke
