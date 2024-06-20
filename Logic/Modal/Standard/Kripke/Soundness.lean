import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard.Kripke

variable {α : Type u} {Ax : AxiomSet α}

open Deduction
open Formula

open DeductionParameter (Normal)

lemma sound [definability : Ax.DefinesKripkeFrameClass 𝔽] (d : (Normal Ax) ⊢! p) : 𝔽 ⊧ p := by
  induction d using Deduction.inducition_with_necOnly! with
  | hMaxm h =>
    simp only [Set.mem_setOf_eq] at h;
    rcases h with (hK | hR);
    . exact (Semantics.RealizeSet.setOf_iff.mp valid_on_KripkeFrameClass.axiomK) _ hK;
    . intro F hF;
      exact Semantics.RealizeSet.setOf_iff.mp (definability.defines.mpr hF) _ hR;
  | hMdp ihpq ihp => exact valid_on_KripkeFrameClass.mdp ihpq ihp;
  | hNec ih => exact valid_on_KripkeFrameClass.nec ih;
  | hDisj₃ =>
    simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [valid_on_KripkeFrameClass, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];

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

private instance instConsistent_of_K' : System.Consistent ((Normal 𝗞) : DeductionParameter α) := consistent (𝔽 := AllFrameClass α)

instance instConsistent_of_K : System.Consistent (𝐊 : DeductionParameter α) := by
  simpa [←Normal.isK] using instConsistent_of_K';



end LO.Modal.Standard.Kripke
