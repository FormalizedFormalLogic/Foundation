module

public import Foundation.InterpretabilityLogic.Veltman.Logic.IL

@[expose] public section

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

abbrev RS {F : Frame} (w : F.World) := Relation.Comp (· ≺ ·) (· ≺[w] ·)
notation:50 x:max " ≺≺[" w "] " y:max => RS w x y

class HasAxiomW (F : Frame) : Prop where
  S_W : ∀ w : F.World, ConverseWellFounded $ (· ≺≺[w] ·)
export HasAxiomW (S_W)

end Frame

@[simp high, grind .]
lemma validate_axiomW_of_HasAxiomW [F.IsIL] [F.HasAxiomW] : F ⊧ Axioms.W φ ψ := by
  intro V x h₁ y Rxy h₂;
  obtain ⟨z, ⟨Sxyz, hz⟩, hb⟩ := F.S_W x |>.has_max ({ z | y ≺[x] z ∧ Satisfies ⟨F, V⟩ z ψ }) $ by
    obtain ⟨z, _, _⟩ := h₁ y Rxy h₂;
    use z;
    tauto;
  use z;
  constructor;
  . tauto;
  . apply Satisfies.and_def.mpr;
    constructor;
    . simpa;
    . apply Satisfies.box_def.mpr;
      intro u Rzu;
      apply Satisfies.neg_def.mpr;
      by_contra hC;
      have Rxu : x ≺ u := F.trans (F.S_J4 Sxyz) Rzu;
      obtain ⟨v, Sxuv, hv⟩ := h₁ u Rxu hC;
      apply hb v;
      . constructor;
        . apply F.S_J2 Sxyz;
          apply F.S_J2 ?_ Sxuv;
          apply F.S_J5 ?_ Rzu;
          apply F.S_J4 Sxyz;
        . assumption;
      . use u;


open Formula (atom) in
lemma Frame.HasAxiomW.of_validate_axiomF [F.IsIL] (h : F ⊧ Axioms.F (.atom 0)) : F.HasAxiomW := by
  constructor;
  contrapose! h;
  obtain ⟨w, hw⟩ := h;
  obtain ⟨f, hf⟩ := not_isEmpty_iff.mp $ wellFounded_iff_isEmpty_descending_chain.not.mp hw;
  replace hf : ∀ n, ∃ v, (f n) ≺ v ∧ v ≺[w] (f (n + 1)) := by simpa [RS, Relation.Comp, flip] using hf;
  apply ValidOnFrame.iff_not_exists_valuation_world.mpr;
  use (λ a u => match a with | 0 => ∃ i > 0, u = (hf i).choose | _ => False), w;
  apply Satisfies.not_imp_def.mpr;
  constructor;
  . apply Satisfies.rhd_def.mpr;
    rintro v Rwy ⟨m, hm, rfl⟩;
    use (f (m + 1));
    constructor;
    . exact hf m |>.choose_spec.2;
    . apply Satisfies.dia_def.mpr;
      use (hf (m + 1)).choose;
      constructor;
      . exact hf (m + 1) |>.choose_spec.1;
      . use m + 1;
        tauto;
  . apply Satisfies.not_box_def.mpr;
    use (hf 1).choose;
    constructor;
    . apply F.trans (F.S_J4 (hf 0).choose_spec.2) (hf 1).choose_spec.1;
    . apply Satisfies.not_neg_def.mpr;
      use 1;
      tauto;

lemma TFAE_HasAxiomW [F.IsIL] : [
    F.HasAxiomW,
    F ⊧ Axioms.W (.atom 0) (.atom 1),
    F ⊧ Axioms.F (.atom 0)
  ].TFAE := by
    tfae_have 1 → 2 := by apply validate_axiomW_of_HasAxiomW;
    tfae_have 2 → 3 := by
      intro h;
      apply Hilbert.Basic.Veltman.soundness_frame (Ax := IL_W.axioms);
      . constructor;
        rintro φ hφ;
        rcases (by simpa using hφ) with (rfl | rfl | rfl | rfl | rfl | rfl);
        . assumption;
        . simp [validate_axiomJ5_of_J5]
        . simp [validate_axiomJ1_of_J1]
        . simp [validate_axiomJ2_of_HasAxiomJ2]
        . simp [validate_axiomJ3]
        . simp [validate_axiomJ4_of_HasAxiomJ4]
      . suffices InterpretabilityLogic.IL_W ⊢ Axioms.F (.atom 0) by tauto;
        simp;
    tfae_have 3 → 1 := Frame.HasAxiomW.of_validate_axiomF;
    tfae_finish;

@[simp high, grind .]
lemma validate_axiomF_of_HasAxiomW [F.IsIL] [F.HasAxiomW] : F ⊧ Axioms.F φ := by
  have : F ⊧ Axioms.F (.atom 0) := TFAE_HasAxiomW.out 0 2 |>.mp (by infer_instance);
  apply ValidOnFrame.subst (s := λ n => φ) this;

lemma Frame.HasAxiomW.of_validate_axiomW [F.IsIL] (h : F ⊧ Axioms.W (.atom 0) (.atom 1)) : F.HasAxiomW := TFAE_HasAxiomW.out 1 0 |>.mp h

end LO.InterpretabilityLogic.Veltman
end
