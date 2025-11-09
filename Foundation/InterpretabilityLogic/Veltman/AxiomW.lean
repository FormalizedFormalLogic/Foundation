import Foundation.InterpretabilityLogic.Veltman.Basic
import Foundation.InterpretabilityLogic.Veltman.AxiomJ2
import Foundation.InterpretabilityLogic.Veltman.Logic.IL

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
lemma validate_axiomW_of_HasAxiomW [F.IsILMinus_J2Plus_J5] [F.HasAxiomW] : F ⊧ Axioms.W φ ψ := by
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
      apply Satisfies.not_def.mpr;
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
lemma Frame.HasAxiomW.of_validate_axiomF [F.IsILMinus_J1_J2_J5] (h : F ⊧ Axioms.F (.atom 0)) : F.HasAxiomW := by
  constructor;
  intro x;
  apply ConverseWellFounded.iff_has_max.mpr;
  rintro S ⟨u₁, hu₁⟩;
  wlog exu : x = u₁;
  . have := @this F _ h x S;
    sorry;
  subst exu;

  have := @h (λ w a => match a with | 0 => ∃ u ∈ S, u ≺≺[x] w | _ => False) x;
  contrapose! this;
  apply Satisfies.imp_def.not.mpr;
  push_neg;
  constructor;
  . intro y Rxy ⟨u, hu, RSxuy⟩;
    use y;
    constructor;
    . apply F.S_J1;
      assumption;
    . apply Satisfies.dia_def.mpr;
      use u;
      constructor;
      . sorry;
      . sorry;
  . apply Satisfies.box_def.not.mpr;
    push_neg;
    obtain ⟨y, hy, ⟨v, Rxv, Sxvy⟩⟩ := this x hu₁;
    use y;
    constructor;
    . apply F.S_J4 Sxvy
    . suffices ∃ u ∈ S, u ≺≺[x] y by simpa [Semantics.Models, Satisfies];
      use x;
      refine ⟨?_, ?_⟩;
      . assumption;
      . use v;


lemma Frame.HasAxiomW.of_validate_axiomW [F.IsILMinus_J1_J2_J5] (h : F ⊧ Axioms.W (.atom 0) (.atom 1)) : F.HasAxiomW := by sorry;

end LO.InterpretabilityLogic.Veltman
