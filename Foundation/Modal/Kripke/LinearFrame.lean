import Foundation.Modal.Kripke.Preservation
import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.AxiomZ
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace LO.Modal.Kripke

abbrev NatLTFrame : Kripke.Frame where
  World := ℕ
  Rel := (· < ·)

namespace NatLTFrame

instance : IsTrans _ NatLTFrame := by
  dsimp only [NatLTFrame];
  infer_instance;

abbrev min : NatLTFrame.World := 0

instance : Frame.IsRooted NatLTFrame NatLTFrame.min where
  root_generates := by
    intro x hx;
    apply Relation.TransGen.single;
    simp_all [Frame.Rel', NatLTFrame, NatLTFrame.min];
    omega;

end NatLTFrame


abbrev NatLEFrame : Kripke.Frame where
  World := ℕ
  Rel := (· ≤ ·)

namespace NatLEFrame

instance : IsTrans _ NatLEFrame := by
  dsimp only [NatLEFrame];
  infer_instance;

instance : IsRefl _ NatLEFrame := by
  dsimp only [NatLEFrame];
  infer_instance;

abbrev min : NatLEFrame.World := 0

instance : Frame.IsRooted NatLEFrame NatLEFrame.min where
  root_generates := by
    intro x _;
    apply Relation.TransGen.single;
    simp_all [Frame.Rel', NatLEFrame, NatLEFrame.min];

end NatLEFrame


abbrev FinLTFrame (n : ℕ) [NeZero n] : Kripke.Frame where
  World := Fin n
  Rel := (· < ·)

namespace FinLTFrame

variable {n : ℕ} [NeZero n]

instance : Finite (FinLTFrame n) := by
  dsimp only [FinLTFrame];
  infer_instance;

end FinLTFrame


abbrev FinLEFrame (n : ℕ) [NeZero n] : Kripke.Frame where
  World := Fin n
  Rel := (· ≤ ·)

namespace FinLEFrame

variable {n : ℕ} [NeZero n]

instance : Finite (FinLTFrame n) := by
  dsimp only [FinLTFrame];
  infer_instance;

instance : IsTrans _ (FinLEFrame n) := by
  dsimp only [FinLEFrame];
  infer_instance;

instance : IsRefl _ (FinLEFrame n) := by
  dsimp only [FinLEFrame];
  infer_instance;

instance : IsAntisymm _ (FinLEFrame n) := by
  dsimp only [FinLEFrame];
  infer_instance;

end FinLEFrame


open
  Formula
  Formula.Kripke
in
/-- Goldblatt, Exercise 8.1 (1) -/
lemma NatLTFrame_validates_AxiomZ : NatLTFrame ⊧ (Axiom.Z (.atom 0)) := by
  intro V x hx₁ hx₂ y lt_xy;
  obtain ⟨z, lt_xz, hz⟩ := Satisfies.dia_def.mp hx₂;
  rcases lt_trichotomy y z with (lt_yz | rfl | lt_zy);
  . rcases or_not_of_imp (hx₁ y lt_xy) with _ | hy;
    . assumption;
    . exfalso;
      obtain ⟨⟨u, u_ioc⟩, hu₁, hu⟩ := @WellFounded.has_min (α := Finset.Ioc y z) (· > ·)
        (Finite.wellFounded_of_trans_of_irrefl _)
        ({ u | ¬Satisfies ⟨NatLTFrame, V⟩ u (.atom 0) })
        (by
          replace hy := Satisfies.box_def.not.mp hy;
          push_neg at hy;
          obtain ⟨u, lt_yu, hu⟩ := hy;
          refine ⟨⟨u, ?_⟩, ?_⟩;
          . apply Finset.mem_Ioc.mpr;
            constructor;
            . tauto;
            . by_contra hC;
              exact hu $ hz _ $ not_le.mp hC;
          . tauto;
        )
      have ⟨lt_yu, le_uz⟩ := Finset.mem_Ioc.mp u_ioc;
      have := not_imp_not.mpr (hx₁ u (lt_trans lt_xy lt_yu)) hu₁;
      replace this := Satisfies.box_def.not.mp this;
      push_neg at this;
      obtain ⟨v, lt_uv, hv⟩ := this;
      have := hu ⟨v, ?_⟩ hv;
      . contradiction;
      . by_contra hC;
        apply hv;
        apply hz;
        replace hC := Finset.mem_Ioc.not.mp hC;
        push_neg at hC;
        apply hC;
        exact lt_trans lt_yu lt_uv;
  . apply hx₁ <;> assumption;
  . apply hz;
    assumption;

end LO.Modal.Kripke
