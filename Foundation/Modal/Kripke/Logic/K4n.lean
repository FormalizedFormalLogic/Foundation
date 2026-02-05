module

public import Foundation.Modal.Kripke.AxiomFourN
public import Foundation.Modal.Kripke.Logic.KTc

@[expose] public section

namespace LO.Modal

open Kripke
open Modal.Kripke

namespace Kripke

abbrev Frame.IsK4n (F : Frame) (n) := F.IsWeakTransitive n

protected abbrev FrameClass.K4n (n : ℕ) : FrameClass := { F | F.IsK4n n }

end Kripke

variable {n m : ℕ}

namespace K4n

instance : Sound (Modal.K4n n) (FrameClass.K4n n) := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  intro F hF;
  exact validate_AxiomFourN_of_weakTransitive (weakTrans := hF);

instance : Entailment.Consistent (Modal.K4n n) :=
  consistent_of_sound_frameclass (FrameClass.K4n n) $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    induction n <;> simp [whitepoint];

instance : Canonical (Modal.K4n n) (FrameClass.K4n n) := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete (Modal.K4n n) (FrameClass.K4n n) := inferInstance


section

open LO.Entailment LO.Modal.Entailment
open Formula.Kripke
open Formula (atom)

abbrev counterframe (n : ℕ) : Kripke.Frame := ⟨Fin (n + 2), λ ⟨x, _⟩ ⟨y, _⟩ => y = min (x + 1) (n + 1)⟩

abbrev counterframe.last : counterframe n |>.World := ⟨n + 1, by omega⟩

lemma counterframe.iff_rel_from_zero {m : ℕ} {x : counterframe n} : (0 : counterframe n) ≺^[m] x ↔ x.1 = min m (n + 1) := by
  induction m generalizing x with
  | zero =>
    simp;
    tauto;
  | succ m ih =>
    constructor;
    . intro R0x;
      obtain ⟨u, R0u, Rux⟩ := Rel.Iterate.forward.mp R0x;
      rw [Rux, ih.mp R0u];
      simp;
    . rintro h;
      apply Rel.Iterate.forward.mpr;
      by_cases hm : m ≤ n + 1;
      . use ⟨m, by omega⟩;
        constructor;
        . apply ih.mpr; simpa;
        . simp_all;
      . use x;
        constructor;
        . apply ih.mpr; omega;
        . omega;

lemma counterframe.iff_rel_from {i j : counterframe n} {m : ℕ} : i ≺^[m] j ↔ j = min (i + m) (n + 1) := by
  induction m generalizing i j with
  | zero =>
    simp only [Rel.Iterate.iff_zero, add_zero]
    constructor;
    . rintro rfl; have := i.2; omega;
    . rintro h; have := j.2; omega;
  | succ m ih =>
    constructor;
    . intro Rij;
      obtain ⟨k, Rik, Rkj⟩ := Rel.Iterate.forward.mp Rij;
      have := @ih i k |>.mp Rik;
      omega;
    . rintro h;
      apply Rel.Iterate.forward.mpr;
      by_cases hm : (i + m) ≤ n + 1;
      . use ⟨i + m, by omega⟩;
        constructor;
        . apply ih.mpr; simpa;
        . omega;
      . use j;
        constructor;
        . apply ih.mpr;
          omega;
        . omega;

instance : Frame.IsWeakTransitive (counterframe n) (n + 1) := by
  constructor;
  intro x y;
  simp only [counterframe.iff_rel_from, le_add_iff_nonneg_left, zero_le, inf_of_le_right];
  omega;

instance : Modal.K ⪱ Modal.K4n n := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.FourN n (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨counterframe n, λ a w => w = n⟩;
      use M, 0;
      constructor;
      . simp;
      . apply Satisfies.not_imp_def.mpr;
        constructor;
        . apply Satisfies.boxItr_def.mpr;
          intro y R0y;
          simp [Semantics.Models, Satisfies, M, counterframe.iff_rel_from.mp R0y];
        . apply Satisfies.boxItr_def.not.mpr;
          push_neg;
          use ⟨(n + 1), by omega⟩;
          constructor;
          . apply counterframe.iff_rel_from.mpr; simp;
          . simp [Semantics.Models, Satisfies, M];

lemma succ_strictlyWeakerThan : Modal.K4n (n + 1) ⪱ Modal.K4n n := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl);
    . simp;
    . suffices Modal.K4n n ⊢ □□^[n](.atom 0) ➝ □□^[(n + 1)](.atom 0) by simpa [Axioms.FourN];
      apply imply_box_distribute'!;
      exact axiomFourN!;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.FourN n (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4n (n + 1))
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨counterframe n, λ a w => w ≠ counterframe.last⟩;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . apply Satisfies.not_imp_def.mpr;
        constructor;
        . apply Satisfies.boxItr_def.mpr;
          intro y R0y;
          replace R0y := counterframe.iff_rel_from_zero.mp R0y;
          simp only [Semantics.Models, Satisfies, counterframe.last, ne_eq, M];
          rintro rfl;
          simp at R0y;
        . apply Satisfies.boxItr_def.not.mpr;
          push_neg;
          use counterframe.last;
          constructor;
          . apply counterframe.iff_rel_from_zero.mpr;
            simp;
          . simp [Semantics.Models, Satisfies, M];

lemma add_strictlyWeakerThan {m : ℕ+} : Modal.K4n (n + m) ⪱ Modal.K4n n := by
  induction m with
  | one => apply succ_strictlyWeakerThan;
  | succ m ih =>
    trans Modal.K4n (n + m);
    . apply succ_strictlyWeakerThan;
    . apply ih;

lemma strictlyWeakerThan_of_lt (hnm : n < m) : Modal.K4n m ⪱ Modal.K4n n := by
  convert add_strictlyWeakerThan (n := n) (m := ⟨m - n, by omega⟩);
  simp;
  omega;

lemma not_equiv_of_ne (hnm : n ≠ m) : ¬(Modal.K4n n ≊ Modal.K4n m) := by
  wlog hnm : n < m;
  . have := @this m n (by omega) (by omega);
    contrapose! this;
    exact this.symm;
  by_contra!;
  apply strictlyWeakerThan_of_lt hnm |>.notWT;
  exact this.le;

instance : Infinite { L : Logic ℕ // Nonempty (L.IsNormal) ∧ Entailment.Consistent L } := Infinite.of_injective (λ n => ⟨Modal.K4n n, ⟨inferInstance⟩, inferInstance⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  intro h;
  apply Logic.iff_equal_provable_equiv.not.mpr;
  apply K4n.not_equiv_of_ne;
  assumption;

instance : Modal.K4n 0 ≊ Modal.KTc := by simp [show Modal.K4n 0 = Modal.KTc by rfl];
instance : Modal.K4n 1 ≊ Modal.K4 := by simp [show Modal.K4n 1 = Modal.K4 by rfl];

instance : Modal.K4n 1 ⪱ Modal.K4n 0 := strictlyWeakerThan_of_lt (by omega)
instance : Modal.K4n 2 ⪱ Modal.K4n 1 := strictlyWeakerThan_of_lt (by omega)
instance : Modal.K ⪱ Modal.K4n 2 := inferInstance

end

end K4n


end LO.Modal
end
