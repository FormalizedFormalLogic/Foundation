import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomFourN
import Foundation.Modal.Kripke.Filtration
import Foundation.Vorspiel.Fin.Supplemental
import Foundation.Modal.Logic.Extension

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Kripke

abbrev Frame.IsK4n (F : Frame) (n) := F.IsWeakTransitive n

protected abbrev FrameClass.K4n (n : ℕ+) : FrameClass := { F | F.IsK4n n }

end Kripke

namespace Hilbert

variable {n : ℕ+}

namespace K4n.Kripke

instance : Sound (Hilbert.K4n n) (FrameClass.K4n n) := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  intro F hF;
  exact validate_AxiomFourN_of_weakTransitive (weakTrans := hF);

instance : Entailment.Consistent (Hilbert.K4n n) :=
  consistent_of_sound_frameclass (FrameClass.K4n n) $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    induction n <;> simp [whitepoint];

instance : Canonical (Hilbert.K4n n) (FrameClass.K4n n) := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete (Modal.K4n n) (FrameClass.K4n n) := inferInstance

end K4n.Kripke

namespace K4nInfiniteChain

open LO.Entailment LO.Modal.Entailment
open Formula.Kripke

variable {n m : ℕ+}

abbrev counterframe (n : ℕ+) : Kripke.Frame := ⟨Fin (n + 2), λ ⟨x, _⟩ ⟨y, _⟩ => y = min (x + 1) (n + 1)⟩

abbrev counterframe.last : counterframe n |>.World := ⟨n + 1, by omega⟩

lemma counterframe.iff_rel_from_zero {m : ℕ} {x : counterframe n} : (0 : counterframe n) ≺^[m] x ↔ x.1 = min m (n + 1) := by
  induction m generalizing x with
  | zero =>
    simp;
    tauto;
  | succ m ih =>
    constructor;
    . intro R0x;
      obtain ⟨u, R0u, Rux⟩ := HRel.Iterate.forward.mp R0x;
      rw [Rux, ih.mp R0u];
      simp;
    . rintro h;
      apply HRel.Iterate.forward.mpr;
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
    simp only [HRel.Iterate.iff_zero, add_zero]
    constructor;
    . rintro rfl; have := i.2; omega;
    . rintro h; have := j.2; omega;
  | succ m ih =>
    constructor;
    . intro Rij;
      obtain ⟨k, Rik, Rkj⟩ := HRel.Iterate.forward.mp Rij;
      have := @ih i k |>.mp Rik;
      omega;
    . rintro h;
      apply HRel.Iterate.forward.mpr;
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
  simp only [counterframe.iff_rel_from, PNat.add_coe, PNat.val_ofNat, le_add_iff_nonneg_left, zero_le, inf_of_le_right];
  omega;

instance succ_strictlyWeakerThan : Hilbert.K4n (n + 1) ⪱ Hilbert.K4n n := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl);
    . simp;
    . suffices Hilbert.K4n n ⊢! □□^[n](.atom 0) ➝ □□^[(n + 1)](.atom 0) by simpa [Axioms.FourN];
      apply imply_box_distribute'!;
      exact axiomFourN!;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.FourN n (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4n (n + 1))
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨counterframe n, λ w a => w ≠ counterframe.last⟩;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . apply Satisfies.not_imp_def.mpr;
        constructor;
        . apply Satisfies.multibox_def.mpr;
          intro y R0y;
          replace R0y := counterframe.iff_rel_from_zero.mp R0y;
          simp only [Semantics.Realize, Satisfies, counterframe.last, ne_eq, M];
          rintro rfl;
          simp at R0y;
        . apply Satisfies.multibox_def.not.mpr;
          push_neg;
          use counterframe.last;
          constructor;
          . apply counterframe.iff_rel_from_zero.mpr;
            simp;
          . simp [Semantics.Realize, Satisfies, M];

instance add_strictlyWeakerThan : Hilbert.K4n (n + m) ⪱ Hilbert.K4n n := by
  induction m with
  | one => infer_instance;
  | succ m ih =>
    trans Hilbert.K4n (n + m);
    . rw [(show n + (m + 1) = n + m + 1 by rfl)];
      infer_instance;
    . apply ih;

instance strictlyWeakerThan_of_lt (hnm : n < m) : Hilbert.K4n m ⪱ Hilbert.K4n n := by
  convert add_strictlyWeakerThan (n := n) (m := m - n);
  exact PNat.add_sub_of_lt hnm |>.symm;

instance not_equiv_of_ne (hnm : n ≠ m) : ¬(Hilbert.K4n n ≊ Hilbert.K4n m) := by
  rcases lt_trichotomy n m with h | rfl | h;
  . by_contra!;
    apply strictlyWeakerThan_of_lt h |>.notWT;
    exact this.le;
  . contradiction;
  . by_contra!;
    apply strictlyWeakerThan_of_lt h |>.notWT;
    exact this.symm.le;

end K4nInfiniteChain

end Hilbert

instance K4n.strictlyWeakerThan (hnm : n < m) : Modal.K4n m ⪱ Modal.K4n n := by
  have := Hilbert.K4nInfiniteChain.strictlyWeakerThan_of_lt hnm;
  grind;

instance K4n.not_equiv (hnm : n ≠ m) : ¬(Modal.K4n n ≊ Modal.K4n m) := by
  have := Hilbert.K4nInfiniteChain.not_equiv_of_ne hnm;
  grind;

instance infinite_consistent_logics : Infinite { L : Logic ℕ // Entailment.Consistent L } := Infinite.of_injective (β := ℕ+) (λ n => ⟨Modal.K4n n, inferInstance⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  intro h;
  apply Logic.iff_equal_provable_equiv.not.mpr;
  apply K4n.not_equiv;
  assumption;

end LO.Modal
