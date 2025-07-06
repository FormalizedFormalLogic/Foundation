import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomFourN
import Foundation.Modal.Kripke.Filtration
import Foundation.Vorspiel.Fin.Supplemental
import Foundation.Modal.Logic.Extension

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Kripke

protected abbrev FrameClass.K4n (n : ℕ+) : FrameClass := { F | F.IsWeakTransitive n }

end Kripke

namespace Hilbert

variable {n : ℕ+}

namespace K4n.Kripke

instance : Sound (Logic.K4n n) (FrameClass.K4n n) := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_trans φ rfl;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;
  apply validate_AxiomFourN_of_weakTransitive;

instance : Entailment.Consistent (Logic.K4n n) :=
  consistent_of_sound_frameclass (FrameClass.K4n n) $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    induction n <;>
    . simp [whitepoint];

instance : Canonical (Logic.K4n n) (FrameClass.K4n n) := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete (Logic.K4n n) (FrameClass.K4n n) := inferInstance

end K4n.Kripke


end Hilbert


namespace Logic

open Formula
open Entailment
open Kripke

namespace K4n

lemma Kripke.eq_K4n_logic (n : ℕ+) : Logic.K4n n = (Kripke.FrameClass.K4n n).logic := eq_hilbert_logic_frameClass_logic

lemma eq_K4_K4n_one : Logic.K4n 1 = Logic.K4 := rfl


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
      obtain ⟨u, R0u, Rux⟩ := HRel.iterate.forward.mp R0x;
      have := ih.mp R0u;
      simp_all;
    . rintro h;
      apply HRel.iterate.forward.mpr;
      by_cases hm : m ≤ n + 1;
      . use ⟨m, by omega⟩;
        constructor;
        . apply ih.mpr;
          simpa;
        . simp_all;
      . use x;
        constructor;
        . apply ih.mpr;
          omega;
        . omega;

@[simp]
lemma counterframe.refl_last : (last : counterframe n) ≺ last := by simp [Frame.Rel'];

instance : Frame.IsWeakTransitive (counterframe n) (n + 1) := by
  constructor;
  intro x y Rxy;
  by_cases ey : y = counterframe.last;
  . subst ey;
    sorry;
  . sorry;

instance succ_strictlyWeakerThan : Logic.K4n (n + 1) ⪱ Logic.K4n n := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms;
    rintro φ (rfl | rfl);
    . simp;
    . suffices (Hilbert.K4n n).logic ⊢! □□^[n](.atom 0) ➝ □□^[(n + 1)](.atom 0) by
        simpa [Axioms.FourN, PNat.add_coe, PNat.val_ofNat, Box.multibox_succ];
      apply imply_box_distribute'!;
      exact axiomFourN!;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.FourN n (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4n (n + 1))
      apply not_validOnFrameClass_of_exists_frame;
      use (counterframe n);
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . apply ValidOnFrame.not_of_exists_valuation_world;
        use (λ w a => w ≠ counterframe.last), 0;
        apply Satisfies.not_imp_def.mpr;
        constructor;
        . apply Satisfies.multibox_def.mpr;
          intro y R0y;
          replace R0y := counterframe.iff_rel_from_zero.mp R0y;
          simp only [Semantics.Realize, Satisfies, counterframe.last, ne_eq];
          aesop;
        . apply Satisfies.multibox_def.not.mpr;
          push_neg;
          use counterframe.last;
          constructor;
          . apply counterframe.iff_rel_from_zero.mpr;
            simp;
          . simp [Semantics.Realize, Satisfies];

instance add_strictlyWeakerThan : Logic.K4n (n + m) ⪱ Logic.K4n n := by
  induction m with
  | one => infer_instance;
  | succ m ih =>
    trans Logic.K4n (n + m);
    . rw [(show n + (m + 1) = n + m + 1 by rfl)];
      infer_instance;
    . apply ih;

instance strictlyWeakerThan_of_lt (hnm : n < m) : Logic.K4n m ⪱ Logic.K4n n := by
  convert add_strictlyWeakerThan (n := n) (m := m - n);
  exact PNat.add_sub_of_lt hnm |>.symm;

instance not_equiv_of_ne (hnm : n ≠ m) : ¬(Logic.K4n n ≊ Logic.K4n m) := by
  rcases lt_trichotomy n m with h | rfl | h;
  . by_contra!;
    apply strictlyWeakerThan_of_lt h |>.notWT;
    exact this.le;
  . contradiction;
  . by_contra!;
    apply strictlyWeakerThan_of_lt h |>.notWT;
    exact this.symm.le;

end K4n

instance : Infinite { L : Logic ℕ // Entailment.Consistent L } := Infinite.of_injective (β := ℕ+) (λ n => ⟨Logic.K4n n, inferInstance⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  intro h;
  apply Logic.iff_equal_provable_equiv.not.mpr;
  apply K4n.not_equiv_of_ne h;

end Logic

end LO.Modal
