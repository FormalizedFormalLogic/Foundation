import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.AxiomMk
import Foundation.Modal.Logic.Basic
import Foundation.Vorspiel.List.Chain
import Foundation.Modal.Kripke.Hilbert

namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsKTMk (F : Frame) extends F.IsReflexive, F.SatisfiesMakinsonCondition

protected abbrev FrameClass.KTMk : FrameClass := { F | F.IsKTMk }

end Kripke



open Kripke
open Hilbert.Kripke


namespace Logic.KTMk.Kripke

instance : Sound (Hilbert.KTMk) Kripke.FrameClass.KTMk := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates
  constructor
  rintro _ (rfl | rfl) F ⟨_, _⟩
  . exact validate_AxiomT_of_reflexive
  . exact validate_axiomMk_of_satisfiesMakinsonCondition

instance : Entailment.Consistent (Hilbert.KTMk) := consistent_of_sound_frameclass Kripke.FrameClass.KTMk $ by
  use whitepoint
  constructor

instance : Canonical (Hilbert.KTMk) Kripke.FrameClass.KTMk := ⟨by constructor⟩

instance : Complete (Hilbert.KTMk) Kripke.FrameClass.KTMk := inferInstance


section

open Formula.Kripke
open Entailment

lemma validate_axiomFour_of_model_finitely {M : Kripke.Model} (hM : M ⊧* Modal.KTMk)
  : Finite M → ∀ φ : Formula ℕ, M ⊧ Axioms.Four φ := by
  contrapose!
  rintro ⟨φ, hφ⟩
  apply not_finite_iff_infinite.mpr
  apply List.Nodup.infinite_of_infinite
  have H : ∀ n : ℕ+, ∃ l : List M.World, l.Nodup ∧ l.length = n ∧ List.Chain' (· ≺ ·) l ∧ (∀ i : Fin l.length, l[i] ⊧ □^[(i + 1)]φ ⋏ ∼□^[(i + 2)]φ) := by
    intro n
    induction n with
    | one =>
      replace ⟨x₀, hφ⟩ := ValidOnModel.exists_world_of_not hφ
      use [x₀]
      simpa using hφ
    | succ n ih =>
      obtain ⟨l, hl_nodup, hl_len, hl_chain, hl⟩ := ih
      let m : Fin l.length := ⟨n - 1, by simp [hl_len]⟩
      have : l[m] ⊧ ◇(□^[(m + 2)]φ ⋏ ∼□^[(m + 3)]φ) := Satisfies.mdp ?_ $ hl m
      obtain ⟨y, Rmy, hy₂⟩ := Satisfies.dia_def.mp this
      let l' := l.concat y
      use l'
      have hl' : ∀ (i : Fin l'.length), l'[i] ⊧ □^[(i + 1)]φ ⋏ ∼□^[(i + 2)]φ := by
        rintro ⟨i, hi'⟩
        replace hi : i < l.length ∨ i = l.length := by
          simp [l'] at hi'
          omega
        rcases hi with (hi | rfl)
        . let i : Fin (l.length) := ⟨i, by omega⟩
          generalize ei' : (⟨i, hi'⟩ : Fin l'.length) = i'
          simpa [
            show l[i] = l'[i'] by simp [←ei', l'],
            show □^[(i + 1)]φ = □^[(i' + 1)]φ by simp [←ei'],
            show ∼□^[(i + 2)]φ = ∼□^[(i' + 2)]φ by simp [←ei']
          ] using @hl i
        . simpa [l', hl_len, m] using hy₂
      refine ⟨?_, by simpa [l'], ?_, hl'⟩
      . apply List.nodup_iff_get_ne_get.mpr
        rintro ⟨i, hi⟩ ⟨j, hj⟩ hij eij
        replace hij : i < j := hij
        apply Satisfies.not_def.mp $ Satisfies.and_def.mp (hl' ⟨i, hi⟩) |>.2
        apply Satisfies.mdp ?_ $ eij ▸ Satisfies.and_def.mp (hl' ⟨j, hj⟩) |>.1
        apply hM.realize
        simp only [Entailment.theory, Set.mem_setOf_eq]
        obtain ⟨c, hc, rfl⟩ := lt_iff_exists_add.mp hij
        match c with
        | 0 => contradiction
        | n + 1 =>
          suffices Hilbert.KTMk ⊢! □^[((i + 2) + n)]φ ➝ □^[(i + 2)]φ by
            rwa [show (i + (n + 1) + 1) = (i + 2 + n) by omega]
          apply reduce_box_in_CAnt!
      . apply List.chain'_concat_of_not_nil (List.length_pos_iff_ne_nil.mp (by simp [hl_len])) |>.mpr
        constructor
        . assumption
        . convert Rmy
          trans l[l.length - 1]'(by simp [hl_len])
          . apply List.getLast_eq_getElem
          . simp [m, hl_len]
      . intro h
        have : l[m] ⊧ □^[(m + 1)]φ ⋏ ∼□^[(m + 2)]φ ➝ ◇(□^[(m + 2)]φ ⋏ ◇(∼□^[(m + 2)]φ)) := by
          apply hM.realize
          simp only [Entailment.theory, Set.mem_setOf_eq]
          simp
        replace : l[m] ⊧ ◇(□^[(m + 2)]φ ⋏ ◇(∼□^[(m + 2)]φ)) := this h
        obtain ⟨y, hy₁, hy₂⟩ := Satisfies.dia_def.mp this
        apply Satisfies.dia_def.mpr
        use y
        constructor
        . assumption
        . apply Satisfies.and_def.mpr
          constructor
          . exact Satisfies.and_def.mp hy₂ |>.1
          . apply Satisfies.not_def.mpr
            simpa using Satisfies.box_dn.not.mp $ Satisfies.not_def.mp $ Satisfies.dia_dual.mp $ Satisfies.and_def.mp hy₂ |>.2
  apply Infinite.of_injective (β := ℕ+) (λ n => ⟨H n |>.choose, H n |>.choose_spec.1⟩)
  intro i j
  simp only [Subtype.mk.injEq]
  contrapose!
  suffices i ≠ j → (H i).choose.length ≠ (H j).choose.length by tauto
  rw [H i |>.choose_spec.2.1, H j |>.choose_spec.2.1]
  simp

lemma model_infinitity_of_not_validate_axiomFour {M : Kripke.Model} (hM : M ⊧* Hilbert.KTMk.logic)
  : (∃ φ : Formula ℕ, ¬M ⊧ Axioms.Four φ) → Infinite M := by
  contrapose!
  intro h
  apply validate_axiomFour_of_model_finitely hM
  simpa using h

abbrev recessionFrame : Kripke.Frame where
  World := ℕ
  Rel i j := i ≤ j + 1


namespace recessionFrame

instance : recessionFrame.IsKTMk where
  refl := by tauto
  makinson := by
    intro i
    use i + 1
    refine ⟨by omega, by omega, by simp_all; omega⟩

lemma not_transitive : ¬recessionFrame.IsTransitive := by
  by_contra h_trans
  have := @Frame.trans recessionFrame _ 2 1 0
  omega

lemma exists_not_validate_axiomFour : ∃ φ : Formula ℕ, ¬recessionFrame ⊧ Axioms.Four φ := by
  use (.atom 0)
  exact not_imp_not.mpr transitive_of_validate_AxiomFour not_transitive

end recessionFrame

lemma exists_not_provable_axiomFour : ∃ φ : Formula ℕ, Hilbert.KTMk ⊬ Axioms.Four φ := by
  obtain ⟨φ, hφ⟩ := recessionFrame.exists_not_validate_axiomFour
  use! φ
  apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.KTMk)
  apply iff_not_validOnFrameClass_exists_frame.mpr
  use recessionFrame
  constructor
  . apply Set.mem_setOf_eq.mpr
    infer_instance
  . assumption

lemma no_finite_model_property : ¬(∀ φ, Hilbert.KTMk ⊬ φ → ∃ M : Kripke.Model, Finite M ∧ M ⊧* Hilbert.KTMk.logic ∧ ¬M ⊧ φ)  := by
  by_contra! hC
  obtain ⟨φ, hφ⟩ := exists_not_provable_axiomFour
  obtain ⟨M, hM₁, hM₂, hM₃⟩ := @hC (Axioms.Four φ) hφ
  apply not_finite_iff_infinite.mpr $ @model_infinitity_of_not_validate_axiomFour M ?_ ⟨φ, hM₃⟩
  . assumption
  . assumption

example : ∃ φ, Hilbert.KTMk ⊬ φ ∧ (∀ M : Kripke.Model, Finite M → M ⊧* Hilbert.KTMk.logic → M ⊧ φ) := by
  simpa using no_finite_model_property

end

end Logic.KTMk.Kripke



namespace Logic

open Formula
open Entailment
open Kripke

instance : Hilbert.KT ⪱ Hilbert.KTMk := by
  constructor
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; simp
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.Mk (.atom 0) (.atom 1))
    constructor
    . exact axiomMk!
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.KT)
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      use ⟨⟨Fin 3, λ x y => x = y ∨ x + 1 = y⟩, λ w a => match a with | 0 => w ≠ 2 | 1 => w = 0 | _ => True⟩, 0
      constructor
      . exact { refl := by omega; }
      . suffices ∀ (x : Fin 3), 0 = x ∨ 1 = x → (∀ y, x = y ∨ x + 1 = y → ∀ z, y = z ∨ y + 1 = z → z ≠ 2) → x ≠ 0 ∧ x + 1 ≠ 0 by
          simpa [Frame.Rel', Satisfies, Semantics.Realize]
        rintro x (rfl | rfl)
        . intro h
          exfalso
          have : (1 : Fin 3) ≠ 2 := h 0 (by omega) 1 (by omega)
          tauto
        . omega

instance : Hilbert.KTMk ⪱ Hilbert.S4 := by
  constructor
  . apply Hilbert.Normal.weakerThan_of_provable_axioms
    intro φ hφ
    rcases hφ with (rfl | rfl | rfl)
    . simp
    . simp
    . apply Complete.complete (𝓢 := Hilbert.S4) (𝓜 := FrameClass.S4)
      intro F hF V x hx
      replace hF := Set.mem_setOf_eq.mp hF
      replace ⟨hx₁, hx₂⟩ := Satisfies.and_def.mp hx
      apply Satisfies.dia_def.mpr
      use x
      constructor
      . apply F.refl
      . apply Satisfies.and_def.mpr
        constructor
        . intro y Rxy z Ryz
          apply hx₁
          exact F.trans Rxy Ryz
        . apply Satisfies.dia_def.mpr
          use x
          constructor
          . apply F.refl
          . assumption
  . apply Entailment.not_weakerThan_iff.mpr
    obtain ⟨φ, hφ⟩ := Logic.KTMk.Kripke.exists_not_provable_axiomFour
    use Axioms.Four φ
    constructor
    . simp
    . assumption

end Logic

instance : Modal.KT ⪱ Modal.KTMk := inferInstance

instance : Modal.KTMk ⪱ Modal.S4 := inferInstance

end LO.Modal
