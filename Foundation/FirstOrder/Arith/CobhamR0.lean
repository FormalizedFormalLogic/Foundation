import Foundation.FirstOrder.Arith.Model
import Foundation.Vorspiel.ExistsUnique
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Nat.Cast.Order.Basic

noncomputable section

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐑₀]

open Language ORingStruc

lemma numeral_add_numeral (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m) := by
  simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₁ n m) (fun _ ↦ 0)

lemma numeral_mul_numeral (n m : ℕ) : (numeral n : M) * numeral m = numeral (n * m) := by
  simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₂ n m) (fun _ ↦ 0)

lemma numeral_ne_numeral_of_ne {n m : ℕ} (h : n ≠ m) : (numeral n : M) ≠ numeral m := by
  simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₃ n m h) (fun _ ↦ 0)

lemma lt_numeral_iff {x : M} {n : ℕ} : x < numeral n ↔ ∃ i : Fin n, x = numeral i := by
  have := by simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₄ n) (fun _ ↦ 0)
  constructor
  · intro hx
    rcases (this x).mp hx with ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact (this (numeral i)).mpr ⟨i, by simp, rfl⟩

@[simp] lemma numeral_inj_iff {n m : ℕ} : (numeral n : M) = numeral m ↔ n = m :=
  ⟨by contrapose; exact numeral_ne_numeral_of_ne, by rintro rfl; rfl⟩

@[simp] lemma numeral_lt_numeral_iff : (numeral n : M) < numeral m ↔ n < m :=
  ⟨by contrapose
      intro h H
      rcases lt_numeral_iff.mp H with ⟨i, hi⟩
      rcases numeral_inj_iff.mp hi
      exact (lt_self_iff_false m).mp (lt_of_le_of_lt (Nat.le_of_not_lt h) i.prop),
   fun h ↦ lt_numeral_iff.mpr ⟨⟨n, h⟩, by simp⟩⟩

open Hierarchy

lemma val_numeral {n} : ∀ (t : Semiterm ℒₒᵣ ξ n),
    ∀ v f, Semiterm.valm M (fun x ↦ numeral (v x)) (fun x ↦ numeral (f x)) t = numeral (Semiterm.valm ℕ v f t)
  | #_,                                 _, _ => by simp
  | &x,                                 _, _ => by simp
  | Semiterm.func Language.Zero.zero _, e, f => by simp
  | Semiterm.func Language.One.one _,   e, f => by simp
  | Semiterm.func Language.Add.add v,   e, f => by simp [Semiterm.val_func, val_numeral (v 0), val_numeral (v 1), numeral_add_numeral]
  | Semiterm.func Language.Mul.mul v,   e, f => by simp [Semiterm.val_func, val_numeral (v 0), val_numeral (v 1), numeral_mul_numeral]

lemma bold_sigma_one_completeness {n} {φ : Semiformula ℒₒᵣ ξ n} (hp : Hierarchy 𝚺 1 φ) {e f} :
    Semiformula.Evalm ℕ e f φ → Semiformula.Evalm M (fun x ↦ numeral (e x)) (fun x ↦ numeral (f x)) φ := by
  revert e
  apply sigma₁_induction' hp
  case hVerum => simp
  case hFalsum => simp
  case hEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hNEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hLT => intro n t₁ t₂ e; simp [val_numeral, Nat.cast_lt]
  case hNLT => intro n t₁ t₂ e; simp [val_numeral]
  case hAnd =>
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, and_imp]
    intro n φ ψ _ _ ihp ihq e hp hq
    exact ⟨ihp hp, ihq hq⟩
  case hOr =>
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rintro n φ ψ _ _ ihp ihq e (hp | hq)
    · left; exact ihp hp
    · right; exact ihq hq
  case hBall =>
    simp only [Semiformula.eval_ball, Nat.succ_eq_add_one, Semiformula.eval_operator₂,
      Semiterm.val_bvar, Matrix.cons_val_zero, Semiterm.val_bShift, Structure.LT.lt, val_numeral]
    intro n t φ _ ihp e hp x hx
    rcases lt_numeral_iff.mp hx with ⟨x, rfl⟩
    simpa [Matrix.comp_vecCons'] using ihp (hp x (by simp))
  case hEx =>
    simp only [Semiformula.eval_ex, Nat.succ_eq_add_one, forall_exists_index]
    intro n φ _ ihp e x hp
    exact ⟨numeral x, by simpa [Matrix.comp_vecCons'] using ihp hp⟩

lemma sigma_one_completeness {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ₀ σ → M ⊧ₘ₀ σ := by
  simp [models₀_iff]; intro h
  simpa [Matrix.empty_eq, Empty.eq_elim] using bold_sigma_one_completeness hσ h

end Arith

namespace FirstOrder.Arith

open LO.Arith

variable {T : Theory ℒₒᵣ} [𝐑₀ ≼ T]

theorem sigma_one_completeness {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ₀ σ → T ⊢! ↑σ := fun H =>
  haveI : 𝐄𝐐 ≼ T := System.Subtheory.comp (𝓣 := 𝐑₀) inferInstance inferInstance
  complete <| oRing_consequence_of.{0} _ _ <| fun M _ _ => by
    haveI : M ⊧ₘ* 𝐑₀ := ModelsTheory.of_provably_subtheory M 𝐑₀ T inferInstance (by assumption)
    exact LO.Arith.sigma_one_completeness hσ H

theorem sigma_one_completeness_iff [ss : Sigma1Sound T] {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ₀ σ ↔ T ⊢! ↑σ :=
  haveI : 𝐑₀ ≼ T := System.Subtheory.comp (𝓣 := T) inferInstance inferInstance
  ⟨fun h ↦ sigma_one_completeness (T := T) hσ h, fun h ↦ ss.sound (by simp [hσ]) h⟩

end FirstOrder.Arith

end LO

end
