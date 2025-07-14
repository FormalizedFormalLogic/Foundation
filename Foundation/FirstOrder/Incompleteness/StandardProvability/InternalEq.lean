import Foundation.Meta.ClProver
import Foundation.FirstOrder.ISigma1.Ind
import Foundation.FirstOrder.ISigma1.Metamath
import Foundation.FirstOrder.Incompleteness.StandardProvability.D1

/-!

# Formalized Theory $\mathsf{R_0}$

-/

open Classical

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

namespace InternalArithmetic

local prefix:max "#'" => Semiterm.bvar (V := V) (L := ℒₒᵣ)

local prefix:max "&'" => Semiterm.fvar (V := V) (L := ℒₒᵣ)

noncomputable abbrev num (n : V) : Semiterm V ℒₒᵣ k := typedNumeral n

scoped postfix:max "⇞" => Semiterm.shift

scoped postfix:max "⤉" => Semiformula.shift

variable (T : ArithmeticTheory) [Theory.Δ₁Definable T] [𝐏𝐀⁻ ⪯ T]

namespace TProof

open Entailment Entailment.FiniteContext Semiformula

section InternalR₀Theory

instance : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (inferInstanceAs (𝐄𝐐 ⪯ 𝐏𝐀⁻)) inferInstance

@[simp] lemma eq_refl (t : Term V ℒₒᵣ) : T.internalize V ⊢! t ≐ t := by
  have : T ⊢! (“∀ x, x = x” : SyntacticFormula ℒₒᵣ) := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by simp [models_iff]
  have : T.internalize V ⊢! ∀' (#'0 ≐ #'0) := by
    simpa using internal_provable_of_outer_provable_arith this
  simpa using TProof.specialize! this t

@[simp] lemma eq_symm (t u : Term V ℒₒᵣ) : T.internalize V ⊢! (t ≐ u) ➝ (u ≐ t) := by
  have : T ⊢! “∀ x y, x = y → y = x” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by simp [models_iff]
  have : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (#'0 ≐ #'1)) := by
    simpa using internal_provable_of_outer_provable_arith this
  simpa using TProof.specialize₂! this u t

variable {T}

lemma eq_comm_ctx {t u : Term V ℒₒᵣ} :
    Γ ⊢[T.internalize V]! t ≐ u → Γ ⊢[T.internalize V]! u ≐ t := fun b ↦
  of'! (eq_symm T t u) ⨀ b

variable (T)

lemma subst_eq (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ ≐ u₁) ➝ (t₂ ≐ u₂) := by
  have : T ⊢! “∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → x₁ = y₁ → x₂ = y₂” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by simp [models_iff]
  have := by simpa using internal_provable_of_outer_provable_arith this (V := V)
  simpa using TProof.specialize₄! this u₂ u₁ t₂ t₁

lemma subst_lt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ <' u₁) ➝ (t₂ <' u₂) := by
  have : T ⊢! “∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → x₁ < y₁ → x₂ < y₂” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff] using fun a b c e h ↦ e ▸ h
  have := by simpa using internal_provable_of_outer_provable_arith this (V := V)
  simpa using TProof.specialize₄! this u₂ u₁ t₂ t₁

lemma subst_ne (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ ≉ u₁) ➝ (t₂ ≉ u₂) := by
  have : T ⊢! “∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → x₁ ≠ y₁ → x₂ ≠ y₂” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff] using fun a b c e h ↦ e ▸ h
  have := by simpa using internal_provable_of_outer_provable_arith this (V := V)
  simpa using TProof.specialize₄! this u₂ u₁ t₂ t₁

lemma subst_nlt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ ≮' u₁) ➝ (t₂ ≮' u₂) := by
  have : T ⊢! “∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → x₁ ≮ y₁ → x₂ ≮ y₂” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff] using fun a b c e h ↦ e ▸ h
  have := by simpa using internal_provable_of_outer_provable_arith this (V := V)
  simpa using TProof.specialize₄! this u₂ u₁ t₂ t₁

lemma subst_add_eq_add (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ + u₁ ≐ t₂ + u₂) := by
  have : T ⊢! “∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → x₁ + y₁ = x₂ + y₂” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff] using fun a b c e ↦ by simp [e]
  have := by simpa using internal_provable_of_outer_provable_arith this (V := V)
  simpa using TProof.specialize₄! this u₂ u₁ t₂ t₁

lemma subst_mul_eq_mul (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! (t₁ ≐ t₂) ➝ (u₁ ≐ u₂) ➝ (t₁ * u₁ ≐ t₂ * u₂) := by
  have : T ⊢! “∀ x₁ x₂ y₁ y₂, x₁ = x₂ → y₁ = y₂ → x₁ * y₁ = x₂ * y₂” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff] using fun a b c e ↦ by simp [e]
  have := by simpa using internal_provable_of_outer_provable_arith this (V := V)
  simpa using TProof.specialize₄! this u₂ u₁ t₂ t₁


lemma vec2_eq {v : V} (h : len v = 2) : ?[v.[0], v.[1]] = v :=
  nth_ext' 2 (by simp [one_add_one_eq_two]) h (by
    intro i hi
    have : i = 0 ∨ i = 1 := le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi)
    rcases this with (rfl | rfl) <;> simp)

set_option pp.rawOnError true

lemma term_replace_aux (t : V) :
    IsSemiterm ℒₒᵣ 1 t →
    T.Provable (^∀ ^∀ imp ℒₒᵣ (^#1 ^= ^#0) (termSubst ℒₒᵣ (^#1 ∷ 0) t ^= termSubst ℒₒᵣ (^#0 ∷ 0) t)) := by
  apply IsSemiterm.sigma1_induction
  · definability
  case hfunc =>
    intro k F v hF hv ih
    rcases isFunc_iff_LOR.mp hF with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rcases show v = 0 by simpa using hv
      suffices
          T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ((typedNumeral 0).substs ![#'1] ≐ (typedNumeral 0).substs ![#'0])) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        simpa [-subst_numeral, val_all, InternalArithmetic.coe_zero_eq] using this
      suffices
        T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (typedNumeral 0 ≐ typedNumeral 0)) by simpa
      suffices T.internalize V ⊢! (&'1 ≐ &'0) ➝ (typedNumeral 0 ≐ typedNumeral 0) by
        apply TProof.all₂!; simpa [Semiformula.free]
      apply dhyp! (eq_refl _ _)
    · rcases show v = 0 by simpa using hv
      suffices
          T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ((typedNumeral 1).substs ![#'1] ≐ (typedNumeral 1).substs ![#'0])) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        simpa [-subst_numeral, val_all, InternalArithmetic.coe_one_eq] using this
      suffices
        T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (typedNumeral 1 ≐ typedNumeral 1)) by simpa
      suffices T.internalize V ⊢! (&'1 ≐ &'0) ➝ (typedNumeral 1 ≐ typedNumeral 1) by
        apply TProof.all₂!; simpa [Semiformula.free]
      apply dhyp! (eq_refl _ _)
    · let t : Semiterm V ℒₒᵣ 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V ℒₒᵣ 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices
          T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ((t + u).substs ![#'1] ≐ (t + u).substs ![#'0])) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        rw [veq]
        simpa [-subst_add, val_all] using this
      let Γ : List (Formula V ℒₒᵣ) := [&'1 ≐ &'0]
      suffices
          Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] + u⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0] + u⇞⇞.substs ![&'0] by
        apply TProof.all₂!; simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
      have iht : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t.substs ![#'1] ≐ t.substs ![#'0])) := by
        apply (internalize_TProvable_iff_provable (T := T)).mpr
        simpa [t] using ih 0 (by simp)
      have ihu : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (u.substs ![#'1] ≐ u.substs ![#'0])) := by
        apply (internalize_TProvable_iff_provable (T := T)).mpr
        simpa [u] using ih 1 (by simp)
      have iht : Γ ⊢[T.internalize V]! (t⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0]) := by
        have := TProof.specialize₂_shift! iht &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using this
      have ihu : Γ ⊢[T.internalize V]! (u⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'0]) := by
        have := TProof.specialize₂_shift! ihu &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using this
      have := subst_add_eq_add T (t⇞⇞.substs ![&'1]) (t⇞⇞.substs ![&'0])
        (u⇞⇞.substs ![&'1]) (u⇞⇞.substs ![&'0])
      exact of'! this ⨀ iht ⨀ ihu
    · let t : Semiterm V ℒₒᵣ 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V ℒₒᵣ 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices
          T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ((t * u).substs ![#'1] ≐ (t * u).substs ![#'0])) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        rw [veq]
        simpa [-subst_mul, val_all] using this
      let Γ : List (Formula V ℒₒᵣ) := [&'1 ≐ &'0]
      suffices
          Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] * u⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0] * u⇞⇞.substs ![&'0] by
        apply TProof.all₂!; simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
      have iht : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t.substs ![#'1] ≐ t.substs ![#'0])) := by
        apply (internalize_TProvable_iff_provable (T := T)).mpr
        simpa [t] using ih 0 (by simp)
      have ihu : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (u.substs ![#'1] ≐ u.substs ![#'0])) := by
        apply (internalize_TProvable_iff_provable (T := T)).mpr
        simpa [u] using ih 1 (by simp)
      have iht : Γ ⊢[T.internalize V]! (t⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0]) := by
        have := TProof.specialize₂_shift! iht &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using this
      have ihu : Γ ⊢[T.internalize V]! (u⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'0]) := by
        have := TProof.specialize₂_shift! ihu &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using this
      have := subst_mul_eq_mul T (t⇞⇞.substs ![&'1]) (t⇞⇞.substs ![&'0])
        (u⇞⇞.substs ![&'1]) (u⇞⇞.substs ![&'0])
      exact of'! this ⨀ iht ⨀ ihu
  case hbvar =>
    intro z hz
    have : z = 0 := lt_one_iff_eq_zero.mp hz
    rcases this with rfl
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (#'1 ≐ #'0)) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa [-substs_equals, val_all] using this
    have : T ⊢! “∀ x y, (x = y → x = y)” := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by simp [models_iff]
    simpa using internal_provable_of_outer_provable_arith this (V := V)
  case hfvar =>
    intro x
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (&'x ≐ &'x)) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa [-substs_equals, val_all] using this
    suffices T.internalize V ⊢! (&'1 ≐ &'0) ➝ (&'(x + 1 + 1) ≐ &'(x + 1 + 1)) by
      apply TProof.all₂!; simpa [Semiformula.free]
    apply dhyp! (eq_refl T _)

lemma term_replace (t : Semiterm V ℒₒᵣ 1) :
    T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t.substs ![#'1] ≐ t.substs ![#'0])) := by
  apply (internalize_TProvable_iff_provable (T := T)).mpr
  simpa using term_replace_aux T t.val

lemma term_replace' (t : Semiterm V ℒₒᵣ 1) (u₁ u₂ : Term V ℒₒᵣ) :
    T.internalize V ⊢! (u₁ ≐ u₂) ➝ (t.substs ![u₁] ≐ t.substs ![u₂]) := by
  have := TProof.specialize₂! (term_replace T t) u₂ u₁
  simpa [Semiterm.substs_substs] using this

lemma replace_eq (t u : Semiterm V ℒₒᵣ 1) :
    T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t ≐ u).substs ![#'1] ➝ (t ≐ u).substs ![#'0]) := by
  suffices
      T.internalize V ⊢!
        (&'1 ≐ &'0) ➝
        (t⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'1]) ➝
        (t⇞⇞.substs ![&'0] ≐ u⇞⇞.substs ![&'0]) by
    apply TProof.all₂!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V ℒₒᵣ) := [t⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'1], &'1 ≐ &'0]
  suffices
      Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'0] ≐ u⇞⇞.substs ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V]! u⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_eq T (t⇞⇞.substs ![&'1]) (t⇞⇞.substs ![&'0])
      (u⇞⇞.substs ![&'1]) (u⇞⇞.substs ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_lt (t u : Semiterm V ℒₒᵣ 1) :
    T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t <' u).substs ![#'1] ➝ (t <' u).substs ![#'0]) := by
  suffices
      T.internalize V ⊢!
        (&'1 ≐ &'0) ➝
        (t⇞⇞.substs ![&'1] <' u⇞⇞.substs ![&'1]) ➝
        (t⇞⇞.substs ![&'0] <' u⇞⇞.substs ![&'0]) by
    apply TProof.all₂!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V ℒₒᵣ) := [t⇞⇞.substs ![&'1] <' u⇞⇞.substs ![&'1], &'1 ≐ &'0]
  suffices
      Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'0] <' u⇞⇞.substs ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] <' u⇞⇞.substs ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V]! u⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_lt T (t⇞⇞.substs ![&'1]) (t⇞⇞.substs ![&'0])
      (u⇞⇞.substs ![&'1]) (u⇞⇞.substs ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_ne (t u : Semiterm V ℒₒᵣ 1) :
    T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t ≉ u).substs ![#'1] ➝ (t ≉ u).substs ![#'0]) := by
  suffices
      T.internalize V ⊢!
        (&'1 ≐ &'0) ➝
        (t⇞⇞.substs ![&'1] ≉ u⇞⇞.substs ![&'1]) ➝
        (t⇞⇞.substs ![&'0] ≉ u⇞⇞.substs ![&'0]) by
    apply TProof.all₂!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V ℒₒᵣ) := [t⇞⇞.substs ![&'1] ≉ u⇞⇞.substs ![&'1], &'1 ≐ &'0]
  suffices
      Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'0] ≉ u⇞⇞.substs ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] ≉ u⇞⇞.substs ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V]! u⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_ne T (t⇞⇞.substs ![&'1]) (t⇞⇞.substs ![&'0])
      (u⇞⇞.substs ![&'1]) (u⇞⇞.substs ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_nlt (t u : Semiterm V ℒₒᵣ 1) :
    T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t ≮' u).substs ![#'1] ➝ (t ≮' u).substs ![#'0]) := by
  suffices
      T.internalize V ⊢!
        (&'1 ≐ &'0) ➝
        (t⇞⇞.substs ![&'1] ≮' u⇞⇞.substs ![&'1]) ➝
        (t⇞⇞.substs ![&'0] ≮' u⇞⇞.substs ![&'0]) by
    apply TProof.all₂!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V ℒₒᵣ) := [t⇞⇞.substs ![&'1] ≮' u⇞⇞.substs ![&'1], &'1 ≐ &'0]
  suffices
      Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'0] ≮' u⇞⇞.substs ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] ≮' u⇞⇞.substs ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V]! t⇞⇞.substs ![&'1] ≐ t⇞⇞.substs ![&'0] :=
    of'! (term_replace' T t⇞⇞ &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V]! u⇞⇞.substs ![&'1] ≐ u⇞⇞.substs ![&'0] :=
    of'! (term_replace' T u⇞⇞ &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_nlt T (t⇞⇞.substs ![&'1]) (t⇞⇞.substs ![&'0])
      (u⇞⇞.substs ![&'1]) (u⇞⇞.substs ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replacse_aux_aux (φ : V) :
    IsSemiformula ℒₒᵣ 1 φ →
    T.Provable (^∀ ^∀ imp ℒₒᵣ (^#1 ^= ^#0) (imp ℒₒᵣ (substs ℒₒᵣ (^#1 ∷ 0) φ) (substs ℒₒᵣ (^#0 ∷ 0) φ))) := by
  apply IsFormula.sigma1_structural_induction₂_ss
  · sorry
  case hand =>
    intro p q hp hq ihp ihq
    let φ : Semiformula V ℒₒᵣ 1 := ⟨p, by simpa using hp⟩
    let ψ : Semiformula V ℒₒᵣ 1 := ⟨q, by simpa using hq⟩
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (φ ⋏ ψ).substs ![#'1] ➝ (φ ⋏ ψ).substs ![#'0]) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa [-Semiformula.substs_and, -substs_and, φ, ψ] using this
    suffices
        T.internalize V ⊢!
          (&'1 ≐ &'0) ➝ φ⤉⤉.substs ![&'1] ⋏ ψ⤉⤉.substs ![&'1] ➝ φ⤉⤉.substs ![&'0] ⋏ ψ⤉⤉.substs ![&'0] by
      apply TProof.all₂!
      simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    have ihφ : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ φ.substs ![#'1] ➝ φ.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ihp
    have ihψ : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ψ.substs ![#'1] ➝ ψ.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ihq
    have ihφ :
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ φ⤉⤉.substs ![&'1] ➝ φ⤉⤉.substs ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs] using this
    have ihψ :
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ ψ⤉⤉.substs ![&'1] ➝ ψ⤉⤉.substs ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs] using this
    cl_prover [ihφ, ihψ]
  case hor =>
    intro p q hp hq ihp ihq
    let φ : Semiformula V ℒₒᵣ 1 := ⟨p, by simpa using hp⟩
    let ψ : Semiformula V ℒₒᵣ 1 := ⟨q, by simpa using hq⟩
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (φ ⋎ ψ).substs ![#'1] ➝ (φ ⋎ ψ).substs ![#'0]) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa [-Semiformula.substs_or, -substs_or, φ, ψ] using this
    suffices
        T.internalize V ⊢!
          (&'1 ≐ &'0) ➝ φ⤉⤉.substs ![&'1] ⋎ ψ⤉⤉.substs ![&'1] ➝ φ⤉⤉.substs ![&'0] ⋎ ψ⤉⤉.substs ![&'0] by
      apply TProof.all₂!
      simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    have ihφ : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ φ.substs ![#'1] ➝ φ.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ihp
    have ihψ : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ψ.substs ![#'1] ➝ ψ.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ihq
    have ihφ :
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ φ⤉⤉.substs ![&'1] ➝ φ⤉⤉.substs ![&'0] := by
      have := TProof.specialize₂_shift! ihφ &'0 &'1
      simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs] using this
    have ihψ :
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ ψ⤉⤉.substs ![&'1] ➝ ψ⤉⤉.substs ![&'0] := by
      have := TProof.specialize₂_shift! ihψ &'0 &'1
      simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs] using this
    cl_prover [ihφ, ihψ]
  case hverum =>
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ⊤ ➝ ⊤) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa [-substs_equals] using this
    suffices Theory.internalize V T ⊢! (&'1 ≐ &'0) ➝ ⊤ ➝ ⊤ by
      apply TProof.all₂!
      simpa
    apply dhyp!; exact CV!
  case hfalsum =>
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ ⊥ ➝ ⊥) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa [-substs_equals] using this
    suffices Theory.internalize V T ⊢! (&'1 ≐ &'0) ➝ ⊥ ➝ ⊥ by
      apply TProof.all₂!
      simpa
    apply dhyp!; exact efq!
  case hrel =>
    intro k R v hR hv
    rcases isRel_iff_LOR.mp hR with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · let t : Semiterm V ℒₒᵣ 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V ℒₒᵣ 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t ≐ u).substs ![#'1] ➝ (t ≐ u).substs ![#'0]) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        simpa [-substs_equals, veq, val_all] using this
      simpa using replace_eq T t u
    · let t : Semiterm V ℒₒᵣ 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V ℒₒᵣ 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t <' u).substs ![#'1] ➝ (t <' u).substs ![#'0]) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        simpa [-substs_lessThan, veq, val_all] using this
      simpa using replace_lt T t u
  case hnrel =>
    intro k R v hR hv
    rcases isRel_iff_LOR.mp hR with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · let t : Semiterm V ℒₒᵣ 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V ℒₒᵣ 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t ≉ u).substs ![#'1] ➝ (t ≉ u).substs ![#'0]) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        simpa [-substs_notEquals, veq, val_all] using this
      simpa using replace_ne T t u
    · let t : Semiterm V ℒₒᵣ 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V ℒₒᵣ 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t ≮' u).substs ![#'1] ➝ (t ≮' u).substs ![#'0]) by
        have := (internalize_TProvable_iff_provable (T := T)).mp this
        simpa [-substs_notLessThan, veq, val_all] using this
      simpa using replace_nlt T t u
  case hall =>
    intro p hp ih
    let φ : Semiformula V ℒₒᵣ 2 := ⟨p, hp⟩
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (∀' φ).substs ![#'1] ➝ (∀' φ).substs ![#'0]) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, val_all,
        val_imp, val_equals, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one,
        Nat.zero_mod, Nat.cast_zero, val_substs, SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, SemitermVec.val_nil] using this
    have ih : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ φ⤉⤉.free1.substs ![#'1] ➝ φ⤉⤉.free1.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ ∀' φ⤉⤉.substs ![#'0, &'1] ➝ ∀' φ⤉⤉.substs ![#'0, &'0] by
      apply TProof.all₂!; simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    apply deduct'!
    apply TProof.all_imp_all!
    apply deductInv'!
    simpa [Semiformula.free1, Semiformula.free, SemitermVec.q,
      Semiformula.shift_substs, Semiformula.substs_substs, one_add_one_eq_two]
    using TProof.specialize₂! ih (&'1) (&'2)
  case hex =>
    intro p hp ih
    let φ : Semiformula V ℒₒᵣ 2 := ⟨p, hp⟩
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (∃' φ).substs ![#'1] ➝ (∃' φ).substs ![#'0]) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, val_all,
        val_imp, val_equals, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one,
        Nat.zero_mod, Nat.cast_zero, val_substs, SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, SemitermVec.val_nil] using this
    have ih : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ φ⤉⤉.free1.substs ![#'1] ➝ φ⤉⤉.free1.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ ∃' φ⤉⤉.substs ![#'0, &'1] ➝ ∃' φ⤉⤉.substs ![#'0, &'0] by
      apply TProof.all₂!; simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    apply deduct'!
    apply TProof.ex_imp_ex!
    apply deductInv'!
    simpa [Semiformula.free1, Semiformula.free, SemitermVec.q,
      Semiformula.shift_substs, Semiformula.substs_substs, one_add_one_eq_two]
      using TProof.specialize₂! ih (&'1) (&'2)
