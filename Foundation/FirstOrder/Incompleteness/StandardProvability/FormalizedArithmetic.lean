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

/-- TODO: move -/
@[simp] lemma two_lt_three : (2 : V) < (1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma two_lt_four : (2 : V) < (1 + 1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma three_lt_four : (3 : V) < (1 + 1 + 1 + 1 : V) := by simp [←two_add_one_eq_three, ←one_add_one_eq_two]
@[simp] lemma two_sub_one_eq_one : (2 : V) - 1 = 1 := by simp [←one_add_one_eq_two]
@[simp] lemma three_sub_one_eq_two : (3 : V) - 1 = 2 := by simp [←two_add_one_eq_three]

local prefix:max "#'" => Semiterm.bvar (V := V) (L := ℒₒᵣ)

local prefix:max "&'" => Semiterm.fvar (V := V) (L := ℒₒᵣ)

noncomputable abbrev num (n : V) : Semiterm V ℒₒᵣ k := typedNumeral n

scoped postfix:max "↟" => Semiformula.shift



/-
section

def _root_.LO.FirstOrder.Arithmetic.eqTheory : 𝚺₁.Semisentence 0 := .mkSigma
  “(∃ b0, !qqBvarDef b0 0 ∧ !qqAllDef )” (by simp)

end
-/

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

lemma vec2_eq {v : V} (h : len v = 2) : ?[v.[0], v.[1]] = v :=
  nth_ext' 2 (by simp [one_add_one_eq_two]) h (by
    intro i hi
    have : i = 0 ∨ i = 1 := le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi)
    rcases this with (rfl | rfl) <;> simp)



lemma term_replace_aux (t : V) :
    IsSemiterm ℒₒᵣ 1 t →
    T.Provable (^∀ ^∀ imp ℒₒᵣ (^#1 ^= ^#0) (termSubst ℒₒᵣ (^#1 ∷ 0) t ^= termSubst ℒₒᵣ (^#0 ∷ 0) t)) := by {
  sorry
     }

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
        ∀' ((&'0 ≐ #'0) ➝ (t.shift.substs ![&'0] ≐ u.shift.substs ![&'0]) ➝ (t.shift.substs ![#'0] ≐ u.shift.substs ![#'0])) by
    apply TProof.all!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  suffices
      T.internalize V ⊢!
        (&'1 ≐ &'0) ➝
        (t.shift.shift.substs ![&'1] ≐ u.shift.shift.substs ![&'1]) ➝
        (t.shift.shift.substs ![&'0] ≐ u.shift.shift.substs ![&'0]) by
    apply TProof.all!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V ℒₒᵣ) := [t.shift.shift.substs ![&'1] ≐ u.shift.shift.substs ![&'1], &'1 ≐ &'0]
  suffices
      Γ ⊢[T.internalize V]! t.shift.shift.substs ![&'0] ≐ u.shift.shift.substs ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V]! t.shift.shift.substs ![&'1] ≐ u.shift.shift.substs ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V]! t.shift.shift.substs ![&'1] ≐ t.shift.shift.substs ![&'0] :=
    of'! (term_replace' T t.shift.shift &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V]! u.shift.shift.substs ![&'1] ≐ u.shift.shift.substs ![&'0] :=
    of'! (term_replace' T u.shift.shift &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_eq T (t.shift.shift.substs ![&'1]) (t.shift.shift.substs ![&'0])
      (u.shift.shift.substs ![&'1]) (u.shift.shift.substs ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_lt (t u : Semiterm V ℒₒᵣ 1) :
    T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (t <' u).substs ![#'1] ➝ (t <' u).substs ![#'0]) := by
  suffices
      T.internalize V ⊢!
        ∀' ((&'0 ≐ #'0) ➝ (t.shift.substs ![&'0] <' u.shift.substs ![&'0]) ➝ (t.shift.substs ![#'0] <' u.shift.substs ![#'0])) by
    apply TProof.all!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  suffices
      T.internalize V ⊢!
        (&'1 ≐ &'0) ➝
        (t.shift.shift.substs ![&'1] <' u.shift.shift.substs ![&'1]) ➝
        (t.shift.shift.substs ![&'0] <' u.shift.shift.substs ![&'0]) by
    apply TProof.all!
    simpa [Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V ℒₒᵣ) := [t.shift.shift.substs ![&'1] <' u.shift.shift.substs ![&'1], &'1 ≐ &'0]
  suffices
      Γ ⊢[T.internalize V]! t.shift.shift.substs ![&'0] <' u.shift.shift.substs ![&'0] by
    apply deduct'!
    apply deduct!
    exact this
  have hh : Γ ⊢[T.internalize V]! t.shift.shift.substs ![&'1] <' u.shift.shift.substs ![&'1] :=
    by_axm₀!
  have ht : Γ ⊢[T.internalize V]! t.shift.shift.substs ![&'1] ≐ t.shift.shift.substs ![&'0] :=
    of'! (term_replace' T t.shift.shift &'1 &'0) ⨀ by_axm₁!
  have hu : Γ ⊢[T.internalize V]! u.shift.shift.substs ![&'1] ≐ u.shift.shift.substs ![&'0] :=
    of'! (term_replace' T u.shift.shift &'1 &'0) ⨀ by_axm₁!
  exact of'!
    (subst_lt T (t.shift.shift.substs ![&'1]) (t.shift.shift.substs ![&'0])
      (u.shift.shift.substs ![&'1]) (u.shift.shift.substs ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh



/--/
lemma replacse_aux_aux (φ : V) :
    IsSemiformula ℒₒᵣ 1 φ →
    T.Provable (^∀ ^∀ imp ℒₒᵣ (^#1 ^= ^#0) (imp ℒₒᵣ (substs ℒₒᵣ (^#1 ∷ 0) φ) (substs ℒₒᵣ (^#0 ∷ 0) φ))) := by {
  apply IsFormula.sigma1_structural_induction₂_ss
  · sorry
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
      --simpa using replace_eq T t u










      --apply TProof.all!;




  /-
  case hall =>
    intro p hp ih
    let φ : Semiformula V ℒₒᵣ 2 := ⟨p, hp⟩
    suffices T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ (∀' φ).substs ![#'1] ➝ (∀' φ).substs ![#'0]) by
      have := (internalize_TProvable_iff_provable (T := T)).mp this
      simpa only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, val_all,
        val_imp, val_equals, Semiterm.bvar_val, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.cast_one,
        Nat.zero_mod, Nat.cast_zero, val_substs, SemitermVec.val_succ, Matrix.head_cons,
        Matrix.tail_cons, SemitermVec.val_nil] using this
    have ih : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ φ↟↟.free1.substs ![#'1] ➝ φ↟↟.free1.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢! ∀' ((&'0 ≐ #'0) ➝ ∀' φ↟.substs ![#'0, &'0] ➝ ∀' φ↟.substs ![#'0, #'1]) by
      apply TProof.all!; simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    suffices
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ ∀' φ↟↟.substs ![#'0, &'1] ➝ ∀' φ↟↟.substs ![#'0, &'0] by
      apply TProof.all!; simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
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
    have ih : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ φ↟↟.free1.substs ![#'1] ➝ φ↟↟.free1.substs ![#'0]) := by
      apply (internalize_TProvable_iff_provable (T := T)).mpr
      simpa using ih
    suffices
        T.internalize V ⊢! ∀' ((&'0 ≐ #'0) ➝ ∃' φ↟.substs ![#'0, &'0] ➝ ∃' φ↟.substs ![#'0, #'1]) by
      apply TProof.all!; simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    suffices
        T.internalize V ⊢! (&'1 ≐ &'0) ➝ ∃' φ↟↟.substs ![#'0, &'1] ➝ ∃' φ↟↟.substs ![#'0, &'0] by
      apply TProof.all!; simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
    apply deduct'!
    apply TProof.ex_imp_ex!
    apply deductInv'!
    simpa [Semiformula.free1, Semiformula.free, SemitermVec.q,
      Semiformula.shift_substs, Semiformula.substs_substs, one_add_one_eq_two]
      using TProof.specialize₂! ih (&'1) (&'2) -/











     }



lemma replace_aux (ψ : Semiformula V ℒₒᵣ 1) (φ : Semiformula V ℒₒᵣ 2) : T.internalize V ⊢! (&'0 ≐ &'1) ➝ (∀' φ).substs ![&'0] ➝ (∀' φ).substs ![&'1] := by {
  apply deduct'!
  apply deduct!
  simp []
  apply TProof.generalize!
  simp [Semiformula.free, Semiformula.shift_substs, SemitermVec.q]
  simp [Semiformula.substs_substs]
  let t : Semiterm V ℒₒᵣ 1 := sorry
  let Φ : Semiformula V ℒₒᵣ 0 := ∀' ∀' ((#'1 ≐ #'0) ➝ (t.substs ![#'1] ≐ t.substs ![#'0]))
  have : Φ.val = 0 := by { simp [Φ] }
 }

/--/
lemma replace_aux (φ : Semiformula V ℒₒᵣ 1) : T.internalize V ⊢! (&'0 ≐ &'1) ➝ φ.substs ![&'0] ➝ φ.substs ![&'1] := by {

 }


lemma replace (φ : Semiformula V ℒₒᵣ 1) : T.internalize V ⊢! ∀' ∀' ((#'1 ≐ #'0) ➝ φ.substs ![#'1] ➝ φ.substs ![#'0]) := by {



 }

lemma replace (φ : Semiformula V ℒₒᵣ (0 + 1)) : T.internalize V ⊢! ((#'1 ≐ #'0) ➝ φ^/[(#'1).sing] ➝ φ^/[(#'0).sing]).all.all := by {  }

@[simp] lemma eq_refl (t : Term V ℒₒᵣ) : T.internalize V ⊢! t ≐ t := by
  have : T ⊢! (“∀ x, x = x” : SyntacticFormula ℒₒᵣ) := oRing_provable_of.{0} _ _ fun _ _ _ ↦ by simp [models_iff]
  have : T.internalize V ⊢! ∀' (#'0 ≐ #'0) := by
    simpa using internal_provable_of_outer_provable_arith this
  simpa using TProof.specialize! this t

/--/
lemma numeral_add (n m : V) :
    T.internalize V ⊢! (num n + num m) ≐ num (n + m) := by {
  induction m using ISigma1.sigma1_pos_succ_induction
  · -- simp only [internalize_TProvable_iff_provable, val_equals, val_add, val_numeral]
    -- definability
    sorry
  case zero =>
    have : T.internalize V ⊢! ((#'0 + typedNumeral (0 + 1) 0) ≐ #'0).all := by
      have : T ⊢! “∀ x, x + 0 = x” := sorry
      have := internal_provable_of_outer_provable_arith (V := V) this
      simpa [Semiformula.typedQuote_all (L := ℒₒᵣ)] using this
    simpa using TProof.specialize! this <| num n
  case one =>
    rcases eq_zero_or_pos n with (rfl | pos)
    · have : T.internalize V ⊢! (num 0 + num 1) ≐ num 1 := by
        have : T ⊢! “0 + 1 = 1” := sorry
        have := internal_provable_of_outer_provable_arith (V := V) this
        rw [typedQuote_eq'] at this
        simpa using this
      simpa using this
    · simp [numeral_succ_pos' pos]
  case succ m ih =>
    suffices
      T.internalize V ⊢!
        (num n + (num (m + 1) + num 1)) ≐ (num (n + m + 1) + num 1) by simpa [←one_add_one_eq_two, ←add_assoc]







 }

open TProof

noncomputable def nltNumeral (t : Term V ℒₒᵣ) (n : V) : T.internalize V ⊢ (t ≮' ↑n) ⭤ (tSubstItr t.sing (#'1 ≉ #'0) n).conj := by
  sorry

noncomputable def ballIntro (φ : Semiformula V ℒₒᵣ (0 + 1)) (n : V)
    (bs : ∀ i < n, T.internalize V ⊢ φ ^/[(i : Term V ℒₒᵣ).sing]) :
    T.internalize V ⊢ φ.ball ↑n := by
  apply TProof.all
  suffices T.internalize V ⊢ (&'0 ≮' ↑n) ⋎ φ.shift^/[(&'0).sing] by
    simpa [Semiformula.free, Semiformula.substs1]
  have : T.internalize V ⊢ (tSubstItr (&'0).sing (#'1 ≉ #'0) n).conj ⋎ φ.shift^/[(&'0).sing] := by
    apply TProof.conjOr'
    intro i hi
    have hi : i < n := by simpa using hi
    let Γ := [&'0 ≐ typedNumeral 0 i]
    suffices Γ ⊢[T.internalize V] φ.shift^/[(&'0).sing] by
      simpa [nth_tSubstItr', hi, Semiformula.imp_def] using deduct' this
    have e : Γ ⊢[T.internalize V] ↑i ≐ &'0 := sorry
    have : T.internalize V ⊢ φ.shift^/[(i : Term V ℒₒᵣ).sing] := by
      simpa [Language.TSemifromula.shift_substs] using TProof.shift (bs i hi)
    sorry--exact of (replace T φ.shift ↑i &'0) ⨀ e ⨀ of this
  exact A_replace_left this (K_right (nltNumeral T (&'0) n))

/--/
noncomputable def ballIntro (φ : Semiformula V ℒₒᵣ (0 + 1)) (n : V)
    (bs : ∀ i < n, T.internalize V ⊢ φ ^/[(i : Term V ℒₒᵣ).sing]) :
    T.internalize V ⊢ φ.ball ↑n := by
  apply TProof.all
  suffices T.internalize V ⊢ (&'0 ≮' ↑n) ⋎ φ.shift^/[(&'0).sing] by
    simpa [Semiformula.free, Semiformula.substs1]
  have : T.internalize V ⊢ (tSubstItr (&'0).sing (#'1 ≉ #'0) n).conj ⋎ φ.shift^/[(&'0).sing] := by
    apply TProof.conjOr'
    intro i hi
    have hi : i < n := by simpa using hi
    let Γ := [&'0 ≐ typedNumeral 0 i]
    suffices Γ ⊢[T.internalize V] φ.shift^/[(&'0).sing] by
      simpa [nth_tSubstItr', hi, Semiformula.imp_def] using deduct' this
    have e : Γ ⊢[T.internalize V] ↑i ≐ &'0 := sorry
    have : T.internalize V ⊢ φ.shift^/[(i : Term V ℒₒᵣ).sing] := by
      simpa [Language.TSemifromula.shift_substs] using TProof.shift (bs i hi)
    sorry--exact of (replace T φ.shift ↑i &'0) ⨀ e ⨀ of this
  exact A_replace_left this (K_right (nltNumeral T (&'0) n))

lemma replace (φ : Semiformula V ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢! t ≐ u ➝ φ^/[t.sing] ➝ φ^/[u.sing] := by {

     }



noncomputable def replace (φ : Semiformula V ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢! t ≐ u ➝ φ^/[t.sing] ➝ φ^/[u.sing] := by
  have : T.internalize V ⊢ (#'1 ≐ #'0 ➝ φ^/[(#'1).sing] ➝ φ^/[(#'0).sing]).all.all := InternalR₀Theory.replace φ
  have := by simpa using specialize this t
  simpa [SemitermVec.q_of_pos, Semiformula.substs1,
    Language.TSemifromula.substs_substs] using specialize this u


/--/
lemma eq_refl! (t : Term V ℒₒᵣ) : T.internalize V ⊢! t ≐ t := ⟨eqRefl T t⟩

noncomputable def replace (φ : Semiformula ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ t ≐ u ➝ φ^/[t.sing] ➝ φ^/[u.sing] := by
  have : T.internalize V ⊢ (#'1 ≐ #'0 ➝ φ^/[(#'1).sing] ➝ φ^/[(#'0).sing]).all.all := InternalR₀Theory.replace φ
  have := by simpa using specialize this t
  simpa [SemitermVec.q_of_pos, Semiformula.substs1,
    Language.TSemifromula.substs_substs] using specialize this u

lemma replace! (φ : Semiformula ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) : T.internalize V ⊢! t ≐ u ➝ φ^/[t.sing] ➝ φ^/[u.sing] := ⟨replace T φ t u⟩

noncomputable def eqSymm (t₁ t₂ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ t₂ ≐ t₁ := by
  apply deduct'
  let Γ := [t₁ ≐ t₂]
  have e₁ : Γ ⊢[T] t₁ ≐ t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₁ ≐ t₁ := of <| eqRefl T t₁
  have : Γ ⊢[T] t₁ ≐ t₂ ➝ t₁ ≐ t₁ ➝ t₂ ≐ t₁ := of <| by
    simpa using replace T (#'0 ≐ t₁.bShift) t₁ t₂
  exact this ⨀ e₁ ⨀ e₂

lemma eq_symm! (t₁ t₂ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ t₂ ≐ t₁ := ⟨eqSymm T t₁ t₂⟩

lemma eq_symm'! {t₁ t₂ : Term V ℒₒᵣ} (h : T.internalize V ⊢! t₁ ≐ t₂) : T.internalize V ⊢! t₂ ≐ t₁ := eq_symm! T t₁ t₂ ⨀ h

noncomputable def eqTrans (t₁ t₂ t₃ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ t₂ ≐ t₃ ➝ t₁ ≐ t₃ := by
  apply deduct'
  apply deduct
  let Γ := [t₂ ≐ t₃, t₁ ≐ t₂]
  have e₁ : Γ ⊢[T] t₁ ≐ t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₂ ≐ t₃ := FiniteContext.byAxm (by simp [Γ])
  have : Γ ⊢[T] t₂ ≐ t₃ ➝ t₁ ≐ t₂ ➝ t₁ ≐ t₃ := of <| by
    simpa using replace T (t₁.bShift ≐ #'0) t₂ t₃
  exact this ⨀ e₂ ⨀ e₁

lemma eq_trans! (t₁ t₂ t₃ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ t₂ ≐ t₃ ➝ t₁ ≐ t₃ := ⟨eqTrans T t₁ t₂ t₃⟩

noncomputable def addExt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ (t₁ + u₁) ≐ (t₂ + u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ ≐ u₂, t₁ ≐ t₂]
  have bt : Γ ⊢[T] t₁ ≐ t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ ≐ u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T.internalize V ⊢ t₁ ≐ t₂ ➝ (t₁ + u₁) ≐ (t₁ + u₁) ➝ (t₁ + u₁) ≐ (t₂ + u₁) := by
    have := replace T ((t₁.bShift + u₁.bShift) ≐ (#'0 + u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ + u₁) ≐ (t₂ + u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T.internalize V ⊢ u₁ ≐ u₂ ➝ (t₁ + u₁) ≐ (t₂ + u₁) ➝ (t₁ + u₁) ≐ (t₂ + u₂) := by
    have := replace T ((t₁.bShift + u₁.bShift) ≐ (t₂.bShift + #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma add_ext! (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ (t₁ + u₁) ≐ (t₂ + u₂) := ⟨addExt T t₁ t₂ u₁ u₂⟩

noncomputable def mulExt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ (t₁ * u₁) ≐ (t₂ * u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ ≐ u₂, t₁ ≐ t₂]
  have bt : Γ ⊢[T] t₁ ≐ t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ ≐ u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T.internalize V ⊢ t₁ ≐ t₂ ➝ (t₁ * u₁) ≐ (t₁ * u₁) ➝ (t₁ * u₁) ≐ (t₂ * u₁) := by
    have := replace T ((t₁.bShift * u₁.bShift) ≐ (#'0 * u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ * u₁) ≐ (t₂ * u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T.internalize V ⊢ u₁ ≐ u₂ ➝ (t₁ * u₁) ≐ (t₂ * u₁) ➝ (t₁ * u₁) ≐ (t₂ * u₂) := by
    have := replace T ((t₁.bShift * u₁.bShift) ≐ (t₂.bShift * #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma mul_ext! (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ (t₁ * u₁) ≐ (t₂ * u₂) := ⟨mulExt T t₁ t₂ u₁ u₂⟩

noncomputable def eqExt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ ≐ u₁ ➝ t₂ ≐ u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≐ u₁, u₁ ≐ u₂, t₁ ≐ t₂]
  have e1 : Γ ⊢[T] t₂ ≐ t₁ := by
    refine (of <| eqSymm T t₁ t₂) ⨀ FiniteContext.byAxm (by simp [Γ])
  have e2 : Γ ⊢[T] t₁ ≐ u₁ := FiniteContext.byAxm (by simp [Γ])
  have e3 : Γ ⊢[T] u₁ ≐ u₂ := FiniteContext.byAxm (by simp [Γ])
  exact (of <| eqTrans T t₂ u₁ u₂) ⨀ ((of <| eqTrans T t₂ t₁ u₁) ⨀ e1 ⨀ e2) ⨀ e3

lemma eq_ext (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ ≐ u₁ ➝ t₂ ≐ u₂ :=
  ⟨eqExt T t₁ t₂ u₁ u₂⟩

noncomputable def neExt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ ≉ u₁ ➝ t₂ ≉ u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≉ u₁, u₁ ≐ u₂, t₁ ≐ t₂]
  have bt : Γ ⊢[T] t₁ ≐ t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ ≐ u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ ≉ u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T.internalize V ⊢ t₁ ≐ t₂ ➝ t₁ ≉ u₁ ➝ t₂ ≉ u₁ := by
    have := replace T (#'0 ≉ u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ ≉ u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T.internalize V ⊢ u₁ ≐ u₂ ➝ t₂ ≉ u₁ ➝ t₂ ≉ u₂ := by
    simpa using replace T (t₂.bShift ≉ #'0) u₁ u₂
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma ne_ext (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ ≉ u₁ ➝ t₂ ≉ u₂ :=
  ⟨neExt T t₁ t₂ u₁ u₂⟩

noncomputable def ltExt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ <' u₁ ➝ t₂ <' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ <' u₁, u₁ ≐ u₂, t₁ ≐ t₂]
  have bt : Γ ⊢[T] t₁ ≐ t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ ≐ u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ <' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T.internalize V ⊢ t₁ ≐ t₂ ➝ t₁ <' u₁ ➝ t₂ <' u₁ := by
    have := replace T (#'0 <' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ <' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T.internalize V ⊢ u₁ ≐ u₂ ➝ t₂ <' u₁ ➝ t₂ <' u₂ := by
    have := replace T (t₂.bShift <' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma lt_ext! (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ <' u₁ ➝ t₂ <' u₂ := ⟨ltExt T t₁ t₂ u₁ u₂⟩

noncomputable def nltExt (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢ t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ ≮' u₁ ➝ t₂ ≮' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≮' u₁, u₁ ≐ u₂, t₁ ≐ t₂]
  have bt : Γ ⊢[T] t₁ ≐ t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ ≐ u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ ≮' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T.internalize V ⊢ t₁ ≐ t₂ ➝ t₁ ≮' u₁ ➝ t₂ ≮' u₁ := by
    have := replace T (#'0 ≮' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ ≮' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T.internalize V ⊢ u₁ ≐ u₂ ➝ t₂ ≮' u₁ ➝ t₂ ≮' u₂ := by
    have := replace T (t₂.bShift ≮' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma nlt_ext (t₁ t₂ u₁ u₂ : Term V ℒₒᵣ) : T.internalize V ⊢! t₁ ≐ t₂ ➝ u₁ ≐ u₂ ➝ t₁ ≮' u₁ ➝ t₂ ≮' u₂ := ⟨nltExt T t₁ t₂ u₁ u₂⟩

noncomputable def ballReplace (φ : Semiformula ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ t ≐ u ➝ φ.ball t ➝ φ.ball u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((φ^/[(#'0).sing]).ball #'0) t u

lemma ball_replace! (φ : Semiformula ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢! t ≐ u ➝ φ.ball t ➝ φ.ball u := ⟨ballReplace T φ t u⟩

noncomputable def bexReplace (φ : Semiformula ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢ t ≐ u ➝ φ.bex t ➝ φ.bex u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((φ^/[(#'0).sing]).bex #'0) t u

lemma bex_replace! (φ : Semiformula ℒₒᵣ (0 + 1)) (t u : Term V ℒₒᵣ) :
    T.internalize V ⊢! t ≐ u ➝ φ.bex t ➝ φ.bex u := ⟨bexReplace T φ t u⟩

noncomputable def eqComplete {n m : V} (h : n = m) : T.internalize V ⊢ ↑n ≐ ↑m := by
  rcases h; exact eqRefl T _

lemma eq_complete! {n m : V} (h : n = m) : T.internalize V ⊢! ↑n ≐ ↑m := ⟨eqComplete T h⟩

def addComplete (n m : V) : T.internalize V ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) ≐ ↑(n + m) := InternalR₀Theory.add n m

lemma add_complete! (n m : V) : T.internalize V ⊢! (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) ≐ ↑(n + m) := ⟨addComplete T n m⟩

def mulComplete (n m : V) : T.internalize V ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) ≐ ↑(n * m) := InternalR₀Theory.mul n m

lemma mul_complete! (n m : V) : T.internalize V ⊢! (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) ≐ ↑(n * m) := ⟨mulComplete T n m⟩

def neComplete {n m : V} (h : n ≠ m) : T.internalize V ⊢ ↑n ≉ ↑m := InternalR₀Theory.ne h

lemma ne_complete! {n m : V} (h : n ≠ m) : T.internalize V ⊢! ↑n ≉ ↑m := ⟨neComplete T h⟩

noncomputable def ltNumeral (t : Term V ℒₒᵣ) (n : V) : T.internalize V ⊢ t <' ↑n ⭤ (tSubstItr t.sing (#'1 ≐ #'0) n).disj := by
  have : T.internalize V ⊢ (#'0 <' ↑n ⭤ (tSubstItr (#'0).sing (#'1 ≐ #'0) n).disj).all := InternalR₀Theory.ltNumeral n
  simpa [SemitermVec.q_of_pos, Semiformula.substs1] using specialize this t

noncomputable def nltNumeral (t : Term V ℒₒᵣ) (n : V) : T.internalize V ⊢ t ≮' ↑n ⭤ (tSubstItr t.sing (#'1 ≉ #'0) n).conj := by
  simpa using ENN_of_E <| ltNumeral T t n

noncomputable def ltComplete {n m : V} (h : n < m) : T.internalize V ⊢ ↑n <' ↑m := by
  have : T.internalize V ⊢ ↑n <' ↑m ⭤ _ := ltNumeral T n m
  apply K_right this ⨀ ?_
  apply disj (i := m - (n + 1)) _ (by simpa using sub_succ_lt_self h)
  simpa [nth_tSubstItr', h] using eqRefl T ↑n

lemma lt_complete! {n m : V} (h : n < m) : T.internalize V ⊢! ↑n <' ↑m := ⟨ltComplete T h⟩

noncomputable def nltComplete {n m : V} (h : m ≤ n) : T.internalize V ⊢ ↑n ≮' ↑m := by
  have : T.internalize V ⊢ ↑n ≮' ↑m ⭤ (tSubstItr (↑n : Term V ℒₒᵣ).sing (#'1 ≉ #'0) m).conj := by
    simpa using ENN_of_E <| ltNumeral T n m
  refine K_right this ⨀ ?_
  apply conj'
  intro i hi
  have hi : i < m := by simpa using hi
  have : n ≠ i := Ne.symm <| ne_of_lt <| lt_of_lt_of_le hi h
  simpa [nth_tSubstItr', hi] using neComplete T this

lemma nlt_complete {n m : V} (h : m ≤ n) : T.internalize V ⊢! ↑n ≮' ↑m := ⟨nltComplete T h⟩

noncomputable def ballIntro (φ : Semiformula ℒₒᵣ (0 + 1)) (n : V)
    (bs : ∀ i < n, T.internalize V ⊢ φ ^/[(i : Term V ℒₒᵣ).sing]) :
    T.internalize V ⊢ φ.ball ↑n := by
  apply all
  suffices T.internalize V ⊢ &'0 ≮' ↑n ⋎ φ.shift^/[(&'0).sing] by
    simpa [Semiformula.free, Semiformula.substs1]
  have : T.internalize V ⊢ (tSubstItr (&'0).sing (#'1 ≉ #'0) n).conj ⋎ φ.shift^/[(&'0).sing] := by
    apply conjOr'
    intro i hi
    have hi : i < n := by simpa using hi
    let Γ := [&'0 ≐ typedNumeral 0 i]
    suffices Γ ⊢[T] φ.shift^/[(&'0).sing] by
      simpa [nth_tSubstItr', hi, Semiformula.imp_def] using deduct' this
    have e : Γ ⊢[T] ↑i ≐ &'0 := of (eqSymm T &'0 ↑i) ⨀ (FiniteContext.byAxm <| by simp [Γ])
    have : T.internalize V ⊢ φ.shift^/[(i : Term V ℒₒᵣ).sing] := by
      simpa [Language.TSemifromula.shift_substs] using shift (bs i hi)
    exact of (replace T φ.shift ↑i &'0) ⨀ e ⨀ of this
  exact A_replace_left this (K_right (nltNumeral T (&'0) n))

lemma ball_intro! (φ : Semiformula ℒₒᵣ (0 + 1)) (n : V)
    (bs : ∀ i < n, T.internalize V ⊢! φ ^/[(i : Term V ℒₒᵣ).sing]) :
    T.internalize V ⊢! φ.ball ↑n := ⟨ballIntro T φ n fun i hi ↦ (bs i hi).get⟩

noncomputable def bexIntro (φ : Semiformula ℒₒᵣ (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T.internalize V ⊢ φ ^/[(i : Term V ℒₒᵣ).sing]) :
    T.internalize V ⊢ φ.bex ↑n := by
  apply ex i
  suffices T.internalize V ⊢ i <' n ⋏ φ^/[(i : Term V ℒₒᵣ).sing] by simpa
  exact Entailment.K_intro (ltComplete T hi) b

lemma bex_intro! (φ : Semiformula ℒₒᵣ (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T.internalize V ⊢! φ ^/[(i : Term V ℒₒᵣ).sing]) :
    T.internalize V ⊢! φ.bex ↑n := ⟨bexIntro T φ n hi b.get⟩

end InternalR₀Theory

end TProof

end InternalArithmetic

end LO.ISigma1.Metamath
