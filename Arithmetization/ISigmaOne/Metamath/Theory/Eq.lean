import Arithmetization.ISigmaOne.Metamath.Proof.Typed

/-!

# Formalized Theory $\mathsf{R_0}$

-/

noncomputable section

open Classical

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace Formalized

variable (V)

abbrev LOR.Theory := @Language.Theory V _ ⌜ℒₒᵣ⌝ (Language.lDef ℒₒᵣ) _

variable {V}

/-- TODO: move -/
@[simp] lemma two_lt_three : (2 : V) < (1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma two_lt_four : (2 : V) < (1 + 1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma three_lt_four : (3 : V) < (1 + 1 + 1 + 1 : V) := by simp [←two_add_one_eq_three, ←one_add_one_eq_two]
@[simp] lemma two_sub_one_eq_one : (2 : V) - 1 = 1 := by simp [←one_add_one_eq_two]
@[simp] lemma three_sub_one_eq_two : (3 : V) - 1 = 2 := by simp [←two_add_one_eq_three]

class EQTheory (T : LOR.TTheory (V := V)) where
  refl : T ⊢ (#'0 =' #'0).all
  add_eq : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 + #'1) =' (#'2 + #'0)).all.all.all.all
  mul_eq : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 * #'1) =' (#'2 * #'0)).all.all.all.all
  lt_eq : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ #'3 <' #'1 ⟶ #'2 <' #'0).all.all.all.all
--  replace (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) : T ⊢ (#'1 =' #'0 ⟶ p^/[(#'1).sing] ⟶ p^/[(#'0).sing]).all.all


variable (T : LOR.TTheory (V := V))

namespace TProof

open Language.Theory.TProof System System.FiniteContext

section EQTheory

variable [EQTheory T]

lemma eq_refl! (t : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t =' t := ⟨by
  have : T ⊢ (#'0 =' #'0).all := EQTheory.refl
  simpa using specialize this t⟩

lemma add_eq! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝[V].TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ + u₁) =' (t₂ + u₂) := ⟨by
  have : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 + #'1) =' (#'2 + #'0)).all.all.all.all := EQTheory.add_eq
  have := specialize this t₁
  simp at this
  have := specialize this t₂
  simp at this
  have := specialize this u₁
  simp at this
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁,
    Language.TSemifromula.substs_substs] using specialize this u₂⟩

lemma mul_eq! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝[V].TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ * u₁) =' (t₂ * u₂) := ⟨by
  have : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 * #'1) =' (#'2 * #'0)).all.all.all.all := EQTheory.mul_eq
  have := specialize this t₁
  simp at this
  have := specialize this t₂
  simp at this
  have := specialize this u₁
  simp at this
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁,
    Language.TSemifromula.substs_substs] using specialize this u₂⟩

lemma lt_eq! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝[V].TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ <' u₁ ⟶ t₂ <' u₂ := ⟨by
  have : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ #'3 <' #'1 ⟶ #'2 <' #'0).all.all.all.all := EQTheory.lt_eq
  have := specialize this t₁
  simp at this
  have := specialize this t₂
  simp at this
  have := specialize this u₁
  simp at this
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁,
    Language.TSemifromula.substs_substs] using specialize this u₂⟩
