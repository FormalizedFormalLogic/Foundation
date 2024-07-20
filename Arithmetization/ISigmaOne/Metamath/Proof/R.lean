import Arithmetization.ISigmaOne.Metamath.Proof.Typed

/-!

# Theory $\mathsf{R}$

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace Formalized


variable (V)

abbrev LOR.Theory := @Language.Theory V _ _ _ _ _ _ ⌜ℒₒᵣ⌝ (Language.lDef ℒₒᵣ) _

variable {V}

abbrev bv {n : V} (x : V) (h : x < n := by simp) : ⌜ℒₒᵣ⌝.TSemiterm n := ⌜ℒₒᵣ⌝.bvar x h

scoped prefix:max "#'" => bv

/-- TODO: move -/
@[simp] lemma two_lt_three : (2 : V) < (1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma two_lt_four : (2 : V) < (1 + 1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma three_lt_four : (3 : V) < (1 + 1 + 1 + 1 : V) := by simp [←two_add_one_eq_three, ←one_add_one_eq_two]
@[simp] lemma two_sub_one_eq_one : (2 : V) - 1 = 1 := by simp [←one_add_one_eq_two]
@[simp] lemma three_sub_one_eq_two : (3 : V) - 1 = 2 := by simp [←two_add_one_eq_three]

class EQTheory (T : LOR.Theory V) where
  refl : (#'0 =' #'0).all ∈' T
  symm : (#'1 =' #'0 ⟶ #'0 =' #'1).all.all ∈' T
  trans : (#'2 =' #'1 ⟶ #'1 =' #'0 ⟶ #'2 =' #'0).all.all.all ∈' T
  addExt : (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 + #'1) =' (#'2 + #'0)).all.all.all.all ∈' T
  mulExt : (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 * #'1) =' (#'2 * #'0)).all.all.all.all ∈' T
  ltExt : (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ #'3 <' #'1 ⟶ #'2 <' #'0).all.all.all.all ∈' T

class R₀Theory (T : LOR.Theory V) where
  add (n m : V) : (↑n + ↑m) =' ↑(n + m) ∈' T
  mul (n m : V) : (↑n * ↑m) =' ↑(n * m) ∈' T
  ne {n m : V} : n ≠ m → ↑n ≠' ↑m ∈' T
  ltNumeral (n : V) : (#'0 <' ↑n ⟷ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all ∈' T

variable {T : LOR.Theory V} {pT : (Language.lDef ℒₒᵣ).TDef} [T.Defined pT] [EQTheory T]

namespace TProof

open Language.Theory.TProof System

def eqRefl (t : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t =' t := by
  have : T ⊢ (#'0 =' #'0).all := byAxm EQTheory.refl
  simpa [Language.TSemiformula.substs₁] using specialize this t

def eqSymm (t₁ t₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ t₂ =' t₁ := by
  have : T ⊢ (#'1 =' #'0 ⟶ #'0 =' #'1).all.all := byAxm EQTheory.symm
  have := by simpa using specialize this t₁
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁] using specialize this t₂

def eqTrans (t₁ t₂ t₃ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ t₂ =' t₃ ⟶ t₁ =' t₃ := by
  have : T ⊢ (#'2 =' #'1 ⟶ #'1 =' #'0 ⟶ #'2 =' #'0).all.all.all := byAxm EQTheory.trans
  have := by simpa using specialize this t₁
  have := by simpa using specialize this t₂
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁] using specialize this t₃

def addExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ + u₁) =' (t₂ + u₂) := by
  have : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 + #'1) =' (#'2 + #'0)).all.all.all.all := byAxm EQTheory.addExt
  have := by simpa using specialize this t₁
  have := by simpa using specialize this t₂
  have := by simpa using specialize this u₁
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁] using specialize this u₂

def mulExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ * u₁) =' (t₂ * u₂) := by
  have : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ (#'3 * #'1) =' (#'2 * #'0)).all.all.all.all := byAxm EQTheory.mulExt
  have := by simpa using specialize this t₁
  have := by simpa using specialize this t₂
  have := by simpa using specialize this u₁
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁] using specialize this u₂

def ltExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ <' u₁ ⟶ t₂ <' u₂ := by
  have : T ⊢ (#'3 =' #'2 ⟶ #'1 =' #'0 ⟶ #'3 <' #'1 ⟶ #'2 <' #'0).all.all.all.all := byAxm EQTheory.ltExt
  have := by simpa using specialize this t₁
  have := by simpa using specialize this t₂
  have := by simpa using specialize this u₁
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁] using specialize this u₂

variable [R₀Theory T]

def addComplete (n m : V) : T ⊢ (↑n + ↑m) =' ↑(n + m) := byAxm (R₀Theory.add n m)

def mulComplete (n m : V) : T ⊢ (↑n * ↑m) =' ↑(n * m) := byAxm (R₀Theory.mul n m)

def neComplete {n m : V} (h : n ≠ m) : T ⊢ ↑n ≠' ↑m := byAxm (R₀Theory.ne h)

def ltNumeral (t : ⌜ℒₒᵣ⌝.TTerm) (n : V) : T ⊢ t <' ↑n ⟷ (tSubstItr t.sing (#'1 =' #'0) n).disj := by
  have : T ⊢ (#'0 <' ↑n ⟷ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all := byAxm (R₀Theory.ltNumeral n)
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁] using specialize this t

def ltComplete {n m : V} (h : n < m) : T ⊢ ↑n <' ↑m := by
  have : T ⊢ ↑n <' ↑m ⟷ _ := ltNumeral (T := T) n m
  apply andRight this ⨀ ?_
  apply disj (i := m - (n + 1)) _ (by simpa using sub_succ_lt_self (by simp [h]))
  simpa [nth_tSubstItr', h] using eqRefl (T := T) ↑n

open Classical

noncomputable def nltComplete {n m : V} (h : m ≤ n) : T ⊢ ↑n ≮' ↑m := by
  have : T ⊢ ↑n ≮' ↑m ⟷ (tSubstItr (↑n : ⌜ℒₒᵣ⌝.TTerm).sing (#'1 ≠' #'0) m).conj := by
    simpa using negReplaceIff' <| ltNumeral (T := T) n m
  refine andRight this ⨀ ?_
  apply conj'
  intro i hi
  have hi : i < m := by simpa using hi
  have : n ≠ i := Ne.symm <| ne_of_lt <| lt_of_lt_of_le hi h
  simpa [nth_tSubstItr', hi] using neComplete this

end TProof

end Formalized

end LO.Arith

end
