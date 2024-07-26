import Arithmetization.ISigmaOne.Metamath.Proof.Typed

/-!

# Formalized Theory $\mathsf{R_0}$

-/

noncomputable section

open Classical

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace Formalized

variable (V)

abbrev LOR.Theory := @Language.Theory V _ _ _ _ _ _ ⌜ℒₒᵣ⌝ (Language.lDef ℒₒᵣ) _

variable {V}

abbrev bv {n : V} (x : V) (h : x < n := by simp) : ⌜ℒₒᵣ⌝.TSemiterm n := ⌜ℒₒᵣ⌝.bvar x h
abbrev fv {n : V} (x : V) : ⌜ℒₒᵣ⌝.TSemiterm n := ⌜ℒₒᵣ⌝.fvar x

scoped prefix:max "#'" => bv
scoped prefix:max "&'" => fv

/-- TODO: move -/
@[simp] lemma two_lt_three : (2 : V) < (1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma two_lt_four : (2 : V) < (1 + 1 + 1 + 1 : V) := by simp [←one_add_one_eq_two]
@[simp] lemma three_lt_four : (3 : V) < (1 + 1 + 1 + 1 : V) := by simp [←two_add_one_eq_three, ←one_add_one_eq_two]
@[simp] lemma two_sub_one_eq_one : (2 : V) - 1 = 1 := by simp [←one_add_one_eq_two]
@[simp] lemma three_sub_one_eq_two : (3 : V) - 1 = 2 := by simp [←two_add_one_eq_three]

class EQTheory (T : LOR.Theory V) : Prop where
  refl : (#'0 =' #'0).all ∈' T
  replace (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) : (#'1 =' #'0 ⟶ p^/[(#'1).sing] ⟶ p^/[(#'0).sing]).all.all ∈' T

class R₀Theory (T : LOR.Theory V) : Prop where
  add (n m : V) : (↑n + ↑m) =' ↑(n + m) ∈' T
  mul (n m : V) : (↑n * ↑m) =' ↑(n * m) ∈' T
  ne {n m : V} : n ≠ m → ↑n ≠' ↑m ∈' T
  ltNumeral (n : V) : (#'0 <' ↑n ⟷ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all ∈' T

/-
section

def _root_.LO.FirstOrder.Arith.eqTheory : 𝚺₁-Semisentence 0 := .mkSigma
  “(∃ b0, !qqBvarDef b0 0 ∧ !qqAllDef )” (by simp)

end
-/

variable (T : LOR.Theory V) {pT : (Language.lDef ℒₒᵣ).TDef} [T.Defined pT] [EQTheory T]

namespace TProof

open Language.Theory.TProof System System.FiniteContext

def eqRefl (t : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t =' t := by
  have : T ⊢ (#'0 =' #'0).all := byAxm EQTheory.refl
  simpa [Language.TSemiformula.substs₁] using specialize this t

lemma eq_refl! (t : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t =' t := ⟨eqRefl T t⟩


noncomputable def replace (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.TTerm) :
    T ⊢ t =' u ⟶ p^/[t.sing] ⟶ p^/[u.sing] := by
  have : T ⊢ (#'1 =' #'0 ⟶ p^/[(#'1).sing] ⟶ p^/[(#'0).sing]).all.all := byAxm <| EQTheory.replace p
  have := by simpa using specialize this t
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁,
    Language.TSemifromula.substs_substs] using specialize this u

lemma replace! (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t =' u ⟶ p^/[t.sing] ⟶ p^/[u.sing] := ⟨replace T p t u⟩

def eqSymm (t₁ t₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ t₂ =' t₁ := by
  apply deduct'
  let Γ := [t₁ =' t₂]
  have e₁ : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₁ =' t₁ := of <| eqRefl T t₁
  have : Γ ⊢[T] t₁ =' t₂ ⟶ t₁ =' t₁ ⟶ t₂ =' t₁ := of <| by
    simpa using replace T (#'0 =' t₁.bShift) t₁ t₂
  exact this ⨀ e₁ ⨀ e₂

lemma eq_symm! (t₁ t₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ t₂ =' t₁ := ⟨eqSymm T t₁ t₂⟩

lemma eq_symm'! {t₁ t₂ : ⌜ℒₒᵣ⌝.TTerm} (h : T ⊢! t₁ =' t₂) : T ⊢! t₂ =' t₁ := eq_symm! T t₁ t₂ ⨀ h

def eqTrans (t₁ t₂ t₃ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ t₂ =' t₃ ⟶ t₁ =' t₃ := by
  apply deduct'
  apply deduct
  let Γ := [t₂ =' t₃, t₁ =' t₂]
  have e₁ : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₂ =' t₃ := FiniteContext.byAxm (by simp [Γ])
  have : Γ ⊢[T] t₂ =' t₃ ⟶ t₁ =' t₂ ⟶ t₁ =' t₃ := of <| by
    simpa using replace T (t₁.bShift =' #'0) t₂ t₃
  exact this ⨀ e₂ ⨀ e₁

lemma eq_trans! (t₁ t₂ t₃ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ t₂ =' t₃ ⟶ t₁ =' t₃ := ⟨eqTrans T t₁ t₂ t₃⟩

noncomputable def addExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ + u₁) =' (t₂ + u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ⟶ (t₁ + u₁) =' (t₁ + u₁) ⟶ (t₁ + u₁) =' (t₂ + u₁) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (#'0 + u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ + u₁) =' (t₂ + u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T ⊢ u₁ =' u₂ ⟶ (t₁ + u₁) =' (t₂ + u₁) ⟶ (t₁ + u₁) =' (t₂ + u₂) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (t₂.bShift + #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma add_ext! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ + u₁) =' (t₂ + u₂) := ⟨addExt T t₁ t₂ u₁ u₂⟩

noncomputable def mulExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ * u₁) =' (t₂ * u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ⟶ (t₁ * u₁) =' (t₁ * u₁) ⟶ (t₁ * u₁) =' (t₂ * u₁) := by
    have := replace T ((t₁.bShift * u₁.bShift) =' (#'0 * u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ * u₁) =' (t₂ * u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T ⊢ u₁ =' u₂ ⟶ (t₁ * u₁) =' (t₂ * u₁) ⟶ (t₁ * u₁) =' (t₂ * u₂) := by
    have := replace T ((t₁.bShift * u₁.bShift) =' (t₂.bShift * #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma mul_ext! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ (t₁ * u₁) =' (t₂ * u₂) := ⟨mulExt T t₁ t₂ u₁ u₂⟩

noncomputable def eqExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ =' u₁ ⟶ t₂ =' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ =' u₁, u₁ =' u₂, t₁ =' t₂]
  have e1 : Γ ⊢[T] t₂ =' t₁ := by
    refine (of <| eqSymm T t₁ t₂) ⨀ FiniteContext.byAxm (by simp [Γ])
  have e2 : Γ ⊢[T] t₁ =' u₁ := FiniteContext.byAxm (by simp [Γ])
  have e3 : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm (by simp [Γ])
  exact (of <| eqTrans T t₂ u₁ u₂) ⨀ ((of <| eqTrans T t₂ t₁ u₁) ⨀ e1 ⨀ e2) ⨀ e3

lemma eq_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ =' u₁ ⟶ t₂ =' u₂ :=
  ⟨eqExt T t₁ t₂ u₁ u₂⟩

noncomputable def neExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ ≠' u₁ ⟶ t₂ ≠' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≠' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ ≠' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ⟶ t₁ ≠' u₁ ⟶ t₂ ≠' u₁ := by
    have := replace T (#'0 ≠' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ ≠' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ⟶ t₂ ≠' u₁ ⟶ t₂ ≠' u₂ := by
    simpa using replace T (t₂.bShift ≠' #'0) u₁ u₂
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma ne_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ ≠' u₁ ⟶ t₂ ≠' u₂ :=
  ⟨neExt T t₁ t₂ u₁ u₂⟩

noncomputable def ltExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ <' u₁ ⟶ t₂ <' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ <' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ <' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ⟶ t₁ <' u₁ ⟶ t₂ <' u₁ := by
    have := replace T (#'0 <' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ <' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ⟶ t₂ <' u₁ ⟶ t₂ <' u₂ := by
    have := replace T (t₂.bShift <' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma lt_ext! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ <' u₁ ⟶ t₂ <' u₂ := ⟨ltExt T t₁ t₂ u₁ u₂⟩

noncomputable def nltExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢ t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ ≮' u₁ ⟶ t₂ ≮' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≮' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ ≮' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ⟶ t₁ ≮' u₁ ⟶ t₂ ≮' u₁ := by
    have := replace T (#'0 ≮' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ ≮' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ⟶ t₂ ≮' u₁ ⟶ t₂ ≮' u₂ := by
    have := replace T (t₂.bShift ≮' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma nlt_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.TTerm) : T ⊢! t₁ =' t₂ ⟶ u₁ =' u₂ ⟶ t₁ ≮' u₁ ⟶ t₂ ≮' u₂ := ⟨nltExt T t₁ t₂ u₁ u₂⟩

noncomputable def ballReplace (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.TTerm) :
    T ⊢ t =' u ⟶ p.ball t ⟶ p.ball u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((p^/[(#'0).sing]).ball #'0) t u

lemma ball_replace! (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.TTerm) :
    T ⊢! t =' u ⟶ p.ball t ⟶ p.ball u := ⟨ballReplace T p t u⟩

noncomputable def bexReplace (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.TTerm) :
    T ⊢ t =' u ⟶ p.bex t ⟶ p.bex u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((p^/[(#'0).sing]).bex #'0) t u

lemma bex_replace! (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.TTerm) :
    T ⊢! t =' u ⟶ p.bex t ⟶ p.bex u := ⟨bexReplace T p t u⟩

variable [R₀Theory T]

def addComplete (n m : V) : T ⊢ (↑n + ↑m) =' ↑(n + m) := byAxm (R₀Theory.add n m)

lemma add_complete! (n m : V) : T ⊢! (↑n + ↑m) =' ↑(n + m) := ⟨addComplete T n m⟩

def mulComplete (n m : V) : T ⊢ (↑n * ↑m) =' ↑(n * m) := byAxm (R₀Theory.mul n m)

lemma mul_complete! (n m : V) : T ⊢! (↑n * ↑m) =' ↑(n * m) := ⟨mulComplete T n m⟩

def neComplete {n m : V} (h : n ≠ m) : T ⊢ ↑n ≠' ↑m := byAxm (R₀Theory.ne h)

lemma ne_complete! {n m : V} (h : n ≠ m) : T ⊢! ↑n ≠' ↑m := ⟨neComplete T h⟩

def ltNumeral (t : ⌜ℒₒᵣ⌝.TTerm) (n : V) : T ⊢ t <' ↑n ⟷ (tSubstItr t.sing (#'1 =' #'0) n).disj := by
  have : T ⊢ (#'0 <' ↑n ⟷ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all := byAxm (R₀Theory.ltNumeral n)
  simpa [Language.TSemitermVec.q_of_pos, Language.TSemiformula.substs₁] using specialize this t

noncomputable def nltNumeral (t : ⌜ℒₒᵣ⌝.TTerm) (n : V) : T ⊢ t ≮' ↑n ⟷ (tSubstItr t.sing (#'1 ≠' #'0) n).conj := by
  simpa using negReplaceIff' <| ltNumeral T t n

def eqComplete {n m : V} (h : n = m) : T ⊢ ↑n =' ↑m := by
  rcases h; exact eqRefl T _

lemma eq_complete! {n m : V} (h : n = m) : T ⊢! ↑n =' ↑m := ⟨eqComplete T h⟩

def ltComplete {n m : V} (h : n < m) : T ⊢ ↑n <' ↑m := by
  have : T ⊢ ↑n <' ↑m ⟷ _ := ltNumeral T n m
  apply andRight this ⨀ ?_
  apply disj (i := m - (n + 1)) _ (by simpa using sub_succ_lt_self (by simp [h]))
  simpa [nth_tSubstItr', h] using eqRefl T ↑n

lemma lt_complete! {n m : V} (h : n < m) : T ⊢! ↑n <' ↑m := ⟨ltComplete T h⟩

noncomputable def nltComplete {n m : V} (h : m ≤ n) : T ⊢ ↑n ≮' ↑m := by
  have : T ⊢ ↑n ≮' ↑m ⟷ (tSubstItr (↑n : ⌜ℒₒᵣ⌝.TTerm).sing (#'1 ≠' #'0) m).conj := by
    simpa using negReplaceIff' <| ltNumeral T n m
  refine andRight this ⨀ ?_
  apply conj'
  intro i hi
  have hi : i < m := by simpa using hi
  have : n ≠ i := Ne.symm <| ne_of_lt <| lt_of_lt_of_le hi h
  simpa [nth_tSubstItr', hi] using neComplete T this

lemma nlt_complete {n m : V} (h : m ≤ n) : T ⊢! ↑n ≮' ↑m := ⟨nltComplete T h⟩

noncomputable def ballIntro (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (n : V)
    (bs : ∀ i < n, T ⊢ p ^/[(i : ⌜ℒₒᵣ⌝.TTerm).sing]) :
    T ⊢ p.ball ↑n := by
  apply all
  suffices T ⊢ &'0 ≮' ↑n ⋎ p.shift^/[(&'0).sing] by
    simpa [Language.TSemiformula.free, Language.TSemiformula.substs₁]
  have : T ⊢ (tSubstItr (&'0).sing (#'1 ≠' #'0) n).conj ⋎ p.shift^/[(&'0).sing] := by
    apply conjOr'
    intro i hi
    have hi : i < n := by simpa using hi
    let Γ := [&'0 =' typedNumeral 0 i]
    suffices Γ ⊢[T] p.shift^/[(&'0).sing] by
      simpa [nth_tSubstItr', hi, Language.TSemiformula.imp_def] using deduct' this
    have e : Γ ⊢[T] ↑i =' &'0 := of (eqSymm T &'0 ↑i) ⨀ (FiniteContext.byAxm <| by simp [Γ])
    have : T ⊢ p.shift^/[(i : ⌜ℒₒᵣ⌝.TTerm).sing] := by
      simpa [Language.TSemifromula.shift_substs] using shift (bs i hi)
    exact of (replace T p.shift ↑i &'0) ⨀ e ⨀ of this
  exact orReplaceLeft' this (andRight (nltNumeral T (&'0) n))

lemma ball_intro! (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (n : V)
    (bs : ∀ i < n, T ⊢! p ^/[(i : ⌜ℒₒᵣ⌝.TTerm).sing]) :
    T ⊢! p.ball ↑n := ⟨ballIntro T p n fun i hi ↦ (bs i hi).get⟩

noncomputable def bexIntro (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T ⊢ p ^/[(i : ⌜ℒₒᵣ⌝.TTerm).sing]) :
    T ⊢ p.bex ↑n := by
  apply ex i
  suffices T ⊢ i <' n ⋏ p^/[(i : ⌜ℒₒᵣ⌝.TTerm).sing] by simpa
  exact System.andIntro (ltComplete T hi) b

lemma bex_intro! (p : ⌜ℒₒᵣ⌝.TSemiformula (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T ⊢! p ^/[(i : ⌜ℒₒᵣ⌝.TTerm).sing]) :
    T ⊢! p.bex ↑n := ⟨bexIntro T p n hi b.get⟩

end TProof

end Formalized

end LO.Arith

end
