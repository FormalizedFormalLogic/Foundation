import Arithmetization.ISigmaOne.Metamath

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

class R₀Theory (T : LOR.TTheory (V := V)) where
  refl : T ⊢ (#'0 =' #'0).all
  replace (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) : T ⊢ (#'1 =' #'0 ➝ φ^/[(#'1).sing] ➝ φ^/[(#'0).sing]).all.all
  add (n m : V) : T ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m)
  mul (n m : V) : T ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m)
  ne {n m : V} : n ≠ m → T ⊢ ↑n ≠' ↑m
  ltNumeral (n : V) : T ⊢ (#'0 <' ↑n ⭤ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all

abbrev oneAbbrev {n} : ⌜ℒₒᵣ⌝[V].Semiterm n := (1 : V)

scoped notation "^1" => oneAbbrev

/-
section

def _root_.LO.FirstOrder.Arith.eqTheory : 𝚺₁.Semisentence 0 := .mkSigma
  “(∃ b0, !qqBvarDef b0 0 ∧ !qqAllDef )” (by simp)

end
-/

variable (T : LOR.TTheory (V := V))

namespace TProof

open Language.Theory.TProof System System.FiniteContext

section R₀Theory

variable [R₀Theory T]

def eqRefl (t : ⌜ℒₒᵣ⌝.Term) : T ⊢ t =' t := by
  have : T ⊢ (#'0 =' #'0).all := R₀Theory.refl
  simpa [Language.Semiformula.substs₁] using specialize this t

lemma eq_refl! (t : ⌜ℒₒᵣ⌝.Term) : T ⊢! t =' t := ⟨eqRefl T t⟩

noncomputable def replace (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t =' u ➝ φ^/[t.sing] ➝ φ^/[u.sing] := by
  have : T ⊢ (#'1 =' #'0 ➝ φ^/[(#'1).sing] ➝ φ^/[(#'0).sing]).all.all := R₀Theory.replace φ
  have := by simpa using specialize this t
  simpa [Language.SemitermVec.q_of_pos, Language.Semiformula.substs₁,
    Language.TSemifromula.substs_substs] using specialize this u

lemma replace! (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) : T ⊢! t =' u ➝ φ^/[t.sing] ➝ φ^/[u.sing] := ⟨replace T φ t u⟩

def eqSymm (t₁ t₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ t₂ =' t₁ := by
  apply deduct'
  let Γ := [t₁ =' t₂]
  have e₁ : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₁ =' t₁ := of <| eqRefl T t₁
  have : Γ ⊢[T] t₁ =' t₂ ➝ t₁ =' t₁ ➝ t₂ =' t₁ := of <| by
    simpa using replace T (#'0 =' t₁.bShift) t₁ t₂
  exact this ⨀ e₁ ⨀ e₂

lemma eq_symm! (t₁ t₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ t₂ =' t₁ := ⟨eqSymm T t₁ t₂⟩

lemma eq_symm'! {t₁ t₂ : ⌜ℒₒᵣ⌝.Term} (h : T ⊢! t₁ =' t₂) : T ⊢! t₂ =' t₁ := eq_symm! T t₁ t₂ ⨀ h

def eqTrans (t₁ t₂ t₃ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ t₂ =' t₃ ➝ t₁ =' t₃ := by
  apply deduct'
  apply deduct
  let Γ := [t₂ =' t₃, t₁ =' t₂]
  have e₁ : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm (by simp [Γ])
  have e₂ : Γ ⊢[T] t₂ =' t₃ := FiniteContext.byAxm (by simp [Γ])
  have : Γ ⊢[T] t₂ =' t₃ ➝ t₁ =' t₂ ➝ t₁ =' t₃ := of <| by
    simpa using replace T (t₁.bShift =' #'0) t₂ t₃
  exact this ⨀ e₂ ⨀ e₁

lemma eq_trans! (t₁ t₂ t₃ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ t₂ =' t₃ ➝ t₁ =' t₃ := ⟨eqTrans T t₁ t₂ t₃⟩

noncomputable def addExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ u₁ =' u₂ ➝ (t₁ + u₁) =' (t₂ + u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ➝ (t₁ + u₁) =' (t₁ + u₁) ➝ (t₁ + u₁) =' (t₂ + u₁) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (#'0 + u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ + u₁) =' (t₂ + u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T ⊢ u₁ =' u₂ ➝ (t₁ + u₁) =' (t₂ + u₁) ➝ (t₁ + u₁) =' (t₂ + u₂) := by
    have := replace T ((t₁.bShift + u₁.bShift) =' (t₂.bShift + #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma add_ext! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ u₁ =' u₂ ➝ (t₁ + u₁) =' (t₂ + u₂) := ⟨addExt T t₁ t₂ u₁ u₂⟩

noncomputable def mulExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ u₁ =' u₂ ➝ (t₁ * u₁) =' (t₂ * u₂) := by
  apply deduct'
  apply deduct
  let Γ := [u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ➝ (t₁ * u₁) =' (t₁ * u₁) ➝ (t₁ * u₁) =' (t₂ * u₁) := by
    have := replace T ((t₁.bShift * u₁.bShift) =' (#'0 * u₁.bShift)) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] (t₁ * u₁) =' (t₂ * u₁) := of (Γ := Γ) this ⨀ bt ⨀ of (eqRefl _ _)
  have : T ⊢ u₁ =' u₂ ➝ (t₁ * u₁) =' (t₂ * u₁) ➝ (t₁ * u₁) =' (t₂ * u₂) := by
    have := replace T ((t₁.bShift * u₁.bShift) =' (t₂.bShift * #'0)) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma mul_ext! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ u₁ =' u₂ ➝ (t₁ * u₁) =' (t₂ * u₂) := ⟨mulExt T t₁ t₂ u₁ u₂⟩

noncomputable def eqExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ =' u₁ ➝ t₂ =' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ =' u₁, u₁ =' u₂, t₁ =' t₂]
  have e1 : Γ ⊢[T] t₂ =' t₁ := by
    refine (of <| eqSymm T t₁ t₂) ⨀ FiniteContext.byAxm (by simp [Γ])
  have e2 : Γ ⊢[T] t₁ =' u₁ := FiniteContext.byAxm (by simp [Γ])
  have e3 : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm (by simp [Γ])
  exact (of <| eqTrans T t₂ u₁ u₂) ⨀ ((of <| eqTrans T t₂ t₁ u₁) ⨀ e1 ⨀ e2) ⨀ e3

lemma eq_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ =' u₁ ➝ t₂ =' u₂ :=
  ⟨eqExt T t₁ t₂ u₁ u₂⟩

noncomputable def neExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ ≠' u₁ ➝ t₂ ≠' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≠' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ ≠' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ➝ t₁ ≠' u₁ ➝ t₂ ≠' u₁ := by
    have := replace T (#'0 ≠' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ ≠' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ➝ t₂ ≠' u₁ ➝ t₂ ≠' u₂ := by
    simpa using replace T (t₂.bShift ≠' #'0) u₁ u₂
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma ne_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ ≠' u₁ ➝ t₂ ≠' u₂ :=
  ⟨neExt T t₁ t₂ u₁ u₂⟩

noncomputable def ltExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ <' u₁ ➝ t₂ <' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ <' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ <' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ➝ t₁ <' u₁ ➝ t₂ <' u₁ := by
    have := replace T (#'0 <' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ <' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ➝ t₂ <' u₁ ➝ t₂ <' u₂ := by
    have := replace T (t₂.bShift <' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma lt_ext! (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ <' u₁ ➝ t₂ <' u₂ := ⟨ltExt T t₁ t₂ u₁ u₂⟩

noncomputable def nltExt (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢ t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ ≮' u₁ ➝ t₂ ≮' u₂ := by
  apply deduct'
  apply deduct
  apply deduct
  let Γ := [t₁ ≮' u₁, u₁ =' u₂, t₁ =' t₂]
  have bt : Γ ⊢[T] t₁ =' t₂ := FiniteContext.byAxm <| by simp [Γ]
  have bu : Γ ⊢[T] u₁ =' u₂ := FiniteContext.byAxm <| by simp [Γ]
  have bl : Γ ⊢[T] t₁ ≮' u₁ := FiniteContext.byAxm <| by simp [Γ]
  have : T ⊢ t₁ =' t₂ ➝ t₁ ≮' u₁ ➝ t₂ ≮' u₁ := by
    have := replace T (#'0 ≮' u₁.bShift) t₁ t₂
    simpa using this
  have b : Γ ⊢[T] t₂ ≮' u₁ := of (Γ := Γ) this ⨀ bt ⨀ bl
  have : T ⊢ u₁ =' u₂ ➝ t₂ ≮' u₁ ➝ t₂ ≮' u₂ := by
    have := replace T (t₂.bShift ≮' #'0) u₁ u₂
    simpa using this
  exact of (Γ := Γ) this ⨀ bu ⨀ b

lemma nlt_ext (t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Term) : T ⊢! t₁ =' t₂ ➝ u₁ =' u₂ ➝ t₁ ≮' u₁ ➝ t₂ ≮' u₂ := ⟨nltExt T t₁ t₂ u₁ u₂⟩

noncomputable def ballReplace (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t =' u ➝ φ.ball t ➝ φ.ball u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((φ^/[(#'0).sing]).ball #'0) t u

lemma ball_replace! (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t =' u ➝ φ.ball t ➝ φ.ball u := ⟨ballReplace T φ t u⟩

noncomputable def bexReplace (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢ t =' u ➝ φ.bex t ➝ φ.bex u := by
  simpa [Language.TSemifromula.substs_substs] using replace T ((φ^/[(#'0).sing]).bex #'0) t u

lemma bex_replace! (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (t u : ⌜ℒₒᵣ⌝.Term) :
    T ⊢! t =' u ➝ φ.bex t ➝ φ.bex u := ⟨bexReplace T φ t u⟩

def eqComplete {n m : V} (h : n = m) : T ⊢ ↑n =' ↑m := by
  rcases h; exact eqRefl T _

lemma eq_complete! {n m : V} (h : n = m) : T ⊢! ↑n =' ↑m := ⟨eqComplete T h⟩

def addComplete (n m : V) : T ⊢ (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := R₀Theory.add n m

lemma add_complete! (n m : V) : T ⊢! (n + m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n + m) := ⟨addComplete T n m⟩

def mulComplete (n m : V) : T ⊢ (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := R₀Theory.mul n m

lemma mul_complete! (n m : V) : T ⊢! (n * m : ⌜ℒₒᵣ⌝[V].Semiterm 0) =' ↑(n * m) := ⟨mulComplete T n m⟩

def neComplete {n m : V} (h : n ≠ m) : T ⊢ ↑n ≠' ↑m := R₀Theory.ne h

lemma ne_complete! {n m : V} (h : n ≠ m) : T ⊢! ↑n ≠' ↑m := ⟨neComplete T h⟩

def ltNumeral (t : ⌜ℒₒᵣ⌝.Term) (n : V) : T ⊢ t <' ↑n ⭤ (tSubstItr t.sing (#'1 =' #'0) n).disj := by
  have : T ⊢ (#'0 <' ↑n ⭤ (tSubstItr (#'0).sing (#'1 =' #'0) n).disj).all := R₀Theory.ltNumeral n
  simpa [Language.SemitermVec.q_of_pos, Language.Semiformula.substs₁] using specialize this t

noncomputable def nltNumeral (t : ⌜ℒₒᵣ⌝.Term) (n : V) : T ⊢ t ≮' ↑n ⭤ (tSubstItr t.sing (#'1 ≠' #'0) n).conj := by
  simpa using negReplaceIff' <| ltNumeral T t n

def ltComplete {n m : V} (h : n < m) : T ⊢ ↑n <' ↑m := by
  have : T ⊢ ↑n <' ↑m ⭤ _ := ltNumeral T n m
  apply andRight this ⨀ ?_
  apply disj (i := m - (n + 1)) _ (by simpa using sub_succ_lt_self (by simp [h]))
  simpa [nth_tSubstItr', h] using eqRefl T ↑n

lemma lt_complete! {n m : V} (h : n < m) : T ⊢! ↑n <' ↑m := ⟨ltComplete T h⟩

noncomputable def nltComplete {n m : V} (h : m ≤ n) : T ⊢ ↑n ≮' ↑m := by
  have : T ⊢ ↑n ≮' ↑m ⭤ (tSubstItr (↑n : ⌜ℒₒᵣ⌝.Term).sing (#'1 ≠' #'0) m).conj := by
    simpa using negReplaceIff' <| ltNumeral T n m
  refine andRight this ⨀ ?_
  apply conj'
  intro i hi
  have hi : i < m := by simpa using hi
  have : n ≠ i := Ne.symm <| ne_of_lt <| lt_of_lt_of_le hi h
  simpa [nth_tSubstItr', hi] using neComplete T this

lemma nlt_complete {n m : V} (h : m ≤ n) : T ⊢! ↑n ≮' ↑m := ⟨nltComplete T h⟩

noncomputable def ballIntro (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V)
    (bs : ∀ i < n, T ⊢ φ ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢ φ.ball ↑n := by
  apply all
  suffices T ⊢ &'0 ≮' ↑n ⋎ φ.shift^/[(&'0).sing] by
    simpa [Language.Semiformula.free, Language.Semiformula.substs₁]
  have : T ⊢ (tSubstItr (&'0).sing (#'1 ≠' #'0) n).conj ⋎ φ.shift^/[(&'0).sing] := by
    apply conjOr'
    intro i hi
    have hi : i < n := by simpa using hi
    let Γ := [&'0 =' typedNumeral 0 i]
    suffices Γ ⊢[T] φ.shift^/[(&'0).sing] by
      simpa [nth_tSubstItr', hi, Language.Semiformula.imp_def] using deduct' this
    have e : Γ ⊢[T] ↑i =' &'0 := of (eqSymm T &'0 ↑i) ⨀ (FiniteContext.byAxm <| by simp [Γ])
    have : T ⊢ φ.shift^/[(i : ⌜ℒₒᵣ⌝.Term).sing] := by
      simpa [Language.TSemifromula.shift_substs] using shift (bs i hi)
    exact of (replace T φ.shift ↑i &'0) ⨀ e ⨀ of this
  exact orReplaceLeft' this (andRight (nltNumeral T (&'0) n))

lemma ball_intro! (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V)
    (bs : ∀ i < n, T ⊢! φ ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢! φ.ball ↑n := ⟨ballIntro T φ n fun i hi ↦ (bs i hi).get⟩

noncomputable def bexIntro (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T ⊢ φ ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢ φ.bex ↑n := by
  apply ex i
  suffices T ⊢ i <' n ⋏ φ^/[(i : ⌜ℒₒᵣ⌝.Term).sing] by simpa
  exact System.andIntro (ltComplete T hi) b

lemma bex_intro! (φ : ⌜ℒₒᵣ⌝.Semiformula (0 + 1)) (n : V) {i}
    (hi : i < n) (b : T ⊢! φ ^/[(i : ⌜ℒₒᵣ⌝.Term).sing]) :
    T ⊢! φ.bex ↑n := ⟨bexIntro T φ n hi b.get⟩

end R₀Theory

end TProof

end Formalized

end LO.Arith

end
