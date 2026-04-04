module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Typed
public import Mathlib.Combinatorics.Colex

@[expose] public section
open Encodable LO FirstOrder Arithmetic PeanoMinus Bootstrapping

namespace LO.FirstOrder.Semiterm

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (V) {n : ℕ}

noncomputable def typedQuote : SyntacticSemiterm L n → Bootstrapping.Semiterm V L n
  |       #x => Bootstrapping.Semiterm.bvar x
  |       &x => Bootstrapping.Semiterm.fvar x
  | func f v => Bootstrapping.Semiterm.func f fun i ↦ (v i).typedQuote

noncomputable instance : GödelQuote (SyntacticSemiterm L n) (Bootstrapping.Semiterm V L n) where
  quote := typedQuote V

variable {V}

@[simp] lemma typed_quote_bvar (x : Fin n) :
    (⌜(#x : SyntacticSemiterm L n)⌝ : Bootstrapping.Semiterm V L n) = Bootstrapping.Semiterm.bvar x := rfl

@[simp] lemma typed_quote_fvar (x : ℕ) :
    (⌜(&x : SyntacticSemiterm L n)⌝ : Bootstrapping.Semiterm V L n) = Bootstrapping.Semiterm.fvar ↑x := rfl

@[simp] lemma typed_quote_func (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : Bootstrapping.Semiterm V L n) = Bootstrapping.Semiterm.func f fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma typed_quote_shift (t : SyntacticSemiterm L n) :
    (⌜Rew.shift t⌝ : Bootstrapping.Semiterm V L n) = Bootstrapping.Semiterm.shift (⌜t⌝ : Bootstrapping.Semiterm V L n) := by
  induction t <;> simp [Rew.func, *]; rfl

@[simp] lemma typed_quote_bShift (t : SyntacticSemiterm L n) :
    (⌜Rew.bShift t⌝ : Bootstrapping.Semiterm V L (n + 1)) = Bootstrapping.Semiterm.bShift (⌜t⌝ : Bootstrapping.Semiterm V L n) := by
  induction t <;> simp [Rew.func, *]; rfl

@[simp] lemma typed_quote_substs {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) :
    (⌜Rew.subst w t⌝ : Bootstrapping.Semiterm V L m) = Bootstrapping.Semiterm.subst (fun i ↦ ⌜w i⌝) ⌜t⌝ := by
  induction t <;> simp [Rew.func, *]; rfl

open Bootstrapping.Arithmetic

@[simp] lemma typed_quote_add (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(‘!!t + !!u’ : SyntacticSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) = ⌜t⌝ + ⌜u⌝ := rfl

@[simp] lemma typed_quote_mul (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(‘!!t * !!u’ : SyntacticSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) = ⌜t⌝ * ⌜u⌝ := rfl

lemma typed_quote_numeral_eq_numeral_one :
    (⌜((1 : ℕ) : SyntacticSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) = typedNumeral 1 := by
  simp [Bootstrapping.Arithmetic.typedNumeral,
    Bootstrapping.Arithmetic.one, Bootstrapping.Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
  rfl

@[simp] lemma typed_quote_numeral_eq_numeral (k : ℕ) :
    (⌜(↑k : SyntacticSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) = typedNumeral ↑k := by
  match k with
  |         0 =>
    simp [Bootstrapping.Arithmetic.typedNumeral,
      Bootstrapping.Arithmetic.zero, Bootstrapping.Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
    rfl
  |         1 => simp [typed_quote_numeral_eq_numeral_one]
  | k + 1 + 1 =>
    calc (⌜(↑(k + 1 + 1) : SyntacticSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n)
      _ = ⌜(↑(k + 1) : SyntacticSemiterm ℒₒᵣ n)⌝ + ⌜((1 : ℕ) : SyntacticSemiterm ℒₒᵣ n)⌝ := rfl
      _ = typedNumeral ↑(k + 1) + typedNumeral 1 := by simp [typed_quote_numeral_eq_numeral (k + 1), typed_quote_numeral_eq_numeral_one]
      _ = typedNumeral (↑k + 1 + 1)              := by simp

lemma typed_quote_inj {t u : SyntacticSemiterm L n} : (⌜t⌝ : Bootstrapping.Semiterm V L n) = ⌜u⌝ → t = u :=
  match t, u with
  |         #x,         #y => by simp
  |         &x,         &y => by simp
  | func f₁ v₁, func f₂ v₂ => by
    simp only [typed_quote_func, Bootstrapping.Semiterm.func, Semiterm.mk.injEq, qqFunc_inj,
      Nat.cast_inj, func.injEq, and_imp]
    rintro rfl
    simp only [quote_func_inj, heq_eq_eq, true_and]
    rintro rfl
    suffices ((fun i ↦ ⌜v₁ i⌝) = fun i ↦ ⌜v₂ i⌝) → v₁ = v₂ by
      simpa [←SemitermVec.val_inj]
    intro h
    ext i
    exact typed_quote_inj (congr_fun h i)
  |         #_,         &_
  |         #_,   func _ _
  |         &_,         #_
  |         &_,   func _ _
  |   func _ _,         #_
  |   func _ _,         &_ => by simp [Bootstrapping.Semiterm.bvar, Bootstrapping.Semiterm.fvar, Bootstrapping.Semiterm.func, qqBvar, qqFvar, qqFunc]

@[simp] lemma typed_quote_inj_iff {t u : SyntacticSemiterm L n} :
    (⌜t⌝ : Bootstrapping.Semiterm V L n) = ⌜u⌝ ↔ t = u := ⟨typed_quote_inj, by rintro rfl; rfl⟩

noncomputable instance : GödelQuote (SyntacticSemiterm L n) V where
  quote t := (⌜t⌝ : Bootstrapping.Semiterm V L n).val

def quote_def (t : SyntacticSemiterm L n) : (⌜t⌝ : V) = (⌜t⌝ : Bootstrapping.Semiterm V L n).val := rfl

private lemma quote_eq_encode'_aux (v : Fin k → Semiterm L ℕ n)
    (H : ∀ i, (⌜v i⌝ : Bootstrapping.Semiterm V L n).val = encode ↑(v i)) :
    (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)) = ↑(Matrix.vecToNat fun i ↦ encode (v i)) := by
  induction k
  case zero => simp
  case succ k ih =>
    suffices
        (⌜v 0⌝ : Bootstrapping.Semiterm V L n).val = encode ↑(v 0) ∧
        SemitermVec.val (fun i ↦ ⌜v i.succ⌝) = ↑(Matrix.vecToNat fun i ↦ encode (v i.succ) : V) by
      simpa [Matrix.vecToNat, coe_pair_eq_pair_coe, adjoin_def, Matrix.vecHead, Matrix.vecTail, Function.comp_def]
    constructor
    · exact H 0
    · exact ih (fun i ↦ v i.succ) (fun i ↦ by simpa using H i.succ)

lemma quote_eq_encode (t : SyntacticSemiterm L n) : (⌜t⌝ : V) = ↑(encode t) := by
  match t with
  |       #x => simp [quote_def, encode_eq_toNat, toNat, qqBvar, coe_pair_eq_pair_coe]
  |       &x => simp [quote_def, encode_eq_toNat, toNat, qqFvar, coe_pair_eq_pair_coe]
  | func f v =>
    suffices (⌜f⌝ : V) = ↑(encode f) ∧ (SemitermVec.val (V := V) fun i ↦ ⌜v i⌝) = ↑(Matrix.vecToNat fun i ↦ encode (v i)) by
      simpa [quote_def, encode_eq_toNat, toNat, Bootstrapping.Semiterm.func, qqFunc, coe_pair_eq_pair_coe]
    constructor
    · rfl
    · exact quote_eq_encode'_aux _ fun i ↦ quote_eq_encode (v i)

lemma quote_eq_encode' (v : Fin k → Semiterm L ℕ n) :
    (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)) = ↑(Matrix.vecToNat fun i ↦ encode (v i)) :=
  quote_eq_encode'_aux _ fun i ↦ quote_eq_encode (v i)

lemma quote_eq_encode_standard (t : SyntacticSemiterm L n) : (⌜t⌝ : ℕ) = encode t := by simp [quote_eq_encode]

lemma coe_quote_eq_quote (t : SyntacticSemiterm L n) : (↑(⌜t⌝ : ℕ) : V) = ⌜t⌝ := by
  simp [quote_eq_encode]

lemma coe_quote_eq_quote' (t : SyntacticSemiterm L n) :
    (↑(⌜t⌝ : Bootstrapping.Semiterm ℕ L n).val : V) = (⌜t⌝ : Bootstrapping.Semiterm V L n).val :=
  coe_quote_eq_quote t

@[simp] lemma quote_bvar (x : Fin n) : (⌜(#x : SyntacticSemiterm L n)⌝ : V) = ^#↑x := rfl

@[simp] lemma quote_fvar (x : ℕ) : (⌜(&x : SyntacticSemiterm L n)⌝ : V) = ^&↑x := rfl

@[simp] lemma quote_func (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : V) = ^func ↑k ⌜f⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)) := rfl

variable (V)

noncomputable instance : GödelQuote (ClosedSemiterm L n) (Bootstrapping.Semiterm V L n) where
  quote t := ⌜(Rew.emb t : SyntacticSemiterm L n)⌝

variable {V}

def empty_typed_quote_def (t : ClosedSemiterm L n) :
    (⌜t⌝ : Bootstrapping.Semiterm V L n) = ⌜(Rew.emb t : SyntacticSemiterm L n)⌝ := rfl

@[simp] lemma empty_typed_quote_bvar (x : Fin n) :
    (⌜(#x : ClosedSemiterm L n)⌝ : Bootstrapping.Semiterm V L n) = Bootstrapping.Semiterm.bvar x := rfl

@[simp] lemma empty_typed_quote_func (f : L.Func k) (v : Fin k → ClosedSemiterm L n) :
    (⌜func f v⌝ : Bootstrapping.Semiterm V L n) = Bootstrapping.Semiterm.func f fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma empty_typed_quote_add (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(‘!!t + !!u’ : ClosedSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) = ⌜t⌝ + ⌜u⌝ := rfl

@[simp] lemma empty_typed_quote_mul (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) = ⌜t⌝ * ⌜u⌝ := rfl

@[simp] lemma empty_typed_quote_numeral_eq_numeral (k : ℕ) :
    (⌜(↑k : ClosedSemiterm ℒₒᵣ n)⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) = typedNumeral ↑k := by
  simp [empty_typed_quote_def]

noncomputable instance : GödelQuote (ClosedSemiterm L n) V where
  quote t := ⌜(Rew.emb t : SyntacticSemiterm L n)⌝

lemma empty_quote_def (t : ClosedSemiterm L n) : (⌜t⌝ : V) = ⌜(Rew.emb t : SyntacticSemiterm L n)⌝ := rfl

def empty_quote_eq (t : ClosedSemiterm L n) : (⌜t⌝ : V) = (⌜t⌝ : Bootstrapping.Semiterm V L n).val := rfl

lemma empty_quote_eq_encode (t : ClosedSemiterm L n) : (⌜t⌝ : V) = ↑(encode t) := by simp [empty_quote_def, quote_eq_encode]

@[simp] lemma coe_quote {ξ n} (t : SyntacticSemiterm L n) : ↑(⌜t⌝ : ℕ) = (⌜t⌝ : Semiterm ℒₒᵣ ξ m) := by
  simp [gödelNumber'_def, quote_eq_encode]

@[simp] lemma coe_empty_quote {ξ n} (t : ClosedSemiterm L n) : ↑(⌜t⌝ : ℕ) = (⌜t⌝ : Semiterm ℒₒᵣ ξ m) := by
  simp [gödelNumber'_def, empty_quote_eq_encode]

end LO.FirstOrder.Semiterm

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open Encodable FirstOrder

set_option backward.isDefEq.respectTransparency false in
lemma mem_iff_mem_bitIndices {x s : ℕ} : x ∈ s ↔ x ∈ s.bitIndices := by
  induction s using Nat.binaryRec generalizing x
  case zero => simp
  case bit b s ih =>
    cases b <;> simp
    · cases' x with x <;> simp [ih]
    · cases' x with x <;> simp [ih]

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma IsSemiterm.sound {n t : ℕ} (ht : IsSemiterm L n t) : ∃ T : FirstOrder.SyntacticSemiterm L n, ⌜T⌝ = t := by
  induction t using Nat.strongRec
  case ind t ih =>
    rcases ht.case with (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
    · exact ⟨#⟨z, hz⟩, by simp⟩
    · exact ⟨&x, by simp [Semiterm.quote_fvar]⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦
        ih v.[i] (nth_lt_qqFunc_of_lt (by simp [hv.lh])) (hv.nth i.prop)
      choose v' hv' using this
      have : ∃ F, encode F = f := isFunc_quote_quote (V := ℕ) (L := L) (x := f) (k := k) |>.mp (by simp [hf])
      rcases this with ⟨f, rfl⟩
      refine ⟨FirstOrder.Semiterm.func f v', ?_⟩
      suffices SemitermVec.val (fun i ↦ ⌜v' i⌝) = v by simpa [Semiterm.quote_func, quote_func_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        (SemitermVec.val fun i ↦ ⌜v' i⌝).[i] = (SemitermVec.val fun i ↦ ⌜v' i⌝).[↑j] := rfl
        _                                    = ⌜v' j⌝ := by
          simpa [Semiterm.quote_def] using SemitermVec.val_nth_eq (fun i ↦ (⌜v' i⌝ : Bootstrapping.Semiterm ℕ L n)) j
        _                                    = v.[i] := hv' j

end LO.FirstOrder.Arithmetic.Bootstrapping
