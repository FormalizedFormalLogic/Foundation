import Foundation.FirstOrder.Basic.Syntax.Language

/-!
# Terms of first-order logic

This file defines the terms of first-order logic.

The bounded variables are denoted by `#x` for `x : Fin n`, and free variables are denoted by `&x` for `x : ξ`.
`t : Semiterm L ξ n` is a (semi-)term of language `L` with bounded variables of `Fin n` and free variables of `ξ`.

-/

namespace LO

namespace FirstOrder

inductive Semiterm (L : Language) (ξ : Type*) (n : ℕ)
  | bvar : Fin n → Semiterm L ξ n
  | fvar : ξ → Semiterm L ξ n
  | func : ∀ {arity}, L.Func arity → (Fin arity → Semiterm L ξ n) → Semiterm L ξ n

scoped prefix:max "&" => Semiterm.fvar
scoped prefix:max "#" => Semiterm.bvar

abbrev Term (L : Language) (ξ : Type*) := Semiterm L ξ 0

abbrev SyntacticSemiterm (L : Language) (n : ℕ) := Semiterm L ℕ n

abbrev SyntacticTerm (L : Language) := SyntacticSemiterm L 0

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

instance [Inhabited ξ] : Inhabited (Semiterm L ξ n) := ⟨&default⟩

section ToString

variable [∀ k, ToString (L.Func k)] [ToString ξ]

def toStr : Semiterm L ξ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "z_{" ++ toString x ++ "}"
  | func (arity := 0) c _     => toString c
  | func (arity := _ + 1) f v => "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"

instance : Repr (Semiterm L ξ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiterm L ξ n) := ⟨toStr⟩

end ToString

section Decidable

variable [∀ k, DecidableEq (L.Func k)] [DecidableEq ξ]

def hasDecEq : (t u : Semiterm L ξ n) → Decidable (Eq t u)
  | #x,                   #y                   => by simp; exact decEq x y
  | #_,                   &_                   => isFalse Semiterm.noConfusion
  | #_,                   func _ _             => isFalse Semiterm.noConfusion
  | &_,                   #_                   => isFalse Semiterm.noConfusion
  | &x,                   &y                   => by simp; exact decEq x y
  | &_,                   func _ _             => isFalse Semiterm.noConfusion
  | func _ _,             #_                   => isFalse Semiterm.noConfusion
  | func _ _,             &_                   => isFalse Semiterm.noConfusion
  | @func L ξ _ k₁ r₁ v₁, @func L ξ _ k₂ r₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq r₁ r₂ with
        | isTrue h => by simp[h]; exact Matrix.decVec _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (Semiterm L ξ n) := hasDecEq

end Decidable

abbrev func! (k) (f : L.Func k) (v : Fin k → Semiterm L ξ n) := func f v

def bv : Semiterm L ξ n → Finset (Fin n)
  | #x       => {x}
  | &_       => ∅
  | func _ v => .biUnion .univ fun i ↦ bv (v i)

@[simp] lemma bv_bvar : (#x : Semiterm L ξ n).bv = {x} := rfl

@[simp] lemma bv_fvar : (&x : Semiterm L ξ n).bv = ∅ := rfl

lemma bv_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) : (func f v).bv = .biUnion .univ fun i ↦ bv (v i) := rfl

@[simp] lemma bv_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).bv = ∅ := rfl

def Positive (t : Semiterm L ξ (n + 1)) : Prop := ∀ x ∈ t.bv, 0 < x

namespace Positive

@[simp] protected lemma bvar : Positive (#x : Semiterm L ξ (n + 1)) ↔ 0 < x := by simp[Positive]

@[simp] protected lemma fvar : Positive (&x : Semiterm L ξ (n + 1)) := by simp[Positive]

@[simp] protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ (n + 1)) :
    Positive (func f v) ↔ ∀ i, Positive (v i) := by simp[Positive, bv]; rw [forall_comm]

end Positive

lemma bv_eq_empty_of_positive {t : Semiterm L ξ 1} (ht : t.Positive) : t.bv = ∅ :=
  Finset.eq_empty_of_forall_not_mem <| by simp [Positive, Fin.eq_zero] at ht ⊢; assumption

variable [DecidableEq ξ]

def fv : Semiterm L ξ n → Finset ξ
  | #_       => ∅
  | &x       => {x}
  | func _ v => .biUnion .univ fun i ↦ fv (v i)

@[simp] lemma fv_bvar : (#x : Semiterm L ξ n).fv = ∅ := rfl

@[simp] lemma fv_fvar : (&x : Semiterm L ξ n).fv = {x} := rfl

lemma fv_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) : (func f v).fv = .biUnion .univ fun i ↦ fv (v i) := rfl

@[simp] lemma fv_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).fv = ∅ := rfl

def complexity : Semiterm L ξ n → ℕ
  | #_       => 0
  | &_       => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1

@[simp] lemma complexity_bvar (x : Fin n) : (#x : Semiterm L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_fvar (x : ξ) : (&x : Semiterm L ξ n).complexity = 0 := rfl

lemma complexity_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) : (func f v).complexity = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1 := rfl

@[simp] lemma complexity_func_lt {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).complexity < (func f v).complexity := by
  simp [complexity_func, Nat.lt_add_one_iff]; exact Finset.le_sup (f := fun i ↦ complexity (v i)) (by simp)

def fvarList : Semiterm L ξ n → List ξ
  | #_       => []
  | &x       => [x]
  | func _ v => List.join $ Matrix.toList (fun i => fvarList (v i))

abbrev fvar? (t : Semiterm L ξ n) (x : ξ) : Prop := x ∈ t.fvarList

@[simp] lemma fvarList_bvar : fvarList (#x : Semiterm L ξ n) = [] := rfl
@[simp] lemma fvarList_fvar : fvarList (&x : Semiterm L ξ n) = [x] := rfl
@[simp] lemma mem_fvarList_func {k} {f : L.Func k} {v : Fin k → Semiterm L ξ n} :
    x ∈ (func f v).fvarList ↔ ∃ i, x ∈ (v i).fvarList :=
  by simp[fvarList]
@[simp] lemma fvar?_bvar (x z) : ¬fvar? (#x : Semiterm L ξ n) z := by simp [fvar?]
@[simp] lemma fvar?_fvar (x z) : fvar? (&x : Semiterm L ξ n) z ↔ x = z := by simp [fvar?, Eq.comm]
@[simp] lemma fvar?_func (x) {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    fvar? (func f v) x ↔ ∃ i, fvar? (v i) x := by simp [fvar?]

@[simp] lemma fvarList_empty {o : Type*} [e : IsEmpty o] {t : Semiterm L o n} : fvarList t = [] := by
  induction t <;> simp[List.eq_nil_iff_forall_not_mem]
  case fvar x => exact IsEmpty.elim e x

@[simp] lemma fvarList_to_finset [DecidableEq ξ] (t : Semiterm L ξ n) : t.fvarList.toFinset = t.fv := by
  induction t <;> try simp [fvarList, fv_func]
  case func ih => ext x; simp [←ih]

section lMap

variable (Φ : L₁ →ᵥ L₂)

def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ ξ n → Semiterm L₂ ξ n
  | #x       => #x
  | &x       => &x
  | func f v => func (Φ.func f) (fun i => lMap Φ (v i))

@[simp] lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ ξ n).lMap Φ = #x := rfl

@[simp] lemma lMap_fvar (x : ξ) : (&x : Semiterm L₁ ξ n).lMap Φ = &x := rfl

lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) (fun i => lMap Φ (v i)) := rfl

@[simp] lemma lMap_positive (t : Semiterm L₁ ξ (n + 1)) : (t.lMap Φ).Positive ↔ t.Positive := by
  induction t <;> simp [lMap_func, *]

@[simp] lemma fvarList_lMap (Φ : L₁ →ᵥ L₂) (t : Semiterm L₁ ξ n) : fvarList (Semiterm.lMap Φ t) = fvarList t := by
  induction t <;> simp [fvarList, *]

end lMap

section fvEnum

variable [DecidableEq ξ] [Inhabited ξ]

def fvEnum (t : Semiterm L ξ n) : ξ → ℕ := t.fvarList.indexOf

def fvEnumInv (t : Semiterm L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < t.fvarList.length then t.fvarList.get ⟨i, hi⟩ else default

lemma fvEnumInv_fvEnum {t : Semiterm L ξ n} {x : ξ} (hx : x ∈ t.fvarList) :
    fvEnumInv t (fvEnum t x) = x := by
  simp [fvEnumInv, fvEnum]; intro h
  exact False.elim <| not_le.mpr (List.indexOf_lt_length.mpr $ hx) h

end fvEnum

section

variable [L.ConstantInhabited]

instance : Inhabited (Semiterm L ξ n) := ⟨func default ![]⟩

lemma default_def : (default : Semiterm L ξ n) = func default ![] := rfl

end

end Semiterm

end FirstOrder

end LO
