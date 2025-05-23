import Foundation.Logic.Predicate.Language

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

def hasDecEq : (t u : Semiterm L ξ n) → Decidable (t = u)
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
        |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ hasDecEq (v₁ i) (v₂ i)
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (Semiterm L ξ n) := hasDecEq

end Decidable

def complexity : Semiterm L ξ n → ℕ
  | #_       => 0
  | &_       => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1

@[simp] lemma complexity_bvar (x : Fin n) : (#x : Semiterm L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_fvar (x : ξ) : (&x : Semiterm L ξ n).complexity = 0 := rfl

lemma complexity_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) : (func f v).complexity = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1 := rfl

@[simp] lemma complexity_func_lt {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).complexity < (func f v).complexity := by
  simpa [complexity_func, Nat.lt_add_one_iff] using Finset.le_sup (f := fun i ↦ complexity (v i)) (by simp)

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

instance Positive.dec : (t : Semiterm L ξ (n + 1)) → Decidable t.Positive
  |        #x => decidable_of_iff (0 < x) (by simp)
  |        &x => .isTrue (by simp)
  | .func f v =>
    have : DecidablePred fun i ↦ (v i).Positive := fun i ↦ Positive.dec (v i)
    have : Decidable (∀ i, (v i).Positive) := inferInstance
    decidable_of_iff (∀ i, (v i).Positive) (by simp)

section freeVariables

variable [DecidableEq ξ]

def freeVariables : Semiterm L ξ n → Finset ξ
  | #_       => ∅
  | &x       => {x}
  | func _ v => .biUnion .univ fun i ↦ freeVariables (v i)

@[simp] lemma freeVariables_bvar : (#x : Semiterm L ξ n).freeVariables = ∅ := rfl

@[simp] lemma freeVariables_fvar : (&x : Semiterm L ξ n).freeVariables = {x} := rfl

lemma freeVariables_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

@[simp] lemma freeVariables_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).freeVariables = ∅ := rfl

@[simp] lemma freeVariables_empty {ο : Type*} [IsEmpty ο] {t : Semiterm L ο n} : t.freeVariables = ∅ := by
  ext x; exact IsEmpty.elim inferInstance x

abbrev FVar? (t : Semiterm L ξ n) (x : ξ) : Prop := x ∈ t.freeVariables

@[simp] lemma fvar?_bvar (x z) : ¬(#x : Semiterm L ξ n).FVar? z := by simp [FVar?]

@[simp] lemma fvar?_fvar (x z) : (&x : Semiterm L ξ n).FVar? z ↔ x = z := by simp [FVar?, Eq.comm]

@[simp] lemma fvar?_func (x) {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_func]

end freeVariables

section lMap

variable (Φ : L₁ →ᵥ L₂)

def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ ξ n → Semiterm L₂ ξ n
  | #x       => #x
  | &x       => &x
  | func f v => func (Φ.func f) (fun i => lMap Φ (v i))

@[simp] lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ ξ n).lMap Φ = #x := rfl

@[simp] lemma lMap_fvar (x : ξ) : (&x : Semiterm L₁ ξ n).lMap Φ = &x := rfl

lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) (fun i ↦ lMap Φ (v i)) := rfl

@[simp] lemma lMap_positive (t : Semiterm L₁ ξ (n + 1)) : (t.lMap Φ).Positive ↔ t.Positive := by
  induction t <;> simp [lMap_func, *]

@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (t : Semiterm L₁ ξ n) :
    (Semiterm.lMap Φ t).freeVariables = t.freeVariables := by
  induction t
  case bvar => simp
  case fvar => simp
  case func k f v ih =>
    ext x; simp [lMap_func, freeVariables_func, ih]

end lMap

section

variable [L.ConstantInhabited]

instance : Inhabited (Semiterm L ξ n) := ⟨func default ![]⟩

lemma default_def : (default : Semiterm L ξ n) = func default ![] := rfl

end

end Semiterm

end FirstOrder

end LO
