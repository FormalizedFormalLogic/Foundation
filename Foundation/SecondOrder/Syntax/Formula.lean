module

public import Foundation.FirstOrder.Basic

@[expose] public section

/-!
# Formulas of monadic second-order logic
-/

namespace LO.SecondOrder

open FirstOrder

inductive Semiformula (L : Language) (ζ ξ : Type*) : ℕ → ℕ → Type _ where
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ζ ξ m n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ζ ξ m n
  |   bvar : Fin m → Semiterm L ξ n → Semiformula L ζ ξ m n
  |  nbvar : Fin m → Semiterm L ξ n → Semiformula L ζ ξ m n
  |   fvar : ζ → Semiterm L ξ n → Semiformula L ζ ξ m n
  |  nfvar : ζ → Semiterm L ξ n → Semiformula L ζ ξ m n
  |  verum : Semiformula L ζ ξ m n
  | falsum : Semiformula L ζ ξ m n
  |    and : Semiformula L ζ ξ m n → Semiformula L ζ ξ m n → Semiformula L ζ ξ m n
  |     or : Semiformula L ζ ξ m n → Semiformula L ζ ξ m n → Semiformula L ζ ξ m n
  |   all₀ : Semiformula L ζ ξ m (n + 1) → Semiformula L ζ ξ m n
  |   exs₀ : Semiformula L ζ ξ m (n + 1) → Semiformula L ζ ξ m n
  |   all₁ : Semiformula L ζ ξ (m + 1) n → Semiformula L ζ ξ m n
  |   exs₁ : Semiformula L ζ ξ (m + 1) n → Semiformula L ζ ξ m n

abbrev Formula (L : Language) (ζ ξ : Type*) := Semiformula L ζ ξ 0 0

abbrev Semisentence (L : Language) (n m : ℕ) := Semiformula L Empty Empty n m

abbrev Sentence (L : Language) := Semiformula L Empty Empty 0 0

abbrev Semistatement (L : Language) (n m : ℕ) := Semiformula L ℕ ℕ n m

abbrev Statement (L : Language) := Semiformula L ℕ ℕ 0 0

namespace Semiformula

variable {L : Language} {ζ ξ : Type*}

instance : Top (Semiformula L ζ ξ n m) := ⟨verum⟩

instance : Bot (Semiformula L ζ ξ n m) := ⟨falsum⟩

instance : Wedge (Semiformula L ζ ξ n m) := ⟨and⟩

instance : Vee (Semiformula L ζ ξ n m) := ⟨or⟩

instance : FirstOrder.Quantifier (Semiformula L ζ ξ n) where
  all := all₀
  exs := exs₀

instance : SecondOrder.Quantifier (Semiformula L ζ ξ) where
  all₁ := all₁
  exs₁ := exs₁

scoped notation:80 t " ∈# " X => Semiformula.bvar X t
scoped notation:80 t " ∉# " X => Semiformula.nbvar X t
scoped notation:80 t " ∈& " X => Semiformula.fvar X t
scoped notation:80 t " ∉& " X => Semiformula.nfvar X t

def neg : Semiformula L ζ ξ n m → Semiformula L ζ ξ n m
  |  rel R v => nrel R v
  | nrel R v => rel R v
  |   t ∈# X => t ∉# X
  |   t ∉# X => t ∈# X
  |   t ∈& X => t ∉& X
  |   t ∉& X => t ∈& X
  |        ⊤ => ⊥
  |        ⊥ => ⊤
  |    φ ⋏ ψ => φ.neg ⋎ ψ.neg
  |    φ ⋎ ψ => φ.neg ⋏ ψ.neg
  |     ∀⁰ φ => ∃⁰ φ.neg
  |     ∃⁰ φ => ∀⁰ φ.neg
  |     ∀¹ φ => ∃¹ φ.neg
  |     ∃¹ φ => ∀¹ φ.neg

instance : Tilde (Semiformula L ζ ξ n m) := ⟨neg⟩

instance : LogicalConnective (Semiformula L ζ ξ n m) where
  arrow φ ψ := ∼φ ⋎ ψ

instance : DeMorgan (Semiformula L ζ ξ n m) where
  verum := rfl
  falsum := rfl
  and _ _ := rfl
  or _ _ := rfl
  imply _ _ := rfl

@[simp] lemma neg_rel (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ∼(rel R v : Semiformula L ζ ξ m n) = nrel R v := rfl

@[simp] lemma neg_nrel (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ∼(nrel R v : Semiformula L ζ ξ m n) = rel R v := rfl

@[simp] lemma neg_bvar (X : Fin m) (t : Semiterm L ξ n) :
    ∼(t ∈# X : Semiformula L ζ ξ m n) = t ∉# X := rfl

@[simp] lemma neg_nbvar (X : Fin m) (t : Semiterm L ξ n) :
    ∼(t ∉# X : Semiformula L ζ ξ m n) = t ∈# X := rfl

@[simp] lemma neg_fvar (X : ζ) (t : Semiterm L ξ n) :
    ∼(t ∈& X : Semiformula L ζ ξ m n) = t ∉& X := rfl

@[simp] lemma neg_nfvar (X : ζ) (t : Semiterm L ξ n) :
    ∼(t ∉& X : Semiformula L ζ ξ m n) = t ∈& X := rfl

@[simp] lemma neg_all₀ (φ : Semiformula L ζ ξ m (n + 1)) :
    ∼(∀⁰ φ : Semiformula L ζ ξ m n) = ∃⁰ ∼φ := rfl

@[simp] lemma neg_exs₀ (φ : Semiformula L ζ ξ m (n + 1)) :
    ∼(∃⁰ φ : Semiformula L ζ ξ m n) = ∀⁰ ∼φ := rfl

@[simp] lemma neg_all₁ (φ : Semiformula L ζ ξ (m + 1) n) :
    ∼(∀¹ φ : Semiformula L ζ ξ m n) = ∃¹ ∼φ := rfl

@[simp] lemma neg_exs₁ (φ : Semiformula L ζ ξ (m + 1) n) :
    ∼(∃¹ φ : Semiformula L ζ ξ m n) = ∀¹ ∼φ := rfl

lemma neg_neg (φ : Semiformula L ζ ξ n m) : ∼∼φ = φ :=
  match φ with
  |  rel R v => rfl
  | nrel R v => rfl
  |   t ∈# X => rfl
  |   t ∉# X => rfl
  |   t ∈& X => rfl
  |   t ∉& X => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ => by simp [neg_neg φ, neg_neg ψ]
  |    φ ⋎ ψ => by simp [neg_neg φ, neg_neg ψ]
  |     ∀⁰ φ => by simp [neg_neg φ]
  |     ∃⁰ φ => by simp [neg_neg φ]
  |     ∀¹ φ => by simp [neg_neg φ]
  |     ∃¹ φ => by simp [neg_neg φ]

instance : NegInvolutive (Semiformula L ζ ξ n m) := ⟨neg_neg⟩

end Semiformula

end SecondOrder

end LO
