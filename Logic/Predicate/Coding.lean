import Logic.Predicate.Term
import Mathlib.Data.W.Basic

variable {L : Language} [∀ k, Encodable (L.func k)] {μ : Type _} [Encodable μ]

namespace SubTerm
open Encodable
variable (L) (μ) (n : ℕ)

private def Label := Fin n ⊕ μ ⊕ Σ n, L.func n

@[reducible]
def LabelType : Label L μ n → Type
  | Sum.inl _                => Empty
  | Sum.inr $ Sum.inl _      => Empty
  | Sum.inr $ Sum.inr ⟨k, _⟩ => Fin k

variable {L μ n}

@[reducible] def ofW : WType (LabelType L μ n) → SubTerm L μ n
  | ⟨Sum.inl x,                _⟩ => #x
  | ⟨Sum.inr $ Sum.inl x,      _⟩ => &x
  | ⟨Sum.inr $ Sum.inr ⟨_, f⟩, F⟩ => func f (fun x => ofW (F x))

def toW : SubTerm L μ n → WType (LabelType L μ n)
  | #x         => ⟨Sum.inl x, Empty.rec⟩
  | &x         => ⟨Sum.inr $ Sum.inl x, Empty.rec⟩
  | (func f v) => ⟨Sum.inr $ Sum.inr ⟨_, f⟩, fun i => toW (v i)⟩

def equivW : SubTerm L μ n ≃ WType (LabelType L μ n) where
  toFun     := toW
  invFun    := ofW
  left_inv  := by intros t; induction t <;> simp[*, toW]
  right_inv := by
    intros w; induction' w with l F ih
    rcases l with (n | b | ⟨k, f⟩) <;> simp[*, ofW, toW]

instance : ∀ t, Fintype (LabelType L μ n t)
  | Sum.inl _                => Fintype.ofIsEmpty
  | Sum.inr $ Sum.inl _      => Fintype.ofIsEmpty
  | Sum.inr $ Sum.inr ⟨k, _⟩ => Fin.fintype k

instance : ∀ t, Encodable (LabelType L μ n t)
  | Sum.inl _                => IsEmpty.toEncodable
  | Sum.inr $ Sum.inl _      => IsEmpty.toEncodable
  | Sum.inr $ Sum.inr ⟨k, _⟩ => Fin.encodable k

instance : Encodable (Label L μ n) := Sum.encodable

instance : Encodable (SubTerm L μ n) := Encodable.ofEquiv _ equivW

end SubTerm


