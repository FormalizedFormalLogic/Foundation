module

public import Foundation.FirstOrder.Completeness.Corollaries
public import Foundation.FirstOrder.Completeness.Corollaries
public import Mathlib.SetTheory.Cardinal.Basic

/-! # Preperations for theory of concatenation -/

@[expose] public section

namespace LO.FirstOrder

namespace Language

namespace concat

inductive Func : ℕ → Type
  | zero   : Func 0
  | one    : Func 0
  | concat : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2

end concat

/-- Language of concat theory -/
@[reducible]
def concat : Language where
  Func := concat.Func
  Rel := concat.Rel

notation "ℒ⌢" => Language.concat

namespace concat

instance (k) : DecidableEq (concat.Func k) := λ a b => by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (concat.Rel k) := λ a b => by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (concat.Func k) where
  encode := fun x =>
    match x with
    | .zero => 0
    | .one  => 1
    | .concat => 0
  decode := fun e =>
    match k, e with
    | 0, 0 => some .zero
    | 0, 1 => some .one
    | 2, 0 => some .concat
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance (k) : Encodable (concat.Rel k) where
  encode := fun x =>
    match x with
    | .eq => 0
  decode := fun e =>
    match k, e with
    | 2, 0 => some .eq
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance : (ℒ⌢).DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒ⌢).Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒ⌢).Zero := ⟨Func.zero⟩

instance : (ℒ⌢).One := ⟨Func.one⟩

instance : (ℒ⌢).Concat := ⟨Func.concat⟩

instance : (ℒ⌢).Eq := ⟨Rel.eq⟩

end concat

end Language

abbrev ConcatTheory := Theory ℒ⌢

abbrev ConcatTheorySemiterm := Semiterm ℒ⌢

variable [ToString ξ]

def ConcatTheorySemiterm.toString' : Semiterm ℒ⌢ ξ n→ String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "a_{" ++ toString x ++ "}"

end LO.FirstOrder
