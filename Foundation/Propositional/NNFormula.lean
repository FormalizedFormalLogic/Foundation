import Foundation.Logic.LogicSymbol
import Foundation.Vorspiel.Collection

namespace LO.Propositional

inductive NNFormula (α : Type u) : Type u where
  | verum  : NNFormula α
  | falsum : NNFormula α
  | atom   : α → NNFormula α
  | natom  : α → NNFormula α
  | and    : NNFormula α → NNFormula α → NNFormula α
  | or     : NNFormula α → NNFormula α → NNFormula α

namespace NNFormula

variable {α : Type u} {α₁ : Type u₁} {α₂ : Type u₂} {α₃ : Type u₃}

def neg : NNFormula α → NNFormula α
  | verum   => falsum
  | falsum  => verum
  | atom a  => natom a
  | natom a => atom a
  | and φ ψ => or (neg φ) (neg ψ)
  | or φ ψ  => and (neg φ) (neg ψ)

lemma neg_neg (φ : NNFormula α) : neg (neg φ) = φ :=
  by induction φ <;> simp [*, neg]

instance : LogicalConnective (NNFormula α) where
  tilde := neg
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  top := verum
  bot := falsum

section ToString

variable [ToString α]

def toStr : NNFormula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | natom a => "\\lnot {" ++ toString a ++ "}"
  | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"

instance : Repr (NNFormula α) := ⟨fun t _ => toStr t⟩

instance : ToString (NNFormula α) := ⟨toStr⟩

end ToString

@[simp] lemma neg_top : ∼(⊤ : NNFormula α) = ⊥ := rfl

@[simp] lemma neg_bot : ∼(⊥ : NNFormula α) = ⊤ := rfl

@[simp] lemma neg_atom (a : α) : ∼(atom a) = natom a := rfl

@[simp] lemma neg_natom (a : α) : ∼(natom a) = atom a := rfl

@[simp] lemma neg_and (φ ψ : NNFormula α) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl

@[simp] lemma neg_or (φ ψ : NNFormula α) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl

@[simp] lemma neg_neg' (φ : NNFormula α) : ∼∼φ = φ := neg_neg φ

@[simp] lemma neg_inj (φ ψ : NNFormula α) : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _

lemma neg_eq (φ : NNFormula α) : ∼φ = neg φ := rfl

lemma imp_eq (φ ψ : NNFormula α) : φ ➝ ψ = ∼φ ⋎ ψ := rfl

lemma iff_eq (φ ψ : NNFormula α) : φ ⭤ ψ = (∼φ ⋎ ψ) ⋏ (∼ψ ⋎ φ) := rfl

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : NNFormula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
by simp [Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : NNFormula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
by simp [Vee.vee]

instance : DeMorgan (NNFormula α) where
  verum := rfl
  falsum := rfl
  and := by simp
  or := by simp
  imply := by simp [imp_eq]
  neg := by simp

def complexity : NNFormula α → ℕ
| ⊤       => 0
| ⊥       => 0
| atom _  => 0
| natom _ => 0
| φ ⋏ ψ   => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ   => max φ.complexity ψ.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : NNFormula α) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : NNFormula α) = 0 := rfl

@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

@[simp] lemma complexity_natom (a : α) : complexity (natom a) = 0 := rfl

@[simp] lemma complexity_and (φ ψ : NNFormula α) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : NNFormula α) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : NNFormula α) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : NNFormula α) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : NNFormula α → Sort w}
    (hverum  : C ⊤)
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hnatom  : ∀ a : α, C (natom a))
    (hand    : ∀ (φ ψ : NNFormula α), C (φ ⋏ ψ))
    (hor     : ∀ (φ ψ : NNFormula α), C (φ ⋎ ψ)) : (φ : NNFormula α) → C φ
  | ⊤       => hverum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | natom a => hnatom a
  | φ ⋏ ψ   => hand φ ψ
  | φ ⋎ ψ   => hor φ ψ

@[elab_as_elim]
def rec' {C : NNFormula α → Sort w}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (hnatom  : ∀ a : α, C (natom a))
  (hand    : ∀ (φ ψ : NNFormula α), C φ → C ψ → C (φ ⋏ ψ))
  (hor     : ∀ (φ ψ : NNFormula α), C φ → C ψ → C (φ ⋎ ψ)) : (φ : NNFormula α) → C φ
  | ⊤       => hverum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | natom a => hnatom a
  | φ ⋏ ψ   => hand φ ψ (rec' hverum hfalsum hatom hnatom hand hor φ) (rec' hverum hfalsum hatom hnatom hand hor ψ)
  | φ ⋎ ψ   => hor φ ψ (rec' hverum hfalsum hatom hnatom hand hor φ) (rec' hverum hfalsum hatom hnatom hand hor ψ)

@[simp] lemma complexity_neg (φ : NNFormula α) : complexity (∼φ) = complexity φ :=
  by induction φ using rec' <;> simp [*]

section Decidable

variable [DecidableEq α]

def hasDecEq : (φ ψ : NNFormula α) → Decidable (φ = ψ)
  | ⊤,       ψ => by cases ψ using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | ⊥,       ψ => by cases ψ using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a,  ψ => by
      cases ψ using cases' <;> try { simp; exact isFalse not_false }
      simp; exact decEq _ _
  | natom a, ψ => by
      cases ψ using cases' <;> try { simp; exact isFalse not_false }
      simp; exact decEq _ _
  | φ ⋏ ψ,   χ => by
      cases χ using cases' <;> try { simp; exact isFalse not_false }
      case hand φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | φ ⋎ ψ,   χ => by
      cases χ using cases' <;> try { simp; exact isFalse not_false }
      case hor φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])

instance : DecidableEq (NNFormula α) := hasDecEq

end Decidable

lemma ne_of_ne_complexity {φ ψ : NNFormula α} (h : φ.complexity ≠ ψ.complexity) : φ ≠ ψ :=
  by rintro rfl; contradiction

end NNFormula


abbrev Theory (α : Type*) := Set (NNFormula α)

instance : Collection (NNFormula α) (Theory α) := inferInstance


end LO.Propositional
