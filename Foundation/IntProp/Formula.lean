import Foundation.Logic.LogicSymbol
import Foundation.Logic.HilbertStyle.Basic

namespace LO.IntProp

inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

abbrev neg {α : Type u} (φ : Formula α) : Formula α := imp φ falsum

abbrev verum {α : Type u} : Formula α := imp falsum falsum

instance : LogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : LO.NegAbbrev (Formula α) := by tauto;

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | ∼φ      => "\\lnot " ++ toStr φ
  | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | φ ➝ ψ   => "\\left(" ++ toStr φ ++ " \\rightarrow " ++ toStr ψ ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩
instance : ToString (Formula α) := ⟨toStr⟩

end ToString

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Arrow.arrow]

@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp[Tilde.tilde]


@[simp] lemma neg_def (φ : Formula α) : ∼φ = φ ➝ ⊥ := rfl

@[simp] lemma top_def : (⊤ : Formula α) = ⊥ ➝ ⊥ := rfl


lemma iff_def (φ ψ : Formula α) : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := by rfl

def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| φ ➝ ψ  => max φ.complexity ψ.complexity + 1
| φ ⋏ ψ   => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ   => max φ.complexity ψ.complexity + 1

@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl

@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

@[simp] lemma complexity_imp (φ ψ : Formula α) : complexity (φ ➝ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_imp' (φ ψ : Formula α) : complexity (imp φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_and (φ ψ : Formula α) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : Formula α) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : Formula α) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : Formula α) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp    : ∀ (φ ψ : Formula α), C (φ ➝ ψ))
    (hand    : ∀ (φ ψ : Formula α), C (φ ⋏ ψ))
    (hor     : ∀ (φ ψ : Formula α), C (φ ⋎ ψ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ ➝ ψ   => himp φ ψ
  | φ ⋏ ψ   => hand φ ψ
  | φ ⋎ ψ   => hor φ ψ

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ➝ ψ))
  (hand    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋏ ψ))
  (hor     : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋎ ψ))
  : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ ➝ ψ  => himp φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋏ ψ   => hand φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋎ ψ   => hor φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)

section Decidable

variable [DecidableEq α]

def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ)
  | ⊥, ψ => by
    cases ψ using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, ψ => by
    cases ψ using cases' <;> try { simp; exact isFalse not_false }
    simp; exact decEq _ _
  | φ ➝ ψ, χ => by
    cases χ using cases' <;> try { simp; exact isFalse not_false }
    case himp φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | φ ⋏ ψ, χ => by
    cases χ using cases' <;> try { simp; exact isFalse not_false }
    case hand φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | φ ⋎ ψ, χ => by
    cases χ using cases' <;> try { simp; exact isFalse not_false }
    case hor φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])

instance : DecidableEq (Formula α) := hasDecEq

end Decidable

section Encodable

variable [Encodable α]
open Encodable

def toNat : Formula α → ℕ
  | ⊥       => (Nat.pair 0 0) + 1
  | atom a  => (Nat.pair 1 <| encode a) + 1
  | φ ➝ ψ   => (Nat.pair 2 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋏ ψ   => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋎ ψ   => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1

def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => some ⊥
    | 1 => (decode c).map Formula.atom
    | 2 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ➝ ψ
    | 3 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ⋏ ψ
    | 4 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ⋎ ψ
    | _ => none

lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some'];
  | ⊥       => by simp [toNat, ofNat]
  | φ ➝ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | φ ⋏ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | φ ⋎ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end Encodable

end Formula


abbrev Theory (α : Type u) := Set (Formula α)

abbrev Context (α : Type u) := Finset (Formula α)

end LO.IntProp
