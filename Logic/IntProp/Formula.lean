import Logic.Logic.LogicSymbol
import Logic.Logic.HilbertStyle.Basic

namespace LO.IntProp

inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | verum  : Formula α
  | falsum : Formula α
  | neg    : Formula α → Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

instance : LogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | ~p      => "\\lnot " ++ toStr p
  | p ⋏ q   => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | p ⋎ q   => "\\left(" ++ toStr p ++ " \\lor "  ++ toStr q ++ "\\right)"
  | p ➝ q   => "\\left(" ++ toStr p ++ " \\rightarrow " ++ toStr q ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩
instance : ToString (Formula α) := ⟨toStr⟩

end ToString

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Wedge.wedge]
@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Vee.vee]
@[simp] lemma imp_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ➝ p₂ = q₁ ➝ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Arrow.arrow]
@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp[Tilde.tilde]

-- lemma neg_def (p : Formula α) : ~p = p ➝ ⊥ := rfl

lemma iff_def (p q : Formula α) : p ⭤ q = (p ➝ q) ⋏ (q ➝ p) := by rfl

def complexity : Formula α → ℕ
| atom _  => 0
| ⊤       => 0
| ⊥       => 0
| ~p      => p.complexity + 1
| p ➝ q  => max p.complexity q.complexity + 1
| p ⋏ q   => max p.complexity q.complexity + 1
| p ⋎ q   => max p.complexity q.complexity + 1

@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl
@[simp] lemma complexity_top : complexity (⊤ : Formula α) = 0 := rfl

@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

@[simp] lemma complexity_imp (p q : Formula α) : complexity (p ➝ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_imp' (p q : Formula α) : complexity (imp p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_and (p q : Formula α) : complexity (p ⋏ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_and' (p q : Formula α) : complexity (and p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or (p q : Formula α) : complexity (p ⋎ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_or' (p q : Formula α) : complexity (or p q) = max p.complexity q.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hverum  : C ⊤)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (~p))
    (himp    : ∀ (p q : Formula α), C (p ➝ q))
    (hand    : ∀ (p q : Formula α), C (p ⋏ q))
    (hor     : ∀ (p q : Formula α), C (p ⋎ q))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | ⊤       => hverum
  | atom a  => hatom a
  | ~p      => hneg p
  | p ➝ q  => himp p q
  | p ⋏ q   => hand p q
  | p ⋎ q   => hor p q

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hverum  : C ⊤)
  (hatom   : ∀ a : α, C (atom a))
  (hneg    : ∀ p : Formula α, C p → C (~p))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ➝ q))
  (hand    : ∀ (p q : Formula α), C p → C q → C (p ⋏ q))
  (hor     : ∀ (p q : Formula α), C p → C q → C (p ⋎ q))
  : (p : Formula α) → C p
  | ⊥       => hfalsum
  | ⊤       => hverum
  | atom a  => hatom a
  | ~p      => hneg p (rec' hfalsum hverum hatom hneg himp hand hor p)
  | p ➝ q  => himp p q (rec' hfalsum hverum hatom hneg himp hand hor p) (rec' hfalsum hverum hatom hneg himp hand hor q)
  | p ⋏ q   => hand p q (rec' hfalsum hverum hatom hneg himp hand hor p) (rec' hfalsum hverum hatom hneg himp hand hor q)
  | p ⋎ q   => hor p q (rec' hfalsum hverum hatom hneg himp hand hor p) (rec' hfalsum hverum hatom hneg himp hand hor q)

section Decidable

variable [DecidableEq α]

def hasDecEq : (p q : Formula α) → Decidable (p = q)
  | ⊥, q => by
    cases q using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | ⊤, q => by
    cases q using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    simp; exact decEq _ _
  | ~p, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    case hneg p' =>
      exact match hasDecEq p p' with
      | isTrue hp  => isTrue (by simp[hp])
      | isFalse hp => isFalse (by simp[hp])
  | p ➝ q, r => by
    cases r using cases' <;> try { simp; exact isFalse not_false }
    case himp p' q' =>
      exact match hasDecEq p p' with
      | isTrue hp =>
        match hasDecEq q q' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | p ⋏ q, r => by
    cases r using cases' <;> try { simp; exact isFalse not_false }
    case hand p' q' =>
      exact match hasDecEq p p' with
      | isTrue hp =>
        match hasDecEq q q' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | p ⋎ q, r => by
    cases r using cases' <;> try { simp; exact isFalse not_false }
    case hor p' q' =>
      exact match hasDecEq p p' with
      | isTrue hp =>
        match hasDecEq q q' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])

instance : DecidableEq (Formula α) := hasDecEq

end Decidable

section Encodable

variable [Encodable α]
open Encodable

def toNat : Formula α → ℕ
  | atom a  => (Nat.pair 0 <| encode a) + 1
  | ⊤       => (Nat.pair 1 0) + 1
  | ⊥       => (Nat.pair 2 0) + 1
  | ~p      => (Nat.pair 3 <| p.toNat) + 1
  | p ➝ q   => (Nat.pair 4 <| p.toNat.pair q.toNat) + 1
  | p ⋏ q   => (Nat.pair 5 <| p.toNat.pair q.toNat) + 1
  | p ⋎ q   => (Nat.pair 6 <| p.toNat.pair q.toNat) + 1

def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => (decode c).map Formula.atom
    | 1 => some ⊤
    | 2 => some ⊥
    | 3 =>
      have : c < e + 1 := Nat.lt_succ.mpr $ Nat.unpair_right_le _
      do
        let p <- ofNat c
        return ~p
    | 4 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let p <- ofNat c.unpair.1
        let q <- ofNat c.unpair.2
        return p ➝ q
    | 5 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let p <- ofNat c.unpair.1
        let q <- ofNat c.unpair.2
        return p ⋏ q
    | 6 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let p <- ofNat c.unpair.1
        let q <- ofNat c.unpair.2
        return p ⋎ q
    | _ => none

lemma ofNat_toNat : ∀ (p : Formula α), ofNat (toNat p) = some p
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some'];
  | ⊤       => by simp [toNat, ofNat]
  | ⊥       => by simp [toNat, ofNat]
  | ~p      => by simp [toNat, ofNat, ofNat_toNat p]
  | p ➝ q   => by simp [toNat, ofNat, ofNat_toNat p, ofNat_toNat q]
  | p ⋏ q   => by simp [toNat, ofNat, ofNat_toNat p, ofNat_toNat q]
  | p ⋎ q   => by simp [toNat, ofNat, ofNat_toNat p, ofNat_toNat q]

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end Encodable

end Formula


abbrev Theory (α : Type u) := Set (Formula α)

abbrev Context (α : Type u) := Finset (Formula α)

end LO.IntProp
