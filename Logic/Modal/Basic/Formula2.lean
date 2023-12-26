import Logic.Propositional.Basic.Formula
import Logic.Modal.LogicSymbol

namespace LO

namespace Modal

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | verum  : Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  | dia    : Formula α → Formula α

namespace Formula

variable {α : Type u}

def neg (p : Formula α) : Formula α := imp p falsum

instance : ModalLogicSymbol (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | p ⋏ q   => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | p ⋎ q   => "\\left(" ++ toStr p ++ " \\lor "  ++ toStr q ++ "\\right)"
  | p ⟶ q   => "\\left(" ++ toStr p ++ " \\to "   ++ toStr q ++ "\\right)"
  | box p      => "\\Box " ++ toStr p
  | dia p      => "\\Diamond " ++ toStr p

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

end ToString

lemma neg_eq (p : Formula α) : ~p = neg p := rfl

lemma iff_eq (p q : Formula α) : p ⟷ q = (p ⟶ q) ⋏ (q ⟶ p) := rfl

@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp[neg_eq, neg, *]

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Arrow.arrow]

@[simp] lemma box_inj (p q : Formula α) : □p = □q ↔ p = q := by simp[Box.box]

@[simp] lemma dia_inj (p q : Formula α) : ◇p = ◇q ↔ p = q := by simp[Dia.dia]
def complexity : Formula α → ℕ
| atom _  => 0
| ⊤       => 0
| ⊥       => 0
| p ⋏ q   => max p.complexity q.complexity + 1
| p ⋎ q   => max p.complexity q.complexity + 1
| p ⟶ q  => max p.complexity q.complexity + 1
| □p      => p.complexity + 1
| ◇p     => p.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Formula α) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl

@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

@[simp] lemma complexity_and (p q : Formula α) : complexity (p ⋏ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_and' (p q : Formula α) : complexity (and p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or (p q : Formula α) : complexity (p ⋎ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_or' (p q : Formula α) : complexity (or p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_imp (p q : Formula α) : complexity (p ⟶ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_imp' (p q : Formula α) : complexity (imp p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_box (p : Formula α) : complexity (□p) = p.complexity + 1 := rfl
@[simp] lemma complexity_box' (p : Formula α) : complexity (box p) = p.complexity + 1 := rfl

@[simp] lemma complexity_dia (p : Formula α) : complexity (◇p) = p.complexity + 1 := rfl
@[simp] lemma complexity_dia' (p : Formula α) : complexity (dia p) = p.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hverum  : C ⊤)
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hand    : ∀ (p q : Formula α), C (p ⋏ q))
    (hor     : ∀ (p q : Formula α), C (p ⋎ q))
    (himp    : ∀ (p q : Formula α), C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    (hdia    : ∀ (p : Formula α), C (◇p))
    : (p : Formula α) → C p
  | ⊤       => hverum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⋏ q   => hand p q
  | p ⋎ q   => hor p q
  | p ⟶ q  => himp p q
  | □p      => hbox p
  | ◇p     => hdia p

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (hand    : ∀ (p q : Formula α), C p → C q → C (p ⋏ q))
  (hor     : ∀ (p q : Formula α), C p → C q → C (p ⋎ q))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hbox    : ∀ (p : Formula α), C p → C (□p))
  (hdia    : ∀ (p : Formula α), C p → C (◇p))
  : (p : Formula α) → C p
  | ⊤       => hverum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⋏ q   => hand p q (rec' hverum hfalsum hatom hand hor himp hbox hdia p) (rec' hverum hfalsum hatom hand hor himp hbox hdia q)
  | p ⋎ q   => hor p q (rec' hverum hfalsum hatom hand hor himp hbox hdia p) (rec' hverum hfalsum hatom hand hor himp hbox hdia q)
  | p ⟶ q  => himp p q (rec' hverum hfalsum hatom hand hor himp hbox hdia p) (rec' hverum hfalsum hatom hand hor himp hbox hdia q)
  | □p      => hbox p (rec' hverum hfalsum hatom hand hor himp hbox hdia p)
  | ◇p     => hdia p (rec' hverum hfalsum hatom hand hor himp hbox hdia p)

-- @[simp] lemma complexity_neg (p : Formula α) : complexity (~p) = p.complexity + 1 :=
--   by induction p using rec' <;> try { simp[neg_eq, neg, *]; rfl;}

section Decidable

variable [DecidableEq α]

def hasDecEq : (p q : Formula α) → Decidable (p = q)
  | ⊤, q => by
    cases q using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | ⊥, q => by
    cases q using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    simp; exact decEq _ _
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
  | p ⟶ q, r => by
    cases r using cases' <;> try { simp; exact isFalse not_false }
    case himp p' q' =>
      exact match hasDecEq p p' with
      | isTrue hp =>
        match hasDecEq q q' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | □p, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    case hbox p' =>
      exact match hasDecEq p p' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse (by simp[hp])
  | ◇p, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    case hdia p' =>
      exact match hasDecEq p p' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse (by simp[hp])

end Decidable

end Formula

end Modal

end LO
