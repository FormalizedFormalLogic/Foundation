import Logic.Propositional.Basic.Formula
import Logic.Modal.LogicSymbol

namespace LO

namespace Modal

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α

namespace Formula

variable {α : Type u}

@[simp] def neg (p : Formula α) : Formula α := imp p falsum

@[simp] def verum : Formula α := neg falsum

@[simp] def or (p q : Formula α) : Formula α := imp (neg p) (q)

@[simp] def and (p q : Formula α) : Formula α := neg (imp p (neg q))

@[simp] def dia (p : Formula α) : Formula α := neg (box (neg p))

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
  | ◇p     => "\\Diamond " ++ toStr p
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | p ⟶ q   => "\\left(" ++ toStr p ++ " \\to "   ++ toStr q ++ "\\right)"
  | □p      => "\\Box " ++ toStr p

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

end ToString

@[simp] lemma or_eq (p q : Formula α) : p ⋎ q = or p q := rfl

@[simp] lemma and_eq (p q : Formula α) : p ⋏ q = and p q := rfl

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
| ⊥       => 0
| p ⟶ q  => max p.complexity q.complexity + 1
| □p      => p.complexity + 1

@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl

@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

@[simp] lemma complexity_imp (p q : Formula α) : complexity (p ⟶ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_imp' (p q : Formula α) : complexity (imp p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_box (p : Formula α) : complexity (□p) = p.complexity + 1 := rfl
@[simp] lemma complexity_box' (p : Formula α) : complexity (box p) = p.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp    : ∀ (p q : Formula α), C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⟶ q  => himp p q
  | □p      => hbox p

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hbox    : ∀ (p : Formula α), C p → C (□p))
  : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⟶ q  => himp p q (rec' hfalsum hatom himp hbox p) (rec' hfalsum hatom himp hbox q)
  | □p      => hbox p (rec' hfalsum hatom himp hbox p)

-- @[simp] lemma complexity_neg (p : Formula α) : complexity (~p) = p.complexity + 1 :=
--   by induction p using rec' <;> try { simp[neg_eq, neg, *]; rfl;}

section Decidable

variable [DecidableEq α]

def hasDecEq : (p q : Formula α) → Decidable (p = q)
  | ⊥, q => by
    cases q using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    simp; exact decEq _ _
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

end Decidable

def multibox (p : Formula α) : ℕ → Formula α
  | 0     => p
  | n + 1 => □(multibox p n)

notation "□^" n:90 p => multibox p n

def multidia (p : Formula α) : ℕ → Formula α
  | 0     => p
  | n + 1 => ◇(multidia p n)

notation "◇^" n:90 p => multidia p n

section Geach

/-- `◇ᵏ□ˡp ⟶ □ᵐ◇ⁿq`   -/
def Geach' (p q : Formula α) : (k : ℕ) → (l : ℕ) → (m : ℕ) → (n : ℕ) → Formula α
  | 0,     0,     0,     0     => p ⟶ q
  | 0,     0,     m + 1, 0     => Geach' p (□q) 0 0 m 0
  | 0,     0,     m,     n + 1 => Geach' p (◇q) 0 0 m n
  | k + 1, 0,     m,     n     => Geach' (◇p) q k 0 m n
  | k,     l + 1, m,     n     => Geach' (□p) q k l m n

def Geach (p: Formula α) := Geach' p p

variable (p : Formula α)

abbrev axiomT := □p ⟶ p
lemma axiomT_def : axiomT p = Geach p 0 1 0 0 := rfl

abbrev axiomB := p ⟶ □◇p
lemma axiomB_def : axiomB p = Geach p 0 0 1 1 := rfl

abbrev axiomD := □p ⟶ ◇p
lemma axiomD_def : axiomD p = Geach p 0 1 0 1 := rfl

abbrev axiom4 := □p ⟶ □□p
lemma axiom4_def : axiom4 p = Geach p 0 1 2 0 := rfl

abbrev axiom5 := ◇p ⟶ □◇p
lemma axiom5_def : axiom5 p = Geach p 1 0 1 1 := rfl

abbrev axiomDot2 := ◇□p ⟶ □◇p
lemma axiomDot2_def : axiomDot2 p = Geach p 1 1 1 1 := rfl

abbrev axiomCD := ◇p ⟶ □p
lemma axiomCD_def : axiomCD p = Geach p 1 0 1 0 := rfl

abbrev axiomC4 := □□p ⟶ □p
lemma axiomC4_def : axiomC4 p = Geach p 0 2 1 0 := rfl

end Geach

end Formula

end Modal

end LO
