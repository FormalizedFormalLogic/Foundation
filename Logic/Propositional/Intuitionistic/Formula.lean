import Logic.Logic.LogicSymbol

namespace LO.Propositional.Intuitionistic

inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

@[simp] def neg (p : Formula α) : Formula α := imp p falsum

@[simp] def verum : Formula α := neg falsum

instance : LogicSymbol (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : NegDefinition (Formula α) where
  neg := rfl

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | p ⋏ q   => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | p ⋎ q   => "\\left(" ++ toStr p ++ " \\lor "  ++ toStr q ++ "\\right)"
  | p ⟶ q   => "\\left(" ++ toStr p ++ " \\rightarrow " ++ toStr q ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩
instance : ToString (Formula α) := ⟨toStr⟩

end ToString

@[simp] lemma neg_bot : ~(⊥ : Formula α) = ⊤ := rfl

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Wedge.wedge]
@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Vee.vee]
@[simp] lemma imp_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Arrow.arrow]
@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp[Tilde.tilde]

lemma iff_def (p q : Formula α) : p ⟷ q = (p ⟶ q) ⋏ (q ⟶ p) := by rfl

def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| p ⟶ q  => max p.complexity q.complexity + 1
| p ⋏ q   => max p.complexity q.complexity + 1
| p ⋎ q   => max p.complexity q.complexity + 1

@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl
@[simp] lemma complexity_top : complexity (⊤ : Formula α) = 1 := rfl

@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

@[simp] lemma complexity_imp (p q : Formula α) : complexity (p ⟶ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_imp' (p q : Formula α) : complexity (imp p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_and (p q : Formula α) : complexity (p ⋏ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_and' (p q : Formula α) : complexity (and p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or (p q : Formula α) : complexity (p ⋎ q) = max p.complexity q.complexity + 1 := rfl
@[simp] lemma complexity_or' (p q : Formula α) : complexity (or p q) = max p.complexity q.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp    : ∀ (p q : Formula α), C (p ⟶ q))
    (hand    : ∀ (p q : Formula α), C (p ⋏ q))
    (hor     : ∀ (p q : Formula α), C (p ⋎ q))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⟶ q  => himp p q
  | p ⋏ q   => hand p q
  | p ⋎ q   => hor p q

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hand   : ∀ (p q : Formula α), C p → C q → C (p ⋏ q))
  (hor    : ∀ (p q : Formula α), C p → C q → C (p ⋎ q))
  : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⟶ q  => himp p q (rec' hfalsum hatom himp hand hor p) (rec' hfalsum hatom himp hand hor q)
  | p ⋏ q   => hand p q (rec' hfalsum hatom himp hand hor p) (rec' hfalsum hatom himp hand hor q)
  | p ⋎ q   => hor p q (rec' hfalsum hatom himp hand hor p) (rec' hfalsum hatom himp hand hor q)

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

end Formula

abbrev Theory (α : Type u) := Set (Formula α)

abbrev Context (α : Type u) := Finset (Formula α)

end LO.Propositional.Intuitionistic
