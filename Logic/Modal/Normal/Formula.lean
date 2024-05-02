import Logic.Modal.Normal.LogicSymbol
import Logic.Vorspiel.Collection

namespace LO.Modal.Normal

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

namespace Formula

variable {α : Type u}

@[simp] def neg (p : Formula α) : Formula α := imp p falsum

@[simp] def verum : Formula α := neg falsum

@[simp] def dia (p : Formula α) : Formula α := neg (box (neg p))

instance : StandardModalLogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  mop i := match i with
    | 0 => box
    | 1 => dia
  mop_injective := by
    simp_all [Function.Injective]
    aesop;
  duality := by simp;

instance : NegDefinition (Formula α) where
  neg := rfl

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | p ⟶ q   => "\\left(" ++ toStr p ++ " \\to "   ++ toStr q ++ "\\right)"
  | p ⋏ q   => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | p ⋎ q   => "\\left(" ++ toStr p ++ " \\lor "   ++ toStr q ++ "\\right)"
  | box p   => "\\Box " ++ toStr p

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

end ToString

lemma or_eq (p q : Formula α) : or p q = p ⋎ q := rfl

lemma and_eq (p q : Formula α) : and p q = p ⋏ q := rfl

lemma neg_eq (p : Formula α) : neg p = ~p := rfl

lemma imp_eq (p q : Formula α) : imp p q = p ⟶ q := rfl

lemma box_eq (p : Formula α) : box p = □p := rfl

lemma iff_eq (p q : Formula α) : p ⟷ q = (p ⟶ q) ⋏ (q ⟶ p) := rfl

lemma dia_eq (p : Formula α) : ◇p = ~(□(~p)) := rfl

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Arrow.arrow]

@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp [NegDefinition.neg]

def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| p ⟶ q   => max p.complexity q.complexity + 1
| p ⋏ q   => max p.complexity q.complexity + 1
| p ⋎ q   => max p.complexity q.complexity + 1
| box p   => p.complexity + 1

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
    (hand    : ∀ (p q : Formula α), C (p ⋏ q))
    (hor     : ∀ (p q : Formula α), C (p ⋎ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⟶ q  => himp p q
  | p ⋏ q   => hand p q
  | p ⋎ q   => hor p q
  | box p      => hbox p

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hand   : ∀ (p q : Formula α), C p → C q → C (p ⋏ q))
  (hor    : ∀ (p q : Formula α), C p → C q → C (p ⋎ q))
  (hbox    : ∀ (p : Formula α), C p → C (□p))
  : (p : Formula α) → C p
  | ⊥      => hfalsum
  | atom a => hatom a
  | p ⟶ q  => himp p q (rec' hfalsum hatom himp hand hor hbox p) (rec' hfalsum hatom himp hand hor hbox q)
  | p ⋏ q  => hand p q (rec' hfalsum hatom himp hand hor hbox p) (rec' hfalsum hatom himp hand hor hbox q)
  | p ⋎ q  => hor p q (rec' hfalsum hatom himp hand hor hbox p) (rec' hfalsum hatom himp hand hor hbox q)
  | box p     => hbox p (rec' hfalsum hatom himp hand hor hbox p)

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
  | box p, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    case hbox p' =>
      exact match hasDecEq p p' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse (by simp[hp, box_eq])

instance : DecidableEq (Formula α) := hasDecEq

end Decidable

def isBox : Formula α → Bool
  | box _ => true
  | _  => false

end Formula

abbrev Theory (α : Type u) := Set (Formula α)

instance : Collection (Formula α) (Theory α) := inferInstance

abbrev Context (α : Type u) := Finset (Formula α)

instance [DecidableEq α] : Collection (Formula α) (Context α) := inferInstance

namespace Context

variable [DecidableEq α]
variable (Γ : Context α)

@[simp] noncomputable def conj : Formula α := Finset.conj Γ
prefix:75 "⋀" => conj

@[simp] noncomputable def disj : Formula α := Finset.disj Γ
prefix:75 "⋁" => disj

end Context

end LO.Modal.Normal
