import Logic.Logic.LogicSymbol
import Logic.Logic.HilbertStyle.Basic

namespace LO.Propositional.Superintuitionistic

inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | verum  : Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

@[simp] def neg (p : Formula α) : Formula α := imp p falsum

instance : LogicalConnective (Formula α) where
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

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Wedge.wedge]
@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Vee.vee]
@[simp] lemma imp_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Arrow.arrow]
@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp[Tilde.tilde]

lemma neg_def (p : Formula α) : ~p = p ⟶ ⊥ := rfl

lemma iff_def (p q : Formula α) : p ⟷ q = (p ⟶ q) ⋏ (q ⟶ p) := by rfl

def complexity : Formula α → ℕ
| atom _  => 0
| ⊤       => 0
| ⊥       => 0
| p ⟶ q  => max p.complexity q.complexity + 1
| p ⋏ q   => max p.complexity q.complexity + 1
| p ⋎ q   => max p.complexity q.complexity + 1

@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl
@[simp] lemma complexity_top : complexity (⊤ : Formula α) = 0 := rfl

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
    (hverum  : C ⊤)
    (hatom   : ∀ a : α, C (atom a))
    (himp    : ∀ (p q : Formula α), C (p ⟶ q))
    (hand    : ∀ (p q : Formula α), C (p ⋏ q))
    (hor     : ∀ (p q : Formula α), C (p ⋎ q))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | ⊤       => hverum
  | atom a  => hatom a
  | p ⟶ q  => himp p q
  | p ⋏ q   => hand p q
  | p ⋎ q   => hor p q

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hverum  : C ⊤)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hand   : ∀ (p q : Formula α), C p → C q → C (p ⋏ q))
  (hor    : ∀ (p q : Formula α), C p → C q → C (p ⋎ q))
  : (p : Formula α) → C p
  | ⊥       => hfalsum
  | ⊤       => hverum
  | atom a  => hatom a
  | p ⟶ q  => himp p q (rec' hfalsum hverum hatom himp hand hor p) (rec' hfalsum hverum hatom himp hand hor q)
  | p ⋏ q   => hand p q (rec' hfalsum hverum hatom himp hand hor p) (rec' hfalsum hverum hatom himp hand hor q)
  | p ⋎ q   => hor p q (rec' hfalsum hverum hatom himp hand hor p) (rec' hfalsum hverum hatom himp hand hor q)

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

section Encodable

abbrev Node (α) := α ⊕ Bool ⊕ Fin 3

@[reducible]
def Edge (α) : Node α → Type
  | (Sum.inl _)                => Empty
  | (Sum.inr $ Sum.inl _)      => Empty
  | (Sum.inr $ Sum.inr ⟨_, _⟩) => Bool

def toW : Formula α → WType (Edge α)
  | atom a  => ⟨Sum.inl a, Empty.elim⟩
  | falsum  => ⟨Sum.inr $ Sum.inl false, Empty.elim⟩
  | verum   => ⟨Sum.inr $ Sum.inl true, Empty.elim⟩
  | imp p q => ⟨Sum.inr $ Sum.inr ⟨0, (by trivial)⟩, Bool.rec p.toW q.toW⟩
  | or p q  => ⟨Sum.inr $ Sum.inr ⟨1, (by trivial)⟩, Bool.rec p.toW q.toW⟩
  | and p q => ⟨Sum.inr $ Sum.inr ⟨2, (by trivial)⟩, Bool.rec p.toW q.toW⟩

def ofW : WType (Edge α) → Formula α
  | ⟨Sum.inl a, _⟩                => atom a
  | ⟨Sum.inr $ Sum.inl true, _⟩   => verum
  | ⟨Sum.inr $ Sum.inl false, _⟩  => falsum
  | ⟨Sum.inr $ Sum.inr ⟨0, _⟩, p⟩ => imp (ofW $ p false) (ofW $ p true)
  | ⟨Sum.inr $ Sum.inr ⟨1, _⟩, p⟩ => or (ofW $ p false) (ofW $ p true)
  | ⟨Sum.inr $ Sum.inr ⟨2, _⟩, p⟩ => and (ofW $ p false) (ofW $ p true)

lemma toW_ofW : ∀ (w : WType (Edge α)), toW (ofW w) = w
  | ⟨Sum.inl a, _⟩                => by simp [ofW, toW, Empty.eq_elim];
  | ⟨Sum.inr $ Sum.inl true, _⟩   => by simp [ofW, toW, Empty.eq_elim];
  | ⟨Sum.inr $ Sum.inl false, _⟩  => by simp [ofW, toW, Empty.eq_elim];
  | ⟨Sum.inr $ Sum.inr ⟨0, _⟩, w⟩ => by
    simp [ofW, toW, toW_ofW (w false), toW_ofW (w true)];
    ext b; cases b <;> simp;
  | ⟨Sum.inr $ Sum.inr ⟨1, _⟩, w⟩ => by
    simp [ofW, toW, toW_ofW (w false), toW_ofW (w true)];
    ext b; cases b <;> simp;
  | ⟨Sum.inr $ Sum.inr ⟨2, _⟩, w⟩ => by
    simp [ofW, toW, toW_ofW (w false), toW_ofW (w true)];
    ext b; cases b <;> simp;

def equivW (α) : Formula α ≃ WType (Edge α) where
  toFun := toW
  invFun := ofW
  right_inv := toW_ofW
  left_inv := λ p => by induction p <;> simp_all [toW, ofW]

instance : (a : Node α) → Fintype (Edge α a)
  | (Sum.inl _)           => Fintype.ofIsEmpty
  | (Sum.inr $ Sum.inl _) => Fintype.ofIsEmpty
  | (Sum.inr $ Sum.inr _) => Bool.fintype

instance : (a : Node α) → Primcodable (Edge α a)
  | (Sum.inl _)           => Primcodable.empty
  | (Sum.inr $ Sum.inl _) => Primcodable.empty
  | (Sum.inr $ Sum.inr _) => Primcodable.bool

variable [Encodable α]

instance : Encodable (Formula α) := Encodable.ofEquiv (WType (Edge α)) (equivW α)

end Encodable

end Formula


abbrev Theory (α : Type u) := Set (Formula α)


abbrev AxiomSet (α : Type u) := Set (Formula α)

namespace AxiomSet

open System

protected abbrev EFQ : AxiomSet α := { Axioms.EFQ p | p }
notation "𝗘𝗙𝗤" => AxiomSet.EFQ

protected abbrev LEM : AxiomSet α := { Axioms.LEM p | p }
notation "𝗟𝗘𝗠" => AxiomSet.LEM

protected abbrev WeakLEM : AxiomSet α := { Axioms.WeakLEM p | p }
notation "𝘄𝗟𝗘𝗠" => AxiomSet.WeakLEM

protected abbrev GD : AxiomSet α := { Axioms.GD p q | (p) (q) }
notation "𝗚𝗗" => AxiomSet.GD

protected abbrev Peirce : AxiomSet α := { Axioms.Peirce p q | (p) (q) }
notation "𝗣𝗲" => AxiomSet.Peirce

protected abbrev DNE : AxiomSet α := { Axioms.DNE p | p }
notation "𝗗𝗡𝗘" => AxiomSet.DNE

end AxiomSet


abbrev Context (α : Type u) := Finset (Formula α)

end LO.Propositional.Superintuitionistic
