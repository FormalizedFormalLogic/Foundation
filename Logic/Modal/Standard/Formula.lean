import Logic.Vorspiel.Collection
import Logic.Modal.LogicSymbol
import Logic.Modal.Standard.System

namespace LO.Modal.Standard

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
  mop b := match b with
    | true => box
    | false => dia
  mop_injective := by simp_all [Function.Injective]
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

abbrev AxiomSet (α) := Set (Formula α)

namespace AxiomSet

open System

variable {p q : Formula α}

protected abbrev K : AxiomSet α := { Axioms.K p q | (p) (q) }
notation "𝐊" => AxiomSet.K

protected abbrev T : AxiomSet α := { Axioms.T p | p }
notation "𝐓" => AxiomSet.T

protected abbrev B : AxiomSet α := { Axioms.B p | p }
notation "𝐁" => AxiomSet.B

protected abbrev D : AxiomSet α := { Axioms.D p | p }
notation "𝐃" => AxiomSet.D

protected abbrev Four : AxiomSet α := { Axioms.Four p | p }
notation "𝟒" => AxiomSet.Four

protected abbrev Five : AxiomSet α := { Axioms.Five p | p }
notation "𝟓" => AxiomSet.Five

protected abbrev L : AxiomSet α := { Axioms.L p | p }
notation "𝐋" => AxiomSet.L

protected abbrev Dot2 : AxiomSet α := { Axioms.Dot2 p | p }
notation ".𝟐" => AxiomSet.Dot2

protected abbrev Dot3 : AxiomSet α := { Axioms.Dot3 p q | (p) (q) }
notation ".𝟑" => AxiomSet.Dot3

protected abbrev Grz : AxiomSet α := { Axioms.Grz p | p }
notation "𝐆𝐫𝐳" => AxiomSet.Grz

protected abbrev M : AxiomSet α := { Axioms.M p | p }
notation "𝐌" => AxiomSet.M

protected abbrev CD : AxiomSet α := { Axioms.CD p | p }
notation "𝐂𝐃" => AxiomSet.CD

protected abbrev C4 : AxiomSet α := { Axioms.C4 p | p }
notation "𝐂𝟒" => AxiomSet.C4

protected abbrev KT : AxiomSet α := 𝐊 ∪ 𝐓
notation "𝐊𝐓" => AxiomSet.KT

protected abbrev KB : AxiomSet α := 𝐊 ∪ 𝐁
notation "𝐊𝐁" => AxiomSet.KB

protected abbrev KD : AxiomSet α := 𝐊 ∪ 𝐃
notation "𝐊𝐃" => AxiomSet.KD

protected abbrev K4 : AxiomSet α := 𝐊 ∪ 𝟒
notation "𝐊𝟒" => AxiomSet.K4

protected abbrev K5 : AxiomSet α := 𝐊 ∪ 𝟓
notation "𝐊𝟓" => AxiomSet.K5

protected abbrev S4 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒
notation "𝐒𝟒" => AxiomSet.S4

protected abbrev S4Dot2 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ .𝟐
notation "𝐒𝟒.𝟐" => AxiomSet.S4Dot2

protected abbrev S4Dot3 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ .𝟑
notation "𝐒𝟒.𝟑" => AxiomSet.S4Dot3

protected abbrev S4Grz : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ 𝐆𝐫𝐳
notation "𝐒𝟒𝐆𝐫𝐳" => AxiomSet.S4Grz

protected abbrev S5 : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟓
notation "𝐒𝟓" => AxiomSet.S5

protected abbrev KT4B : AxiomSet α := 𝐊 ∪ 𝐓 ∪ 𝟒 ∪ 𝐁
notation "𝐊𝐓𝟒𝐁" => AxiomSet.KT4B

protected abbrev GL : AxiomSet α := 𝐊 ∪ 𝐋
notation "𝐆𝐋" => AxiomSet.GL

end AxiomSet

end LO.Modal.Standard
