import Logic.Vorspiel.Collection
import Logic.Modal.LogicSymbol
import Logic.Modal.Standard.System

namespace LO.Modal.Standard

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | verum  : Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

namespace Formula

variable {α : Type u}

@[simp] def neg (p : Formula α) : Formula α := imp p falsum

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

instance : NegAbbrev (Formula α) where
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

instance : Coe α (Formula α) := ⟨atom⟩

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

@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp [NegAbbrev.neg]

def complexity : Formula α → ℕ
| atom _  => 0
| ⊤       => 0
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

/-- Max numbers of `□` -/
def degree : Formula α → Nat
  | atom _ => 0
  | ⊤ => 0
  | ⊥ => 0
  | box p => p.degree + 1
  | p ⟶ q => max p.degree q.degree
  | p ⋏ q => max p.degree q.degree
  | p ⋎ q => max p.degree q.degree

@[simp] lemma degree_bot : degree (⊥ : Formula α) = 0 := rfl
@[simp] lemma degree_top : degree (⊤ : Formula α) = 0 := rfl
@[simp] lemma degree_atom {a : α} : degree (atom a) = 0 := rfl
@[simp] lemma degree_imp {p q : Formula α} : degree (p ⟶ q) = max p.degree q.degree := rfl
@[simp] lemma degree_box {p : Formula α} : degree (□p) = p.degree + 1 := rfl
@[simp] lemma degree_and {p q : Formula α} : degree (p ⋏ q) = max p.degree q.degree := rfl
@[simp] lemma degree_or {p q : Formula α} : degree (p ⋎ q) = max p.degree q.degree := rfl
@[simp] lemma degree_not {p : Formula α} : degree (~p) = p.degree := by simp [NegAbbrev.neg]

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hVerum  : C ⊤)
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp    : ∀ (p q : Formula α), C (p ⟶ q))
    (hand    : ∀ (p q : Formula α), C (p ⋏ q))
    (hor     : ∀ (p q : Formula α), C (p ⋎ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊤       => hVerum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | p ⟶ q  => himp p q
  | p ⋏ q   => hand p q
  | p ⋎ q   => hor p q
  | box p      => hbox p

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hVerum  : C ⊤)
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hand   : ∀ (p q : Formula α), C p → C q → C (p ⋏ q))
  (hor    : ∀ (p q : Formula α), C p → C q → C (p ⋎ q))
  (hbox    : ∀ (p : Formula α), C p → C (□p))
  : (p : Formula α) → C p
  | ⊤      => hVerum
  | ⊥      => hfalsum
  | atom a => hatom a
  | p ⟶ q  => himp p q (rec' hVerum hfalsum hatom himp hand hor hbox p) (rec' hVerum hfalsum hatom himp hand hor hbox q)
  | p ⋏ q  => hand p q (rec' hVerum hfalsum hatom himp hand hor hbox p) (rec' hVerum hfalsum hatom himp hand hor hbox q)
  | p ⋎ q  => hor p q (rec' hVerum hfalsum hatom himp hand hor hbox p) (rec' hVerum hfalsum hatom himp hand hor hbox q)
  | box p     => hbox p (rec' hVerum hfalsum hatom himp hand hor hbox p)

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

abbrev Theory (α) := Set (Formula α)

instance : Collection (Formula α) (Theory α) := inferInstance


section Subformula

variable [DecidableEq α]

def Formula.Subformulas: Formula α → Finset (Formula α)
  | ⊤      => {⊤}
  | ⊥      => {⊥}
  | atom a => {(atom a)}
  | p ⟶ q => insert (p ⟶ q) (p.Subformulas ∪ q.Subformulas)
  | p ⋏ q  => {p ⋏ q} ∪ (p.Subformulas ∪ q.Subformulas)
  | p ⋎ q  => insert (p ⋎ q) (p.Subformulas ∪ q.Subformulas)
  | box p  => insert (□p) p.Subformulas

namespace Formula.Subformulas

@[simp]
lemma mem_self (p : Formula α) : p ∈ p.Subformulas := by induction p using Formula.rec' <;> simp [Subformulas];

variable {p q r : Formula α}

lemma mem_and (h : (q ⋏ r) ∈ p.Subformulas) : q ∈ p.Subformulas ∧ r ∈ p.Subformulas := by
  induction p using Formula.rec' <;> { simp_all [Subformulas]; try aesop; };

lemma mem_or (h : (q ⋎ r) ∈ p.Subformulas) : q ∈ p.Subformulas ∧ r ∈ p.Subformulas := by
  induction p using Formula.rec' <;> { simp_all [Subformulas]; try aesop; };

lemma mem_imp (h : (q ⟶ r) ∈ p.Subformulas) : q ∈ p.Subformulas ∧ r ∈ p.Subformulas := by
  induction p using Formula.rec' <;> { simp_all [Subformulas]; try aesop; };

lemma mem_box (h : □q ∈ p.Subformulas) : q ∈ p.Subformulas := by
  induction p using Formula.rec' <;> { simp_all [Subformulas]; try aesop; };

end Formula.Subformulas

-- TOOD: より抽象的にして`Modal/LogicalSymbol`などに移してもよいかも．
class Formula.SubformulaClosed (C : (Formula α) → Prop) where
  and : C (p ⋏ q) → C p ∧ C q
  or  : C (p ⋎ q) → C p ∧ C q
  imp : C (p ⟶ q) → C p ∧ C q
  box : C (□p) → C p

open Formula (Subformulas)

instance {p : Formula α} : (Formula.SubformulaClosed (p.Subformulas).toSet) where
  and := by intro q r hqr; exact Subformulas.mem_and hqr;
  or  := by intro q r hqr; exact Subformulas.mem_or hqr;
  imp := by intro q r hqr; exact Subformulas.mem_imp hqr;
  box := by intro q hq; exact Subformulas.mem_box hq;

end Subformula


section Axiomset

abbrev AxiomSet (α) := Set (Formula α)

namespace AxiomSet

open System

variable {p q : Formula α}

protected abbrev K : AxiomSet α := { Axioms.K p q | (p) (q) }
notation "𝗞" => AxiomSet.K

protected abbrev T : AxiomSet α := { Axioms.T p | p }
notation "𝗧" => AxiomSet.T

protected abbrev B : AxiomSet α := { Axioms.B p | p }
notation "𝗕" => AxiomSet.B

protected abbrev D : AxiomSet α := { Axioms.D p | p }
notation "𝗗" => AxiomSet.D

protected abbrev Four : AxiomSet α := { Axioms.Four p | p }
notation "𝟰" => AxiomSet.Four

protected abbrev Five : AxiomSet α := { Axioms.Five p | p }
notation "𝟱" => AxiomSet.Five

protected abbrev L : AxiomSet α := { Axioms.L p | p }
notation "𝗟" => AxiomSet.L

protected abbrev Dot2 : AxiomSet α := { Axioms.Dot2 p | p }
notation ".𝟮" => AxiomSet.Dot2

protected abbrev Dot3 : AxiomSet α := { Axioms.Dot3 p q | (p) (q) }
notation ".𝟯" => AxiomSet.Dot3

protected abbrev Grz : AxiomSet α := { Axioms.Grz p | p }
notation "𝗚𝗿𝘇" => AxiomSet.Grz

protected abbrev M : AxiomSet α := { Axioms.M p | p }
notation "𝗠" => AxiomSet.M

protected abbrev CD : AxiomSet α := { Axioms.CD p | p }
notation "𝗖𝗗" => AxiomSet.CD

protected abbrev C4 : AxiomSet α := { Axioms.C4 p | p }
notation "𝗖𝟰" => AxiomSet.C4

protected abbrev Ver : AxiomSet α := { Axioms.Ver p | p }
notation "𝗩𝗲𝗿" => AxiomSet.Ver

protected abbrev Tc : AxiomSet α := { Axioms.Tc p | p }
notation "𝗧𝗰" => AxiomSet.Tc

protected abbrev H : AxiomSet α := { Axioms.H p | p }
notation "𝗛" => AxiomSet.H

end AxiomSet

end Axiomset

end LO.Modal.Standard
