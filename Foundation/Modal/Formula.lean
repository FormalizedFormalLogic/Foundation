import Foundation.Logic.HilbertStyle.Lukasiewicz
import Foundation.Vorspiel.Collection
import Foundation.Modal.System

namespace LO.Modal

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

namespace Formula

abbrev neg (p : Formula α) : Formula α := imp p falsum

abbrev verum : Formula α := imp falsum falsum

abbrev top : Formula α := imp falsum falsum

abbrev or (p q : Formula α) : Formula α := imp (neg p) q

abbrev and (p q : Formula α) : Formula α := neg (imp p (neg q))

abbrev dia (p : Formula α) : Formula α := neg (box (neg p))

variable {α : Type u}

instance : BasicModalLogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

instance : LukasiewiczAbbrev (Formula α) where
  top := rfl
  neg := rfl
  or := rfl
  and := rfl
instance : DiaAbbrev (Formula α) := ⟨rfl⟩

section ToString

variable [ToString α]

def toStr : Formula α → String
  -- | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | □p      => "\\Box " ++ toStr p
  -- | ◇p      => "\\Diamond " ++ toStr p
  | p ➝ q   => "\\left(" ++ toStr p ++ " \\to " ++ toStr q ++ "\\right)"
  -- | p ⋏ q   => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  -- | p ⋎ q   => "\\left(" ++ toStr p ++ " \\lor "   ++ toStr q ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

instance : Coe α (Formula α) := ⟨atom⟩

end ToString

-- @[simp] lemma neg_top : ∼(⊤ : Formula α) = ⊥ := rfl

@[simp] lemma neg_bot : ∼(⊥ : Formula α) = ⊤ := rfl

-- @[simp] lemma neg_atom (a : α) : ∼(atom a) = natom a := rfl

-- @[simp] lemma neg_natom (a : α) : ∼(natom a) = atom a := rfl

-- @[simp] lemma neg_and (p q : Formula α) : ∼(p ⋏ q) = ∼p ⋎ ∼q := rfl

-- @[simp] lemma neg_or (p q : Formula α) : ∼(p ⋎ q) = ∼p ⋏ ∼q := rfl

-- @[simp] lemma neg_neg' (p : Formula α) : ∼∼p = p := neg_neg p

-- @[simp] lemma neg_box (p : Formula α) : ∼(□p) = ◇(∼p) := rfl

-- @[simp] lemma neg_dia (p : Formula α) : ∼(◇p) = □(∼p) := rfl

/-
@[simp] lemma neg_inj (p q : Formula α) : ∼p = ∼q ↔ p = q := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _
-/

lemma or_eq (p q : Formula α) : or p q = p ⋎ q := rfl

lemma and_eq (p q : Formula α) : and p q = p ⋏ q := rfl

lemma imp_eq (p q : Formula α) : imp p q = p ➝ q := rfl

lemma neg_eq (p : Formula α) : neg p = ∼p := rfl

lemma box_eq (p : Formula α) : box p = □p := rfl

lemma dia_eq (p : Formula α) : dia p = ◇p := rfl

lemma iff_eq (p q : Formula α) : p ⭤ q = (p ➝ q) ⋏ (q ➝ p) := rfl

lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ➝ p₂ = q₁ ➝ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Arrow.arrow]

@[simp] lemma neg_inj (p q : Formula α) : ∼p = ∼q ↔ p = q := by simp [NegAbbrev.neg];

/-
instance : ModalDeMorgan (Formula α) where
  verum := rfl
  falsum := rfl
  and := by simp
  or := by simp
  imply := by simp[imp_eq]
  neg := by simp
  dia := by simp
  box := by simp
-/

/-- Formula complexity -/
def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| p ➝ q   => max p.complexity q.complexity + 1
| □p   => p.complexity + 1

/-- Max numbers of `□` -/
def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | p ➝ q => max p.degree q.degree
  | □p => p.degree + 1

@[simp] lemma degree_neg (p : Formula α) : degree (∼p) = degree p := by induction p <;> simp_all [degree, neg, neg_eq]
@[simp] lemma degree_imp (p q : Formula α) : degree (p ➝ q) = max (degree p) (degree q) := by simp [degree, imp_eq]

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp     : ∀ (p q : Formula α), C (p ➝ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p
  | p ➝ q   => himp p q

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ➝ q))
  (hbox    : ∀ (p : Formula α), C p → C (□p))
  : (p : Formula α) → C p
  | ⊥      => hfalsum
  | atom a => hatom a
  | p ➝ q  => himp p q (rec' hfalsum hatom himp hbox p) (rec' hfalsum hatom himp hbox q)
  | □p     => hbox p (rec' hfalsum hatom himp hbox p)

-- @[simp] lemma complexity_neg (p : Formula α) : complexity (∼p) = p.complexity + 1 :=
--   by induction p using rec' <;> try { simp[neg_eq, neg, *]; rfl;}

section Decidable

variable [DecidableEq α]

def hasDecEq : (p q : Formula α) → Decidable (p = q)
  | ⊥, q => by
    cases q using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, q => by
    cases q <;> try { simp; exact isFalse not_false }
    simp; exact decEq _ _;
  | p ➝ q, r => by
    cases r using cases' <;> try { simp; exact isFalse not_false }
    case himp p' q' =>
      exact match hasDecEq p p' with
      | isTrue hp =>
        match hasDecEq q q' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | □p, q => by
    cases q <;> try { simp; exact isFalse not_false }
    case box p' =>
      exact match hasDecEq p p' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse (by simp[hp, box_eq])
instance : DecidableEq (Formula α) := hasDecEq


end Decidable

def isBox : Formula α → Bool
  | box _ => true
  | _  => false


end Formula

abbrev Formulae (α) := Finset (Formula α)

abbrev Theory (α) := Set (Formula α)
instance : Collection (Formula α) (Theory α) := inferInstance

section Subformula

def Formula.subformulae [DecidableEq α] : Formula α → Formulae α
  | atom a => {(atom a)}
  | ⊥      => {⊥}
  | p ➝ q  => insert (p ➝ q) (p.subformulae ∪ q.subformulae)
  | □p     => insert (□p) p.subformulae

namespace Formula.subformulae

variable [DecidableEq α]

@[simp] lemma mem_self {p : Formula α} : p ∈ p.subformulae := by induction p <;> { simp [subformulae]; try tauto; }

variable {p q r : Formula α}

lemma mem_imp (h : (q ➝ r) ∈ p.subformulae) : q ∈ p.subformulae ∧ r ∈ p.subformulae := by
  induction p using Formula.rec' with
  | himp => simp_all [subformulae]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [subformulae];

lemma mem_imp₁ (h : (q ➝ r) ∈ p.subformulae) : q ∈ p.subformulae := mem_imp h |>.1

lemma mem_imp₂ (h : (q ➝ r) ∈ p.subformulae) : r ∈ p.subformulae := mem_imp h |>.2

lemma mem_box (h : □q ∈ p.subformulae := by assumption) : q ∈ p.subformulae := by
  induction p using Formula.rec' <;> {
    simp_all [subformulae];
    try rcases h with (hq | hr); simp_all; simp_all;
  };

-- TODO: add tactic like `subformulae`.
attribute [aesop safe 5 forward]
  mem_imp₁
  mem_imp₂
  mem_box

@[simp]
lemma complexity_lower (h : q ∈ p.subformulae) : q.complexity ≤ p.complexity  := by
  induction p using Formula.rec' with
  | himp p₁ p₂ ihp₁ ihp₂ =>
    simp_all [subformulae];
    rcases h with _ | h₁ | h₂;
    . subst_vars; simp [Formula.complexity];
    . have := ihp₁ h₁; simp [Formula.complexity]; omega;
    . have := ihp₂ h₂; simp [Formula.complexity]; omega;
  | hbox p ihp =>
    simp_all [subformulae];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.complexity];
    . have := ihp h₁; simp [Formula.complexity]; omega;
  | hatom => simp_all [subformulae];
  | hfalsum => simp_all [subformulae, Formula.complexity];

/-
@[simp]
lemma degree_lower (h : q ∈ p.subformulae) : q.degree ≤ p.degree := by
  induction p using Formula.rec' with
  | himp p₁ p₂ ihp₁ ihp₂ =>
    simp_all [subformulae];
    rcases h with rfl | h₁ | h₂;
    . simp [Formula.degree];
    . have := ihp₁ h₁; simp [Formula.degree]; omega;
    . have := ihp₂ h₂; simp [Formula.degree]; omega;
  | hbox p ihp =>
    simp_all [subformulae];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.degree];
    . have := ihp h₁; simp [Formula.degree]; omega;
  | hatom =>
    simp_all [subformulae];
    rcases h with rfl | rfl <;> simp [Formula.degree];
  | hfalsum => simp_all [subformulae, Formula.degree];

lemma sub_of_top (h : p ∈ 𝒮 ⊤) : p = ⊤ := by simp_all [subformulae];
lemma sub_of_bot (h : p ∈ 𝒮 ⊥) : p = ⊥ := by simp_all [subformulae];

-/


end Formula.subformulae


class Formulae.SubformulaClosed (X : Formulae α) where
  imp_closed : ∀ {p q}, p ➝ q ∈ X → p ∈ X ∧ q ∈ X
  box_closed : ∀ {p}, □p ∈ X → p ∈ X

namespace SubformulaClosed

instance [DecidableEq α] {p : Formula α} : Formulae.SubformulaClosed (p.subformulae) where
  imp_closed hpq := ⟨Formula.subformulae.mem_imp₁ hpq, Formula.subformulae.mem_imp₂ hpq⟩
  box_closed hp := Formula.subformulae.mem_box hp


variable {p : Formula α} {X : Formulae α} [closed : X.SubformulaClosed]

lemma mem_box (h : □p ∈ X) : p ∈ X := closed.box_closed h
macro_rules | `(tactic| trivial) => `(tactic| apply mem_box $ by assumption)

lemma mem_imp (h : p ➝ q ∈ X) : p ∈ X ∧ q ∈ X := closed.imp_closed h

lemma mem_imp₁ (h : p ➝ q ∈ X) : p ∈ X := mem_imp h |>.1
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ $ by assumption)

lemma mem_imp₂ (h : p ➝ q ∈ X) : q ∈ X := mem_imp h |>.2
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ $ by assumption)

attribute [aesop safe 5 forward]
  mem_box
  mem_imp₁
  mem_imp₂

end SubformulaClosed


class Theory.SubformulaClosed (T : Theory α) where
  imp_closed : ∀ {p q}, p ➝ q ∈ T → p ∈ T ∧ q ∈ T
  box_closed : ∀ {p}, □p ∈ T → p ∈ T

namespace Theory.SubformulaClosed

instance {p : Formula α} [DecidableEq α] : Theory.SubformulaClosed (p.subformulae).toSet where
  box_closed := Formulae.SubformulaClosed.box_closed;
  imp_closed := Formulae.SubformulaClosed.imp_closed;

variable {p : Formula α} {T : Theory α} [T_closed : T.SubformulaClosed]

lemma mem_box (h : □p ∈ T) : p ∈ T := T_closed.box_closed h
macro_rules | `(tactic| trivial) => `(tactic| apply mem_box $ by assumption)

lemma mem_imp (h : p ➝ q ∈ T) : p ∈ T ∧ q ∈ T := T_closed.imp_closed h

lemma mem_imp₁ (h : p ➝ q ∈ T) : p ∈ T := mem_imp h |>.1
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ $ by assumption)

lemma mem_imp₂ (h : p ➝ q ∈ T) : q ∈ T := mem_imp h |>.2
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₂ $ by assumption)

end Theory.SubformulaClosed

end Subformula


/-
section Atoms

variable [DecidableEq α]

namespace Formula

def atoms : Formula α → Finset (α)
  | .atom a => {a}
  | ⊤      => ∅
  | ⊥      => ∅
  | ∼p     => p.atoms
  | □p  => p.atoms
  | p ➝ q => p.atoms ∪ q.atoms
  | p ⋏ q  => p.atoms ∪ q.atoms
  | p ⋎ q  => p.atoms ∪ q.atoms
prefix:70 "𝒜 " => Formula.atoms

@[simp]
lemma mem_atoms_iff_mem_subformulae {a : α} {p : Formula α} : a ∈ 𝒜 p ↔ (atom a) ∈ p.subformulae := by
  induction p using Formula.rec' <;> simp_all [subformulae, atoms];

end Formula

end Atoms
-/


namespace Formula

variable {p q r : Formula α}

@[elab_as_elim]
def cases_neg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (∼p))
    (himp    : ∀ (p q : Formula α), q ≠ ⊥ → C (p ➝ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p
  | ∼p      => hneg p
  | p ➝ q  => if e : q = ⊥ then e ▸ hneg p else himp p q e

@[elab_as_elim]
def rec_neg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (p) → C (∼p))
    (himp    : ∀ (p q : Formula α), q ≠ ⊥ → C p → C q → C (p ➝ q))
    (hbox    : ∀ (p : Formula α), C (p) → C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p (rec_neg hfalsum hatom hneg himp hbox p)
  | ∼p      => hneg p (rec_neg hfalsum hatom hneg himp hbox p)
  | p ➝ q  =>
    if e : q = ⊥
    then e ▸ hneg p (rec_neg hfalsum hatom hneg himp hbox p)
    else himp p q e (rec_neg hfalsum hatom hneg himp hbox p) (rec_neg hfalsum hatom hneg himp hbox q)


section negated

def negated : Formula α → Bool
  | ∼_ => True
  | _  => False

@[simp] lemma negated_def : (∼p).negated := by simp [negated]

@[simp]
lemma negated_imp : (p ➝ q).negated ↔ (q = ⊥) := by
  simp [negated, Formula.imp_eq];
  split;
  . simp_all [Formula.imp_eq]; rfl;
  . simp_all [Formula.imp_eq]; simpa;

lemma negated_iff [DecidableEq α] : p.negated ↔ ∃ q, p = ∼q := by
  induction p using Formula.cases_neg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

lemma not_negated_iff [DecidableEq α] : ¬p.negated ↔ ∀ q, p ≠ ∼q := by
  induction p using Formula.cases_neg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

@[elab_as_elim]
def rec_negated [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (p) → C (∼p))
    (himp    : ∀ (p q : Formula α), ¬(p ➝ q).negated → C p → C q → C (p ➝ q))
    (hbox    : ∀ (p : Formula α), C (p) → C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p (rec_negated hfalsum hatom hneg himp hbox p)
  | ∼p      => hneg p (rec_negated hfalsum hatom hneg himp hbox p)
  | p ➝ q  => by
    by_cases e : q = ⊥
    . exact e ▸ hneg p (rec_negated hfalsum hatom hneg himp hbox p)
    . refine himp p q ?_ (rec_negated hfalsum hatom hneg himp hbox p) (rec_negated hfalsum hatom hneg himp hbox q)
      . simpa [negated_imp]

end negated

section Encodable

variable [Encodable α]
open Encodable

def toNat : Formula α → ℕ
  | atom a  => (Nat.pair 0 <| encode a) + 1
  | ⊥       => (Nat.pair 1 0) + 1
  | □p      => (Nat.pair 2 <| p.toNat) + 1
  | p ➝ q   => (Nat.pair 3 <| p.toNat.pair q.toNat) + 1

def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => (decode c).map Formula.atom
    | 1 => some ⊥
    | 2 =>
      have : c < e + 1 := Nat.lt_succ.mpr $ Nat.unpair_right_le _
      do
        let p <- ofNat c
        return □p
    | 3 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let p <- ofNat c.unpair.1
        let q <- ofNat c.unpair.2
        return p ➝ q
    | _ => none

lemma ofNat_toNat : ∀ (p : Formula α), ofNat (toNat p) = some p
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some'];
  | ⊥       => by simp [toNat, ofNat]
  | □p      => by simp [toNat, ofNat, ofNat_toNat p]
  | p ➝ q   => by simp [toNat, ofNat, ofNat_toNat p, ofNat_toNat q]

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end Encodable

end Formula


end LO.Modal
