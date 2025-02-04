import Foundation.Logic.HilbertStyle.Lukasiewicz
import Foundation.Vorspiel.Collection
import Foundation.Modal.LogicSymbol

namespace LO.Modal

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

namespace Formula

abbrev neg (φ : Formula α) : Formula α := imp φ falsum

abbrev verum : Formula α := imp falsum falsum

abbrev top : Formula α := imp falsum falsum

abbrev or (φ ψ : Formula α) : Formula α := imp (neg φ) ψ

abbrev and (φ ψ : Formula α) : Formula α := neg (imp φ (neg ψ))

abbrev dia (φ : Formula α) : Formula α := neg (box (neg φ))

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
  | □φ      => "\\Box " ++ toStr φ
  -- | ◇φ      => "\\Diamond " ++ toStr φ
  | φ ➝ ψ   => "\\left(" ++ toStr φ ++ " \\to " ++ toStr ψ ++ "\\right)"
  -- | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  -- | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "   ++ toStr ψ ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

instance : Coe α (Formula α) := ⟨atom⟩

end ToString

-- @[simp] lemma neg_top : ∼(⊤ : Formula α) = ⊥ := rfl

@[simp] lemma neg_bot : ∼(⊥ : Formula α) = ⊤ := rfl

-- @[simp] lemma neg_atom (a : α) : ∼(atom a) = natom a := rfl

-- @[simp] lemma neg_natom (a : α) : ∼(natom a) = atom a := rfl

-- @[simp] lemma neg_and (φ ψ : Formula α) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl

-- @[simp] lemma neg_or (φ ψ : Formula α) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl

-- @[simp] lemma neg_neg' (φ : Formula α) : ∼∼φ = φ := neg_neg φ

-- @[simp] lemma neg_box (φ : Formula α) : ∼(□φ) = ◇(∼φ) := rfl

-- @[simp] lemma neg_dia (φ : Formula α) : ∼(◇φ) = □(∼φ) := rfl

/-
@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _
-/

lemma or_eq (φ ψ : Formula α) : or φ ψ = φ ⋎ ψ := rfl

lemma and_eq (φ ψ : Formula α) : and φ ψ = φ ⋏ ψ := rfl

lemma imp_eq (φ ψ : Formula α) : imp φ ψ = φ ➝ ψ := rfl

lemma neg_eq (φ : Formula α) : neg φ = ∼φ := rfl

lemma box_eq (φ : Formula α) : box φ = □φ := rfl

lemma dia_eq (φ : Formula α) : dia φ = ◇φ := rfl

lemma iff_eq (φ ψ : Formula α) : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := rfl

lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Arrow.arrow]

@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp [NegAbbrev.neg];

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
| φ ➝ ψ   => max φ.complexity ψ.complexity + 1
| □φ   => φ.complexity + 1

/-- Max numbers of `□` -/
def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | φ ➝ ψ => max φ.degree ψ.degree
  | □φ => φ.degree + 1

@[simp] lemma degree_neg (φ : Formula α) : degree (∼φ) = degree φ := by induction φ <;> simp_all [degree, neg, neg_eq]
@[simp] lemma degree_imp (φ ψ : Formula α) : degree (φ ➝ ψ) = max (degree φ) (degree ψ) := by simp [degree, imp_eq]

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp     : ∀ (φ ψ : Formula α), C (φ ➝ ψ))
    (hbox    : ∀ (φ : Formula α), C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | φ ➝ ψ   => himp φ ψ

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ➝ ψ))
  (hbox    : ∀ (φ : Formula α), C φ → C (□φ))
  : (φ : Formula α) → C φ
  | ⊥      => hfalsum
  | atom a => hatom a
  | φ ➝ ψ  => himp φ ψ (rec' hfalsum hatom himp hbox φ) (rec' hfalsum hatom himp hbox ψ)
  | □φ     => hbox φ (rec' hfalsum hatom himp hbox φ)

-- @[simp] lemma complexity_neg (φ : Formula α) : complexity (∼φ) = φ.complexity + 1 :=
--   by induction φ using rec' <;> try { simp[neg_eq, neg, *]; rfl;}

section Decidable

variable [DecidableEq α]

def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ)
  | ⊥, ψ => by
    cases ψ using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, ψ => by
    cases ψ <;> try { simp; exact isFalse not_false }
    simp; exact decEq _ _;
  | φ ➝ ψ, χ => by
    cases χ using cases' <;> try { simp; exact isFalse not_false }
    case himp φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | □φ, ψ => by
    cases ψ <;> try { simp; exact isFalse not_false }
    case box φ' =>
      exact match hasDecEq φ φ' with
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
  | φ ➝ ψ  => insert (φ ➝ ψ) (φ.subformulae ∪ ψ.subformulae)
  | □φ     => insert (□φ) φ.subformulae

namespace Formula.subformulae

variable [DecidableEq α]

@[simp] lemma mem_self {φ : Formula α} : φ ∈ φ.subformulae := by induction φ <;> { simp [subformulae]; try tauto; }

variable {φ ψ χ : Formula α}

lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulae) : ψ ∈ φ.subformulae ∧ χ ∈ φ.subformulae := by
  induction φ using Formula.rec' with
  | himp => simp_all [subformulae]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [subformulae];

lemma mem_imp₁ (h : (ψ ➝ χ) ∈ φ.subformulae) : ψ ∈ φ.subformulae := mem_imp h |>.1

lemma mem_imp₂ (h : (ψ ➝ χ) ∈ φ.subformulae) : χ ∈ φ.subformulae := mem_imp h |>.2

lemma mem_box (h : □ψ ∈ φ.subformulae := by assumption) : ψ ∈ φ.subformulae := by
  induction φ using Formula.rec' <;> {
    simp_all [subformulae];
    try rcases h with (hq | hr); simp_all; simp_all;
  };

-- TODO: add tactic like `subformulae`.
attribute [aesop safe 5 forward]
  mem_imp₁
  mem_imp₂
  mem_box

@[simp]
lemma complexity_lower (h : ψ ∈ φ.subformulae) : ψ.complexity ≤ φ.complexity  := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp_all [subformulae];
    rcases h with _ | h₁ | h₂;
    . subst_vars; simp [Formula.complexity];
    . have := ihp₁ h₁; simp [Formula.complexity]; omega;
    . have := ihp₂ h₂; simp [Formula.complexity]; omega;
  | hbox φ ihp =>
    simp_all [subformulae];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.complexity];
    . have := ihp h₁; simp [Formula.complexity]; omega;
  | hatom => simp_all [subformulae];
  | hfalsum => simp_all [subformulae, Formula.complexity];

/-
@[simp]
lemma degree_lower (h : ψ ∈ φ.subformulae) : ψ.degree ≤ φ.degree := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp_all [subformulae];
    rcases h with rfl | h₁ | h₂;
    . simp [Formula.degree];
    . have := ihp₁ h₁; simp [Formula.degree]; omega;
    . have := ihp₂ h₂; simp [Formula.degree]; omega;
  | hbox φ ihp =>
    simp_all [subformulae];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.degree];
    . have := ihp h₁; simp [Formula.degree]; omega;
  | hatom =>
    simp_all [subformulae];
    rcases h with rfl | rfl <;> simp [Formula.degree];
  | hfalsum => simp_all [subformulae, Formula.degree];

lemma sub_of_top (h : φ ∈ 𝒮 ⊤) : φ = ⊤ := by simp_all [subformulae];
lemma sub_of_bot (h : φ ∈ 𝒮 ⊥) : φ = ⊥ := by simp_all [subformulae];

-/


end Formula.subformulae


class Formulae.SubformulaClosed (X : Formulae α) where
  imp_closed : ∀ {φ ψ}, φ ➝ ψ ∈ X → φ ∈ X ∧ ψ ∈ X
  box_closed : ∀ {φ}, □φ ∈ X → φ ∈ X

namespace SubformulaClosed

instance [DecidableEq α] {φ : Formula α} : Formulae.SubformulaClosed (φ.subformulae) where
  imp_closed hpq := ⟨Formula.subformulae.mem_imp₁ hpq, Formula.subformulae.mem_imp₂ hpq⟩
  box_closed hp := Formula.subformulae.mem_box hp


variable {φ : Formula α} {X : Formulae α} [closed : X.SubformulaClosed]

lemma mem_box (h : □φ ∈ X) : φ ∈ X := closed.box_closed h
macro_rules | `(tactic| trivial) => `(tactic| apply mem_box $ by assumption)

lemma mem_imp (h : φ ➝ ψ ∈ X) : φ ∈ X ∧ ψ ∈ X := closed.imp_closed h

lemma mem_imp₁ (h : φ ➝ ψ ∈ X) : φ ∈ X := mem_imp h |>.1
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ $ by assumption)

lemma mem_imp₂ (h : φ ➝ ψ ∈ X) : ψ ∈ X := mem_imp h |>.2
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ $ by assumption)

attribute [aesop safe 5 forward]
  mem_box
  mem_imp₁
  mem_imp₂

end SubformulaClosed


class Theory.SubformulaClosed (T : Theory α) where
  imp_closed : ∀ {φ ψ}, φ ➝ ψ ∈ T → φ ∈ T ∧ ψ ∈ T
  box_closed : ∀ {φ}, □φ ∈ T → φ ∈ T

namespace Theory.SubformulaClosed

instance {φ : Formula α} [DecidableEq α] : Theory.SubformulaClosed (φ.subformulae).toSet where
  box_closed := Formulae.SubformulaClosed.box_closed;
  imp_closed := Formulae.SubformulaClosed.imp_closed;

variable {φ : Formula α} {T : Theory α} [T_closed : T.SubformulaClosed]

lemma mem_box (h : □φ ∈ T) : φ ∈ T := T_closed.box_closed h
macro_rules | `(tactic| trivial) => `(tactic| apply mem_box $ by assumption)

lemma mem_imp (h : φ ➝ ψ ∈ T) : φ ∈ T ∧ ψ ∈ T := T_closed.imp_closed h

lemma mem_imp₁ (h : φ ➝ ψ ∈ T) : φ ∈ T := mem_imp h |>.1
macro_rules | `(tactic| trivial) => `(tactic| apply mem_imp₁ $ by assumption)

lemma mem_imp₂ (h : φ ➝ ψ ∈ T) : ψ ∈ T := mem_imp h |>.2
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
  | ∼φ     => φ.atoms
  | □φ  => φ.atoms
  | φ ➝ ψ => φ.atoms ∪ ψ.atoms
  | φ ⋏ ψ  => φ.atoms ∪ ψ.atoms
  | φ ⋎ ψ  => φ.atoms ∪ ψ.atoms
prefix:70 "𝒜 " => Formula.atoms

@[simp]
lemma mem_atoms_iff_mem_subformulae {a : α} {φ : Formula α} : a ∈ 𝒜 φ ↔ (atom a) ∈ φ.subformulae := by
  induction φ using Formula.rec' <;> simp_all [subformulae, atoms];

end Formula

end Atoms
-/


namespace Formula

variable {φ ψ χ : Formula α}

@[elab_as_elim]
def cases_neg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C (φ ➝ ψ))
    (hbox    : ∀ (φ : Formula α), C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | ∼φ      => hneg φ
  | φ ➝ ψ  => if e : ψ = ⊥ then e ▸ hneg φ else himp φ ψ e

@[elab_as_elim]
def rec_neg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (φ) → C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C φ → C ψ → C (φ ➝ ψ))
    (hbox    : ∀ (φ : Formula α), C (φ) → C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ (rec_neg hfalsum hatom hneg himp hbox φ)
  | ∼φ      => hneg φ (rec_neg hfalsum hatom hneg himp hbox φ)
  | φ ➝ ψ  =>
    if e : ψ = ⊥
    then e ▸ hneg φ (rec_neg hfalsum hatom hneg himp hbox φ)
    else himp φ ψ e (rec_neg hfalsum hatom hneg himp hbox φ) (rec_neg hfalsum hatom hneg himp hbox ψ)


section negated

def negated : Formula α → Bool
  | ∼_ => True
  | _  => False

@[simp] lemma negated_def : (∼φ).negated := by simp [negated]

@[simp]
lemma negated_imp : (φ ➝ ψ).negated ↔ (ψ = ⊥) := by
  simp [negated, Formula.imp_eq];
  split;
  . simp_all [Formula.imp_eq]; rfl;
  . simp_all [Formula.imp_eq]; simpa;

lemma negated_iff [DecidableEq α] : φ.negated ↔ ∃ ψ, φ = ∼ψ := by
  induction φ using Formula.cases_neg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

lemma not_negated_iff [DecidableEq α] : ¬φ.negated ↔ ∀ ψ, φ ≠ ∼ψ := by
  induction φ using Formula.cases_neg with
  | himp => simp [negated_imp, NegAbbrev.neg];
  | _ => simp [negated]

@[elab_as_elim]
def rec_negated [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (φ) → C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ¬(φ ➝ ψ).negated → C φ → C ψ → C (φ ➝ ψ))
    (hbox    : ∀ (φ : Formula α), C (φ) → C (□φ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ (rec_negated hfalsum hatom hneg himp hbox φ)
  | ∼φ      => hneg φ (rec_negated hfalsum hatom hneg himp hbox φ)
  | φ ➝ ψ  => by
    by_cases e : ψ = ⊥
    . exact e ▸ hneg φ (rec_negated hfalsum hatom hneg himp hbox φ)
    . refine himp φ ψ ?_ (rec_negated hfalsum hatom hneg himp hbox φ) (rec_negated hfalsum hatom hneg himp hbox ψ)
      . simpa [negated_imp]

end negated

section Encodable

variable [Encodable α]
open Encodable

def toNat : Formula α → ℕ
  | atom a  => (Nat.pair 0 <| encode a) + 1
  | ⊥       => (Nat.pair 1 0) + 1
  | □φ      => (Nat.pair 2 <| φ.toNat) + 1
  | φ ➝ ψ   => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1

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
        let φ <- ofNat c
        return □φ
    | 3 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ➝ ψ
    | _ => none

lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some'];
  | ⊥       => by simp [toNat, ofNat]
  | □φ      => by simp [toNat, ofNat, ofNat_toNat φ]
  | φ ➝ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end Encodable

end Formula


/-
section subst

namespace Formula

variable {φ ψ : Formula α}
variable {σ : α → Formula α}

def subst (σ : α → Formula α) : Formula α → Formula α
  | atom a  => σ a
  | ⊥       => ⊥
  | □φ      => □(φ.subst σ)
  | φ ➝ ψ   => φ.subst σ ➝ ψ.subst σ

@[simp] lemma subst_atom {a : α} : (atom a).subst σ = σ a := rfl

@[simp] lemma subst_bot : (⊥ : Formula α).subst σ = ⊥ := rfl

@[simp] lemma subst_imp : (φ ➝ ψ).subst σ = φ.subst σ ➝ ψ.subst σ := rfl

@[simp] lemma subst_neg : (∼φ).subst σ = ∼(φ.subst σ) := rfl

@[simp] lemma subst_and : (φ ⋏ ψ).subst σ = φ.subst σ ⋏ ψ.subst σ := rfl

@[simp] lemma subst_or : (φ ⋎ ψ).subst σ = φ.subst σ ⋎ ψ.subst σ := rfl

@[simp] lemma subst_iff : (φ ⭤ ψ).subst σ = (φ.subst σ ⭤ ψ.subst σ) := rfl

@[simp] lemma subst_box : (□φ).subst σ = □(φ.subst σ) := rfl

@[simp] lemma subst_dia : (◇φ).subst σ = ◇(φ.subst σ) := rfl


end Formula

namespace Theory

open Formula
variable {T : Theory α}

class SubstClosed (T : Theory α) : Prop where
  closed : ∀ {φ}, φ ∈ T → ∀ {σ}, φ.subst σ ∈ T

def instSubstClosed
  (hAtom : ∀ a : α, (atom a) ∈ T → ∀ {σ}, (atom a).subst σ ∈ T)
  (hImp : ∀ {φ ψ}, φ ➝ ψ ∈ T → ∀ {σ}, (φ ➝ ψ).subst σ ∈ T)
  (hBox : ∀ {φ}, □φ ∈ T → ∀ {σ}, (□φ).subst σ ∈ T)
  : T.SubstClosed := ⟨
  by
    intro φ hφ σ;
    induction φ using Formula.cases' with
    | hatom a => apply hAtom; assumption;
    | hfalsum => apply hφ;
    | himp φ ψ => apply hImp; assumption;
    | hbox φ => apply hBox; assumption;
⟩

namespace SubstClosed

variable [T.SubstClosed]

lemma mem_atom (h : atom a ∈ T) : (atom a).subst σ ∈ T := SubstClosed.closed h

lemma mem_bot (h : ⊥ ∈ T) : (⊥ : Formula α).subst σ ∈ T := SubstClosed.closed h

lemma mem_imp (h : φ ➝ ψ ∈ T) : (φ ➝ ψ).subst σ ∈ T := SubstClosed.closed h

lemma mem_neg (h : ∼φ ∈ T) : (∼φ).subst σ ∈ T := SubstClosed.closed h

lemma mem_and (h : φ ⋏ ψ ∈ T) : (φ ⋏ ψ).subst σ ∈ T := SubstClosed.closed h

lemma mem_or (h : φ ⋎ ψ ∈ T) : (φ ⋎ ψ).subst σ ∈ T := SubstClosed.closed h

lemma mem_box (h : □φ ∈ T) : (□φ).subst σ ∈ T := SubstClosed.closed h

instance union {T₁ T₂ : Theory α} [T₁_closed : T₁.SubstClosed] [T₂_closed : T₂.SubstClosed] : (T₁ ∪ T₂).SubstClosed := by
  refine instSubstClosed ?_ ?_ ?_;
  . rintro a (ha₁ | ha₂) σ;
    . left; apply mem_atom ha₁;
    . right; apply mem_atom ha₂;
  . rintro φ ψ (h₁ | h₂) σ;
    . left; apply mem_imp h₁;
    . right; apply mem_imp h₂;
  . rintro φ (h₁ | h₂) σ;
    . left; apply mem_box h₁;
    . right; apply mem_box h₂;

end SubstClosed

end Theory

end subst
-/

end LO.Modal
