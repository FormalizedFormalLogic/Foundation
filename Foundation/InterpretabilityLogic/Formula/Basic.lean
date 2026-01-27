module

public import Foundation.InterpretabilityLogic.LogicSymbol
public import Foundation.Modal.Formula.Basic

@[expose] public section

namespace LO.InterpretabilityLogic

variable {α : Type*}

@[grind]
inductive Formula (α : Type*) where
  | atom    : α → Formula α
  | falsum  : Formula α
  | imp     : Formula α → Formula α → Formula α
  | box     : Formula α → Formula α
  | rhd     : Formula α → Formula α → Formula α

abbrev FormulaSet (α) := Set (Formula α)
abbrev FormulaFinset (α) := Finset (Formula α)
abbrev FormulaSeq (α) := List (Formula α)

namespace Formula

variable {φ φ₁ φ₂ ψ ψ₁ ψ₂ : Formula α}

abbrev neg (φ : Formula α) : Formula α := imp φ falsum

abbrev verum : Formula α := imp falsum falsum

abbrev top : Formula α := imp falsum falsum

abbrev or (φ ψ : Formula α) : Formula α := imp (neg φ) ψ

abbrev and (φ ψ : Formula α) : Formula α := neg (imp φ (neg ψ))

abbrev dia (φ : Formula α) : Formula α := neg (box (neg φ))

instance : InterpretabilityLogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia
  rhd := rhd

instance : ŁukasiewiczAbbrev (Formula α) where
  top := rfl
  neg := rfl
  or := rfl
  and := rfl

instance : DiaByBox (Formula α) := ⟨rfl⟩

lemma eq_falsum : (falsum : Formula α) = ⊥ := rfl
lemma eq_or  : or φ ψ = φ ⋎ ψ := rfl
lemma eq_and : and φ ψ = φ ⋏ ψ := rfl
lemma eq_imp : imp φ ψ = φ ➝ ψ := rfl
lemma eq_rhd : rhd φ ψ = φ ▷ ψ := rfl
lemma eq_neg : neg φ = ∼φ := rfl
lemma eq_box : box φ = □φ := rfl
lemma eq_dia : dia φ = ◇φ := rfl
lemma eq_iff : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := rfl


lemma inj_and : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Wedge.wedge]
lemma inj_or  : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Vee.vee]
lemma inj_imp : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Arrow.arrow]
lemma inj_rhd : φ₁ ▷ φ₂ = ψ₁ ▷ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Rhd.rhd];
lemma inj_neg : ∼φ = ∼ψ ↔ φ = ψ := by simp [Tilde.tilde];
lemma inj_box : □φ = □ψ ↔ φ = ψ := by simp [Box.box]
lemma inj_dia : ◇φ = ◇ψ ↔ φ = ψ := by simp [Dia.dia]
attribute [simp, grind =] inj_and inj_or inj_imp inj_neg inj_box inj_dia inj_rhd

@[simp, grind =]
lemma inj_iff : (φ₁ ⭤ φ₂) = (ψ₁ ⭤ ψ₂) ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [LogicalConnective.iff]; grind;


section ToString

variable [ToString α]

def toStr : Formula α → String
  -- | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | □φ      => "\\Box " ++ toStr φ
  -- | ◇φ      => "\\Diamond " ++ toStr φ
  | φ ➝ ψ   => "\\left(" ++ toStr φ ++ " \\to " ++ toStr ψ ++ "\\right)"
  | φ ▷ ψ   => "\\left(" ++ toStr φ ++ " \\rhd " ++ toStr ψ ++ "\\right)"
  -- | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  -- | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "   ++ toStr ψ ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

end ToString

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp     : ∀ (φ ψ), C (φ ➝ ψ))
    (hbox    : ∀ (φ), C (□φ))
    (hrhd    : ∀ (φ ψ), C (φ ▷ ψ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | φ ➝ ψ   => himp φ ψ
  | φ ▷ ψ   => hrhd φ ψ

@[induction_eliminator]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ), C φ → C ψ → C (φ ➝ ψ))
  (hbox    : ∀ (φ), C φ → C (□φ))
  (hrhd    : ∀ (φ ψ), C φ → C ψ → C (φ ▷ ψ))
  : (φ : Formula α) → C φ
  | ⊥      => hfalsum
  | atom a => hatom a
  | φ ➝ ψ  => himp φ ψ (rec' hfalsum hatom himp hbox hrhd φ) (rec' hfalsum hatom himp hbox hrhd ψ)
  | □φ     => hbox φ (rec' hfalsum hatom himp hbox hrhd φ)
  | φ ▷ ψ  => hrhd φ ψ (rec' hfalsum hatom himp hbox hrhd φ) (rec' hfalsum hatom himp hbox hrhd ψ)

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
    cases χ using cases'
    case himp φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp_all)
      | isFalse hp => isFalse (by simp_all)
    any_goals simpa using isFalse not_false
  | □φ, ψ => by
    cases ψ
    case box φ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse $ by simp [hp, eq_box];
    all_goals
    . apply isFalse;
      simp;
  | φ ▷ ψ, χ => by
    cases χ using cases'
    case hrhd φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp_all )
      | isFalse hp => isFalse (by simp_all)
    any_goals simpa using isFalse not_false

instance : DecidableEq (Formula α) := hasDecEq

end Decidable

end Formula





end LO.InterpretabilityLogic
end
