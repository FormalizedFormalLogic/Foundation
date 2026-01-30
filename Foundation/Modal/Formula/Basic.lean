module

public import Foundation.Modal.LogicSymbol
public import Foundation.Propositional.Formula.Basic

@[expose] public section

namespace LO

namespace Modal

@[grind]
inductive Formula (α : Type*) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

abbrev FormulaSet (α) := Set (Formula α)

abbrev FormulaFinset (α) := Finset (Formula α)


namespace Formula

variable {α} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ : Formula α}

abbrev neg (φ : Formula α) : Formula α := imp φ falsum
abbrev verum : Formula α := imp falsum falsum
abbrev top : Formula α := imp falsum falsum
abbrev or (φ ψ : Formula α) : Formula α := imp (neg φ) ψ
abbrev and (φ ψ : Formula α) : Formula α := neg (imp φ (neg ψ))
abbrev dia (φ : Formula α) : Formula α := neg (box (neg φ))

instance : BasicModalLogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

instance : ŁukasiewiczAbbrev (Formula α) where
  top := rfl
  neg := rfl
  or := rfl
  and := rfl

instance : DiaByBox (Formula α) := ⟨rfl⟩

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

@[grind =] lemma eq_verum_neg_falsum : ⊤ = ∼(⊥ : Formula α) := rfl

lemma falsum_eq : (⊥ : Formula α) = falsum := rfl
lemma verum_eq : (⊤ : Formula α) = verum := rfl
lemma or_eq  : φ ⋎ ψ = or φ ψ := rfl
lemma and_eq : φ ⋏ ψ = and φ ψ := rfl
lemma imp_eq : φ ➝ ψ = imp φ ψ := rfl
lemma neg_eq : ∼φ = neg φ := rfl
lemma box_eq : □φ = box φ := rfl
lemma dia_eq : ◇φ = dia φ := rfl
lemma iff_eq : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := rfl
attribute [grind =_] falsum_eq verum_eq or_eq and_eq imp_eq neg_eq box_eq dia_eq iff_eq

lemma inj_and : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Wedge.wedge]
lemma inj_or  : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Vee.vee]
lemma inj_imp : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Arrow.arrow]
lemma inj_neg : ∼φ = ∼ψ ↔ φ = ψ := by simp [Tilde.tilde]
lemma inj_box : □φ = □ψ ↔ φ = ψ := by simp [Box.box]
lemma inj_dia : ◇φ = ◇ψ ↔ φ = ψ := by simp [Dia.dia]
-- attribute [grind! =>] inj_and inj_or inj_imp inj_neg inj_box inj_dia

instance : InjectiveBox (Formula α) := ⟨λ _ _ => inj_box.mp⟩
instance : InjectiveDia (Formula α) := ⟨λ _ _ => inj_dia.mp⟩

/-- Formula complexity -/
@[grind]
def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| φ ➝ ψ   => max φ.complexity ψ.complexity + 1
| □φ   => φ.complexity + 1

/-- Max numbers of `□` -/
@[grind]
def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | φ ➝ ψ => max φ.degree ψ.degree
  | □φ => φ.degree + 1

@[grind =] lemma degree_falsum : degree (⊥ : Formula α) = 0 := by rfl
@[grind =] lemma degree_imp : degree (φ ➝ ψ) = max (degree φ) (degree ψ) := by rfl
@[simp, grind =] lemma degree_neg : degree (∼φ) = degree φ := by dsimp [degree]; omega;


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

@[induction_eliminator]
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

section Decidable

variable [DecidableEq α]

def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ)
  | ⊥, ψ => by
    cases ψ using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, ψ => by
    cases ψ using cases';
    case hatom b =>
      exact match decEq a b with
      | isTrue h  => isTrue (h ▸ rfl)
      | isFalse h => isFalse (by simp [h])
    all_goals
    . apply isFalse;
      simp;
  | φ ➝ ψ, χ => by
    cases χ using cases';
    case himp φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse $ by grind [Formula.inj_imp]
      | isFalse hp => isFalse $ by grind [Formula.inj_imp]
    all_goals
    . apply isFalse;
      simp;
  | □φ, ψ => by
    cases ψ
    case box φ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse $ by grind [Formula.inj_box]
    all_goals
    . apply isFalse;
      simp;
instance : DecidableEq (Formula α) := hasDecEq

end Decidable


def isBox : Formula α → Bool
  | box _ => true
  | _  => false

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

@[grind]
def negated : Formula α → Bool
  | ∼_ => True
  | _  => False

@[simp] lemma negated_def : (∼φ).negated := by simp [negated]

@[simp, grind =]
lemma negated_imp : (φ ➝ ψ).negated ↔ (ψ = ⊥) := by
  dsimp [negated];
  split;
  . simp_all [Formula.imp_eq]; rfl;
  . simp_all [Formula.imp_eq]; simpa;

lemma negated_iff [DecidableEq α] : φ.negated ↔ ∃ ψ, φ = ∼ψ := by
  induction φ using Formula.cases_neg with
  | himp => grind;
  | _ => simp [negated]

lemma not_negated_iff [DecidableEq α] : ¬φ.negated ↔ ∀ ψ, φ ≠ ∼ψ := by
  induction φ using Formula.cases_neg with
  | himp => grind;
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
      have : c < e + 1 := Nat.lt_succ_iff.mpr $ Nat.unpair_right_le _
      do
        let φ <- ofNat c
        return □φ
    | 3 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ➝ ψ
    | _ => none

lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek];
  | ⊥       => by simp [toNat, ofNat]
  | □φ      => by simp [toNat, ofNat, ofNat_toNat φ]
  | φ ➝ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end Encodable

end Formula


section Substitution
section Subformula

@[grind]
def Formula.subformulas [DecidableEq α] : Formula α → FormulaFinset α
  | atom a => {(atom a)}
  | ⊥      => {⊥}
  | φ ➝ ψ  => insert (φ ➝ ψ) (φ.subformulas ∪ ψ.subformulas)
  | □φ     => insert (□φ) φ.subformulas

namespace Formula.subformulas

variable [DecidableEq α] {φ ψ χ ξ : Formula α}

@[simp, grind .] lemma mem_self {φ : Formula α} : φ ∈ φ.subformulas := by induction φ <;> simp [subformulas]

@[grind ⇒]
protected lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with ⟨rfl, rfl⟩ | h | h <;> simp_all [subformulas];
  | _ => simp_all [subformulas];

@[grind ⇒]
protected lemma mem_box (h : □ψ ∈ φ.subformulas) : ψ ∈ φ.subformulas := by
  induction φ with
  | hbox ψ ihψ =>
    simp only [subformulas, Finset.mem_insert, inj_box] at h ⊢;
    rcases h with rfl | h <;> simp_all;
  | himp ψ χ ihψ ihχ =>
    simp_all only [subformulas, Finset.mem_insert, reduceCtorEq, Finset.mem_union, false_or];
    grind;
  | _ => simp_all [subformulas];

@[grind ⇒]
protected lemma mem_neg (h : (∼ψ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ ⊥ ∈ φ.subformulas := subformulas.mem_imp h

@[grind ⇒]
protected lemma mem_and (h : (ψ ⋏ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  rw [ŁukasiewiczAbbrev.and] at h;
  grind;

@[grind ⇒]
protected lemma mem_or (h : (ψ ⋎ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  rw [ŁukasiewiczAbbrev.or] at h;
  grind;

example {_ : φ ∈ φ.subformulas} : φ ∈ φ.subformulas := by grind;
example {_ : ψ ➝ χ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind
example {_ : ψ ➝ χ ∈ φ.subformulas} : χ ∈ φ.subformulas := by grind
example {_ : □ψ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind;
example {_ : ∼ψ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind;
example {_ : ∼ψ ∈ φ.subformulas} : ⊥ ∈ φ.subformulas := by grind;
example {_ : ψ ⋏ χ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind
example {_ : ψ ⋎ χ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind
example {_ : ψ ➝ χ ∈ φ.subformulas} : χ ∈ φ.subformulas := by grind
example {_ : ψ ⋏ (ψ ⋎ □(□χ ➝ ξ)) ∈ φ.subformulas} : χ ∈ φ.subformulas := by grind;

lemma complexity_lower (h : ψ ∈ φ.subformulas) : ψ.complexity ≤ φ.complexity := by
  induction φ using Formula.rec' with
  | hfalsum => simp_all [subformulas, complexity];
  | hatom => simp_all [subformulas, complexity];
  | hbox φ ihφ =>
    simp only [subformulas, Finset.mem_insert] at h;
    rcases h with rfl | h;
    . rfl;
    . simp_all [complexity];
      omega;
  | himp φ₁ φ₂ ihφ₁ ihφ₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    . rfl;
    . simp [complexity];
      have := ihφ₁ h;
      omega;
    . simp [complexity];
      have := ihφ₂ h;
      omega;

lemma subset_of_mem (hψ : ψ ∈ φ.subformulas) : (ψ.subformulas ⊆ φ.subformulas) := by
  intro ξ hξ;
  induction ψ with
  | hatom => simp_all [Formula.subformulas];
  | hfalsum => simp_all [Formula.subformulas];
  | himp ψ₁ ψ₂ ihψ₁ ihψ₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at hξ;
    rcases hξ with rfl | hξ | hξ <;> grind;
  | hbox ψ ihψ =>
    simp only [subformulas, Finset.mem_insert] at hξ;
    rcases hξ with rfl | hξ <;> grind;

end Formula.subformulas


def FormulaSet.SubformulaClosed [DecidableEq α] (Γ : FormulaSet α) : Prop := ∀ φ ∈ Γ, φ.subformulas.toSet ⊆ Γ

namespace FormulaSet.SubformulaClosed

variable {α} [DecidableEq α] {φ ψ : Formula α} {Γ : FormulaSet α}

lemma of_mem_imp₁ (h : SubformulaClosed Γ) : φ ➝ ψ ∈ Γ → φ ∈ Γ := by
  intro hφψ;
  apply @h _ hφψ;
  simp [Formula.subformulas];

lemma of_mem_imp₂ (h : SubformulaClosed Γ) : φ ➝ ψ ∈ Γ → ψ ∈ Γ := by
  intro hφψ;
  apply @h _ hφψ;
  simp [Formula.subformulas];

lemma of_mem_box (h : SubformulaClosed Γ) : □φ ∈ Γ → φ ∈ Γ := by
  intro hφ;
  apply @h _ hφ;
  simp [Formula.subformulas];

end FormulaSet.SubformulaClosed


class FormulaSet.IsSubformulaClosed [DecidableEq α] (Γ : FormulaSet α) where
  closed : Γ.SubformulaClosed

namespace FormulaSet.IsSubformulaClosed

variable {α} [DecidableEq α] {φ ψ : Formula α} {Γ : FormulaSet α} [Γ.IsSubformulaClosed]

lemma of_mem_imp₁ : φ ➝ ψ ∈ Γ → φ ∈ Γ := SubformulaClosed.of_mem_imp₁ IsSubformulaClosed.closed
lemma of_mem_imp₂ : φ ➝ ψ ∈ Γ → ψ ∈ Γ := SubformulaClosed.of_mem_imp₂ IsSubformulaClosed.closed
lemma of_mem_box : □φ ∈ Γ → φ ∈ Γ := SubformulaClosed.of_mem_box IsSubformulaClosed.closed

end FormulaSet.IsSubformulaClosed


instance {φ : Formula α} [DecidableEq α] : FormulaSet.IsSubformulaClosed (φ.subformulas.toSet) where
  closed := fun _ hψ ↦ Formula.subformulas.subset_of_mem hψ


end Subformula


abbrev Substitution (α) := α → (Formula α)

def Formula.subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | □φ      => □(φ.subst s)
  | φ ➝ ψ   => φ.subst s ➝ ψ.subst s

notation:80 φ "⟦" s "⟧" => Modal.Formula.subst s φ

namespace Formula.subst

variable {s : Substitution α} {φ ψ ξ : Formula α}

lemma subst_atom {a} : (.atom a)⟦s⟧ = s a := rfl
lemma subst_falsum : ⊥⟦s⟧ = ⊥ := rfl
lemma subst_verum : ⊤⟦s⟧ = ⊤ := rfl
lemma subst_imp : (φ ➝ ψ)⟦s⟧ = φ⟦s⟧ ➝ ψ⟦s⟧ := rfl
lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl
lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl
lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl
lemma subst_iff : (φ ⭤ ψ)⟦s⟧ = (φ⟦s⟧ ⭤ ψ⟦s⟧) := rfl
attribute [simp, grind =]
  subst_atom
  subst_falsum
  subst_verum
  subst_neg
  subst_and
  subst_or
  subst_imp
  subst_iff

@[simp, grind =] lemma subst_box : (□φ)⟦s⟧ = □(φ⟦s⟧) := rfl
@[simp, grind =] lemma subst_boxItr : (□^[n]φ)⟦s⟧ = □^[n](φ⟦s⟧) := by induction n <;> grind;
@[simp, grind =] lemma subst_dia : (◇φ)⟦s⟧ = ◇(φ⟦s⟧) := rfl
@[simp, grind =] lemma subst_diaItr : (◇^[n]φ)⟦s⟧ = ◇^[n](φ⟦s⟧) := by induction n <;> grind;

end Formula.subst

abbrev Substitution.id {α} : Substitution α := λ a => .atom a

@[simp]
lemma Formula.subst.def_id {φ : Formula α} : φ⟦.id⟧ = φ := by induction φ <;> simp_all;


def Substitution.comp (s₁ s₂ : Substitution α) : Substitution α := λ a => (s₁ a)⟦s₂⟧
infixr:80 " ∘ " => Substitution.comp

@[simp]
lemma Formula.subst.def_comp {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ <;> simp_all [Substitution.comp];


class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)

end Substitution



section Atoms

namespace Formula

variable {α} [DecidableEq α]

def atoms : Formula α → Finset α
  | ⊥ => ∅
  | .atom v => {v}
  | □φ => φ.atoms
  | φ ➝ ψ => φ.atoms ∪ ψ.atoms

lemma iff_mem_atoms_mem_subformula {a : α} {φ : Formula α} : (a ∈ φ.atoms) ↔ (atom a ∈ φ.subformulas) := by
  induction φ <;> simp_all [atoms, subformulas];

section

variable {a : ℕ} {φ : Formula ℕ}

def freshAtom (φ : Formula ℕ) : ℕ := if h : φ.atoms.Nonempty then φ.atoms.max' h + 1 else 0

lemma le_max_atoms_of_mem_atoms {a : ℕ} (ha : a ∈ φ.atoms) : a ≤ φ.atoms.max' (⟨a, ha⟩) := by
  induction φ with
  | hfalsum => simp [atoms] at ha;
  | hatom b => simp [atoms] at ha ⊢; omega;
  | hbox φ ihφ => apply ihφ; simpa using ha;
  | himp φ ψ ihφ ihψ =>
    rcases (show a ∈ φ.atoms ∨ a ∈ ψ.atoms by simpa [atoms] using ha) with (hφ | hψ);
    . by_cases hψ : ψ.atoms.Nonempty;
      . simp [atoms, Finset.max'_union ⟨_, hφ⟩ hψ, ihφ hφ];
      . simp [atoms, Finset.not_nonempty_iff_eq_empty.mp hψ, ihφ hφ];
    . by_cases hφ : φ.atoms.Nonempty;
      . simp [atoms, Finset.max'_union hφ ⟨_, hψ⟩, ihψ hψ];
      . simp [atoms, Finset.not_nonempty_iff_eq_empty.mp hφ, ihψ hψ];

lemma le_max_atoms_freshAtom (h : φ.atoms.Nonempty) : Finset.max' φ.atoms h < φ.freshAtom := by
  simp only [freshAtom, Finset.max'_lt_iff];
  intro a ha;
  split;
  . have := le_max_atoms_of_mem_atoms ha;
    omega;
  . exfalso;
    have : φ.atoms.Nonempty := ⟨a, ha⟩;
    contradiction;

lemma ne_freshAtom_of_mem_subformulas (h : atom a ∈ φ.subformulas) : φ.freshAtom ≠ a := by
  by_contra hC; subst hC;
  apply Nat.not_lt.mpr $ le_max_atoms_of_mem_atoms $ iff_mem_atoms_mem_subformula.mpr h;
  apply le_max_atoms_freshAtom;

end

end Formula

end Atoms




section Letterless

variable {α} {a : α} {n : ℕ} {φ ψ : Formula α}

namespace Formula

@[grind]
def Letterless : Formula α → Prop
  | atom _ => False
  | ⊥ => True
  | □φ => φ.Letterless
  | φ ➝ ψ => (φ.Letterless) ∧ (ψ.Letterless)

@[grind .] lemma not_letterless_atom {a : α} : ¬(Formula.Letterless (.atom a)) := by grind;
@[grind .] lemma letterless_falsum : (⊥ : Formula α).Letterless := by simp [Letterless];
@[grind .] lemma letterless_verum : (⊤ : Formula α).Letterless := by simp [Letterless];
@[grind =] lemma letterless_imp : (φ ➝ ψ).Letterless ↔ φ.Letterless ∧ ψ.Letterless := by simp [Letterless];
@[grind =] lemma letterless_neg : (∼φ).Letterless ↔ φ.Letterless := by grind;
@[grind =] lemma letterless_and : (φ ⋏ ψ).Letterless ↔ φ.Letterless ∧ ψ.Letterless := by grind;
@[grind =] lemma letterless_or : (φ ⋎ ψ).Letterless ↔ φ.Letterless ∧ ψ.Letterless := by grind;
@[grind =] lemma letterless_iff : (φ ⭤ ψ).Letterless ↔ φ.Letterless ∧ ψ.Letterless := by grind [iff_eq];
@[grind =] lemma letterless_box : (□φ).Letterless ↔ φ.Letterless := by simp [Letterless];
@[grind =] lemma letterless_boxItr : (□^[n]φ).Letterless ↔ φ.Letterless := by induction n <;> grind;
@[grind =] lemma letterless_dia : (◇φ).Letterless ↔ φ.Letterless := by grind;
@[grind =] lemma letterless_diaItr : (◇^[n]φ).Letterless ↔ φ.Letterless := by induction n <;> grind;

@[grind =]
lemma letterless_lconj₂ {l : List (Formula α)} : (l.conj₂).Letterless ↔ ∀ φ ∈ l, φ.Letterless := by
  induction l using List.induction_with_singleton <;> simp_all [Letterless];

@[grind =]
lemma letterless_fconj {s : Finset (Formula α)} : (s.conj).Letterless ↔ ∀ φ ∈ s, φ.Letterless := by
  apply Iff.trans letterless_lconj₂;
  simp;

@[grind =]
lemma letterless_lconj' {α β : Type*} {l : List β} {Φ : β → Formula α} : (l.conj' Φ).Letterless ↔ ∀ i ∈ l, (Φ i).Letterless := by
  apply Iff.trans letterless_lconj₂;
  grind;

lemma letterless_fconj' {α β : Type*} {s : Finset β} {Φ : β → Formula α} : (⩕ i ∈ s, Φ i).Letterless ↔ ∀ i ∈ s, (Φ i).Letterless := by
  apply Iff.trans letterless_lconj';
  simp;

@[grind =]
lemma subst_letterless (hφ : φ.Letterless) {s : Substitution α} : φ⟦s⟧ = φ := by induction φ <;> grind;

end Formula


namespace FormulaSet

variable {Γ : FormulaSet α} {φ : Formula α}

@[grind]
def Letterless (Γ : FormulaSet α) : Prop := ∀ φ ∈ Γ, φ.Letterless

@[simp, grind =]
lemma letterless_singleton {φ : Formula α} : ({φ} : FormulaSet α).Letterless ↔ φ.Letterless := by grind;

@[grind <=]
lemma letterless_of_mem (hΓ : Γ.Letterless) (hφ : φ ∈ Γ) : φ.Letterless := hΓ φ hφ

end FormulaSet

end Letterless

end Modal


section toModalFormula

namespace Propositional

@[grind]
def Formula.toModalFormula : Propositional.Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (toModalFormula φ) ➝ (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)

instance : Coe (Propositional.Formula α) (Modal.Formula α) := ⟨Formula.toModalFormula⟩
variable {α} {a : α} {φ ψ : Propositional.Formula α}

local postfix:80 "ᴹ" => Formula.toModalFormula
@[simp, grind =] lemma toModalFormula_atom : (.atom a)ᴹ = .atom a := by rfl
@[simp, grind =] lemma toModalFormula_top : (⊤ : Propositional.Formula α)ᴹ = ⊤ := by rfl
@[simp, grind =] lemma toModalFormula_bot : (⊥ : Propositional.Formula α)ᴹ = ⊥ := by rfl
@[simp, grind =] lemma toModalFormula_not : (∼φ)ᴹ = ∼(φᴹ) := by rfl
@[simp, grind =] lemma toModalFormula_imp : (φ ➝ ψ)ᴹ = (φᴹ) ➝ (ψᴹ) := by rfl
@[simp, grind =] lemma toModalFormula_and : (φ ⋏ ψ)ᴹ = (φᴹ) ⋏ (ψᴹ) := by rfl
@[simp, grind =] lemma toModalFormula_or : (φ ⋎ ψ)ᴹ = (φᴹ) ⋎ (ψᴹ) := by rfl
@[grind →] lemma toModalFormula_letterless (h : φ.Letterless) : φᴹ.Letterless := by induction φ <;> grind;

end Propositional

end toModalFormula


section toPropFormula

def Modal.Formula.toPropFormula (φ : Modal.Formula α) (_ : φ.degree = 0 := by grind) : Propositional.Formula α :=
  match φ with
  | atom a => Propositional.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => φ.toPropFormula ➝ ψ.toPropFormula

end toPropFormula



section ZeroSubst

namespace Modal

def ZeroSubstitution (α) := {s : Substitution α // ∀ {a : α}, ((.atom a)⟦s⟧).Letterless }

@[grind .]
lemma Formula.letterless_zeroSubst {φ : Formula α} {s : ZeroSubstitution α} : (φ⟦s.1⟧).Letterless := by induction φ <;> grind;

end Modal

instance : Coe (Propositional.ZeroSubstitution α) (Modal.ZeroSubstitution α) := ⟨λ ⟨s, p⟩ => ⟨λ φ => (s φ), λ {_} => Propositional.toModalFormula_letterless p⟩⟩

end ZeroSubst

end LO
