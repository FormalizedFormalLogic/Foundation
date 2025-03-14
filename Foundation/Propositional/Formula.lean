import Foundation.Logic.LogicSymbol

namespace LO.Propositional

inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

namespace Formula

abbrev neg {α : Type u} (φ : Formula α) : Formula α := imp φ falsum

abbrev verum {α : Type u} : Formula α := imp falsum falsum

instance : LogicalConnective (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : LO.NegAbbrev (Formula α) := by tauto;

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | ∼φ      => "\\lnot " ++ toStr φ
  | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | φ ➝ ψ   => "\\left(" ++ toStr φ ++ " \\rightarrow " ++ toStr ψ ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩
instance : ToString (Formula α) := ⟨toStr⟩

end ToString

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Arrow.arrow]

@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp[Tilde.tilde]


lemma neg_def (φ : Formula α) : ∼φ = φ ➝ ⊥ := rfl

lemma top_def : (⊤ : Formula α) = ⊥ ➝ ⊥ := rfl


lemma iff_def (φ ψ : Formula α) : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := by rfl

def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| φ ➝ ψ  => max φ.complexity ψ.complexity + 1
| φ ⋏ ψ   => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ   => max φ.complexity ψ.complexity + 1

@[simp] lemma complexity_bot : complexity (⊥ : Formula α) = 0 := rfl

@[simp] lemma complexity_atom (a : α) : complexity (atom a) = 0 := rfl

@[simp] lemma complexity_imp (φ ψ : Formula α) : complexity (φ ➝ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_imp' (φ ψ : Formula α) : complexity (imp φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_and (φ ψ : Formula α) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_and' (φ ψ : Formula α) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[simp] lemma complexity_or (φ ψ : Formula α) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
@[simp] lemma complexity_or' (φ ψ : Formula α) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp    : ∀ (φ ψ : Formula α), C (φ ➝ ψ))
    (hand    : ∀ (φ ψ : Formula α), C (φ ⋏ ψ))
    (hor     : ∀ (φ ψ : Formula α), C (φ ⋎ ψ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ ➝ ψ   => himp φ ψ
  | φ ⋏ ψ   => hand φ ψ
  | φ ⋎ ψ   => hor φ ψ

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ➝ ψ))
  (hand    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋏ ψ))
  (hor     : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋎ ψ))
  : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ ➝ ψ  => himp φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋏ ψ   => hand φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋎ ψ   => hor φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)

section Decidable

variable [DecidableEq α]

def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ)
  | ⊥, ψ => by
    cases ψ using cases' <;>
    { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, ψ => by
    cases ψ using cases' <;> try { simp; exact isFalse not_false }
    simp; exact decEq _ _
  | φ ➝ ψ, χ => by
    cases χ using cases' <;> try { simp; exact isFalse not_false }
    case himp φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | φ ⋏ ψ, χ => by
    cases χ using cases' <;> try { simp; exact isFalse not_false }
    case hand φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])
  | φ ⋎ ψ, χ => by
    cases χ using cases' <;> try { simp; exact isFalse not_false }
    case hor φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp[hp, hq])
      | isFalse hp => isFalse (by simp[hp])

instance : DecidableEq (Formula α) := hasDecEq

end Decidable

section Encodable

variable [Encodable α]
open Encodable

def toNat : Formula α → ℕ
  | ⊥       => (Nat.pair 0 0) + 1
  | atom a  => (Nat.pair 1 <| encode a) + 1
  | φ ➝ ψ   => (Nat.pair 2 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋏ ψ   => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋎ ψ   => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1

def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => some ⊥
    | 1 => (decode c).map Formula.atom
    | 2 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ➝ ψ
    | 3 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ⋏ ψ
    | 4 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ⋎ ψ
    | _ => none

lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek, Option.map_some'];
  | ⊥       => by simp [toNat, ofNat]
  | φ ➝ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | φ ⋏ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | φ ⋎ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]

instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

end Encodable


def letterless : Formula α → Prop
  | .atom _ => False
  | ⊥ => True
  | φ ➝ ψ => (φ.letterless) ∧ (ψ.letterless)
  | φ ⋏ ψ => (φ.letterless) ∧ (ψ.letterless)
  | φ ⋎ ψ => (φ.letterless) ∧ (ψ.letterless)

namespace letterless

variable {φ ψ : Formula α}

@[simp] lemma not_atom : ¬(letterless (atom p)) := by simp [letterless]

@[simp] lemma def_bot : (⊥ : Formula α).letterless := by simp [letterless]

@[simp] lemma def_top : (⊤ : Formula α).letterless := by simp [letterless]


lemma def_imp : (φ ➝ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]
lemma def_imp₁ : (φ ➝ ψ).letterless → φ.letterless := λ h => def_imp h |>.1
lemma def_imp₂ : (φ ➝ ψ).letterless → ψ.letterless := λ h => def_imp h |>.2

lemma def_and : (φ ⋏ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]
lemma def_and₁ : (φ ⋏ ψ).letterless → φ.letterless := λ h => def_and h |>.1
lemma def_and₂ : (φ ⋏ ψ).letterless → ψ.letterless := λ h => def_and h |>.2

lemma def_or : (φ ⋎ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]
lemma def_or₁ : (φ ⋎ ψ).letterless → φ.letterless := λ h => def_or h |>.1
lemma def_or₂ : (φ ⋎ ψ).letterless → ψ.letterless := λ h => def_or h |>.2

end letterless

end Formula


section Subformula

variable [DecidableEq α]

def Formula.subformulas : Formula α → Finset (Formula α)
  | ⊥      => {⊥}
  | atom a => {atom a}
  | φ ➝ ψ  => insert (φ ➝ ψ) (φ.subformulas ∪ ψ.subformulas)
  | φ ⋏ ψ  => insert (φ ⋏ ψ) (φ.subformulas ∪ ψ.subformulas)
  | φ ⋎ ψ  => insert (φ ⋎ ψ) (φ.subformulas ∪ ψ.subformulas)

namespace Formula

variable {φ ψ χ : Formula α}

@[simp] lemma mem_self : φ ∈ φ.subformulas := by induction φ <;> { simp [subformulas]; try tauto; }

lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | himp =>
    simp_all only [subformulas, Finset.mem_insert, imp_inj, Finset.mem_union];
    rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all;
  | hor => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | hand => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | _ => simp_all [subformulas];

lemma mem_imp₁ (h : (ψ ➝ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := mem_imp h |>.1

lemma mem_imp₂ (h : (ψ ➝ χ) ∈ φ.subformulas) : χ ∈ φ.subformulas := mem_imp h |>.2

lemma mem_and (h : (ψ ⋏ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | himp => simp_all only [subformulas, Finset.mem_insert, imp_inj, Finset.mem_union]; tauto;
  | hor => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | hand =>
    simp_all only [subformulas, Finset.mem_insert, Finset.mem_union];
    rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all;
  | _ => simp_all [subformulas];

lemma mem_and₁ (h : (ψ ⋏ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := mem_and h |>.1

lemma mem_and₂ (h : (ψ ⋏ χ) ∈ φ.subformulas) : χ ∈ φ.subformulas := mem_and h |>.2

lemma mem_or (h : (ψ ⋎ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | himp => simp_all only [subformulas, Finset.mem_insert, imp_inj, Finset.mem_union]; tauto;
  | hor =>
    simp_all only [subformulas, Finset.mem_insert, Finset.mem_union];
    rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all;
  | hand => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | _ => simp_all [subformulas];

lemma mem_or₁ (h : (ψ ⋎ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := mem_or h |>.1

lemma mem_or₂ (h : (ψ ⋎ χ) ∈ φ.subformulas) : χ ∈ φ.subformulas := mem_or h |>.2


@[simp] lemma subset_imp₁ : φ.subformulas ⊆ (φ ➝ ψ).subformulas := by intro ξ; simp_all [subformulas];

@[simp] lemma subset_imp₂ : φ.subformulas ⊆ (ψ ➝ φ).subformulas := by intro ξ; simp_all [subformulas];

@[simp] lemma subset_and₁ : φ.subformulas ⊆ (φ ⋏ ψ).subformulas := by intro ξ; simp_all [subformulas];

@[simp] lemma subset_and₂ : φ.subformulas ⊆ (ψ ⋏ φ).subformulas := by intro ξ; simp_all [subformulas];

@[simp] lemma subset_or₁ : φ.subformulas ⊆ (φ ⋎ ψ).subformulas := by intro ξ; simp_all [subformulas];

@[simp] lemma subset_or₂ : φ.subformulas ⊆ (ψ ⋎ φ).subformulas := by intro ξ; simp_all [subformulas];

end Formula


abbrev FormulaSet (α) := Set (Formula α)

abbrev FormulaFinset (α) := Finset (Formula α)


class FormulaFinset.SubformulaClosed (Γ : FormulaFinset α) where
  closed : ∀ φ ∈ Γ, φ.subformulas ⊆ Γ

namespace FormulaFinset.SubformulaClosed

variable {φ ψ χ : Formula α} {Γ : FormulaFinset α} [Γ.SubformulaClosed]

lemma mem_and₁ (h : φ ⋏ ψ ∈ Γ) : φ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];
lemma mem_and₂ (h : φ ⋏ ψ ∈ Γ) : ψ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];
lemma mem_or₁ (h : φ ⋎ ψ ∈ Γ) : φ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];
lemma mem_or₂ (h : φ ⋎ ψ ∈ Γ) : ψ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];
lemma mem_imp₁ (h : φ ➝ ψ ∈ Γ) : φ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];
lemma mem_imp₂ (h : φ ➝ ψ ∈ Γ) : ψ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];

instance subformulaClosed_subformulas [DecidableEq α] {φ : Formula α} : SubformulaClosed (φ.subformulas) := ⟨by
  induction φ using Formula.rec' with
  | hatom => simp [Formula.subformulas];
  | hfalsum => simp [Formula.subformulas];
  | himp φ ψ ihφ ihψ =>
    rintro ξ hξ;
    rcases (by simpa [Formula.subformulas] using hξ) with (rfl | hξ | hξ);
    . tauto;
    . trans φ.subformulas;
      . exact ihφ _ hξ;
      . simp;
    . trans ψ.subformulas;
      . exact ihψ _ hξ;
      . simp;
  | hand φ ψ ihφ ihψ =>
    rintro ξ hξ;
    rcases (by simpa [Formula.subformulas] using hξ) with (rfl | hξ | hξ);
    . tauto;
    . trans φ.subformulas;
      . exact ihφ _ hξ;
      . simp;
    . trans ψ.subformulas;
      . exact ihψ _ hξ;
      . simp;
  | hor φ ψ ihφ ihψ =>
    rintro ξ hξ;
    rcases (by simpa [Formula.subformulas] using hξ) with (rfl | hξ | hξ);
    . tauto;
    . trans φ.subformulas;
      . exact ihφ _ hξ;
      . simp;
    . trans ψ.subformulas;
      . exact ihψ _ hξ;
      . simp;
⟩

end FormulaFinset.SubformulaClosed


class FormulaSet.SubformulaClosed (T : FormulaSet α) where
  closed : ∀ φ ∈ T, ↑φ.subformulas ⊆ T


namespace FormulaSet.SubformulaClosed

variable {φ ψ χ : Formula α} {T : FormulaSet α} [T.SubformulaClosed]

lemma mem_and₁ (h : φ ⋏ ψ ∈ T) : φ ∈ T := by apply closed _ h; simp [Formula.subformulas];
lemma mem_and₂ (h : φ ⋏ ψ ∈ T) : ψ ∈ T := by apply closed _ h; simp [Formula.subformulas];
lemma mem_or₁ (h : φ ⋎ ψ ∈ T) : φ ∈ T := by apply closed _ h; simp [Formula.subformulas];
lemma mem_or₂ (h : φ ⋎ ψ ∈ T) : ψ ∈ T := by apply closed _ h; simp [Formula.subformulas];
lemma mem_imp₁ (h : φ ➝ ψ ∈ T) : φ ∈ T := by apply closed _ h; simp [Formula.subformulas];
lemma mem_imp₂ (h : φ ➝ ψ ∈ T) : ψ ∈ T := by apply closed _ h; simp [Formula.subformulas];

instance subformulaClosed_subformulas [DecidableEq α] {φ : Formula α} : SubformulaClosed φ.subformulas.toSet := ⟨by
  simpa using FormulaFinset.SubformulaClosed.subformulaClosed_subformulas (φ := φ) |>.closed;
⟩

end FormulaSet.SubformulaClosed

end Subformula


section Substitution

abbrev Substitution (α) := α → (Formula α)

abbrev Substitution.id {α} : Substitution α := λ a => .atom a

namespace Formula

variable {φ ψ : Formula α} {s : Substitution α}

def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | φ ⋏ ψ   => φ.subst s ⋏ ψ.subst s
  | φ ⋎ ψ   => φ.subst s ⋎ ψ.subst s
  | φ ➝ ψ   => φ.subst s ➝ ψ.subst s

notation:80 φ "⟦" s "⟧" => Formula.subst s φ

namespace subst

@[simp] protected lemma subst_atom {a} : (.atom a)⟦s⟧ = s a := rfl

@[simp] protected lemma subst_bot : ⊥⟦s⟧ = ⊥ := rfl

@[simp] protected lemma subst_top : ⊤⟦s⟧ = ⊤ := rfl

@[simp] protected lemma subst_imp : (φ ➝ ψ)⟦s⟧ = φ⟦s⟧ ➝ ψ⟦s⟧ := rfl

@[simp] protected lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl

@[simp] protected lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl

@[simp] protected lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl

@[simp] protected lemma subst_iff : (φ ⭤ ψ)⟦s⟧ = (φ⟦s⟧ ⭤ ψ⟦s⟧) := rfl

end subst

end Formula

@[simp]
lemma Formula.subst_id {φ : Formula α} : φ⟦.id⟧ = φ := by induction φ using Formula.rec' <;> simp_all;

def Substitution.comp (s₁ s₂ : Substitution α) : Substitution α := λ a => (s₁ a)⟦s₂⟧
infixr:80 " ∘ " => Substitution.comp

@[simp]
lemma Formula.subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ using Formula.rec' <;> simp_all [Substitution.comp];


def ZeroSubstitution (α) := {s : Substitution α // ∀ {a : α}, ((.atom a)⟦s⟧).letterless }

lemma Formula.letterless_zeroSubst {φ : Formula α} {s : ZeroSubstitution α} : (φ⟦s.1⟧).letterless := by
  induction φ using Formula.rec' <;> simp [Formula.letterless, *];
  case hatom => exact s.2;


class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)

end Substitution



end LO.Propositional
