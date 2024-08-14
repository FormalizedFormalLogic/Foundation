import Logic.Logic.HilbertStyle.Lukasiewicz
import Logic.Vorspiel.Collection
import Logic.Modal.Standard.System

namespace LO.Modal.Standard

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
  | p ⟶ q   => "\\left(" ++ toStr p ++ " \\to " ++ toStr q ++ "\\right)"
  -- | p ⋏ q   => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  -- | p ⋎ q   => "\\left(" ++ toStr p ++ " \\lor "   ++ toStr q ++ "\\right)"

instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

instance : ToString (Formula α) := ⟨toStr⟩

instance : Coe α (Formula α) := ⟨atom⟩

end ToString

-- @[simp] lemma neg_top : ~(⊤ : Formula α) = ⊥ := rfl

@[simp] lemma neg_bot : ~(⊥ : Formula α) = ⊤ := rfl

-- @[simp] lemma neg_atom (a : α) : ~(atom a) = natom a := rfl

-- @[simp] lemma neg_natom (a : α) : ~(natom a) = atom a := rfl

-- @[simp] lemma neg_and (p q : Formula α) : ~(p ⋏ q) = ~p ⋎ ~q := rfl

-- @[simp] lemma neg_or (p q : Formula α) : ~(p ⋎ q) = ~p ⋏ ~q := rfl

-- @[simp] lemma neg_neg' (p : Formula α) : ~~p = p := neg_neg p

-- @[simp] lemma neg_box (p : Formula α) : ~(□p) = ◇(~p) := rfl

-- @[simp] lemma neg_dia (p : Formula α) : ~(◇p) = □(~p) := rfl

/-
@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by
  constructor
  · intro h; simpa using congr_arg (~·) h
  · exact congr_arg _
-/

lemma or_eq (p q : Formula α) : or p q = p ⋎ q := rfl

lemma and_eq (p q : Formula α) : and p q = p ⋏ q := rfl

lemma imp_eq (p q : Formula α) : imp p q = p ⟶ q := rfl

lemma neg_eq (p : Formula α) : neg p = ~p := rfl

lemma box_eq (p : Formula α) : box p = □p := rfl

lemma dia_eq (p : Formula α) : dia p = ◇p := rfl

lemma iff_eq (p q : Formula α) : p ⟷ q = (p ⟶ q) ⋏ (q ⟶ p) := rfl

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (p₁ q₁ p₂ q₂ : Formula α) : p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp[Arrow.arrow]

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
| p ⟶ q   => max p.complexity q.complexity + 1
| □p   => p.complexity + 1

/-- Max numbers of `□` -/
def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | p ⟶ q => max p.degree q.degree
  | □p => p.degree + 1

@[simp] lemma degree_neg (p : Formula α) : degree (~p) = degree p := by induction p <;> simp_all [degree, neg, neg_eq]
@[simp] lemma degree_imp (p q : Formula α) : degree (p ⟶ q) = max (degree p) (degree q) := by simp [degree, imp_eq]

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp     : ∀ (p q : Formula α), C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p
  | p ⟶ q   => himp p q

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hbox    : ∀ (p : Formula α), C p → C (□p))
  : (p : Formula α) → C p
  | ⊥      => hfalsum
  | atom a => hatom a
  | p ⟶ q  => himp p q (rec' hfalsum hatom himp hbox p) (rec' hfalsum hatom himp hbox q)
  | □p     => hbox p (rec' hfalsum hatom himp hbox p)

-- @[simp] lemma complexity_neg (p : Formula α) : complexity (~p) = p.complexity + 1 :=
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
  | p ⟶ q, r => by
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

abbrev Theory (α) := Set (Formula α)

instance : Collection (Formula α) (Theory α) := inferInstance

abbrev AxiomSet (α) := Set (Formula α)

section Subformula

variable [DecidableEq α]

def Formula.Subformulas: Formula α → Finset (Formula α)
  | atom a => {(atom a)}
  | ⊥      => {⊥}
  | p ⟶ q  => insert (p ⟶ q) (p.Subformulas ∪ q.Subformulas)
  | □p     => insert (□p) p.Subformulas

prefix:70 "𝒮 " => Formula.Subformulas

namespace Formula.Subformulas

@[simp]
lemma mem_self (p : Formula α) : p ∈ 𝒮 p := by induction p <;> { simp [Subformulas]; try tauto; }

variable {p q r : Formula α}

lemma mem_imp (h : (q ⟶ r) ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p ∧ r ∈ 𝒮 p := by
  induction p using Formula.rec' with
  | himp => simp_all [Subformulas]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [Subformulas]; try rcases h with (hq | hr); simp_all; simp_all;

lemma mem_imp₁ (h : (q ⟶ r) ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p := mem_imp (r := r) |>.1

lemma mem_imp₂ (h : (q ⟶ r) ∈ 𝒮 p := by assumption) : r ∈ 𝒮 p := mem_imp (r := r) |>.2

/-
lemma mem_and (h : (q ⋏ r) ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p ∧ r ∈ 𝒮 p := by
  induction p using Formula.rec' with
  | hand => simp_all [Subformulas]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [Subformulas]; try rcases h with (hq | hr); simp_all; simp_all;

lemma mem_and₁ (h : (q ⋏ r) ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p := mem_and (r := r) |>.1

lemma mem_and₂ (h : (q ⋏ r) ∈ 𝒮 p := by assumption) : r ∈ 𝒮 p := mem_and (r := r) |>.2

lemma mem_or (h : (q ⋎ r) ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p ∧ r ∈ 𝒮 p := by
  induction p using Formula.rec' with
  | hor => simp_all [Subformulas]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [Subformulas]; try rcases h with (hq | hr); simp_all; simp_all;

lemma mem_or₁ (h : (q ⋎ r) ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p := mem_or (r := r) |>.1

lemma mem_or₂ (h : (q ⋎ r) ∈ 𝒮 p := by assumption) : r ∈ 𝒮 p := mem_or (r := r) |>.2

lemma mem_dia (h : ◇q ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p := by
  induction p using Formula.rec' <;> {
    simp_all [Subformulas];
    try rcases h with (hq | hr); simp_all; simp_all;
  };

attribute [aesop safe 5 forward]
  mem_and₁
  mem_and₂
  mem_or₁
  mem_or₂
  mem_box
  mem_dia
-/

lemma mem_box (h : □q ∈ 𝒮 p := by assumption) : q ∈ 𝒮 p := by
  induction p using Formula.rec' <;> {
    simp_all [Subformulas];
    try rcases h with (hq | hr); simp_all; simp_all;
  };

attribute [aesop safe 5 forward]
  mem_imp₁
  mem_imp₂
  mem_box

@[simp]
lemma complexity_lower (h : q ∈ 𝒮 p) : q.complexity ≤ p.complexity  := by
  induction p using Formula.rec' with
  | himp p₁ p₂ ihp₁ ihp₂ =>
    simp_all [Subformulas];
    rcases h with _ | h₁ | h₂;
    . subst_vars; simp [Formula.complexity];
    . have := ihp₁ h₁; simp [Formula.complexity]; omega;
    . have := ihp₂ h₂; simp [Formula.complexity]; omega;
  | hbox p ihp =>
    simp_all [Subformulas];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.complexity];
    . have := ihp h₁; simp [Formula.complexity]; omega;
  | hatom => simp_all [Subformulas];
  | hfalsum => simp_all [Subformulas, Formula.complexity];

/-
@[simp]
lemma degree_lower (h : q ∈ 𝒮 p) : q.degree ≤ p.degree := by
  induction p using Formula.rec' with
  | himp p₁ p₂ ihp₁ ihp₂ =>
    simp_all [Subformulas];
    rcases h with rfl | h₁ | h₂;
    . simp [Formula.degree];
    . have := ihp₁ h₁; simp [Formula.degree]; omega;
    . have := ihp₂ h₂; simp [Formula.degree]; omega;
  | hbox p ihp =>
    simp_all [Subformulas];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.degree];
    . have := ihp h₁; simp [Formula.degree]; omega;
  | hatom =>
    simp_all [Subformulas];
    rcases h with rfl | rfl <;> simp [Formula.degree];
  | hfalsum => simp_all [Subformulas, Formula.degree];

lemma sub_of_top (h : p ∈ 𝒮 ⊤) : p = ⊤ := by simp_all [Subformulas];
lemma sub_of_bot (h : p ∈ 𝒮 ⊥) : p = ⊥ := by simp_all [Subformulas];


lemma mem_atom_of_mem_natom (h : (natom a) ∈ 𝒮 p) : (atom a) ∈ 𝒮 p := by
  induction p using Formula.rec' with
  | hand q r ihq ihr =>
    simp_all [Subformulas];
    rcases h with (hq | hr);
    . left; exact ihq hq;
    . right; exact ihr hr;
  | hor q r ihq ihr =>
    simp_all [Subformulas];
    rcases h with (hq | hr);
    . left; exact ihq hq;
    . right; exact ihr hr;
  | _ => simp_all [Subformulas];

attribute [aesop safe forward] mem_atom_of_mem_natom
-/

end Formula.Subformulas


open Formula
class Theory.SubformulaClosed (T : Theory α) where
  imp_closed    : ∀ {p q}, p ⟶ q ∈ T → p ∈ T ∧ q ∈ T
  box_closed   : ∀ {p}, □p ∈ T → p ∈ T

namespace Theory.SubformulaClosed

instance {p : Formula α} : Theory.SubformulaClosed (𝒮 p).toSet where
  box_closed   := by aesop;
  imp_closed   := by aesop;

variable {p : Formula α} {T : Theory α} [T_closed : T.SubformulaClosed]

lemma sub_mem_box (h : □p ∈ T) : p ∈ T := T_closed.box_closed h
lemma sub_mem_imp (h : p ⟶ q ∈ T) : p ∈ T ∧ q ∈ T := T_closed.imp_closed h
lemma sub_mem_imp₁ (h : p ⟶ q ∈ T) : p ∈ T := (T_closed.imp_closed h).1
lemma sub_mem_imp₂ (h : p ⟶ q ∈ T) : q ∈ T := (T_closed.imp_closed h).2

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply sub_mem_box   $ by assumption
    | apply sub_mem_imp₁  $ by assumption
    | apply sub_mem_imp₂  $ by assumption
  )

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
  | ~p     => p.atoms
  | □p  => p.atoms
  | p ⟶ q => p.atoms ∪ q.atoms
  | p ⋏ q  => p.atoms ∪ q.atoms
  | p ⋎ q  => p.atoms ∪ q.atoms
prefix:70 "𝒜 " => Formula.atoms

@[simp]
lemma mem_atoms_iff_mem_subformulae {a : α} {p : Formula α} : a ∈ 𝒜 p ↔ (atom a) ∈ 𝒮 p := by
  induction p using Formula.rec' <;> simp_all [Subformulas, atoms];

end Formula

end Atoms


section Complement

variable [DecidableEq α]

namespace Formula

def negated : Formula α → Bool
  | ~_ => true
  | _  => false

lemma negated_iff {p : Formula α} : p.negated ↔ ∃ q, p = ~q := by
  induction p using Formula.rec' <;> simp [negated]

lemma not_negated_iff {p : Formula α} : ¬p.negated ↔ ∀ q, p ≠ ~q := by
  induction p using Formula.rec' <;> simp [negated]

def complement (p : Formula α) : Formula α := if p.negated then p else ~p
postfix:80 "⁻" => complement

lemma eq_complement_negated {p : Formula α} (hp : p.negated) : p⁻ = p := by
  induction p using Formula.rec' <;> simp_all [negated, complement]

lemma eq_complement_not_negated {p : Formula α} (hp : ¬p.negated) : p⁻ = ~p := by
  induction p using Formula.rec' <;> simp_all [negated, complement]


abbrev complement_subformula (p : Formula α) : Finset (Formula α) := (𝒮 p) ∪ (Finset.image (·⁻) $ 𝒮 p)
prefix:70 "𝒮⁻ " => Formula.ComplementSubformula

end Formula

end Complement
-/

end LO.Modal.Standard
