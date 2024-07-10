import Logic.Vorspiel.Collection
import Logic.Modal.LogicSymbol
import Logic.Modal.Standard.System

namespace LO.Modal.Standard

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | verum  : Formula α
  | falsum : Formula α
  | neg    : Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

namespace Formula

variable {α : Type u}

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

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | ~p      => "\\neg " ++ toStr p
  | p ⟶ q  => "\\left(" ++ toStr p ++ " \\to "   ++ toStr q ++ "\\right)"
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

@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp[Tilde.tilde]

def complexity : Formula α → ℕ
| atom _  => 0
| ⊤       => 0
| ⊥       => 0
| ~p      => p.complexity + 1
| p ⟶ q  => max p.complexity q.complexity + 1
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
  | ~p => p.degree
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
@[simp] lemma degree_neg {p : Formula α} : degree (~p) = p.degree := rfl

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hverum  : C ⊤)
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ (p : Formula α), C (~p))
    (himp    : ∀ (p q : Formula α), C (p ⟶ q))
    (hand    : ∀ (p q : Formula α), C (p ⋏ q))
    (hor     : ∀ (p q : Formula α), C (p ⋎ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊤       => hverum
  | ⊥       => hfalsum
  | atom a  => hatom a
  | ~p      => hneg p
  | p ⟶ q  => himp p q
  | p ⋏ q   => hand p q
  | p ⋎ q   => hor p q
  | box p      => hbox p

@[elab_as_elim]
def rec' {C : Formula α → Sort w}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (hneg    : ∀ (p : Formula α), C p → C (~p))
  (himp    : ∀ (p q : Formula α), C p → C q → C (p ⟶ q))
  (hand    : ∀ (p q : Formula α), C p → C q → C (p ⋏ q))
  (hor     : ∀ (p q : Formula α), C p → C q → C (p ⋎ q))
  (hbox    : ∀ (p : Formula α), C p → C (□p))
  : (p : Formula α) → C p
  | ⊤      => hverum
  | ⊥      => hfalsum
  | atom a => hatom a
  | ~p    => hneg p (rec' hverum hfalsum hatom hneg himp hand hor hbox p)
  | p ⟶ q  => himp p q (rec' hverum hfalsum hatom hneg himp hand hor hbox p) (rec' hverum hfalsum hatom hneg himp hand hor hbox q)
  | p ⋏ q  => hand p q (rec' hverum hfalsum hatom hneg himp hand hor hbox p) (rec' hverum hfalsum hatom hneg himp hand hor hbox q)
  | p ⋎ q  => hor p q (rec' hverum hfalsum hatom hneg himp hand hor hbox p) (rec' hverum hfalsum hatom hneg himp hand hor hbox q)
  | box p     => hbox p (rec' hverum hfalsum hatom hneg himp hand hor hbox p)

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
  | ~p, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    case hneg p' =>
      exact match hasDecEq p p' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse (by simp[hp])
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
  | ~p     => insert (~p) p.Subformulas
  | p ⟶ q => insert (p ⟶ q) (p.Subformulas ∪ q.Subformulas)
  | p ⋏ q  => {p ⋏ q} ∪ (p.Subformulas ∪ q.Subformulas)
  | p ⋎ q  => insert (p ⋎ q) (p.Subformulas ∪ q.Subformulas)
  | box p  => insert (□p) p.Subformulas

-- notation "Sub(" p ")" => Formula.Subformulas p
prefix:70 "𝒮 " => Formula.Subformulas

namespace Formula.Subformulas

@[simp]
lemma mem_self (p : Formula α) : p ∈ 𝒮 p := by induction p using Formula.rec' <;> simp [Subformulas];

variable {p q r : Formula α}

@[aesop safe forward]
lemma mem_neg (h : ~q ∈ 𝒮 p) : q ∈ 𝒮 p := by
  induction p using Formula.rec' <;> {
    simp_all [Subformulas];
    try rcases h with (hq | hr); simp_all; simp_all;
  };

@[aesop safe forward]
lemma mem_and (h : (q ⋏ r) ∈ 𝒮 p) : q ∈ 𝒮 p ∧ r ∈ 𝒮 p := by
  induction p using Formula.rec' with
  | hand => simp_all [Subformulas]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [Subformulas]; try rcases h with (hq | hr); simp_all; simp_all;

@[aesop safe forward]
lemma mem_or (h : (q ⋎ r) ∈ 𝒮 p) : q ∈ 𝒮 p ∧ r ∈ 𝒮 p := by
  induction p using Formula.rec' with
  | hor => simp_all [Subformulas]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [Subformulas]; try rcases h with (hq | hr); simp_all; simp_all;

@[aesop safe forward]
lemma mem_imp (h : (q ⟶ r) ∈ 𝒮 p) : q ∈ 𝒮 p ∧ r ∈ 𝒮 p := by
  induction p using Formula.rec' with
  | himp => simp_all [Subformulas]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [Subformulas]; try rcases h with (hq | hr); simp_all; simp_all;

@[aesop safe forward]
lemma mem_box (h : □q ∈ 𝒮 p) : q ∈ 𝒮 p := by
  induction p using Formula.rec' <;> {
    simp_all [Subformulas];
    try rcases h with (hq | hr); simp_all; simp_all;
  };

end Formula.Subformulas

end Subformula

abbrev AxiomSet (α) := Set (Formula α)

end LO.Modal.Standard


namespace LO

class Tilde.Subclosed [Tilde F] (C : F → Prop) where
  tilde_closed : C (~p) → C p

class Arrow.Subclosed [Arrow F] (C : F → Prop) where
  arrow_closed : C (p ⟶ q) → C p ∧ C q

class Wedge.Subclosed [Wedge F] (C : F → Prop) where
  wedge_closed : C (p ⋏ q) → C p ∧ C q

class Vee.Subclosed [Vee F] (C : F → Prop) where
  vee_closed : C (p ⋎ q) → C p ∧ C q

class LogicalConnective.Subclosed [LogicalConnective F] (C : F → Prop) extends
  Tilde.Subclosed C,
  Arrow.Subclosed C,
  Wedge.Subclosed C,
  Vee.Subclosed C

class StandardModalLogicalConnective.Subclosed
  [StandardModalLogicalConnective F] (C : F → Prop) extends LogicalConnective.Subclosed C where
  box_closed : C (□p) → C p

attribute [aesop safe 5 forward]
  Tilde.Subclosed.tilde_closed
  Arrow.Subclosed.arrow_closed
  Wedge.Subclosed.wedge_closed
  Vee.Subclosed.vee_closed
  StandardModalLogicalConnective.Subclosed.box_closed

namespace Modal.Standard

variable [DecidableEq α]

abbrev Theory.SubformulaClosed (T : Theory α) := StandardModalLogicalConnective.Subclosed (· ∈ T)

namespace Theory.SubformulaClosed

instance {p : Formula α} : (Theory.SubformulaClosed ((𝒮 p).toSet)) where
  tilde_closed := by aesop;
  arrow_closed := by aesop;
  wedge_closed := by aesop;
  vee_closed   := by aesop;
  box_closed   := by aesop;

variable {p : Formula α} {T : Theory α} [T_closed : T.SubformulaClosed]

lemma sub_mem_neg (h : ~p ∈ T) : p ∈ T := T_closed.tilde_closed h
lemma sub_mem_and (h : p ⋏ q ∈ T) : p ∈ T ∧ q ∈ T := T_closed.wedge_closed h
lemma sub_mem_or (h : p ⋎ q ∈ T) : p ∈ T ∧ q ∈ T := T_closed.vee_closed h
lemma sub_mem_imp (h : p ⟶ q ∈ T) : p ∈ T ∧ q ∈ T := T_closed.arrow_closed h
lemma sub_mem_box (h : □p ∈ T) : p ∈ T := T_closed.box_closed h

attribute [aesop safe 5 forward]
  sub_mem_neg
  sub_mem_and
  sub_mem_or
  sub_mem_imp
  sub_mem_box

end Theory.SubformulaClosed

end Modal.Standard

end LO
