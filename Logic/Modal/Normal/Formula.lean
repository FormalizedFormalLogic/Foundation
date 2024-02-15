import Logic.Modal.Normal.LogicSymbol

namespace LO.Modal.Normal

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

instance : ModalLogicSymbol (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

instance : NegDefinition (Formula α) where
  neg := rfl

instance : ModalDuality (Formula α) where
  dia := rfl

section ToString

variable [ToString α]

def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | p ⟶ q   => "\\left(" ++ toStr p ++ " \\to "   ++ toStr q ++ "\\right)"
  | p ⋏ q   => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | p ⋎ q   => "\\left(" ++ toStr p ++ " \\lor "   ++ toStr q ++ "\\right)"
  | □p      => "\\Box " ++ toStr p

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

@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp[*]

@[simp] lemma box_inj (p q : Formula α) : □p = □q ↔ p = q := by simp[Box.box]

@[simp] lemma dia_inj (p q : Formula α) : ◇p = ◇q ↔ p = q := by simp[Dia.dia]

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
  | □p      => hbox p

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
  | □p     => hbox p (rec' hfalsum hatom himp hand hor hbox p)

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
  | □p, q => by
    cases q using cases' <;> try { simp; exact isFalse not_false }
    case hbox p' =>
      exact match hasDecEq p p' with
      | isTrue hp  => isTrue (hp ▸ rfl)
      | isFalse hp => isFalse (by simp[hp])

instance : DecidableEq (Formula α) := hasDecEq

end Decidable

def multibox (p : Formula α) : ℕ → Formula α
  | 0     => p
  | n + 1 => □(multibox p n)

notation "□^" n:90 p => multibox p n

def multidia (p : Formula α) : ℕ → Formula α
  | 0     => p
  | n + 1 => ◇(multidia p n)

notation "◇^" n:90 p => multidia p n

def isBox : Formula α → Bool
  | □_ => true
  | _  => false

end Formula

abbrev Theory (α : Type u) := Set (Formula α)

namespace Theory

variable (Γ : Theory α)

def box : Theory α := .box '' Γ
prefix:74 "□" => Theory.box

@[simp]
lemma box_empty : □(∅ : Theory α) = ∅ := by simp [box]

@[simp]
lemma box_subset {Γ Δ : Theory α} (d : Γ ⊆ Δ) : □Γ ⊆ □Δ := by
  simp_all [box, Set.subset_def];

lemma box_union {Γ Δ : Theory α} : □(Γ ∪ Δ) = □Γ ∪ □Δ := by
  simp_all [box, Set.image_union]

lemma box_mem {Γ : Theory α} : p ∈ □Γ ↔ (∃ q ∈ Γ, □q = p) := by
  simp_all [box]
  rfl;

def dia : Theory α := .dia '' Γ
prefix:74 "◇" => Theory.dia

@[simp]
lemma dia_empty : ◇(∅ : Theory α) = ∅ := by simp [dia]

@[simp]
lemma dia_subset {Γ Δ : Theory α} (d : Γ ⊆ Δ) : ◇Γ ⊆ ◇Δ := by
  simp_all [dia, Set.subset_def];

lemma dia_union {Γ Δ : Theory α} : ◇(Γ ∪ Δ) = ◇Γ ∪ ◇Δ := by
  simp_all [dia, Set.image_union]

lemma dia_mem {Γ : Theory α} : p ∈ ◇Γ ↔ (∃ q ∈ Γ, ◇q = p) := by
  simp_all [dia]
  rfl;

def prebox : Theory α := .box ⁻¹' Γ
prefix:73 "□⁻¹" => Theory.prebox

def box_prebox {Γ} : □(□⁻¹Γ) = { □p | (p : Formula α) (_ : □p ∈ Γ) } := by aesop;

@[simp]
def box_prebox_subset {Γ : Theory α} : □(□⁻¹Γ) ⊆ Γ := by simp [box_prebox, Set.subset_def];

@[simp]
lemma prebox_subset {Γ Δ : Theory α} (d : Γ ⊆ Δ) : □⁻¹Γ ⊆ □⁻¹Δ := by
  simp_all [prebox, Set.subset_def];

def predia : Theory α := .dia ⁻¹' Γ
prefix:73 "◇⁻¹" => Theory.predia

@[simp]
lemma predia_subset {Γ Δ : Theory α} (d : Γ ⊆ Δ) : ◇⁻¹Γ ⊆ ◇⁻¹Δ := by
  simp_all [predia, Set.subset_def];

def dia_predia {Γ} : ◇(◇⁻¹Γ) = { ◇p | (p : Formula α) (_ : ◇p ∈ Γ) } := by aesop;

@[simp]
def dia_predia_subset {Γ : Theory α} : ◇(◇⁻¹Γ) ⊆ Γ := by simp [dia_predia, Set.subset_def];

end Theory

abbrev Context (α : Type u) := Finset (Formula α)

namespace Context

-- instance : Coe (Context α) (Theory α) := ⟨Finset.toSet⟩

variable [DecidableEq α]
variable (Γ : Context α)

def box : Context α := Γ.image Formula.box
prefix:73 "□" => box

lemma box_union {Γ₁ Γ₂ : Context α} : (□(Γ₁ ∪ Γ₂) : Context α) = (□Γ₁ ∪ □Γ₂ : Context α) := by
  simp only [Theory.box, Context.box, Finset.image_union]

@[simp]
lemma box_coe : (□(↑Γ : Theory α)) = ↑(□Γ : Context α) := by
  simp only [Theory.box, Context.box, Finset.coe_image];

def dia : Context α := Γ.image Formula.dia
prefix:73 "◇" => dia

lemma dia_union {Γ₁ Γ₂ : Context α} : (◇(Γ₁ ∪ Γ₂) : Context α) = (◇Γ₁ ∪ ◇Γ₂ : Context α) := by
  simp only [Theory.dia, Context.dia, Finset.image_union]

@[simp]
lemma dia_coe : (◇(↑Γ : Theory α)) = ↑(◇Γ : Context α) := by
  simp only [Theory.dia, Context.dia, Finset.coe_image];

end Context

end LO.Modal.Normal
