import Logic.Modal.Normal.LogicSymbol
import Logic.Propositional.Intuitionistic.Formula

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
  dia_to_box := rfl

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

@[simp] lemma neg_inj (p q : Formula α) : ~p = ~q ↔ p = q := by simp [NegDefinition.neg]

instance : ModalInjective (Formula α) where
  box_injective := by simp [Function.Injective, Box.box]
  dia_injective := by simp [Function.Injective, Dia.dia]

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

def degree : Formula α → Nat
  | atom _ => 0
  | ⊥ => 0
  | box p => p.degree + 1
  | p ⟶ q => max p.degree q.degree
  | p ⋏ q => max p.degree q.degree
  | p ⋎ q => max p.degree q.degree

def toPropFormula (p : Formula α) (_ : p.degree = 0) : LO.Propositional.Intuitionistic.Formula α :=
  match p with
  | atom a => LO.Propositional.Intuitionistic.Formula.atom a
  | ⊥ => LO.Propositional.Intuitionistic.Formula.falsum
  | p ⋏ q => LO.Propositional.Intuitionistic.Formula.and
    (p.toPropFormula (by simp_all [degree]))
    (q.toPropFormula (by simp_all [degree]))
  | p ⋎ q => LO.Propositional.Intuitionistic.Formula.or
    (p.toPropFormula (by simp_all [degree]))
    (q.toPropFormula (by simp_all [degree]))
  | p ⟶ q => LO.Propositional.Intuitionistic.Formula.imp
    (p.toPropFormula (by simp_all [degree]))
    (q.toPropFormula (by simp_all [degree]))

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

def isBox : Formula α → Bool
  | □_ => true
  | _  => false

end Formula

abbrev Theory (α : Type u) := Set (Formula α)

namespace Theory

variable (Γ : Theory α)

@[simp] def box : Theory α := Set.box Γ
prefix:73 "□" => Theory.box

@[simp] def dia : Theory α := Set.dia Γ
prefix:73 "◇" => Theory.dia

@[simp] def prebox : Theory α := Set.prebox Γ
prefix:73 "□⁻¹" => Theory.prebox

@[simp] def predia : Theory α := Set.predia Γ
prefix:73 "◇⁻¹" => Theory.predia

@[simp] def multibox (n : ℕ) (Γ : Theory α) : Theory α := Set.multibox n Γ
notation:72 "□[" n:90 "]" Γ:80 => Theory.multibox n Γ

@[simp] def multidia (n : ℕ) (Γ : Theory α) : Theory α := Set.multidia n Γ
notation:72 "◇[" n:90 "]" Γ:80 => Theory.multidia n Γ

@[simp] def premultibox (n : ℕ) (Γ : Theory α) : Theory α := Set.premultibox n Γ
notation:72 "□⁻¹[" n:90 "]" Γ:80 => Theory.premultibox n Γ

@[simp] def premultidia (n : ℕ) (Γ : Theory α) : Theory α := Set.premultidia n Γ
notation:72 "◇⁻¹[" n:90 "]" Γ:80 => Theory.premultidia n Γ

variable {Γ}

@[simp] lemma prebox_box_eq : □⁻¹□Γ = Γ := by simp;

@[simp] lemma predia_dia_eq : ◇⁻¹◇Γ = Γ := by simp;

@[simp] lemma premultibox_multibox_eq : □⁻¹[n](□[n]Γ) = Γ := by simp;

@[simp] lemma premultidia_multidia_eq : ◇⁻¹[n](◇[n]Γ) = Γ := by simp;

end Theory


abbrev Context (α : Type u) := Finset (Formula α)

namespace Context

variable [DecidableEq α]
variable (Γ : Context α)

@[simp] noncomputable def conj : Formula α := Finset.conj Γ
prefix:75 "⋀" => conj

@[simp] noncomputable def disj : Formula α := Finset.disj Γ
prefix:75 "⋁" => disj

@[simp] noncomputable abbrev box : Context α := Finset.box Γ
prefix:75 "□" => box

@[simp] noncomputable def dia : Context α := Finset.dia Γ
prefix:75 "◇" => dia

@[simp] noncomputable def multibox (n : ℕ) (Γ : Context α) : Context α := Finset.multibox n Γ
notation:75 "□[" n:90 "]" Γ:80 => Context.multibox n Γ

@[simp] noncomputable def multidia (n : ℕ)  (Γ : Context α) : Context α := Finset.multidia n Γ
notation:75 "◇[" n:90 "]" Γ:80 => Context.multidia n Γ

@[simp] noncomputable def prebox (Γ : Context α) : Context α := Finset.prebox Γ
prefix:75 "□⁻¹" => Context.prebox

@[simp] noncomputable def predia (Γ : Context α) : Context α := Finset.predia Γ
prefix:75 "◇⁻¹" => Context.predia

@[simp] noncomputable def premultibox (n : ℕ) (Γ : Context α) : Context α := Finset.premultibox n Γ
notation:75 "□⁻¹[" n:90 "]" Γ:80 => Context.premultibox n Γ

@[simp] noncomputable def premultidia (n : ℕ) (Γ : Context α) : Context α := Finset.premultidia n Γ
notation:75 "◇⁻¹[" n:90 "]" Γ:80 => Context.premultidia n Γ

variable {Γ : Context α}

@[simp] lemma box_coe_eq : ↑(□Γ : Context α) = □(↑Γ : Theory α) := by apply Finset.multibox_coe

@[simp] lemma dia_coe_eq  : ↑(◇Γ : Context α) = ◇(↑Γ : Theory α) := by apply Finset.multidia_coe

@[simp] lemma multibox_coe_eq : ↑(□[n]Γ : Context α) = □[n](↑Γ : Theory α) := by apply Finset.multibox_coe

@[simp] lemma multidia_coe_eq : ↑(◇[n]Γ : Context α) = ◇[n](↑Γ : Theory α) := by apply Finset.multidia_coe

@[simp] lemma prebox_coe_eq : ↑(□⁻¹Γ : Context α) = (□⁻¹(↑Γ : Theory α)) := by apply Finset.premultibox_coe

@[simp] lemma predia_coe_eq : ↑(◇⁻¹Γ : Context α) = (◇⁻¹(↑Γ : Theory α)) := by apply Finset.premultidia_coe

@[simp] lemma premultibox_coe_eq : ↑(□⁻¹[n]Γ : Context α) = (□⁻¹[n](↑Γ : Theory α)) := by apply Finset.premultibox_coe

@[simp] lemma premultidia_coe_eq : ↑(◇⁻¹[n]Γ : Context α) = (◇⁻¹[n](↑Γ : Theory α)) := by apply Finset.premultidia_coe

end Context

end LO.Modal.Normal
