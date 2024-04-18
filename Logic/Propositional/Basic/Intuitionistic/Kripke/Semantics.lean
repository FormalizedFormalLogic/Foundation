import Logic.Logic.LogicSymbol
import Logic.Propositional.Basic.Formula

namespace LO.Propositional.Basic

namespace Intuitionistic.Kripke

variable (α β : Type u)

abbrev Frame := α → α → Prop

abbrev Valuation := α → β → Prop

structure Model where
  frame : Kripke.Frame α
  val : Valuation α β
  trans : Transitive frame
  refl: Reflexive frame
  hereditary : ∀ {w₁ w₂}, (frame w₁ w₂) → ∀ a, (val w₁ a) → (val w₂ a)

namespace Model

variable {M : Model α β}
local infix:20 "≺" => M.frame

@[trans] lemma frame_trans : (w₁ ≺ w₂) → (w₂ ≺ w₃) → (w₁ ≺ w₃) := by apply M.trans

@[refl] lemma frame_refl : (w ≺ w) := by apply M.refl

instance : Inhabited (Model α β) where
  default := ⟨
    λ _ _ => True,
    λ _ _ => True,
    by simp [Transitive],
    by simp [Reflexive],
    by simp
  ⟩

end Model

end Intuitionistic.Kripke

namespace Formula

variable {α β}
variable {M : Intuitionistic.Kripke.Model α β}
local infix:20 "≺" => M.frame

def Intuitionistic.Kripke.Satisfies (M : Intuitionistic.Kripke.Model α β) (w : α) : Formula β → Prop
  | atom a => M.val w a
  | ⊤      => True
  | ⊥      => False
  | p ⋏ q  => Intuitionistic.Kripke.Satisfies M w p ∧ Intuitionistic.Kripke.Satisfies M w q
  | p ⋎ q  => Intuitionistic.Kripke.Satisfies M w p ∨ Intuitionistic.Kripke.Satisfies M w q
  | p ⟶ q => ∀ w', (M.frame w w') → (¬Intuitionistic.Kripke.Satisfies M w' p ∨ Intuitionistic.Kripke.Satisfies M w' q)
notation w " ⊩ⁱ[" M "] " p => Intuitionistic.Kripke.Satisfies M w p

namespace Intuitionistic.Kripke.Satisfies

local notation w " ⊩ⁱ " p => w ⊩ⁱ[M] p

@[simp] lemma atom_def : (w ⊩ⁱ atom a) ↔ M.val w a := by simp [Intuitionistic.Kripke.Satisfies];
@[simp] lemma bot_def : ¬(w ⊩ⁱ ⊥) := by simp [Intuitionistic.Kripke.Satisfies];
@[simp] lemma top_def : (w ⊩ⁱ ⊤) := by simp [Intuitionistic.Kripke.Satisfies];
@[simp] lemma and_def : (w ⊩ⁱ p ⋏ q) ↔ (w ⊩ⁱ p) ∧ (w ⊩ⁱ q) := by simp [Intuitionistic.Kripke.Satisfies];
@[simp] lemma or_def : (w ⊩ⁱ p ⋎ q) ↔ (w ⊩ⁱ p) ∨ (w ⊩ⁱ q) := by simp [Intuitionistic.Kripke.Satisfies];

lemma imp_def : (w ⊩ⁱ p ⟶ q) ↔ ∀ w', (w ≺ w') → (¬(w' ⊩ⁱ p) ∨ (w' ⊩ⁱ q)) := by simp [Intuitionistic.Kripke.Satisfies]

@[simp]
lemma imp_def' : (w ⊩ⁱ p ⟶ q) ↔ ∀ w', (w ≺ w') → (w' ⊩ⁱ p) → (w' ⊩ⁱ q) := by simp [Intuitionistic.Kripke.Satisfies, imp_iff_not_or];

@[simp]
lemma neg_def : (w ⊩ⁱ ~p) ↔ ∀ w', (w ≺ w') → ¬(w' ⊩ⁱ p) := by simp [NegDefinition.neg, imp_def']

lemma modus_ponens {p q} (hpq : w ⊩ⁱ p ⟶ q) (hp : w ⊩ⁱ p) : w ⊩ⁱ q := by
  have := hpq w M.frame_refl;
  tauto;

end Intuitionistic.Kripke.Satisfies

def Intuitionistic.Kripke.Models (M : Intuitionistic.Kripke.Model α β) (p : Formula β) := ∀ w, (w ⊩ⁱ[M] p)
infix:50 " ⊧ⁱ " => Intuitionistic.Kripke.Models

lemma Intuitionistic.Kripke.Models.modus_ponens {p q} (hpq : M ⊧ⁱ p ⟶ q) (hp : M ⊧ⁱ p) : M ⊧ⁱ q := by
  intro w;
  exact Satisfies.modus_ponens (hpq w) (hp w);

def Intuitionistic.Kripke.Valid (p : Formula β) := ∀ {α}, ∀ (M : Intuitionistic.Kripke.Model α β), (M ⊧ⁱ p)
prefix:50 "⊧ⁱ " => Intuitionistic.Kripke.Valid

lemma Intuitionistic.Kripke.modus_ponens {p q : Formula β} (hpq : ⊧ⁱ (p ⟶ q)) (hp : ⊧ⁱ p) : ⊧ⁱ q := by
  intro _ M;
  exact Models.modus_ponens (hpq M) (hp M);

end Formula

variable {α β}

theorem Intuitionistic.Kripke.hereditary_formula
  {M : Intuitionistic.Kripke.Model α β} {p : Formula β} {w w' : α}
  (hw : M.frame w w') : (w ⊩ⁱ[M] p) → (w' ⊩ⁱ[M] p) := by
  induction p using Formula.rec' with
  | hatom => simp;   apply M.hereditary hw;
  | himp => simp; intro hpq v hv; exact hpq v $ M.frame_trans hw hv;
  | hor => simp_all; tauto;
  | _ => simp_all;

def Theory.Intuitionistic.Kripke.Satisfies (M : Intuitionistic.Kripke.Model α β) (w : α) (Γ : Theory β) := ∀ p ∈ Γ, (w ⊩ⁱ[M] p)
notation w " ⊩ⁱ[" M "] " Γ => Theory.Intuitionistic.Kripke.Satisfies M w Γ

@[simp]
lemma Theory.Intuitionistic.Kripke.satisfies_empty {M : Intuitionistic.Kripke.Model α β} {w : α} : w ⊩ⁱ[M] ∅ := fun _ ↦ by simp

def Formula.Intuitionistic.Kripke.Consequence.{u} (Γ : Theory β) (p : Formula β) := ∀ {α : Type u}, ∀ (M : Intuitionistic.Kripke.Model α β) {w : α}, (w ⊩ⁱ[M] Γ) → (w ⊩ⁱ[M] p)
infix:50 " ⊨ⁱ " => Formula.Intuitionistic.Kripke.Consequence

-- abbrev Formula.KripkeInconsequence (Γ : Theory β) (p : Formula β) := ¬(Γ ⊨ⁱ p)
-- infix:50 " ⊭ⁱ " => Formula.KripkeInconsequence

namespace Formula.Intuitionistic.Kripke.Consequence

variable {Γ : Theory β} {p q r : Formula β}

lemma verum : Γ ⊨ⁱ ⊤ := by simp [Consequence];

lemma imply₁ : Γ ⊨ⁱ (p ⟶ q ⟶ p) := by
  simp [Consequence];
  intro _ _ _ _ _ _ hp _ hw _;
  simpa using Intuitionistic.Kripke.hereditary_formula hw hp;

lemma imply₂ : Γ ⊨ⁱ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) := by
  simp [Consequence];
  intro _ M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
  exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃ w₄ (M.frame_refl) (h₂ w₄ hw₃w₄ h₃);

lemma conj₁ : (Γ ⊨ⁱ (p ⋏ q ⟶ p)) := by simp [Consequence]; intros; assumption;

lemma conj₂ : (Γ ⊨ⁱ (p ⋏ q ⟶ q)) := by simp [Consequence];

lemma conj₃ : (Γ ⊨ⁱ (p ⟶ q ⟶ p ⋏ q)) := by
  simp [Consequence];
  intro _ _ _ _ _ _ hp _ _ _;
  constructor;
  . simpa using Intuitionistic.Kripke.hereditary_formula (by assumption) $ hp;
  . simpa;

lemma disj₁ : (Γ ⊨ⁱ (p ⟶ p ⋎ q)) := by
  simp [Consequence];
  intros;
  left;
  assumption;

lemma disj₂ : (Γ ⊨ⁱ (q ⟶ p ⋎ q)) := by
  simp [Consequence];
  intros;
  right;
  assumption;

lemma disj₃ : (Γ ⊨ⁱ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))) := by
  simp [Consequence];
  intro _ M w₁ _ w₂ _ h₁ w₃ hw₂w₃ h₂ w₄ hw₃w₄ h₃;
  cases h₃ with
  | inl h₃ => exact h₁ w₄ (M.frame_trans hw₂w₃ hw₃w₄) h₃;
  | inr h₃ => exact h₂ w₄ hw₃w₄ h₃;

lemma efq : (Γ ⊨ⁱ (⊥ ⟶ p)) := by simp [Consequence];

end Formula.Intuitionistic.Kripke.Consequence

end LO.Propositional.Basic
