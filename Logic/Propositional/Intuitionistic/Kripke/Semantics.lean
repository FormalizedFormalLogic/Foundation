import Logic.Logic.LogicSymbol
import Logic.Propositional.Intuitionistic.Formula

universe u v

namespace LO.Propositional.Intuitionistic

namespace Kripke

variable (α : Type u)
variable (β : Type v)

abbrev Frame := α → α → Prop

abbrev Valuation := α → β → Prop

structure Model where
  frame : Kripke.Frame α
  val : Valuation α β
  trans : Transitive frame
  refl: Reflexive frame
  herditary : ∀ {w₁ w₂}, (frame w₁ w₂) → ∀ a, (val w₁ a) → (val w₂ a)

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

end Kripke

namespace Formula

variable {α β : Type _}
variable {M : Kripke.Model α β}
local infix:20 "≺" => M.frame

def KripkeSatisfies (M : Kripke.Model α β) (w : α) : Formula β → Prop
  | atom a => M.val w a
  | ⊥ => False
  | p ⋏ q => (p.KripkeSatisfies M w) ∧ (q.KripkeSatisfies M w)
  | p ⋎ q => (p.KripkeSatisfies M w) ∨ (q.KripkeSatisfies M w)
  | p ⟶ q => ∀ w', (M.frame w w') → (¬(p.KripkeSatisfies M w') ∨ (q.KripkeSatisfies M w'))

notation w " ⊩[" M "] " p => KripkeSatisfies M w p

local notation w "⊩" p => w ⊩[M] p

namespace KripkeSatisfies

@[simp] lemma atom_def : (w ⊩ atom a) ↔ M.val w a := by simp [KripkeSatisfies];
@[simp] lemma bot_def : (w ⊩ ⊥) ↔ False := by simp [KripkeSatisfies];
@[simp] lemma top_def : (w ⊩ ⊤) := by simp [KripkeSatisfies];
@[simp] lemma and_def : (w ⊩ p ⋏ q) ↔ (w ⊩ p) ∧ (w ⊩ q) := by simp [KripkeSatisfies];
@[simp] lemma or_def : (w ⊩ p ⋎ q) ↔ (w ⊩ p) ∨ (w ⊩ q) := by simp [KripkeSatisfies];

lemma imp_def : (w ⊩ p ⟶ q) ↔ ∀ w', (w ≺ w') → (¬(w' ⊩ p) ∨ (w' ⊩ q)) := by simp [KripkeSatisfies]

@[simp]
lemma imp_def' : (w ⊩ p ⟶ q) ↔ ∀ w', (w ≺ w') → (w' ⊩ p) → (w' ⊩ q) := by
  simp [KripkeSatisfies];
  constructor;
  . intros h w' a; have := h w' a; tauto;
  . intros h w' a; have := h w' a; tauto;

lemma modus_ponens {p q} (hpq : w ⊩ p ⟶ q) (hp : w ⊩ p) : w ⊩ q := by
  have := hpq w M.frame_refl;
  tauto;

end KripkeSatisfies

def KripkeModels (M : Kripke.Model α β) (p : Formula β) := ∀ w, (w ⊩[M] p)
infix:50 " ⊧ " => KripkeModels

lemma KripkeModels.modus_ponens {p q} (hpq : M ⊧ p ⟶ q) (hp : M ⊧ p) : M ⊧ q := by
  intro w;
  have := hpq w w M.frame_refl;
  tauto;

def KripkeValid (p : Formula β) := ∀ {α : Type}, ∀ (M : Kripke.Model α β), (M ⊧ p)
prefix:50 "⊧ " => KripkeValid

lemma KripkeValid.modus_ponens {p q : Formula β} (hpq : ⊧ p ⟶ q) (hp : ⊧ p) : ⊧ q := by
  intro α M;
  exact KripkeModels.modus_ponens (hpq M) (hp M);

end Formula

variable {α β : Type _}

theorem Kripke.herditary_formula
  {M : Kripke.Model α β} {p : Formula β} {w w' : α}
  (hw : M.frame w w') : (w ⊩[M] p) → (w' ⊩[M] p) := by
  induction p using Formula.rec'; simp [Formula.KripkeSatisfies] at *;
  case hatom => apply M.herditary hw;
  case hand => simp [Formula.KripkeSatisfies] at *; tauto;
  case hor => simp [Formula.KripkeSatisfies] at *; tauto;
  case himp => intro hpq v hv; exact hpq v $ M.frame_trans hw hv;

def Theory.KripkeSatisfies (M : Kripke.Model α β) (w : α) (Γ : Theory β) := ∀ p ∈ Γ, (w ⊩[M] p)
notation w " ⊩[" M "] " Γ => Theory.KripkeSatisfies M w Γ

def Formula.KripkeConsequence (Γ : Theory β) (p : Formula β) := ∀ {α : Type*}, ∀ (M : Kripke.Model α β) w, (w ⊩[M] Γ) → (w ⊩[M] p)
infix:50 " ⊨ᴵ " => Formula.KripkeConsequence

abbrev Formula.KripkeInconsequence (Γ : Theory β) (p : Formula β) := ¬(Γ ⊨ᴵ p)
infix:50 " ⊭ᴵ " => Formula.KripkeInconsequence

@[simp]
theorem Kripke.bot_inconsequence {Γ : Theory β} : Γ ⊭ᴵ ⊥ := by
  by_contra h;
  simp [Formula.KripkeInconsequence, Formula.KripkeConsequence] at h;
  sorry;

end LO.Propositional.Intuitionistic
