import Logic.Logic.System
import Logic.Logic.Calculus

namespace LO

class Deduction {F : Type u} [LogicSymbol F] (Bew : Set F → F → Type*) where
  axm : ∀ {f}, f ∈ Γ → Bew Γ f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace Hilbert

variable {F : Type u} [LogicSymbol F] [DecidableEq F] [NegDefinition F]

section

variable (Bew : Set F → F → Type*)

class HasModusPonens where
  modus_ponens {Γ₁ Γ₂ p q} : (Bew Γ₁ (p ⟶ q)) → (Bew Γ₂ p) → (Bew (Γ₁ ∪ Γ₂) q)

section

variable {Bew : Set F → F → Type*} [HasModusPonens Bew]

abbrev modus_ponens {Γ₁ Γ₂ p q} (d₁ : Bew Γ₁ (p ⟶ q)) (d₂ : Bew Γ₂ p) : Bew (Γ₁ ∪ Γ₂) q := HasModusPonens.modus_ponens d₁ d₂
infixr:90 "⨀" => modus_ponens

def modus_ponens' {Γ p q} (d₁ : Bew Γ (p ⟶ q)) (d₂ : Bew Γ p) : Bew Γ q := by simpa using d₁ ⨀ d₂
infixr:90 "⨀" => modus_ponens'

end

/--
  Minimal Propositional Logic.
-/
class Minimal [NegDefinition F] extends Deduction Bew, HasModusPonens Bew where
  verum        (Γ : Set F)             : Bew Γ ⊤
  imply₁       (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ (q ⟶ p))
  imply₂       (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  conj₁        (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ p)
  conj₂        (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ q)
  conj₃        (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ q ⟶ p ⋏ q)
  disj₁        (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ p ⋎ q)
  disj₂        (Γ : Set F) (p q : F)   : Bew Γ (q ⟶ p ⋎ q)
  disj₃        (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r)

/-- Supplymental -/
class HasDT where
  dtr {Γ : Set F} {p q : F} : (Bew (insert p Γ) q) → (Bew Γ (p ⟶ q))

class HasEFQ where
  efq (Γ : Set F) (p : F) : Bew Γ (⊥ ⟶ p)

class HasWeakLEM where
  wlem (Γ : Set F) (p : F) : Bew Γ (~p ⋎ ~~p)

class HasLEM where
  lem (Γ : Set F) (p : F) : Bew Γ (p ⋎ ~p)

class HasDNE where
  dne (Γ : Set F) (p : F) : Bew Γ (~~p ⟶ p)

class HasDummett where
  dummett (Γ : Set F) (p q : F) : Bew Γ ((p ⟶ q) ⋎ (q ⟶ p))

class HasPeirce where
  peirce (Γ : Set F) (p q : F) : Bew Γ (((p ⟶ q) ⟶ p) ⟶ p)

class Compact where
  compact {Γ p} : (Bew Γ p) → ((Δ : { Δ : Finset F | ↑Δ ⊆ Γ}) × (Bew ↑Δ p))

/--
  Intuitionistic Propositional Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic extends Minimal Bew, HasEFQ Bew where

/--
  Propositional Logic for Weak Law of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WeakLEM extends Intuitionistic Bew, HasWeakLEM Bew where


/--
  Gödel-Dummett Propositional Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD extends Intuitionistic Bew, HasDummett Bew where

/--
  Classical Propositional Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical extends Minimal Bew, HasDNE Bew

end

open Deduction Minimal HasDT Intuitionistic Classical HasDNE

variable {Bew : Set F → F → Type u} (Γ : Set F) (p q r : F)

section Minimal

variable [hM : Minimal Bew] [hDT : HasDT Bew] [hEFQ : HasEFQ Bew]

abbrev efq := hEFQ.efq

def efq' {Γ p} : (Bew Γ ⊥) → (Bew Γ p) := modus_ponens' (efq _ _)

abbrev dtr {Γ p q} (d : Bew (insert p Γ) q) := HasDT.dtr d

def verum (Γ : Set F) : Bew Γ ⊤ := hM.verum Γ

abbrev imply₁ := hM.imply₁

def imply₁' {Γ p q} : Bew Γ p → Bew Γ (q ⟶ p) := modus_ponens' (imply₁ _ _ _)

abbrev imply₂ := hM.imply₂

def imply₂' {Γ p q r} (d₁ : Bew Γ (p ⟶ q ⟶ r)) (d₂ : Bew Γ (p ⟶ q)) (d₃ : Bew Γ p) : Bew Γ r := (((imply₂ _ _ _ _) ⨀ d₁) ⨀ d₂) ⨀ d₃

abbrev conj₁ := hM.conj₁

def conj₁' {Γ p q} : Bew Γ (p ⋏ q) → Bew Γ p := modus_ponens' (conj₁ _ _ _)

abbrev conj₂ := hM.conj₂

def conj₂' {Γ p q} : Bew Γ (p ⋏ q) → Bew Γ q := modus_ponens' (conj₂ _ _ _)

abbrev conj₃ := hM.conj₃

def conj₃' {Γ p q} (d₁ : Bew Γ p) (d₂: Bew Γ q) : Bew Γ (p ⋏ q) := (conj₃ _ _ _ ⨀ d₁) ⨀ d₂

abbrev disj₁ := hM.disj₁

def disj₁' {Γ p q} (d : Bew Γ p) : Bew Γ (p ⋎ q) := (disj₁ _ _ _ ⨀ d)

abbrev disj₂ := hM.disj₂

def disj₂' {Γ p q} (d : Bew Γ q) : Bew Γ (p ⋎ q) := (disj₂ _ _ _ ⨀ d)

abbrev disj₃ := hM.disj₃

def disj₃' {Γ p q r} (d₁ : Bew Γ (p ⟶ r)) (d₂ : Bew Γ (q ⟶ r)) (d₃ : Bew Γ (p ⋎ q)) : Bew Γ r := (((disj₃ _ _ _ _) ⨀ d₁) ⨀ d₂) ⨀ d₃

def iff_mp' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (p ⟶ q) := by
  simp [LogicSymbol.iff] at d;
  exact conj₁' d

def iff_right' {Γ p q} (dpq : Bew Γ (p ⟷ q)) (dp : Bew Γ p) : Bew Γ q := (iff_mp' dpq) ⨀ dp

def iff_mpr' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (q ⟶ p) := by
  simp [LogicSymbol.iff] at d;
  exact conj₂' d

def iff_left' {Γ p q} (dpq : Bew Γ (p ⟷ q)) (dq : Bew Γ q) : Bew Γ p := (iff_mpr' dpq) ⨀ dq

def iff_intro {Γ p q} (dpq : Bew Γ (p ⟶ q)) (dqp : Bew Γ (q ⟶ p)) : Bew Γ (p ⟷ q) := by
  simp [LogicSymbol.iff];
  exact conj₃' dpq dqp

def iff_symm' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (q ⟷ p) := iff_intro (iff_mpr' d) (iff_mp' d)

def dtl {Γ p q} (d : Bew Γ (p ⟶ q)) : Bew (insert p Γ) q := modus_ponens' (weakening' (by simp) d) (axm (by simp))

def imp_id : Bew Γ (p ⟶ p) := ((imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ _ _ _)) ⨀ (imply₁ _ _ _)

def id_insert (Γ p) : Bew (insert p Γ) p := axm (by simp)

def id_singleton (p) : Bew {p} p := by simpa using id_insert ∅ p

def dni : Bew Γ (p ⟶ ~~p) := by
  simp [NegDefinition.neg]
  have h₁ : Bew (insert (p ⟶ ⊥) (insert p Γ)) (p ⟶ ⊥) := axm (by simp);
  have h₂ : Bew (insert (p ⟶ ⊥) (insert p Γ)) p := axm (by simp);
  apply dtr;
  apply dtr;
  exact h₁ ⨀ h₂;

def dni' {Γ p} : (Bew Γ p) → (Bew Γ (~~p)) := modus_ponens' (dni _ _)

def contra₀' {Γ p q} : (Bew Γ (p ⟶ q)) → (Bew Γ (~q ⟶ ~p)) := by
  intro h;
  simp [NegDefinition.neg];
  apply dtr;
  apply dtr;
  have d₁ : Bew (insert p $ insert (q ⟶ ⊥) Γ) (q ⟶ ⊥) := axm (by simp);
  have d₂ : Bew (insert p $ insert (q ⟶ ⊥) Γ) p := axm (by simp);
  simpa using d₁ ⨀ h ⨀ d₂;

def neg_iff' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (~p ⟷ ~q) := by
  simp only [LogicSymbol.iff];
  apply conj₃';
  . apply contra₀';
    apply iff_mpr' d;
  . apply contra₀';
    apply iff_mp' d

end Minimal

section Classical

variable [c : Classical Bew] [HasDT Bew]

def dne : Bew Γ (~~p ⟶ p) := c.dne Γ p

def dne' {Γ p} : (Bew Γ (~~p)) → (Bew Γ p) := modus_ponens' (dne _ _)

def equiv_dn : Bew Γ (p ⟷ ~~p) := by
  simp only [LogicSymbol.iff];
  exact (conj₃ _ _ _ ⨀ (dni _ _)) ⨀ (dne _ _);

instance : HasEFQ Bew where
  efq Γ p := by
    have h₁ : Bew (insert ⊥ Γ) (⊥ ⟶ (p ⟶ ⊥) ⟶ ⊥) := imply₁ (insert ⊥ Γ) ⊥ (p ⟶ ⊥);
    have h₂ : Bew (insert ⊥ Γ) (((p ⟶ ⊥) ⟶ ⊥) ⟶ p) := by simpa using dne (insert ⊥ Γ) p;
    exact dtr $ h₂ ⨀ h₁ ⨀ (axm (by simp));

instance : Intuitionistic Bew where

instance : HasLEM Bew where
  lem Γ p := by sorry;

end Classical

section

variable [LogicSymbol F] [NegDefinition F]
variable (Bew : Set F → F → Type u) [hd : Deduction Bew] [HasModusPonens Bew] [HasDT Bew] [Minimal Bew] [Classical Bew]

local infix:20 " ⊢ " => Bew

variable (Γ : Set F) (p : F)

@[simp] def Deducible := Nonempty (Bew Γ p)
local infix:20 "⊢!" => Deducible Bew

namespace Deducible

variable {Bew : Set F → F → Type u} [hd : Deduction Bew] [HasModusPonens Bew]

def modus_ponens {Γ₁ Γ₂ : Set F} {p q : F} (d₁ : Deducible Bew Γ₁ (p ⟶ q)) (d₂ : Deducible Bew Γ₂ p) : Deducible Bew (Γ₁ ∪ Γ₂) q := ⟨d₁.some ⨀ d₂.some⟩

def modus_ponens' {Γ : Set F} {p q : F} (d₁ : Deducible Bew Γ (p ⟶ q)) (d₂ : Deducible Bew Γ p) : Deducible Bew Γ q := by simpa using d₁.modus_ponens d₂

end Deducible

@[simp] def Undeducible := ¬(Γ ⊢! p)
local infix:20 "⊬!" => Undeducible Bew

@[simp] def Inconsistent := Γ ⊢! ⊥

@[simp] def Consistent := ¬(Inconsistent Bew Γ)

lemma consistent_iff_undeducible_falsum : Consistent Bew Γ ↔ (Γ ⊬! ⊥) := Iff.rfl

lemma consistent_no_falsum {Γ} (h : Consistent Bew Γ) : ⊥ ∉ Γ := by
  by_contra hC;
  exact h ⟨hd.axm hC⟩

lemma consistent_of_subset {Γ Δ : Set F} (h : Γ ⊆ Δ) (hConsis : Consistent Bew Δ) : Consistent Bew Γ := by
  intro hD;
  exact hConsis ⟨hd.weakening' h hD.some⟩;

lemma consistent_of_insert {p} (hConsis : Consistent Bew (insert p Γ)) : Consistent Bew Γ := consistent_of_subset Bew (by simp) hConsis

lemma consistent_no_falsum_subset {Γ Δ} (hConsis : Consistent Bew Γ) (hΔ : Δ ⊆ Γ) : ⊥ ∉ Δ := consistent_no_falsum Bew $ consistent_of_subset Bew hΔ hConsis

lemma consistent_subset_undeducible_falsum {Γ Δ} (hConsis : Consistent Bew Γ) (hΔ : Δ ⊆ Γ) : (Δ ⊬! ⊥) := by
  by_contra hC;
  simp_all [Consistent, Undeducible, Deducible];
  exact hConsis.false $ hd.weakening' hΔ hC.some;

lemma consistent_neither_undeducible {Γ : Set F} (hConsis : Consistent Bew Γ) (p) : (Γ ⊬! p) ∨ (Γ ⊬! ~p) := by
  by_contra hC; simp only [not_or] at hC;
  have h₁ : Γ ⊢! p  := by simpa using hC.1;
  have h₂ : Γ ⊢! p ⟶ ⊥ := by simpa using hC.2;
  exact hConsis $ h₂.modus_ponens' h₁;

lemma inconsistent_of_deduction {Γ : Set F} (d : Γ ⊢ ⊥) : Inconsistent Bew Γ := ⟨d⟩

lemma inconsistent_of_deducible {Γ : Set F} (d : Γ ⊢! ⊥) : Inconsistent Bew Γ := by simpa [Inconsistent];

lemma inconsistent_insert_falsum : Inconsistent Bew (insert ⊥ Γ) := ⟨hd.axm (by simp)⟩

lemma inconsistent_insert {Γ p} (h : Inconsistent Bew (insert p Γ)) : (∃ Δ, (Δ ⊆ Γ) ∧ ((insert p Δ) ⊢! ⊥)) := by
  existsi Γ;
  constructor;
  . rfl;
  . exact h;

/--
  **This lemma require classical logic.**
-/
lemma inconsistent_iff_insert_neg {Γ p} : Inconsistent Bew (insert (~p) Γ) ↔ (Γ ⊢! p) := by
  constructor;
  . intro h;
    have : Γ ⊢ ~~p := by simpa using (dtr h.some);
    exact ⟨(dne' this)⟩
  . intro h;
    have : Γ ⊢ ((p ⟶ ⊥) ⟶ ⊥) := by simpa using dni' h.some
    exact ⟨by simpa using (dtl this)⟩;

lemma consistent_iff_insert_neg {Γ p} : Consistent Bew (insert (~p) Γ) ↔ (Γ ⊬! p) := (inconsistent_iff_insert_neg Bew).not

lemma consistent_either {Γ : Set F} (hConsis : Consistent Bew Γ) (p) : (Consistent Bew (insert p Γ)) ∨ (Consistent Bew (insert (~p) Γ)) := by
  by_contra hC; simp [not_or, Consistent] at hC;
  have ⟨Δ₁, hΔ₁, ⟨dΔ₁⟩⟩ := inconsistent_insert Bew hC.1;
  have ⟨Δ₂, hΔ₂, ⟨dΔ₂⟩⟩ := inconsistent_insert Bew hC.2;
  exact consistent_subset_undeducible_falsum _ hConsis (by aesop) ⟨(dtr dΔ₂) ⨀ (dtr dΔ₁)⟩;

end

end Hilbert

end LO
