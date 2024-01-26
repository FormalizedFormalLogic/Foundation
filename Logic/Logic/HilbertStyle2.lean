import Logic.Logic.System
import Logic.Logic.Calculus

namespace LO

class Deduction {F : Type u} [LogicSymbol F] (Bew : Finset F → F → Sort*) where
  axm : ∀ {f}, f ∈ Γ → Bew Γ f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace Hilbert

variable {F : Type u} [LogicSymbol F] [DecidableEq F] [NegDefinition F]

section

variable (Bew : Finset F → F → Sort*)

/--
  Minimal Propositional Logic.
-/
class Minimal [NegDefinition F] extends Deduction Bew where
  modus_ponens {Γ₁ Γ₂ : Finset F} {p q : F} : (Bew Γ₁ (p ⟶ q)) → (Bew Γ₂ p) → (Bew (Γ₁ ∪ Γ₂) q)
  verum        (Γ : Finset F)             : Bew Γ ⊤
  imply₁       (Γ : Finset F) (p q : F)   : Bew Γ (p ⟶ (q ⟶ p))
  imply₂       (Γ : Finset F) (p q r : F) : Bew Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  conj₁        (Γ : Finset F) (p q : F)   : Bew Γ (p ⋏ q ⟶ p)
  conj₂        (Γ : Finset F) (p q : F)   : Bew Γ (p ⋏ q ⟶ q)
  conj₃        (Γ : Finset F) (p q : F)   : Bew Γ (p ⟶ q ⟶ p ⋏ q)
  disj₁        (Γ : Finset F) (p q : F)   : Bew Γ (p ⟶ p ⋎ q)
  disj₂        (Γ : Finset F) (p q : F)   : Bew Γ (q ⟶ p ⋎ q)
  disj₃        (Γ : Finset F) (p q r : F) : Bew Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r)

/-- Supplymental -/
class HasDT where
  dtr {Γ : Finset F} {p q : F} : (Bew (insert p Γ) q) → (Bew Γ (p ⟶ q))

class HasEFQ where
  efq (Γ : Finset F) (p : F) : Bew Γ (⊥ ⟶ p)

class HasWeakLEM where
  wlem (Γ : Finset F) (p : F) : Bew Γ (~p ⋎ ~~p)

class HasLEM where
  lem (Γ : Finset F) (p : F) : Bew Γ (p ⋎ ~p)

class HasDNE where
  dne (Γ : Finset F) (p : F) : Bew Γ (~~p ⟶ p)

class HasDummett where
  dummett (Γ : Finset F) (p q : F) : Bew Γ ((p ⟶ q) ⋎ (q ⟶ p))

class HasPeirce where
  peirce (Γ : Finset F) (p q : F) : Bew Γ (((p ⟶ q) ⟶ p) ⟶ p)

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

infixr:90 " ⨀ " => modus_ponens

variable {Bew : Finset F → F → Sort*} (Γ : Finset F) (p q r : F)

section Minimal

variable [hM : Minimal Bew] [hDT : HasDT Bew] [hEFQ : HasEFQ Bew]

def modus_ponens' {Γ p q} (d₁ : Bew Γ (p ⟶ q)) (d₂ : Bew Γ p) : Bew Γ q := by simpa using d₁ ⨀ d₂

infixr:90 " ⨀ " => modus_ponens'

abbrev efq := hEFQ.efq

def efq' {Γ p} : (Bew Γ ⊥) → (Bew Γ p) := modus_ponens' (efq _ _)

abbrev dtr {Γ p q} (d : Bew (insert p Γ) q) := HasDT.dtr d

def verum (Γ : Finset F) : Bew Γ ⊤ := hM.verum Γ

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

def dtl {Γ p q} (d : Bew Γ (p ⟶ q)) : Bew (insert p Γ) q := (weakening' (by simp) d) ⨀ (axm (by simp))

def imp_id : Bew Γ (p ⟶ p) := ((imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ _ _ _)) ⨀ (imply₁ _ _ _)

def id_insert (Γ p) : Bew (insert p Γ) p := axm (by simp)

def id_singleton (p) : Bew {p} p := id_insert ∅ p

def dni : Bew Γ (p ⟶ ~~p) := by
  have h₁ : Bew (insert (p ⟶ ⊥) (insert p Γ)) (p ⟶ ⊥) := axm (by simp);
  have h₂ : Bew (insert (p ⟶ ⊥) (insert p Γ)) p := axm (by simp);
  simpa using dtr $ dtr $ h₁ ⨀ h₂;

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

end Hilbert

end LO
