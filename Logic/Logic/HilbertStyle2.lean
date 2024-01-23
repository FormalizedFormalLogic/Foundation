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

variable [hM : Minimal Bew] [HasDT Bew]

def modus_ponens' {Γ p q} (d₁ : Bew Γ (p ⟶ q)) (d₂ : Bew Γ p) : Bew Γ q := by simpa using d₁ ⨀ d₂

infixr:90 " ⨀ " => modus_ponens'

def dtl {Γ p q} (d : Bew Γ (p ⟶ q)) : Bew (insert p Γ) q := (weakening' (by simp) d) ⨀ (axm (by simp))

@[simp]
lemma imp_id : Bew Γ (p ⟶ p) := ((imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ _ _ _)) ⨀ (imply₁ _ _ _)

lemma dni : Bew Γ (p ⟶ ~~p) := by
  have h₁ : Bew (insert (p ⟶ ⊥) (insert p Γ)) (p ⟶ ⊥) := axm (by simp);
  have h₂ : Bew (insert (p ⟶ ⊥) (insert p Γ)) p := axm (by simp);
  simpa using dtr $ dtr $ h₁ ⨀ h₂;

end Minimal


section Classical

variable [c : Classical Bew] [HasDT Bew]

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
