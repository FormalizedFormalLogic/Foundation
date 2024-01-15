import Logic.Logic.System
import Logic.Logic.Calculus

namespace LO

class Deduction {F : Type u} [LogicSymbol F] (Bew : Finset F → F → Sort*) where
  axm : ∀ {f}, f ∈ Γ → Bew Γ f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace Hilbert

variable {F : Type u} [LogicSymbol F] [DecidableEq F]

section

variable (Bew : Finset F → F → Sort*)

/--
  Minimal Propositional Logic.
-/
class Minimal extends Deduction Bew where
  neg_def      {p : F}                    : ~p = p ⟶ ⊥
  modus_ponens {Γ : Finset F} {p q : F}   : (Bew Γ (p ⟶ q)) → (Bew Γ p) → (Bew Γ q)
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
  dt {Γ : Finset F} {p q : F} : (Bew (insert p Γ) q) → (Bew Γ (p ⟶ q))

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

open Deduction Minimal HasDT Intuitionistic Classical

infixl:90 " ⨀ " => modus_ponens

variable {Bew : Finset F → F → Sort*} (Γ : Finset F) (p q r : F)

section Minimal

variable [hM : Minimal Bew] [HasDT Bew]

/-
lemma imply₁ : Bew Γ (p ⟶ (q ⟶ p)) := by
  repeat apply dtr;
  apply axm;
  simp;

lemma imply₂ : Bew Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) := by
  repeat apply dtr;
  have h₁ : Bew (insert p (insert (p ⟶ q) (insert (p ⟶ q ⟶ r) Γ))) p := axm (by simp);
  have h₂ : Bew (insert p (insert (p ⟶ q) (insert (p ⟶ q ⟶ r) Γ))) (p ⟶ q) := axm (by simp);
  have h₃ : Bew (insert p (insert (p ⟶ q) (insert (p ⟶ q ⟶ r) Γ))) (p ⟶ q ⟶ r) := axm (by simp);
  exact (h₃ ⨀ h₁) ⨀ (h₂ ⨀ h₁);
-/

lemma dtl (d : Bew Γ (p ⟶ q)) : Bew (insert p Γ) q := (weakening' (by simp) d) ⨀ (axm (by simp))

@[simp]
lemma imp_id : Bew Γ (p ⟶ p) := (imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ _ _ _) ⨀ (imply₁ _ _ _)

lemma dni : Bew Γ (p ⟶ ~~p) := by
  have h₁ : Bew (insert (p ⟶ ⊥) (insert p Γ)) (p ⟶ ⊥) := axm (by simp);
  have h₂ : Bew (insert (p ⟶ ⊥) (insert p Γ)) p := axm (by simp);
  repeat rw [hM.neg_def];
  exact dt $ dt $ h₁ ⨀ h₂;

end Minimal


section Classical

variable [c : Classical Bew] [HasDT Bew]

instance : HasEFQ Bew where
  efq Γ p := by
    have h₁ : Bew (insert ⊥ Γ) ⊥ := axm (by simp);
    have h₂ := c.imply₁ (insert ⊥ Γ) ⊥ (p ⟶ ⊥);
    have h₃ := h₂ ⨀ h₁;
    have h₄ := c.dne (insert ⊥ Γ) p; simp [c.neg_def] at h₄;
    have h₅ := h₄ ⨀ h₃;
    exact dt h₅;

instance : Intuitionistic Bew where

instance : HasLEM Bew where
  lem Γ p := by sorry;

end Classical

end Hilbert

end LO
