import Logic.Logic.System
import Logic.Logic.Calculus

namespace LO

class Hilbert (F : Type u) where
  Derivation : Finset F → F → Type u

namespace Hilbert

instance [TwoSided F] : Hilbert F := by
  apply Hilbert.mk;
  intro Γ p;
  exact TwoSided.Derivation Γ.toList [p];

variable {F : Type u} [LogicSymbol F]

class Minimal (F : Type u) [LogicSymbol F] extends System F where
  neg          {p : F}                 : ~p = p ⟶ ⊥
  modus_ponens {Γ : Set F} {p q}       : (Γ ⊢! (p ⟶ q)) → (Γ ⊢! p) → (Γ ⊢! q)
  verum        (Γ : Set F)             : Γ ⊢! ⊤
  imply₁       (Γ : Set F) (p q : F)   : Γ ⊢! (p ⟶ (q ⟶ p))
  imply₂       (Γ : Set F) (p q r : F) : Γ ⊢! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  conj₁        (Γ : Set F) (p q : F)   : Γ ⊢! (p ⋏ q ⟶ p)
  conj₂        (Γ : Set F) (p q : F)   : Γ ⊢! (p ⋏ q ⟶ q)
  conj₃        (Γ : Set F) (p q : F)   : Γ ⊢! (p ⟶ q ⟶ p ⋏ q)
  disj₁        (Γ : Set F) (p q : F)   : Γ ⊢! (p ⟶ p ⋎ q)
  disj₂        (Γ : Set F) (p q : F)   : Γ ⊢! (q ⟶ p ⋎ q)
  disj₃        (Γ : Set F) (p q r : F) : Γ ⊢! ((p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r)

open Minimal

infixl:90 " ⨀ " => modus_ponens

namespace Minimal

variable [Minimal F]

/-
@[simp]
lemma imp_id (Γ : Finset F) (p : F) : Γ ⊢! p ⟶ p := (imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ Γ p (p ⟶ p)) ⨀ (imply₁ Γ p p)

theorem deduction [Insert F (Finset F)] {Γ : Finset F} {p : F} : (Γ ⊢! p ⟶ q) ↔ ((insert p Γ) ⊢ᴴ! q) := by
  apply Iff.intro;
  . intro h; sorry;
  . intro h; sorry;
-/

end Minimal


class Intuitionistic (F : Type u) [LogicSymbol F] extends Minimal F where
  explode (Γ : Finset F) (p : F) : Γ ⊢! (⊥ ⟶ p)

open Intuitionistic

/-- Logic for Weak version of Excluded Middle. -/
class WEM (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  wem (Γ : Finset F) (p : F) : Γ ⊢! (~p ⋎ ~~p)


/-- known as *Gödel-Dummett Logic*. -/
class Dummettean (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  dummett (Γ : Finset F) (p q : F) : Γ ⊢! ((p ⟶ q) ⋎ (q ⟶ p))

class Classical (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  dne (Γ : Finset F) (p : F) : Γ ⊢! (~~p ⟶ p)

open Classical

namespace Classical

open Minimal Intuitionistic Classical

variable [Classical F]

instance : WEM F where
  wem Γ p := by sorry;

-- TODO:
-- instance : Gentzen F := sorry

end Classical

end Hilbert

end LO
