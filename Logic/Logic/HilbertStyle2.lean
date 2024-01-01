import Logic.Logic.System
import Logic.Logic.Calculus

namespace LO

class Deduction {F : Type u} [LogicSymbol F] (Bew : Set F → F → Sort*) where
  axm : ∀ {f}, f ∈ T → Bew T f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace Hilbert

variable {F : Type u} [LogicSymbol F] (Bew : Set F → F → Sort*)

/--
  Minimal Logic.
-/
class Minimal extends Deduction Bew where
  neg          {p : F}                 : ~p = p ⟶ ⊥
  modus_ponens {Γ : Set F} {p q}       : (Bew Γ (p ⟶ q)) → (Bew Γ p) → (Bew Γ q)
  verum        (Γ : Set F)             : Bew Γ ⊤
  imply₁       (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ (q ⟶ p))
  imply₂       (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  conj₁        (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ p)
  conj₂        (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ q)
  conj₃        (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ q ⟶ p ⋏ q)
  disj₁        (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ p ⋎ q)
  disj₂        (Γ : Set F) (p q : F)   : Bew Γ (q ⟶ p ⋎ q)
  disj₃        (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r)

open Minimal

infixl:90 " ⨀ " => modus_ponens

namespace Minimal

variable [Minimal Bew]

/-
@[simp]
lemma imp_id (Γ : Finset F) (p : F) : Bew Γ p ⟶ p := (imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ Γ p (p ⟶ p)) ⨀ (imply₁ Γ p p)

theorem deduction [Insert F (Finset F)] {Γ : Finset F} {p : F} : (Bew Γ p ⟶ q) ↔ ((insert p Γ) ⊢ᴴ! q) := by
  apply Iff.intro;
  . intro h; sorry;
  . intro h; sorry;
-/

end Minimal


/--
  Intuitionistic Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic extends Minimal Bew where
  explode (Γ : Set F) (p : F) : Bew Γ (⊥ ⟶ p)

open Intuitionistic

/--
  Logic for Weak version of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WEM extends Intuitionistic Bew where
  wem (Γ : Set F) (p : F) : Bew Γ (~p ⋎ ~~p)


/--
  Gödel-Dummett Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD extends Intuitionistic Bew where
  dummett (Γ : Set F) (p q : F) : Bew Γ ((p ⟶ q) ⋎ (q ⟶ p))

/--
  Classical Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical extends Intuitionistic Bew where
  dne (Γ : Set F) (p : F) : Bew Γ (~~p ⟶ p)

open Classical

namespace Classical

open Minimal Intuitionistic Classical

variable [Classical Bew]

instance : WEM Bew where
  wem Γ p := by sorry;

-- TODO:
-- instance : Gentzen F := sorry

end Classical

end Hilbert

end LO
