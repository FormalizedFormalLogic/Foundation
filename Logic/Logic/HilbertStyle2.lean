import Logic.Logic.System
import Logic.Logic.Calculus

namespace LO

class Hilbert (F : Type u) where
  Derivation : Finset F → F → Type u

infix:45 " ⊢ᴴ " => Hilbert.Derivation

namespace Hilbert

def Derivable [Hilbert F] (Γ : Finset F) (p : F) := Nonempty (Γ ⊢ᴴ p)

infix:45 " ⊢ᴴ! " => Hilbert.Derivable

instance [TwoSided F] : Hilbert F := by
  apply Hilbert.mk;
  intro Γ p;
  exact TwoSided.Derivation Γ.toList [p];

variable {F : Type u} [LogicSymbol F]

class Minimal (F : Type u) [LogicSymbol F] extends Hilbert F where
  neg          {p : F}                    : ~p = p ⟶ ⊥
  axm          {Γ : Finset F} {p : F}     : p ∈ Γ → Γ ⊢ᴴ! p
  modus_ponens {Γ : Finset F} {p q : F}   : (Γ ⊢ᴴ! p ⟶ q) → (Γ ⊢ᴴ! p) → (Γ ⊢ᴴ! q)
  verum        (Γ : Finset F)             : Γ ⊢ᴴ! ⊤
  imply₁       (Γ : Finset F) (p q : F)   : Γ ⊢ᴴ! p ⟶ (q ⟶ p)
  imply₂       (Γ : Finset F) (p q r : F) : Γ ⊢ᴴ! (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁        (Γ : Finset F) (p q : F)   : Γ ⊢ᴴ! p ⋏ q ⟶ p
  conj₂        (Γ : Finset F) (p q : F)   : Γ ⊢ᴴ! p ⋏ q ⟶ q
  conj₃        (Γ : Finset F) (p q : F)   : Γ ⊢ᴴ! p ⟶ q ⟶ p ⋏ q
  disj₁        (Γ : Finset F) (p q : F)   : Γ ⊢ᴴ! p ⟶ p ⋎ q
  disj₂        (Γ : Finset F) (p q : F)   : Γ ⊢ᴴ! q ⟶ p ⋎ q
  disj₃        (Γ : Finset F) (p q r : F) : Γ ⊢ᴴ! (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

open Minimal

infixl:90 " ⨀ " => modus_ponens

namespace Minimal

variable [Minimal F]

@[simp]
lemma imp_id (Γ : Finset F) (p : F) : Γ ⊢ᴴ! p ⟶ p := (imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ Γ p (p ⟶ p)) ⨀ (imply₁ Γ p p)

theorem deduction [Insert F (Finset F)] {Γ : Finset F} {p : F} : (Γ ⊢ᴴ! p ⟶ q) ↔ ((insert p Γ) ⊢ᴴ! q) := by
  apply Iff.intro;
  . intro h; sorry;
  . intro h; sorry;

end Minimal


class Intuitionistic (F : Type u) [LogicSymbol F] extends Minimal F where
  explode (Γ : Finset F) (p : F) : Γ ⊢ᴴ! ⊥ ⟶ p

open Intuitionistic

/-- Logic for Weak version of Excluded Middle. -/
class WEM (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  wem (Γ : Finset F) (p : F) : Γ ⊢ᴴ! ~p ⋎ ~~p


/-- known as *Gödel-Dummett Logic*. -/
class Dummettean (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  dummett (Γ : Finset F) (p q : F) : Γ ⊢ᴴ! (p ⟶ q) ⋎ (q ⟶ p)

class Classical (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  dne (Γ : Finset F) (p : F) : Γ ⊢ᴴ! ~~p ⟶ p

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
