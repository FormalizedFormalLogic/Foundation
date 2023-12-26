import Logic.Logic.Calculus

namespace LO

namespace Hilbert

variable {F : Type u} [LogicSymbol F]

notation Γ "⊢ᴴ" p => Γ ⊢² [p]

class Minimal (F : Type u) [LogicSymbol F] extends TwoSided F where
  MP           {Γ : List F} {p q : F}   : (Γ ⊢ᴴ p ⟶ q) → (Γ ⊢ᴴ p) → (Γ ⊢ᴴ q)
  verum        (Γ : List F)             : Γ ⊢ᴴ ⊤
  imply₁       (Γ : List F) (p q : F)   : Γ ⊢ᴴ p ⟶ (q ⟶ p)
  imply₂       (Γ : List F) (p q r : F) : Γ ⊢ᴴ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁        (Γ : List F) (p q : F)   : Γ ⊢ᴴ p ⋏ q ⟶ p
  conj₂        (Γ : List F) (p q : F)   : Γ ⊢ᴴ p ⋏ q ⟶ q
  conj₃        (Γ : List F) (p q : F)   : Γ ⊢ᴴ p ⟶ q ⟶ p ⋏ q
  disj₁        (Γ : List F) (p q : F)   : Γ ⊢ᴴ p ⟶ p ⋎ q
  disj₂        (Γ : List F) (p q : F)   : Γ ⊢ᴴ q ⟶ p ⋎ q
  disj₃        (Γ : List F) (p q r : F) : Γ ⊢ᴴ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/-
theorem deduction.mp [Minimal F] (Γ : List F): (Γ ⊢ᴴ p ⟶ q) → ((p :: Γ) ⊢ᴴ q) := by sorry;

theorem deduction.mpr [Minimal F] (Γ : List F): ((p :: Γ) ⊢ᴴ q) → (Γ ⊢ᴴ p ⟶ q) := by sorry;
-/

class Intuitionistic (F : Type u) [LogicSymbol F] extends Minimal F where
  explode (Γ : List F) (p : F) : Γ ⊢ᴴ ⊥ ⟶ p

/-- Logic for Weak version of Excluded Middle. -/
class WEM (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  wem (Γ : List F) (p : F) : Γ ⊢ᴴ ~p ⋎ ~~p

/-- known as *Gödel-Dummett Logic*. -/
class Dummettean (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  dummett (Γ : List F) (p q : F) : Γ ⊢ᴴ (p ⟶ q) ⋎ (q ⟶ p)

class Classical (F : Type u) [LogicSymbol F] extends Intuitionistic F where
  em (Γ : List F) (p : F) : Γ ⊢ᴴ p ⋎ ~p

namespace Classical

variable [Classical F]

instance : WEM F where
  wem Γ p := em Γ (~p)

-- TODO:
-- instance : Gentzen F := sorry

end Classical

end Hilbert

end LO
