import Logic.Logic.HilbertStyle2
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

section Axioms

variable (F : Type u) [ModalLogicSymbol F]

class HasNeccesitation extends Hilbert.Classical F where
  nec {Γ : List F} {p : F} : (Γ ⊢ᴴ p) → (Γ ⊢ᴴ □p)

class HasAxiomK extends Hilbert.Classical F where
  K (Γ : List F) (p q : F) : Γ ⊢ᴴ □(p ⟶ q) ⟶ □p ⟶ □q

class LogicK extends HasNeccesitation F, HasAxiomK F
notation "𝗞" => LogicK

class HasAxiomT extends Hilbert.Classical F where
  T (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ p

class HasAxiomD extends Hilbert.Classical F where
  D (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ ◇p

class HasAxiomB extends Hilbert.Classical F where
  B (Γ : List F) (p q : F) : Γ ⊢ᴴ p ⟶ □◇p

class HasAxiom4 extends Hilbert.Classical F where
  A4 (Γ : List F) (p : F) : Γ ⊢ᴴ □p ⟶ □□p

class LogicS4 extends 𝗞 F, HasAxiomT F, HasAxiom4 F
notation "𝗦𝟰" => LogicS4

class HasAxiom5 extends Hilbert.Classical F where
  A5 (Γ : List F) (p q : F) : Γ ⊢ᴴ ◇p ⟶ □◇p

class HasAxiomL extends Hilbert.Classical F where
  L (Γ : List F) (p : F) : Γ ⊢ᴴ □(□p ⟶ p) ⟶ □p

class LogicGL extends 𝗞 F, HasAxiomL F
notation "𝗚𝗟" => LogicGL

class HasAxiomDot2 extends Hilbert.Classical F where
  Dot2 (Γ : List F) (p : F) : Γ ⊢ᴴ ◇□p ⟶ □◇p

class LogicS4Dot2 extends 𝗦𝟰 F, HasAxiomDot2 F
notation "𝗦𝟰.𝟮" => LogicS4Dot2

class HasAxiomDot3 extends Hilbert.Classical F where
  Dot3 (Γ : List F) (p : F) : Γ ⊢ᴴ □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

class LogicS4Dot3 extends 𝗦𝟰 F, HasAxiomDot3 F
notation "𝗦𝟰.𝟯" => LogicS4Dot3

class HasAxiomGrz extends Hilbert.Classical F where
  Grz (Γ : List F) (p : F) : Γ ⊢ᴴ □(□(p ⟶ □p) ⟶ p) ⟶ p

class LogicS4Grz extends 𝗦𝟰 F, HasAxiomGrz F
notation "𝗦𝟰𝗚𝗿𝘇" => LogicS4Grz

end Axioms

end Modal

end LO
