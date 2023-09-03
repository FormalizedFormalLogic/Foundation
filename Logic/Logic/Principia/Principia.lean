import Logic.Logic.Logic

namespace LO

namespace Logic

class Principia (F : Type u) [LogicSymbol F] extends Proof F where
  Pr : Set F → List F → F → Type u
  toBew : {T : Set F} → {Δ : List F} → {f : F} → Pr T Δ f → T ⊢ Δ.conj ⟶ f
  PrWeakening' : {Δ Γ : List F} → {f : F} → Δ ⊆ Γ → Pr T Δ f → Pr T Γ f

namespace Principia

notation Δ:0 " ⟹[" T "] " f => Pr T Δ f

class Propositional (F : Type u) [LogicSymbol F] extends Principia F where
  verumRight {T : Set F} {Δ} : Δ ⟹[T] ⊤
  andRight {T : Set F} {Δ f₁ f₂} : (Δ ⟹[T] f₁) → (Δ ⟹[T] f₂) → (Δ ⟹[T] f₁ ⋏ f₂)
  orRight₁ {T : Set F} {Δ f₁ f₂} : (Δ ⟹[T] f₁) → (Δ ⟹[T] f₁ ⋎ f₂)
  orRight₂ {T : Set F} {Δ f₁ f₂} : (Δ ⟹[T] f₂) → (Δ ⟹[T] f₁ ⋎ f₂)
  intro {T : Set F} {Δ f₁ f₂} : ((f₁ :: Δ) ⟹[T] f₂) → (Δ ⟹[T] f₁ ⟶ f₂)
  absurd {T : Set F} {Δ f} : ((f :: Δ) ⟹[T] ⊥) → (Δ ⟹[T] ~f)

variable {F : Type u} [LogicSymbol F]

end Principia

end Logic

end LO

