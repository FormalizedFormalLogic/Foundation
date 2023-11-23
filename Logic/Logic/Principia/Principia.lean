import Logic.Logic.System

namespace LO

namespace Logic

variable {F : Type u} [LogicSymbol F]

class Axiom (F : Type u) (α : outParam (Type*)) where
  toTheory : α → Set F

class Principia (F : Type u) [LogicSymbol F] (α : outParam (Type*)) extends Axiom F α where
  Pr : α → List F → F → Type u
  byAxiom (a : α) : σ ∈ @Axiom.toTheory F _ _ a → Pr a Δ σ

class LawfulPrincipia (F : Type u) [LogicSymbol F] [System F] (α : outParam (Type*)) [Principia F α] where
  toBew {a : α} {f : F} : Principia.Pr a [] f → Axiom.toTheory a ⊢ f

namespace Principia

local notation Δ:0 " ⟹[" T "] " f => Pr T Δ f

class Intuitionistic (F : Type u) [LogicSymbol F] (α : outParam (Type*)) extends Principia F α where
  weakening' {α : α} {Δ Γ} {p q : F}  : ~p :: Δ ⊆ ~q :: Γ → (Δ ⟹[a] p) → (Γ ⟹[a] q)
  trans {a : α} {Δ} {p q : F}         : (Δ ⟹[a] p) → ((p :: Δ) ⟹[a] q) → (Δ ⟹[a] q)
  assumption {a : α} {Δ} {p : F}      : p ∈ Δ → (Δ ⟹[a] p)
  contradiction {a : α} {Δ} {p q : F} : (Δ ⟹[a] p) → (Δ ⟹[a] ~p) → (Δ ⟹[a] q)
  trivial {a : α} {Δ : List F}        : Δ ⟹[a] ⊤
  explode {a : α} {Δ} {p : F}         : (Δ ⟹[a] ⊥) → Δ ⟹[a] p
  intro {a : α} {Δ} {p q : F}         : ((p :: Δ) ⟹[a] q) → (Δ ⟹[a] p ⟶ q)
  modusPonens {a : α} {Δ} {p q : F}   : (Δ ⟹[a] p ⟶ q) → (Δ ⟹[a] p) → (Δ ⟹[a] q)
  split {a : α} {Δ} {p q : F}         : (Δ ⟹[a] p) → (Δ ⟹[a] q) → (Δ ⟹[a] p ⋏ q)
  andLeft {a : α} {Δ} {p q : F}       : (Δ ⟹[a] p ⋏ q) → (Δ ⟹[a] p)
  andRight {a : α} {Δ} {p q : F}      : (Δ ⟹[a] p ⋏ q) → (Δ ⟹[a] q)
  orLeft {a : α} {Δ} {p q : F}        : (Δ ⟹[a] p) → (Δ ⟹[a] p ⋎ q)
  orRight {a : α} {Δ} {p q : F}       : (Δ ⟹[a] q) → (Δ ⟹[a] p ⋎ q)
  cases {a : α} {Δ} {p q r : F}       :
    (Δ ⟹[a] (p ⋎ q)) → ((p :: Δ) ⟹[a] r) → ((q :: Δ) ⟹[a] r) → (Δ ⟹[a] r)

variable {F : Type u} [LogicSymbol F]

end Principia

end Logic

end LO
