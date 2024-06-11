import Logic.FirstOrder.Arith.Theory

namespace LO.FirstOrder

structure ProvabilityPredicate (L₀ L : Language) where
  prov : Semisentence L₀ 1

namespace ProvabilityPredicate

section

variable [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]

def pr (β : ProvabilityPredicate L₀ L) (σ : Sentence L) : Semisentence L₀ n := β.prov/[⸢σ⸣]

notation "⦍" β "⦎" σ:80 => pr β σ

class Conservative (β : ProvabilityPredicate L₀ L) (T₀ : Theory L₀) (T : outParam (Theory L)) where
  iff (σ : Sentence L) : T ⊢! σ ↔ T₀ ⊢! ⦍β⦎ σ

end

section HilbertBernays

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class HilbertBernays₁ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D1 (σ : Sentence L) : T ⊢! σ → T₀ ⊢! ⦍β⦎σ

class HilbertBernays₂ (β : ProvabilityPredicate L L) (T₀ : Theory L) where
  D2 (σ τ : Sentence L) : T₀ ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ

class HilbertBernays₃ (β : ProvabilityPredicate L L) (T₀ : Theory L) where
  D3 (σ : Sentence L) : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ

class HilbertBernays (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L))
  extends β.HilbertBernays₁ T₀ T, β.HilbertBernays₂ T₀, β.HilbertBernays₃ T₀

end HilbertBernays

end ProvabilityPredicate

end LO.FirstOrder
