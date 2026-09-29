module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.BoundedSatisfaction

/-!
# Satisfaction for prenex formulas with a $\Delta_0$ matrix

`HierarchicalSatisfaction Γ s p e` says that `Q₀ x₀ ⋯ Q_{s-1} x_{s-1} θ` holds under the
assignment `e`, where `p` codes the $\Delta_0$ matrix `θ` and the quantifiers alternate starting
with `Γ`; the value of `x_i` is pushed onto the front of `e`. For `s ≥ 1` it is definable at
level `Γ`-`s`.

## References

- [HP98, 1.64, Definition I.1.74, Theorem I.1.75]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def HierarchicalSatisfaction : Polarity → ℕ → V → V → Prop
  | _, 0 => BoundedSatisfaction
  | 𝚺, s + 1 => fun p e ↦ ∃ x, HierarchicalSatisfaction 𝚷 s p (x ∷ e)
  | 𝚷, s + 1 => fun p e ↦ ∀ x, HierarchicalSatisfaction 𝚺 s p (x ∷ e)

section
variable {Γ : Polarity} {s : ℕ} {p e : V}

@[simp] lemma HierarchicalSatisfaction.zero_iff :
    HierarchicalSatisfaction Γ 0 p e ↔ BoundedSatisfaction p e := by
  cases Γ <;> rfl

@[simp] lemma HierarchicalSatisfaction.sigma_succ_iff :
    HierarchicalSatisfaction 𝚺 (s + 1) p e ↔ ∃ x, HierarchicalSatisfaction 𝚷 s p (x ∷ e) :=
  Iff.rfl

@[simp] lemma HierarchicalSatisfaction.pi_succ_iff :
    HierarchicalSatisfaction 𝚷 (s + 1) p e ↔ ∀ x, HierarchicalSatisfaction 𝚺 s p (x ∷ e) :=
  Iff.rfl

end

noncomputable def hierarchicalSatisfaction : (Γ : Polarity) → (s : ℕ) → Γᴬ-[s + 1].Semisentence 2
  | 𝚺, 0 => .mkSigma “p e. ∃ x e', !adjoinDef e' x e ∧ !boundedSatisfaction.sigma p e'”
  | 𝚷, 0 => .mkPi “p e. ∀ x e', !adjoinDef e' x e → !boundedSatisfaction.pi p e'”
  | 𝚺, s + 1 => .mkSigma
      “p e. ∃ x e', !adjoinDef e' x e ∧ !(hierarchicalSatisfaction 𝚷 s).val p e'”
      (by simpa using (hierarchicalSatisfaction 𝚷 s).polarity_prop.accum 𝚺)
  | 𝚷, s + 1 => .mkPi
      “p e. ∀ x e', !adjoinDef e' x e → !(hierarchicalSatisfaction 𝚺 s).val p e'”
      (by simpa using (hierarchicalSatisfaction 𝚺 s).polarity_prop.accum 𝚷)

mutual

instance HierarchicalSatisfaction.sigma_defined : (s : ℕ) →
    𝚺ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚺 (s + 1) : V → V → Prop)
      via hierarchicalSatisfaction 𝚺 s
  | 0 => .mk fun v ↦ by simp [hierarchicalSatisfaction]
  | s + 1 => .mk fun v ↦ by simp [hierarchicalSatisfaction, (pi_defined s).df]

instance HierarchicalSatisfaction.pi_defined : (s : ℕ) →
    𝚷ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚷 (s + 1) : V → V → Prop)
      via hierarchicalSatisfaction 𝚷 s
  | 0 => .mk fun v ↦ by simp [hierarchicalSatisfaction]
  | s + 1 => .mk fun v ↦ by simp [hierarchicalSatisfaction, (sigma_defined s).df]

end

instance HierarchicalSatisfaction.sigma_definable (s : ℕ) :
    𝚺ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚺 (s + 1) : V → V → Prop) :=
  (sigma_defined s).to_definable

instance HierarchicalSatisfaction.pi_definable (s : ℕ) :
    𝚷ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚷 (s + 1) : V → V → Prop) :=
  (pi_defined s).to_definable

end FFL.FirstOrder.Arithmetic.Bootstrapping
