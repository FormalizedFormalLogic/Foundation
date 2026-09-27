module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Hierarchy

/-!
# Formulas sorted by the arithmetical hierarchy

This module specializes the bounding hierarchy to the strict-order operator of the language of
arithmetic. The hierarchy wrappers themselves are defined in
`FirstOrder.Bounding.HierarchySymbol`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

scoped notation:max Γ:max "ᴬ-[" n "]" =>
  @Bounding.HierarchySymbol.mk _ ℬ[<, ℒₒᵣ] Γ n

scoped notation "𝚺ᴬ₀" => (𝚺ᴬ-[0])
scoped notation "𝚷ᴬ₀" => (𝚷ᴬ-[0])
scoped notation "𝚫ᴬ₀" => (𝚫ᴬ-[0])
scoped notation "𝚺ᴬ₁" => (𝚺ᴬ-[1])
scoped notation "𝚷ᴬ₁" => (𝚷ᴬ-[1])
scoped notation "𝚫ᴬ₁" => (𝚫ᴬ-[1])

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula

universe w

open FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Semiformula (Operator)

variable {ξ : Type*} {n m : ℕ}

variable {Γ : HierarchySymbol ℬ[<, ℒₒᵣ]}

def arithmetic_ball (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    Γ.Semiformula ξ n :=
  ball (R := Operator.LT.lt) (by rfl) t φ

def arithmetic_bexs (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    Γ.Semiformula ξ n :=
  bexs (R := Operator.LT.lt) (by rfl) t φ

@[simp] lemma val_arithmetic_ball (t : ArithmeticSemiterm ξ n)
    (φ : Γ.Semiformula ξ (n + 1)) :
  (arithmetic_ball t φ).val = ∀¹[“#0 < !!(Rew.bShift t)”] φ.val :=
  val_ball (R := Operator.LT.lt) (by rfl) t φ

@[simp] lemma val_arithmetic_bexs (t : ArithmeticSemiterm ξ n)
    (φ : Γ.Semiformula ξ (n + 1)) :
  (arithmetic_bexs t φ).val = ∃¹[“#0 < !!(Rew.bShift t)”] φ.val :=
  val_bexs (R := Operator.LT.lt) (by rfl) t φ

lemma ProvablyProperOn.arithmetic_ofProperOn (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T]
    {φ : 𝚫ᴬ-[m].Semisentence n}
    (h : ∀ (M : Type w) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T], φ.ProperOn M) :
    φ.ProvablyProperOn T := by
  apply FirstOrder.Arithmetic.complete.{w} T _
  intro M _ _
  simpa [models_iff] using! (h M).iff

end FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula
