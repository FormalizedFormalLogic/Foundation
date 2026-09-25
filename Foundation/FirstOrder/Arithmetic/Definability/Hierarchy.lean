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

abbrev HierarchySymbol := Bounding.HierarchySymbol

@[match_pattern] abbrev HierarchySymbol.mk (Γ : SigmaPiDelta) (n : ℕ) : HierarchySymbol :=
  Bounding.HierarchySymbol.mk Γ n

scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n

abbrev HierarchySymbol.sigmaZero : HierarchySymbol := 𝚺-[0]

abbrev HierarchySymbol.piZero : HierarchySymbol := 𝚷-[0]

abbrev HierarchySymbol.deltaZero : HierarchySymbol := 𝚫-[0]

abbrev HierarchySymbol.sigmaOne : HierarchySymbol := 𝚺-[1]

abbrev HierarchySymbol.piOne : HierarchySymbol := 𝚷-[1]

abbrev HierarchySymbol.deltaOne : HierarchySymbol := 𝚫-[1]

notation "𝚺₀" => HierarchySymbol.sigmaZero

notation "𝚷₀" => HierarchySymbol.piZero

notation "𝚫₀" => HierarchySymbol.deltaZero

notation "𝚺₁" => HierarchySymbol.sigmaOne

notation "𝚷₁" => HierarchySymbol.piOne

notation "𝚫₁" => HierarchySymbol.deltaOne

namespace HierarchySymbol

protected abbrev Semiformula (Γ : HierarchySymbol) (ξ : Type*) (n : ℕ) :=
  Bounding.HierarchySymbol.Semiformula ℬ[<, ℒₒᵣ] ξ n Γ

protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) :=
  Γ.Semiformula Empty n

protected abbrev Sentence (Γ : HierarchySymbol) :=
  Γ.Semiformula Empty 0

variable {Γ : HierarchySymbol}

namespace Semiformula

def ball (t : ArithmeticSemiterm ξ n) {Γ : HierarchySymbol}
    (φ : Γ.Semiformula ξ (n + 1)) : Γ.Semiformula ξ n :=
  Bounding.HierarchySymbol.Semiformula.ball (ℬ := ℬ[<, ℒₒᵣ])
    (R := Semiformula.Operator.LT.lt) (by rfl) t φ

def bexs (t : ArithmeticSemiterm ξ n) {Γ : HierarchySymbol}
    (φ : Γ.Semiformula ξ (n + 1)) : Γ.Semiformula ξ n :=
  Bounding.HierarchySymbol.Semiformula.bexs (ℬ := ℬ[<, ℒₒᵣ])
    (R := Semiformula.Operator.LT.lt) (by rfl) t φ

@[simp] lemma val_ball (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (ball t φ).val = ∀¹[“#0 < !!(Rew.bShift t)”] φ.val :=
  Bounding.HierarchySymbol.Semiformula.val_ball (ℬ := ℬ[<, ℒₒᵣ])
    (R := Semiformula.Operator.LT.lt) (by rfl) t φ

@[simp] lemma val_bexs (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (bexs t φ).val = ∃¹[“#0 < !!(Rew.bShift t)”] φ.val :=
  Bounding.HierarchySymbol.Semiformula.val_bexs (ℬ := ℬ[<, ℒₒᵣ])
    (R := Semiformula.Operator.LT.lt) (by rfl) t φ

lemma ProvablyProperOn.ofProperOn (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T]
    {φ : 𝚫-[m].Semisentence n}
    (h : ∀ (M : Type w) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T], φ.ProperOn M) :
    φ.ProvablyProperOn T := by
  apply FirstOrder.Arithmetic.complete.{w} T _
  intro M _ _
  simpa [models_iff] using! (h M).iff

end Semiformula

end HierarchySymbol

end FFL.FirstOrder.Arithmetic
