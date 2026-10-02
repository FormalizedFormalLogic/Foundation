module

public import Foundation.FirstOrder.SetTheory.Z
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Hierarchy

/-!
# Lévy hierarchy
-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

abbrev lévy :=   @Bounding.HierarchySymbol.mk _ ℬ[∈, ℒₛₑₜ]

/-- Notation for the Lévy hierarchy -/
scoped notation:max Γ:max "ᴸ-[" n "]" => lévy Γ n

notation "𝚺ᴸ₀" => (𝚺ᴸ-[0])
notation "𝚷ᴸ₀" => (𝚷ᴸ-[0])
notation "𝚫ᴸ₀" => (𝚫ᴸ-[0])
notation "𝚺ᴸ₁" => (𝚺ᴸ-[1])
notation "𝚷ᴸ₁" => (𝚷ᴸ-[1])
notation "𝚫ᴸ₁" => (𝚫ᴸ-[1])

end FFL.FirstOrder.SetTheory

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula

universe w

open FFL.FirstOrder.SetTheory
open FFL.FirstOrder.Semiformula (Operator)

variable {ξ : Type*} {n m : ℕ}

variable {Γ : HierarchySymbol ℬ[∈, ℒₛₑₜ]}

def lévy_ball (t : Semiterm ℒₛₑₜ ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    Γ.Semiformula ξ n :=
  ball (R := Operator.Mem.mem) (by rfl) t φ

def lévy_bexs (t : Semiterm ℒₛₑₜ ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    Γ.Semiformula ξ n :=
  bexs (R := Operator.Mem.mem) (by rfl) t φ

@[simp] lemma val_lévy_ball (t : Semiterm ℒₛₑₜ ξ n)
    (φ : Γ.Semiformula ξ (n + 1)) :
  (lévy_ball t φ).val = ∀¹[“#0 ∈ !!(Rew.bShift t)”] φ.val :=
  val_ball (R := Operator.Mem.mem) (by rfl) t φ

@[simp] lemma val_lévy_bexs (t : Semiterm ℒₛₑₜ ξ n)
    (φ : Γ.Semiformula ξ (n + 1)) :
  (lévy_bexs t φ).val = ∃¹[“#0 ∈ !!(Rew.bShift t)”] φ.val :=
  val_bexs (R := Operator.Mem.mem) (by rfl) t φ

lemma ProvablyProperOn.lévy_ofProperOn (T : Theory ℒₛₑₜ) [𝗘𝗤 ℒₛₑₜ ⪯ T]
    {φ : 𝚫ᴸ-[m].Semisentence n}
    (h : ∀ (M : Type w) [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* T], φ.ProperOn M) :
    φ.ProvablyProperOn T :=
  FirstOrder.SetTheory.complete T _
  fun M _ _ ↦ by simpa [models_iff] using! (h M).iff

end FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula
