module

public import Foundation.FirstOrder.SetTheory.Definability.Hierarchy
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic

/-!
# Lévy definability
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.HierarchySymbol

open FFL.FirstOrder.Semiformula (Operator)
open scoped FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

namespace Definable

section

variable {k : ℕ} {ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol}

lemma lévy_ball {P : (Fin k → V) → V → Prop}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : SetTheorySemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x ∈ t.val v id, P v x :=
  ball (R := Operator.Mem.mem) (by rfl) h t

lemma lévy_bexs {P : (Fin k → V) → V → Prop}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : SetTheorySemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x ∈ t.val v id, P v x :=
  bexs (R := Operator.Mem.mem) (by rfl) h t

lemma lévy_ballCons {P : (Fin (k + 1) → V) → Prop} (h : ℌ.Definable P)
    (t : SetTheorySemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x ∈ t.val v id, P (x :> v) :=
  lévy_ball (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma lévy_bexsCons {P : (Fin (k + 1) → V) → Prop} (h : ℌ.Definable P)
    (t : SetTheorySemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x ∈ t.val v id, P (x :> v) :=
  lévy_bexs (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

end

section

variable {k m : ℕ} {Γ : SigmaPiDelta}

@[elab_as_elim]
theorem lévy_sigma_succ_induction
    {motive : (k : ℕ) → (P : (Fin k → V) → Prop) → 𝚺ᴸ_[m + 1].Definable P → Prop}
    (pi : ∀ {k} {P : (Fin k → V) → Prop} (hP : 𝚷ᴸ_[m].Definable P),
      motive k P (hP.of_lt (Nat.lt_succ_self m)))
    (and : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺ᴸ_[m + 1].Definable P) (hQ : 𝚺ᴸ_[m + 1].Definable Q),
      motive k P hP → motive k Q hQ → motive k (fun v ↦ P v ∧ Q v) (.and hP hQ))
    (or : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺ᴸ_[m + 1].Definable P) (hQ : 𝚺ᴸ_[m + 1].Definable Q),
      motive k P hP → motive k Q hQ → motive k (fun v ↦ P v ∨ Q v) (.or hP hQ))
    (ball : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (t : SetTheorySemiterm V k)
      (hP : 𝚺ᴸ_[m + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∀ x ∈ t.val v id, P (x :> v))
        (lévy_ballCons hP t))
    (bexs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (t : SetTheorySemiterm V k)
      (hP : 𝚺ᴸ_[m + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∃ x ∈ t.val v id, P (x :> v))
        (lévy_bexsCons hP t))
    (exs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (hP : 𝚺ᴸ_[m + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∃ x, P (x :> v)) (.exsCons hP))
    (k : ℕ) (P : (Fin k → V) → Prop) (hP : 𝚺ᴸ_[m + 1].Definable P) : motive k P hP := by
  apply sigma_succ_induction (motive := motive) pi and or ?_ ?_ exs k P hP
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using ball t hP ih
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using bexs t hP ih

end

end Definable

abbrev ExtDefinedFunction (ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol) {k} (f : (Fin k → V) → V) :=
  ℌ.Definable fun v ↦ v 0 ∈ f (v ·.succ)

abbrev ExtDefinedFunction₀ (ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol) (c : V) : Prop :=
  ℌ.ExtDefinedFunction (fun _ : Fin 0 → V ↦ c)

abbrev ExtDefinedFunction₁ (ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol) (f : V → V) : Prop :=
  ℌ.ExtDefinedFunction (fun v : Fin 1 → V ↦ f (v 0))

abbrev ExtDefinedFunction₂ (ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol) (f : V → V → V) : Prop :=
  ℌ.ExtDefinedFunction (fun v : Fin 2 → V ↦ f (v 0) (v 1))

abbrev ExtDefinedFunction₃ (ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol) (f : V → V → V → V) : Prop :=
  ℌ.ExtDefinedFunction (fun v : Fin 3 → V ↦ f (v 0) (v 1) (v 2))

namespace ExtDefinedFunction

variable {ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol}

@[definability] instance proj {k} (i : Fin k) : ℌ.ExtDefinedFunction (fun v : Fin k → V ↦ v i) := sorry

lemma toDefinableFunction {k} {f : (Fin k → V) → V} (h : ℌ.ExtDefinedFunction f) :
    ℌ.DefinableFunction f := sorry

end ExtDefinedFunction

end FFL.FirstOrder.Bounding.HierarchySymbol
