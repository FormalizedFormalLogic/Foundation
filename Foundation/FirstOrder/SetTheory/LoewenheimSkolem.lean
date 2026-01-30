module

public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.FirstOrder.Skolemization.Hull

@[expose] public section
/-!
# Downward Löwenheim-Skolem theorem for models of set theory
-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] (s : Set V)

def Hull : Set V := Structure.SkolemHull ℒₛₑₜ s

variable (V)

abbrev Collapse : Set V := Hull ∅

variable {V}

namespace Hull

@[simp] lemma mk_mem_mk_iff {x y : V} {hx hy} : (⟨x, hx⟩ : Hull s) ∈ (⟨y, hy⟩ : Hull s) ↔ x ∈ y := by rfl

lemma str_eq : Structure.SkolemHull.str (standardStructure V) s = standardStructure (Hull s) := by
  have : (Structure.SkolemHull.str (standardStructure V) s).Eq ℒₛₑₜ (Hull s) := Structure.SkolemHull.eq
  have : (Structure.SkolemHull.str (standardStructure V) s).Mem ℒₛₑₜ (Hull s) := Structure.SkolemHull.mem
  exact standardStructure_unique (Hull s) (Structure.SkolemHull.str (standardStructure V) s)

@[simp] lemma subset : s ⊆ Hull s := Structure.SkolemHull.subset

lemma closed {v : Fin k → V} (hv : ∀ i, v i ∈ Hull s)
    {φ : Semisentence ℒₛₑₜ (k + 1)} (H : ∃ z, V ⊧/(z :> v) φ) :
    ∃ z ∈ Hull s, V ⊧/(z :> v) φ :=
  Structure.SkolemHull.closed hv H

@[simp] lemma hull_models_iff {φ : Semisentence ℒₛₑₜ n} :
    (Hull s) ⊧/b φ ↔ V ⊧/(b ·) φ := by
  have :
      Semiformula.Evalb (Structure.SkolemHull.str (standardStructure V) s) b φ ↔
      V ⊧/(b ·) φ :=
    Structure.SkolemHull.str_eval (𝓼 := standardStructure V) (φ := φ) (b := b)
  rw [str_eq] at this
  exact this

instance set_nonempty : (Hull s).Nonempty := Structure.SkolemHull.set_nonempty _ _

instance nonempty : Nonempty (Hull s) := Structure.SkolemHull.nonempty _ _

instance elementaryEquiv : (Hull s) ≡ₑ[ℒₛₑₜ] V  where
  models {φ} := by simp [models_iff, Matrix.empty_eq]

instance set_countable [hs : Countable s] : (Hull s).Countable := Structure.SkolemHull.set_countable hs

instance countable [hs : Countable s] : Countable (Hull s) := Structure.SkolemHull.set_countable hs

instance countable₀ : Countable (Collapse V) := Structure.SkolemHull.countable₀

instance small [hs : Countable s] : Small.{w} ↑(Hull s) := Countable.toSmall (Hull s)

end Hull

end LO.FirstOrder.SetTheory
