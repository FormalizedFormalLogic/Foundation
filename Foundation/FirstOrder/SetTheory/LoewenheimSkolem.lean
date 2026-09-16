module

public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.FirstOrder.Tarski.Skolemization

@[expose] public section
/-!
# Downward Löwenheim-Skolem theorem for models of set theory
-/

namespace FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] (s : Set V)

def Hull : Set V := Tarski.Structure.SkolemHull ℒₛₑₜ s

variable (V)

abbrev Collapse : Set V := Hull ∅

variable {V}

namespace Hull

@[simp] lemma mk_mem_mk_iff {x y : V} {hx hy} : (⟨x, hx⟩ : Hull s) ∈ (⟨y, hy⟩ : Hull s) ↔ x ∈ y := by rfl

lemma str_eq : Tarski.Structure.SkolemHull.str (standardStructure V) s = standardStructure (Hull s) := by
  have : (Tarski.Structure.SkolemHull.str (standardStructure V) s).Eq ℒₛₑₜ (Hull s) := Tarski.Structure.SkolemHull.eq
  have : (Tarski.Structure.SkolemHull.str (standardStructure V) s).Mem ℒₛₑₜ (Hull s) := Tarski.Structure.SkolemHull.mem
  exact standardStructure_unique (Hull s) (Tarski.Structure.SkolemHull.str (standardStructure V) s)

@[simp] lemma subset : s ⊆ Hull s := Tarski.Structure.SkolemHull.subset

lemma closed {v : Fin k → V} (hv : ∀ i, v i ∈ Hull s)
    {φ : SetTheorySemisentence (k + 1)} (H : ∃ z, V ⊧/(z :> v) φ) :
    ∃ z ∈ Hull s, V ⊧/(z :> v) φ :=
  Tarski.Structure.SkolemHull.closed hv H

@[simp] lemma hull_models_iff {φ : SetTheorySemisentence n} :
    (Hull s) ⊧/b φ ↔ V ⊧/(b ·) φ := by
  have :
      φ.Evalb (s := Tarski.Structure.SkolemHull.str (standardStructure V) s) b ↔
      V ⊧/(b ·) φ :=
    Tarski.Structure.SkolemHull.str_eval (𝓼 := standardStructure V) (φ := φ) (b := b)
  rw [str_eq] at this
  exact this

lemma set_nonempty : (Hull s).Nonempty := Tarski.Structure.SkolemHull.set_nonempty _ _

instance nonempty : Nonempty (Hull s) := Tarski.Structure.SkolemHull.nonempty _ _

instance elementaryEquiv : (Hull s) ≡ₑ[ℒₛₑₜ] V  where
  models {φ} := by simp [models_iff, Matrix.empty_eq]

lemma set_countable [hs : Countable s] : (Hull s).Countable := Tarski.Structure.SkolemHull.set_countable hs

instance countable [hs : Countable s] : Countable (Hull s) := Tarski.Structure.SkolemHull.set_countable hs

instance countable₀ : Countable (Collapse V) := Tarski.Structure.SkolemHull.countable₀

instance small [hs : Countable s] : Small.{w} ↑(Hull s) := Countable.toSmall (Hull s)

end Hull

end FFL.FirstOrder.SetTheory
