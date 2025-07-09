import Foundation.FirstOrder.ISigma1.Metamath.Formula.Coding
import Foundation.FirstOrder.ISigma1.Metamath.Formula.Iteration

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

class _root_.LO.FirstOrder.Theory.Δ₁Definable (T : Theory L) where
  ch : 𝚫₁.Semisentence 1
  mem_iff : ∀ φ, ℕ ⊧/![⌜φ⌝] ch.val ↔ φ ∈ T
  isDelta1 : ch.ProvablyProperOn 𝐈𝚺₁

abbrev _root_.LO.FirstOrder.Theory.Δ₁ch (T : Theory L) [T.Δ₁Definable] : 𝚫₁.Semisentence 1 := Theory.Δ₁Definable.ch T

def _root_.LO.FirstOrder.Theory.Δ₁Class (T : Theory L) [T.Δ₁Definable] : Set V := { φ : V | V ⊧/![φ] T.Δ₁ch.val }

variable {T : Theory L} [T.Δ₁Definable]

instance Δ₁Class.defined : 𝚫₁-Predicate[V] (· ∈ T.Δ₁Class) via T.Δ₁ch := by
  constructor
  · intro v
    have : V ⊧/![v 0] (Theory.Δ₁Definable.ch T).sigma.val ↔ V ⊧/![v 0] (Theory.Δ₁Definable.ch T).pi.val := by
      have := (consequence_iff (T := 𝐈𝚺₁)).mp (sound!₀ <| FirstOrder.Theory.Δ₁Definable.isDelta1 (T := T)) V inferInstance
      simp [models_iff] at this ⊢
      simpa [Matrix.constant_eq_singleton] using this ![v 0]
    rwa [show v = ![v 0] from Matrix.fun_eq_vec_one]
  · intro v; simp [←Matrix.fun_eq_vec_one, Theory.Δ₁Class]

instance Δ₁Class.definable : 𝚫₁-Predicate[V] (· ∈ T.Δ₁Class) := Δ₁Class.defined.to_definable

omit [L.LORDefinable]

@[simp] lemma Δ₁Class.proper : T.Δ₁ch.ProperOn V := (Theory.Δ₁Definable.isDelta1 (T := T)).properOn V

@[simp] lemma Δ₁Class.mem_iff {φ : SyntacticFormula L} : (⌜φ⌝ : V) ∈ T.Δ₁Class ↔ φ ∈ T :=
  have : V ⊧/![⌜φ⌝] T.Δ₁ch.val ↔ ℕ ⊧/![⌜φ⌝] T.Δ₁ch.val := by
    simpa [coe_quote, Matrix.constant_eq_singleton]
      using FirstOrder.Arithmetic.models_iff_of_Delta1 (V := V) (σ := T.Δ₁ch) (by simp) (by simp) (e := ![⌜φ⌝])
  Iff.trans this (Theory.Δ₁Definable.mem_iff _)

end LO.ISigma1.Metamath
