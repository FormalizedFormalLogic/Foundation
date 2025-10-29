import Foundation.FirstOrder.Kripke.Basic

namespace LO.FirstOrder.RelationalKripkeModel

variable {L : Language} [L.Relational] {ℙ : RelationalKripkeModel L}

def WeaklyForces {n} (p : ℙ) (bv : Fin n → ℙ.Name) (fv : ξ → ℙ.Name) : Semiformula L ξ n → Prop
  |  .rel R t => ∀ q ≤ p, ∃ r ≤ q, ℙ.Rel r R fun i ↦ (t i).relationalVal bv fv
  | .nrel R t => ∀ q ≤ p, ¬ℙ.Rel q R fun i ↦ (t i).relationalVal bv fv
  |         ⊤ => True
  |         ⊥ => False
  |     φ ⋏ ψ => WeaklyForces p bv fv φ ∧ WeaklyForces p bv fv ψ
  |     φ ⋎ ψ => ∀ q ≤ p, ∃ r ≤ q, WeaklyForces r bv fv φ ∨ WeaklyForces r bv fv ψ
  |      ∀' φ => ∀ q ≤ p, ∀ x : q, WeaklyForces q (x :> bv) fv φ
  |      ∃' φ => ∀ q ≤ p, ∃ r ≤ q, ∃ x : r, WeaklyForces r (x :> bv) fv φ

local notation:45 w " ⊩[" bv "|" fv "] " φ:46 => WeaklyForces w bv fv φ

section WeaklyForces

variable {bv : Fin n → ℙ.Name} {fv : ξ → ℙ.Name}

@[simp] lemma weaklyForces_rel {R : L.Rel k} {t : Fin k → Semiterm L ξ n} :
    p ⊩[bv|fv] Semiformula.rel R t ↔ ∀ q ≤ p, ∃ r ≤ q, ℙ.Rel r R fun i ↦ (t i).relationalVal bv fv := by rfl

@[simp] lemma weaklyForces_nrel {R : L.Rel k} {t : Fin k → Semiterm L ξ n} :
    p ⊩[bv|fv] Semiformula.nrel R t ↔ ∀ q ≤ p, ¬ℙ.Rel q R fun i ↦ (t i).relationalVal bv fv := by rfl

@[simp] lemma weaklyForces_verum : p ⊩[bv|fv] (⊤ : Semiformula L ξ n) := trivial

@[simp] lemma weaklyForces_falsum : ¬p ⊩[bv|fv] (⊥ : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma weaklyForces_and {φ ψ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ⋏ ψ ↔ p ⊩[bv|fv] φ ∧ p ⊩[bv|fv] ψ := by rfl

@[simp] lemma weaklyForces_or {φ ψ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ⋎ ψ ↔ ∀ q ≤ p, ∃ r ≤ q, WeaklyForces r bv fv φ ∨ WeaklyForces r bv fv ψ := by rfl

@[simp] lemma weaklyForces_all {φ : Semiformula L ξ (n + 1)} :
    p ⊩[bv|fv] ∀' φ ↔ ∀ q ≤ p, ∀ x : q, WeaklyForces q (x :> bv) fv φ := by rfl

@[simp] lemma weaklyForces_ex {φ : Semiformula L ξ (n + 1)} :
    p ⊩[bv|fv] ∃' φ ↔ ∀ q ≤ p, ∃ r ≤ q, ∃ x : r, WeaklyForces r (x :> bv) fv φ := by rfl

@[simp] lemma weaklyForces_not {φ : Semiformula L ξ n} :
    p ⊩[bv|fv] ∼φ ↔ ∀ q ≤ p, ¬q ⊩[bv|fv] φ := by {
  induction φ using Semiformula.rec' <;> try simp

     }

[simp] lemma weaklyForces_imply {φ ψ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ➝ ψ ↔ ∀ q ≤ p, q ⊩[bv|fv] φ → q ⊩[bv|fv] ψ := by {
  simp [DeMorgan.imply]
     }

end WeaklyForces

end RelationalKripkeModel
