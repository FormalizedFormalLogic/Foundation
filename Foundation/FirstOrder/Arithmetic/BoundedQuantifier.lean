import Foundation.FirstOrder.PeanoMinus.Basic

namespace LO.FirstOrder.Semiformula

open PeanoMinus

variable {M : Type*} [ORingStructure M] [M ⊧ₘ* 𝗣𝗔⁻] {L : Language} [L.LT] [L.Zero] [L.One] [L.Add]

variable [Structure L M] [Structure.LT L M] [Structure.One L M] [Structure.Add L M]

@[simp] lemma eval_ballLTSucc' {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)} :
    Semiformula.Evalm M e ε (φ.ballLTSucc t) ↔ ∀ x ≤ Semiterm.valm M e ε t, Semiformula.Evalm M (x :> e) ε φ := by
  simp [Semiformula.eval_ballLTSucc, lt_succ_iff_le]

@[simp] lemma eval_bexLTSucc' {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)} :
    Semiformula.Evalm M e ε (φ.bexLTSucc t) ↔ ∃ x ≤ Semiterm.valm M e ε t, Semiformula.Evalm M (x :> e) ε φ := by
  simp [Semiformula.eval_bexLTSucc, lt_succ_iff_le]

end LO.FirstOrder.Semiformula
