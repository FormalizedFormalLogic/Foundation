module

public import Foundation.FirstOrder.Completeness.CanonicalModel
public import Foundation.Vorspiel.Order.Dense
public import Mathlib.Logic.Equiv.List
public import Mathlib.Logic.Encodable.Basic

@[expose] public section

namespace LO.FirstOrder.Derivation.Canonical

open Order

variable {L : Language}

local notation "ℙ" => Sequent L
local notation "ℙ⁻" => ConsistentSequent L

scoped notation "ℍ" => LowerSet ℙ⁻

instance [L.Encodable] [L.DecidableEq] : Encodable (Sequent L) := List.encodable

open Classical in
noncomputable instance [L.Encodable] : Encodable ℙ⁻ := Subtype.encodable

def value (φ : Proposition L) : ℍ where
  carrier := { p | p ⊩ᶜ φ }
  lower'  _ _ hqp hp := IsWeaklyForced.monotone hqp hp

notation "‖" φ "‖" => value φ

lemma provable_iff_dense {φ : Proposition L} :
    𝐋𝐊¹ ⊢ φ ↔ IsDense (‖φ‖ : Set ℙ⁻) := calc
  𝐋𝐊¹ ⊢ φ ↔ ℙ⁻ ∀⊩ᶜ φ := IsWeaklyForced.complete.symm
  _      ↔ IsDense (‖φ‖ : Set ℙ⁻) := by
    constructor
    · intro h p
      suffices ∃ q ≤ p, q ⊩ᶜ φ by simpa [value]
      refine ⟨p, by simp, h p⟩
    · intro h p
      apply IsWeaklyForced.gnericity.mpr
      intro q hqp
      simpa [value] using h q

open Classical
def decidablePoints (φ : Proposition L) : DenseSet ℙ⁻ where
  set := {p | p ⊩ᶜ φ ∨ p ⊩ᶜ ∼φ}
  is_dense := by
    intro p
    have : p ⊩ᶜ φ ⋎ ∼φ := IsWeaklyForced.complete.mpr Entailment.lem! p
    have : ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ ∨ r ⊩ᶜ ∼φ := by simpa using this
    simpa using this p (by rfl)

variable [L.Encodable]

theorem genericFIlter_exists (p : ℙ⁻) :
    ∃ G : PFilter ℙ⁻, G.IsGeneric (Set.range decidablePoints) ∧ p ∈ G :=
  PFilter.countable_isGeneric (Set.range decidablePoints) (Set.countable_range decidablePoints) p

noncomputable def genericFilter (p : ℙ⁻) : PFilter ℙ⁻ := Classical.choose (genericFIlter_exists p)

instance genericFilter_isGeneric (p : ℙ⁻) : (genericFilter p).IsGeneric (Set.range decidablePoints) :=
  Classical.choose_spec (genericFIlter_exists p) |>.1

@[simp] lemma mem_genericFilter (p : ℙ⁻) : p ∈ genericFilter p :=
  Classical.choose_spec (genericFIlter_exists p) |>.2

end LO.FirstOrder.Derivation.Canonical
