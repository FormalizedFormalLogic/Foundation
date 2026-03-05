module

public import Foundation.Modal.Neighborhood2.Basic
public import Foundation.Modal.MaximalConsistentSet

@[expose] public section

namespace LO

variable {S F : Type*} [Entailment S F] {𝓢 : S}

structure ProofStructure {S : Type*} {F : Type*} [Entailment S F] (𝓢 : S) where
  S : F → Set (Set F)
  iff_mem {φ Γ}    : Γ ∈ (S φ) ↔ φ ∈ Γ
  iff_provable {φ} : (S φ) = Set.univ ↔ 𝓢 ⊢ φ

namespace ProofStructure

variable {P : ProofStructure 𝓢}

instance : CoeFun (ProofStructure 𝓢) (λ P => F → Set (Set F)) := ⟨λ P => P.S⟩

class BooleanFalsum [Bot F] (P : ProofStructure 𝓢) where
  def_falsum : P ⊥ = ∅
export BooleanFalsum (def_falsum)

class BooleanImply [Arrow F] (P : ProofStructure 𝓢) where
  def_imp {φ ψ} : P (φ ➝ ψ) = (P φ)ᶜ ∪ P ψ
export BooleanImply (def_imp)

class BooleanNeg [Tilde F] (P : ProofStructure 𝓢) where
  def_neg {φ} : P (∼φ) = (P φ)ᶜ
export BooleanNeg (def_neg)

class BooleanAnd [Wedge F] (P : ProofStructure 𝓢) where
  def_and {φ ψ} : P (φ ⋏ ψ) = P φ ∩ P ψ
export BooleanAnd (def_and)

class BooleanOr [Vee F] (P : ProofStructure 𝓢) where
  def_or {φ ψ} : P (φ ⋎ ψ) = P φ ∪ P ψ
export BooleanOr (def_or)

attribute [grind .] def_falsum
attribute [grind =] def_imp def_neg def_and def_or

section

variable [LogicalConnective F] [ŁukasiewiczAbbrev F]
         [P.BooleanFalsum] [P.BooleanImply]

instance : P.BooleanNeg := ⟨by grind⟩
instance : P.BooleanAnd := ⟨by grind⟩
instance : P.BooleanOr  := ⟨by grind⟩

end

end ProofStructure

end LO


namespace LO.Modal

variable {ν : Type v} [Nonempty ν]
         {α : Type u} [DecidableEq α]
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S} [Entailment.E 𝓢] [Entailment.Consistent 𝓢]

namespace NeighborhoodModel

class IsCanonical (M : NeighborhoodModel (Set (Formula α)) α) (P : ProofStructure 𝓢) where
  canonical_neighborhood : ∀ X φ, X ∈ M.box (P φ) ↔ □φ ∈ X
  canonical_val : ∀ a, M.val a = P (.atom a)

namespace IsCanonical

variable {M : NeighborhoodModel _ α} {P : ProofStructure 𝓢} [P.BooleanImply] [P.BooleanFalsum] [M.IsCanonical P]

attribute [grind .] canonical_val

@[grind .]
lemma def_box : (M.box (P.S φ)) = (P (□φ)) := by
  ext x;
  apply Iff.trans (canonical_neighborhood x φ) P.iff_mem.symm;

lemma truthlemma : M φ = P φ := by induction φ <;> grind;

lemma completenes
  (C : ∀ {ν}, [Nonempty ν] → NeighborhoodModel ν α → Prop)
  (hI : ∃ M, C M ∧ (M.IsCanonical P)) : (∀ {ν}, [Nonempty ν] → ∀ M : NeighborhoodModel.{u, u} ν α, C M → M ⊧ φ) → 𝓢 ⊢ φ := by
  contrapose!;
  intro h;
  obtain ⟨M, A, hM⟩ := hI;
  use (Set (Formula α)), inferInstance, M;
  constructor;
  . assumption;
  . simpa [iff_validates_eq_truthset_univ, truthlemma (M := M) (P := P), P.iff_provable];

end IsCanonical


end NeighborhoodModel

end LO.Modal

end
