import Foundation.Vorspiel.Preorder
import Foundation.FirstOrder.Basic
import Foundation.Logic.Predicate.Relational
import Foundation.Logic.ForcingRelation
import Mathlib.Order.PFilter

namespace LO.FirstOrder

/-- Kripke model for relational first-order language -/
structure RelationalKripkeModel (L : Language) [L.Relational] where
  Condition : Type*
  [preorder : Preorder Condition]
  Name : Type*
  Domain : Condition → Set Name
  domain_nonempty : ∀ w, ∃ x, x ∈ Domain w
  domain_antimonotone : w ≥ v → Domain w ⊆ Domain v
  Rel (w : Condition) {k : ℕ} (R : L.Rel k) : (Fin k → Name) → Prop
  rel_monotone : w ≥ v → Rel w R t → Rel v R t

variable (L : Language) [L.Relational]

instance : CoeSort (RelationalKripkeModel L) (Type _) := ⟨fun 𝓚 ↦ 𝓚.Condition⟩

instance (𝓚 : RelationalKripkeModel L) : CoeSort 𝓚.Condition (Type _) := ⟨fun w ↦ 𝓚.Domain w⟩

instance (𝓚 : RelationalKripkeModel L) : Preorder 𝓚.Condition := 𝓚.preorder

variable {L}

namespace RelationalKripkeModel

variable (𝓚 : RelationalKripkeModel L)

abbrev Filter : Type _ := Order.PFilter 𝓚

variable {𝓚}

namespace Filter

/-- A domain of filter `F` -/
@[ext] structure Domain (F : 𝓚.Filter) where
  val : 𝓚.Name
  mem_filter : ∃ p ∈ F, val ∈ 𝓚.Domain p

attribute [coe] Domain.val

variable (F : 𝓚.Filter)

instance : CoeOut F.Domain 𝓚.Name := ⟨fun x ↦ x.val⟩

lemma finite_colimit [Fintype ι] (p : ι → 𝓚) (hp : ∀ i, p i ∈ F) : ∃ q ∈ F, ∀ i, q ≤ p i :=
  DirectedOn.fintype_colimit transitive_ge (Order.PFilter.nonempty F) F.directed p hp

lemma finite_colimit_domain [Fintype ι] (v : ι → F.Domain) :
    ∃ q ∈ F, ∀ i, (v i).val ∈ 𝓚.Domain q := by
  have : ∀ i, ∃ p ∈ F, (v i).val ∈ 𝓚.Domain p := fun i ↦ (v i).mem_filter
  choose p hp using this
  have : ∃ q ∈ F, ∀ i, q ≤ p i := F.finite_colimit p fun i ↦ (hp i).1
  rcases this with ⟨q, hq, hqp⟩
  refine ⟨q, hq, fun i ↦ 𝓚.domain_antimonotone (hqp i) (hp i).2⟩

instance Str : Structure L F.Domain where
  func _ f _ := IsEmpty.elim' inferInstance f
  rel _ R v := ∀ p ∈ F, (∀ i, (v i).val ∈ 𝓚.Domain p) → 𝓚.Rel p R fun i ↦ v i

@[simp] lemma Str.rel_iff {k : ℕ} (R : L.Rel k) (v : Fin k → F.Domain) :
    F.Str.rel R v ↔ ∀ p ∈ F, (∀ i, (v i).val ∈ 𝓚.Domain p) → 𝓚.Rel p R fun i ↦ v i := by rfl

end Filter

end RelationalKripkeModel

end LO.FirstOrder
