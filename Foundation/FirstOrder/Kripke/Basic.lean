module

public import Foundation.FirstOrder.Basic
public import Foundation.Logic.Predicate.Relational
public import Foundation.Logic.ForcingRelation
public import Mathlib.Order.PFilter
public import Foundation.Vorspiel.Preorder

@[expose] public section
namespace LO.FirstOrder

/-- Kripke model for relational first-order language -/
class KripkeModel
    (L : outParam Language) [L.Relational]
    (World : Type*) [Preorder World]
    (Carrier : outParam Type*) where
  Domain : World → Set Carrier
  domain_nonempty : ∀ w, ∃ x, x ∈ Domain w
  domain_antimonotone : w ≥ v → Domain w ⊆ Domain v
  Rel (w : World) {k : ℕ} (R : L.Rel k) : (Fin k → Carrier) → Prop
  rel_monotone : Rel w R t → ∀ v ≤ w, Rel v R t

class KripkeModel.ConstantDomain
    {L : Language} [L.Relational]
    (World : Type*) [Preorder World]
    {Carrier : Type*} [KripkeModel L World Carrier] where
  const_domain : ∀ w : World, Domain w = Set.univ

attribute [simp] KripkeModel.ConstantDomain.const_domain

variable (L : Language) [L.Relational] (W : Type*) [Preorder W] (C : outParam Type*) [KripkeModel L W C]

instance : CoeSort W (Type _) := ⟨fun w ↦ KripkeModel.Domain w⟩

instance : ForcingExists W C := ⟨fun p x ↦ x ∈ KripkeModel.Domain p⟩

variable {L W C}

namespace KripkeModel

lemma domain_nonempty' (p : W) : ∃ x, p ⊩↓ x := domain_nonempty p

lemma domain_monotone {p : W} : p ⊩↓ x → ∀ q ≤ p, q ⊩↓ x := fun hx _ h ↦
  domain_antimonotone h hx

@[simp] lemma domain_forcesExists {p : W} (x : p) : p ⊩↓ x.val := x.prop

@[simp] lemma forcingExists_of_constantDomain [ConstantDomain W] (w : W) (x : C) : w ⊩↓ x := by
  suffices x ∈ Domain w from this; simp

section point_model

instance domain (w : W) : Structure L w where
  func _ f _ := IsEmpty.elim' inferInstance f
  rel _ R v := Rel w R fun i ↦ ↑(v i)

set_option linter.unusedVariables false in
def Point [KripkeModel L W C] (w : W) := C

instance domain' (w : W) : Structure L (Point w) where
  func _ f _ := IsEmpty.elim' inferInstance f
  rel _ R v := Rel w R v

variable {w : W}

@[simp] lemma domain_models_rel {R : L.Rel k} {v : Fin k → w} :
    (domain w).rel R v ↔ Rel w R fun i ↦ ↑(v i) := by rfl

@[simp] lemma domain'_models_rel {R : L.Rel k} {v : Fin k → Point w} :
    (domain' w).rel R v ↔ Rel w R fun i ↦ ↑(v i) := by rfl

@[simp] lemma domain_val (t : Semiterm L ξ n) : t.val (domain w) bv fv = t.relationalVal bv fv := by
  rcases Semiterm.bvar_or_fvar_of_relational t with (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> simp

@[simp] lemma domain'_val (t : Semiterm L ξ n) : t.val (domain' w) bv fv = t.relationalVal bv fv := by
  rcases Semiterm.bvar_or_fvar_of_relational t with (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> simp

end point_model

section filter

variable (W)

abbrev Filter : Type _ := Order.PFilter W

variable {W}

namespace Filter

/-- A domain of filter `F` -/
@[ext] structure Model (F : Filter W) where
  val : C
  mem_filter : ∃ p ∈ F, p ⊩↓ val

attribute [coe] Model.val

variable (F : Filter W)

instance : CoeOut F.Model C := ⟨fun x ↦ x.val⟩

lemma finite_colimit [Fintype ι] (p : ι → W) (hp : ∀ i, p i ∈ F) : ∃ q ∈ F, ∀ i, q ≤ p i :=
  DirectedOn.fintype_colimit transitive_ge (Order.PFilter.nonempty F) F.directed p hp

lemma finite_colimit_domain [Fintype ι] (v : ι → F.Model) :
    ∃ q ∈ F, ∀ i, q ⊩↓ ↑(v i) := by
  have : ∀ i, ∃ p ∈ F, p ⊩↓ ↑(v i) := fun i ↦ (v i).mem_filter
  choose p hp using this
  have : ∃ q ∈ F, ∀ i, q ≤ p i := F.finite_colimit p fun i ↦ (hp i).1
  rcases this with ⟨q, hq, hqp⟩
  refine ⟨q, hq, fun i ↦ domain_antimonotone (hqp i) (hp i).2⟩

instance Str : Structure L F.Model where
  func _ f _ := IsEmpty.elim' inferInstance f
  rel _ R v := ∀ p ∈ F, (∀ i, p ⊩↓ ↑(v i)) → Rel p R fun i ↦ (v i).val

@[simp] lemma Str.rel_iff {k : ℕ} (R : L.Rel k) (v : Fin k → F.Model) :
    F.Str.rel R v ↔ ∀ p ∈ F, (∀ i, p ⊩↓ ↑(v i)) → Rel p R fun i ↦ (v i).val := by rfl

end Filter

end filter

end KripkeModel

end LO.FirstOrder
