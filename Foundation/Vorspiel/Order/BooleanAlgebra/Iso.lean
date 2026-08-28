module

public import Foundation.Vorspiel.Order.BooleanAlgebra.Extension
public import Mathlib.Order.Ideal

/-!
# Countable atomless Boolean algebras are isomorphic

Any two countable, nontrivial, atomless (equivalently, densely ordered) Boolean algebras are
order isomorphic (`iso_of_countable_atomless`), by a back-and-forth argument over the preorder
`PartialIso α β` of isomorphisms between finite Boolean subalgebras, modeled on
`Order.iso_of_countable_dense` (`Mathlib.Order.CountableDenseLinearOrder`).

Analogue, for Boolean algebras, of Cantor's isomorphism theorem for countable dense
linear orders; there is no direct literature source for the Boolean algebra case.
-/

@[expose] public section

open BooleanSubalgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

lemma BooleanSubalgebra.coe_bot_finite : ((⊥ : BooleanSubalgebra α) : Set α).Finite := by
  rw [coe_bot]; exact (Set.finite_singleton _).insert _

variable (α β) in
/-- A partial isomorphism between `α` and `β`: an order isomorphism between two finite
Boolean subalgebras. -/
structure PartialIso where
  domSubalg : BooleanSubalgebra α
  codSubalg : BooleanSubalgebra β
  finite_dom : (domSubalg : Set α).Finite
  finite_cod : (codSubalg : Set β).Finite
  iso : domSubalg ≃o codSubalg

namespace PartialIso

instance : Preorder (PartialIso α β) where
  le f g := ∃ hA : f.domSubalg ≤ g.domSubalg, ∀ x : f.domSubalg, (g.iso ⟨x, hA x.2⟩ : β) = f.iso x
  le_refl _ := ⟨le_refl _, fun _ ↦ rfl⟩
  le_trans _ _ _ := fun ⟨hfg, hfg'⟩ ⟨hgh, hgh'⟩ ↦
    ⟨hfg.trans hgh, fun x ↦ (hgh' ⟨x, hfg x.2⟩).trans (hfg' x)⟩

noncomputable instance [Nontrivial α] [Nontrivial β] : Inhabited (PartialIso α β) :=
  ⟨⟨⊥, ⊥, coe_bot_finite, coe_bot_finite, botOrderIso⟩⟩

def comm : PartialIso α β → PartialIso β α :=
  fun f => ⟨f.codSubalg, f.domSubalg, f.finite_cod, f.finite_dom, f.iso.symm⟩

section

variable {f g : PartialIso α β}

lemma le_def :
    f ≤ g ↔ ∃ hA : f.domSubalg ≤ g.domSubalg,
      ∀ x : f.domSubalg, (g.iso ⟨x, hA x.2⟩ : β) = f.iso x := Iff.rfl

lemma cod_le_of_le (hfg : f ≤ g) : f.codSubalg ≤ g.codSubalg := by
  obtain ⟨hA, hval⟩ := hfg
  intro v hv
  have h : (g.iso ⟨f.iso.symm ⟨v, hv⟩, hA (f.iso.symm ⟨v, hv⟩).2⟩ : β) = v := by
    rw [hval, OrderIso.apply_symm_apply]
  exact h ▸ (g.iso _).2

lemma symm_agree_of_le (hfg : f ≤ g) (v : f.codSubalg) :
    (g.iso.symm ⟨v, cod_le_of_le hfg v.2⟩ : α) = f.iso.symm v := by
  obtain ⟨hA, hval⟩ := id hfg
  have h : g.iso ⟨f.iso.symm v, hA (f.iso.symm v).2⟩ = ⟨v, cod_le_of_le hfg v.2⟩ :=
    Subtype.ext (by rw [hval, OrderIso.apply_symm_apply])
  rw [← h, OrderIso.symm_apply_apply]

lemma comm_le_comm (hfg : f ≤ g) : f.comm ≤ g.comm :=
  ⟨cod_le_of_le hfg, symm_agree_of_le hfg⟩

end

theorem exists_le_mem_dom [Nontrivial β] [DenselyOrdered β]
    (f : PartialIso α β) (a : α) : ∃ g : PartialIso α β, f ≤ g ∧ a ∈ g.domSubalg := by
  obtain ⟨b, h⟩ := exists_isCompanion f.finite_dom f.iso a
  exact ⟨⟨_, _, closure_insert_finite f.finite_dom a, closure_insert_finite f.finite_cod b,
    IsCompanion.extend h⟩, ⟨le_closure_insert, IsCompanion.extend_coe h⟩, self_mem_closure_insert⟩

def definedAtLeft [Nontrivial β] [DenselyOrdered β] (a : α) : Order.Cofinal (PartialIso α β) where
  carrier := {f | a ∈ f.domSubalg}
  isCofinal f := by
    obtain ⟨g, hfg, hmem⟩ := exists_le_mem_dom f a
    exact ⟨g, hmem, hfg⟩

def definedAtRight [Nontrivial α] [DenselyOrdered α] (b : β) : Order.Cofinal (PartialIso α β) where
  carrier := {f | b ∈ f.codSubalg}
  isCofinal f := by
    obtain ⟨g, hmem, hfg⟩ := (definedAtLeft (β := α) b).isCofinal f.comm
    exact ⟨g.comm, hmem, comm_le_comm hfg⟩

end PartialIso

open PartialIso

/-- Any two countable, nontrivial, atomless (densely ordered) Boolean algebras are
order isomorphic. -/
theorem iso_of_countable_atomless
    [Countable α] [Nontrivial α] [DenselyOrdered α]
    [Countable β] [Nontrivial β] [DenselyOrdered β] :
    Nonempty (α ≃o β) := by
  sorry
