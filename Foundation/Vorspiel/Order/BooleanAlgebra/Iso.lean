module

public import Foundation.Vorspiel.Order.BooleanAlgebra.Extension
public import Mathlib.Order.Ideal

/-!
# Countable atomless Boolean algebras are isomorphic

Any two countable, nontrivial, atomless (equivalently, densely ordered) Boolean
algebras are order isomorphic (`iso_of_countable_atomless`). The proof is a
back-and-forth argument, modeled on `Order.iso_of_countable_dense`
(`Mathlib.Order.CountableDenseLinearOrder`):

* `PartialIso α β` bundles an order isomorphism between two finite Boolean
  subalgebras of `α` and `β`, preordered by extension.
* `PartialIso.definedAtLeft`/`PartialIso.definedAtRight` are cofinal in that preorder
  whenever the codomain is a nontrivial densely ordered (atomless) Boolean algebra.
* A generic ideal in this poset, obtained from `Order.idealOfCofinals`, is directed and
  meets every `definedAtLeft`/`definedAtRight`, hence assembles into a total order
  isomorphism `α ≃o β`.

Analogue, for Boolean algebras, of Cantor's isomorphism theorem for countable dense
linear orders; there is no direct literature source for the Boolean algebra case.
-/

@[expose] public section

open BooleanSubalgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

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

/-- `f ≤ g` when `g`'s domain extends `f`'s and `g`'s isomorphism agrees with `f`'s on
`f`'s domain. -/
instance : Preorder (PartialIso α β) where
  le f g := ∃ hA : f.domSubalg ≤ g.domSubalg, ∀ x : f.domSubalg, (g.iso ⟨x, hA x.2⟩ : β) = f.iso x
  le_refl f := ⟨le_refl _, fun x => by sorry⟩
  le_trans f g h hfg hgh := by sorry

noncomputable instance [Nontrivial α] [Nontrivial β] : Inhabited (PartialIso α β) :=
  ⟨⟨⊥, ⊥, by sorry, by sorry, botOrderIso⟩⟩

lemma le_def {f g : PartialIso α β} :
    f ≤ g ↔ ∃ hA : f.domSubalg ≤ g.domSubalg,
      ∀ x : f.domSubalg, (g.iso ⟨x, hA x.2⟩ : β) = f.iso x := Iff.rfl

/-- The codomain of an extension `g` of `f` also extends `f`'s codomain. -/
lemma cod_le_of_le {f g : PartialIso α β} (hfg : f ≤ g) : f.codSubalg ≤ g.codSubalg := by
  sorry

/-- The inverse isomorphisms of `f ≤ g` agree on `f`'s codomain. -/
lemma symm_agree_of_le {f g : PartialIso α β} (hfg : f ≤ g) (v : f.codSubalg) :
    (g.iso.symm ⟨v, cod_le_of_le hfg v.2⟩ : α) = f.iso.symm v := by
  sorry

/-- A partial isomorphism between `α` and `β` is also one between `β` and `α`. -/
def comm : PartialIso α β → PartialIso β α :=
  fun f => ⟨f.codSubalg, f.domSubalg, f.finite_cod, f.finite_dom, f.iso.symm⟩

lemma comm_le_comm {f g : PartialIso α β} (hfg : f ≤ g) : f.comm ≤ g.comm := by
  sorry

/-- Any `f : PartialIso α β` extends to some `g` whose domain contains `a`, provided `β`
is a nontrivial densely ordered (atomless) Boolean algebra. -/
theorem exists_le_mem_dom [Nontrivial β] [DenselyOrdered β]
    (f : PartialIso α β) (a : α) : ∃ g : PartialIso α β, f ≤ g ∧ a ∈ g.domSubalg := by
  sorry

/-- The set of partial isomorphisms whose domain contains `a`, which is cofinal whenever
`β` is a nontrivial densely ordered (atomless) Boolean algebra. -/
def definedAtLeft [Nontrivial β] [DenselyOrdered β] (a : α) : Order.Cofinal (PartialIso α β) where
  carrier := {f | a ∈ f.domSubalg}
  isCofinal f := by
    sorry

/-- The set of partial isomorphisms whose codomain contains `b`, which is cofinal
whenever `α` is a nontrivial densely ordered (atomless) Boolean algebra. -/
def definedAtRight [Nontrivial α] [DenselyOrdered α] (b : β) : Order.Cofinal (PartialIso α β) where
  carrier := {f | b ∈ f.codSubalg}
  isCofinal f := by
    sorry

end PartialIso

open PartialIso

/-- Any two countable, nontrivial, atomless (densely ordered) Boolean algebras are
order isomorphic. -/
theorem iso_of_countable_atomless
    [Countable α] [Nontrivial α] [DenselyOrdered α]
    [Countable β] [Nontrivial β] [DenselyOrdered β] :
    Nonempty (α ≃o β) := by
  sorry
