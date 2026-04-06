module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Image

@[expose] public section

variable {α : Type*}

namespace Finset

section sup

variable [SemilatticeSup α] [OrderBot α]

lemma subtype_sup_val_of (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → α) (h : ∀ i ∈ s, p i) :
    (s.subtype p).sup (f ∘ Subtype.val) = s.sup f := by
  have : s.filter p = s := by ext i; simpa using h i
  simp only [Finset.subtype, Function.comp_def, sup_map, Function.Embedding.coeFn_mk, sup_attach, this]

end sup

section inf

variable [SemilatticeInf α] [OrderTop α]

lemma subtype_inf_val_of (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → α) (h : ∀ i ∈ s, p i) :
    (s.subtype p).inf (f ∘ Subtype.val) = s.inf f := by
  have : s.filter p = s := by ext i; simpa using h i
  simp only [Finset.subtype, Function.comp_def, inf_map, Function.Embedding.coeFn_mk, inf_attach, this]

end inf

end Finset
