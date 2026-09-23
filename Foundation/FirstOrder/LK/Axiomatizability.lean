module

public import Foundation.FirstOrder.LK.Basic

@[expose] public section
/-!
# Axiomatizability by a class of sentences

`AxiomatizableBy C T U` says that `U` axiomatizes `T` through sentences satisfying `C`, and
`Axiomatizable C T` that such a `U` exists. Foundation's `Entailment.FiniteAxiomatizable` already
covers finite axiomatizability over an arbitrary entailment structure.

## References

- [HP98, Discussion III.2.28]
-/

namespace FFL.FirstOrder

open FFL.Entailment

variable {L : Language} {C D : Sentence L → Prop} {T U V : Theory L}

structure AxiomatizableBy (C : Sentence L → Prop) (T U : Theory L) : Prop where
  forall_mem : ∀ σ ∈ U, C σ
  equiv : T ≊ U

def Axiomatizable (C : Sentence L → Prop) (T : Theory L) : Prop :=
  ∃ U : Theory L, AxiomatizableBy C T U

namespace AxiomatizableBy

lemma refl (h : ∀ σ ∈ T, C σ) : AxiomatizableBy C T T := ⟨h, .refl T⟩

lemma of_equiv (h : AxiomatizableBy C T U) (e : T ≊ V) : AxiomatizableBy C V U :=
  ⟨h.forall_mem, e.symm.trans h.equiv⟩

lemma mono (h : AxiomatizableBy C T U) (hCD : ∀ σ, C σ → D σ) : AxiomatizableBy D T U :=
  ⟨fun σ hσ ↦ hCD σ (h.forall_mem σ hσ), h.equiv⟩

lemma axiomatizable (h : AxiomatizableBy C T U) : Axiomatizable C T := ⟨U, h⟩

end AxiomatizableBy

namespace Axiomatizable

lemma of_forall_mem (h : ∀ σ ∈ T, C σ) : Axiomatizable C T := (AxiomatizableBy.refl h).axiomatizable

lemma of_equiv (h : Axiomatizable C T) (e : T ≊ U) : Axiomatizable C U := by
  obtain ⟨V, hV⟩ := h;
  exact (hV.of_equiv e).axiomatizable;

lemma mono (h : Axiomatizable C T) (hCD : ∀ σ, C σ → D σ) : Axiomatizable D T := by
  obtain ⟨U, hU⟩ := h;
  exact (hU.mono hCD).axiomatizable;

end Axiomatizable

end FFL.FirstOrder
