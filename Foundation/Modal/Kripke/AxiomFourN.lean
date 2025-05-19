import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filtration
import Foundation.Vorspiel.Relation.Iterate

namespace LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} [HasAxiomFourN n 𝓢]

instance : HasAxiomGeach ⟨0, n + 1, n, 0⟩ 𝓢 := ⟨fun _ ↦ axiomFourN⟩

end LO.Entailment


section

variable {n : ℕ+}  {α : Type u} {rel : α → α → Prop}

def WeakTransitive (n : ℕ+) (rel : α → α → Prop) := ∀ x y, (Rel.iterate rel (n + 1)) x y → (Rel.iterate rel n) x y

@[simp]
lemma weak_transitive_one_transitive : (WeakTransitive 1 rel) ↔ Transitive rel := by
  simp only [WeakTransitive, PNat.val_ofNat, Nat.reduceAdd, Rel.iterate.iff_succ, Rel.iterate.iff_zero, exists_eq_right, forall_exists_index, and_imp, Transitive];
  constructor;
  . intro h x y z; apply h;
  . intro h x y z; apply h;

class IsWeakTrans (n) (α) (rel : α → α → Prop) : Prop where
  weakTrans : WeakTransitive n rel

instance [IsWeakTrans n _ rel] : IsGeachean ⟨0, n + 1, n, 0⟩ _ rel := ⟨by
  simp only [Rel.iterate.iff_zero, Rel.iterate.iff_succ, exists_eq_right', and_imp, forall_exists_index];
  rintro x _ y rfl u Rxw Rwz;
  apply IsWeakTrans.weakTrans;
  use u;
⟩

instance [IsGeachean ⟨0, n + 1, n, 0⟩ _ rel] : IsWeakTrans n _ rel := ⟨by
  rintro x y ⟨u, Rxu, Ruy⟩;
  have : ∀ u, rel x u → Rel.iterate rel (↑n) u y → Rel.iterate rel (↑n) x y := by
    simpa using @IsGeachean.geachean (g := ⟨0, n + 1, n, 0⟩) (R := rel) _ _ x x y;
  apply this u Rxu Ruy;
⟩

end


namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke

variable {n : ℕ+}

lemma validate_axiomFourN_of_weak_transitive {F : Kripke.Frame} [IsWeakTrans n _ F.Rel] : F ⊧ (Axioms.FourN n (.atom 0)) := validate_AxiomGeach_of_Geachean (g := ⟨0, n + 1, n, 0⟩)

namespace Canonical

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Modal.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance isWeakTrans [Entailment.HasAxiomFourN n 𝓢] : IsWeakTrans n _ (canonicalFrame 𝓢).Rel := by
  have : IsGeachean ⟨0, n + 1, n, 0⟩ _ (canonicalFrame 𝓢).Rel := isGeachean (g := ⟨0, n + 1, n, 0⟩) (𝓢 := 𝓢);
  infer_instance;

end Canonical

end Kripke

end LO.Modal
