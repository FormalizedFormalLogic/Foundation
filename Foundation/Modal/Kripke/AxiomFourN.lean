import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Filtration
import Foundation.Vorspiel.Relation.Iterate


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

instance [IsWeakTrans n _ rel] : IsGeachConfluent ⟨0, n + 1, n, 0⟩ _ rel := ⟨by
  suffices ∀ ⦃x y z : α⦄, x = y → ∀ (x_1 : α), rel x x_1 → Rel.iterate rel n x_1 z → Rel.iterate rel n y z by
    simpa [GeachConfluent];
  rintro x _ y rfl u Rxw Rwz;
  apply IsWeakTrans.weakTrans;
  use u;
⟩

instance [IsGeachConfluent ⟨0, n + 1, n, 0⟩ _ rel] : IsWeakTrans n _ rel := ⟨by
  rintro x y ⟨u, Rxu, Ruy⟩;
  have : ∀ u, rel x u → Rel.iterate rel (↑n) u y → Rel.iterate rel (↑n) x y := by
    simpa using @IsGeachConfluent.geachean (g := ⟨0, n + 1, n, 0⟩) (R := rel) _ _ x x y;
  apply this u Rxu Ruy;
⟩

end


namespace LO.Modal

open Kripke
open IsGeachConfluent

namespace Kripke

variable {n : ℕ+}

lemma validate_axiomFourN_of_weak_transitive {F : Kripke.Frame} [IsWeakTrans n _ F.Rel] : F ⊧ (Axioms.FourN n (.atom 0)) := validate_AxiomGeach_of_GeachConfluent (g := ⟨0, n + 1, n, 0⟩)

namespace Canonical

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance isWeakTrans [Entailment.HasAxiomFourN n 𝓢] : IsWeakTrans n _ (canonicalFrame 𝓢).Rel := by
  have := isGeachConfluent (g := ⟨0, n + 1, n, 0⟩) (𝓢 := 𝓢);
  infer_instance;

end Canonical

end Kripke

end LO.Modal
