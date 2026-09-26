module

public import Foundation.ProvabilityLogic.GL.CIP
public import Foundation.ProvabilityLogic.S.Basic

/-!
# Craig interpolation property of `S`

## References

- [Bek87]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment

universe u

variable {α : Type u} [DecidableEq α] {A B : Formula α}

lemma Formula.rflSubfmls_imp (A B : Formula α) :
    (A 🡒 B).rflSubfmls = A.rflSubfmls ∪ B.rflSubfmls := by
  ext;
  simp [Formula.rflSubfmls, FormulaFinset.mem_prebox, Formula.subfmls, or_and_right, exists_or];

namespace Logic.S

lemma atoms_rflSubfmls_subset (A : Formula α) : A.rflSubfmls.atoms ⊆ A.atoms :=
  Finset.biUnion_subset.mpr <| Finset.forall_mem_image.mpr fun B hB ↦ by
    simpa using Formula.atoms_subset_of_mem_subfmls
      (Formula.subfmls_trans (FormulaFinset.mem_prebox.mp hB) Formula.mem_subfmls_box)

lemma provable_fconj_rflSubfmls (A : Formula α) : 𝐒 ⊢ A.rflSubfmls.conj :=
  FConj_iff_forall_provable.mpr fun φ hφ ↦ by
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hφ;
    exact axiomT;

/-- **Craig interpolation property** of `𝐒`.

- [Bek87, Theorem 2] -/
theorem CIP (h : 𝐒 ⊢ A 🡒 B) :
    ∃ C, 𝐒 ⊢ A 🡒 C ∧ 𝐒 ⊢ C 🡒 B ∧ C.atoms ⊆ A.atoms ∩ B.atoms := by
  have h' : 𝐆𝐋 ⊢ A.rflSubfmls.conj ⋏ B.rflSubfmls.conj 🡒 A 🡒 B :=
    C_trans CKFconjFconjUnion <| Formula.rflSubfmls_imp A B ▸ iff_provable_GL.mp h;
  obtain ⟨C, hC₁, hC₂, hCAtoms⟩ := GL.CIP (A := A.rflSubfmls.conj ⋏ A)
    (B := B.rflSubfmls.conj 🡒 B) (by cl_prover [h']);
  use C;
  and_intros;
  · exact of_GL (by cl_prover [hC₁]) ⨀ provable_fconj_rflSubfmls A;
  · exact of_GL (by cl_prover [hC₂]) ⨀ provable_fconj_rflSubfmls B;
  · have (X : Formula α) : X.rflSubfmls.conj.atoms ∪ X.atoms ⊆ X.atoms :=
      Finset.union_subset
        ((FormulaFinset.atoms_conj_subset _).trans (atoms_rflSubfmls_subset X)) subset_rfl;
    exact hCAtoms.trans <| Finset.inter_subset_inter (by simpa using this A) (this B);

end Logic.S

end FFL.ProvabilityLogic

end
