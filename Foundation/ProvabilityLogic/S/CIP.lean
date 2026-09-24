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
  unfold Formula.rflSubfmls;
  rw [show (A 🡒 B).subfmls.prebox = A.subfmls.prebox ∪ B.subfmls.prebox from ?_,
    Finset.image_union];
  ext C;
  simp [FormulaFinset.mem_prebox, Formula.subfmls];

namespace Logic.S

lemma atoms_rflSubfmls_subset (A : Formula α) : A.rflSubfmls.atoms ⊆ A.atoms := by
  intro a ha;
  simp only [Formula.rflSubfmls, FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at ha;
  obtain ⟨_, ⟨B, hB, rfl⟩, ha⟩ := ha;
  have hBmem : B ∈ A.subfmls :=
    Formula.subfmls_trans (FormulaFinset.mem_prebox.mp hB) Formula.mem_subfmls_box;
  simp only [Formula.atoms_imp, Formula.atoms_box, Finset.union_self] at ha;
  exact Formula.atoms_subset_of_mem_subfmls hBmem ha;

lemma provable_fconj_rflSubfmls (A : Formula α) : 𝐒 ⊢ A.rflSubfmls.conj :=
  FConj_iff_forall_provable.mpr fun φ hφ ↦ by
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hφ;
    exact axiomT;

lemma provable_reassoc_of_provable_imp (h : 𝐒 ⊢ A 🡒 B) :
    𝐆𝐋 ⊢ (A.rflSubfmls.conj ⋏ A) 🡒 (B.rflSubfmls.conj 🡒 B) := by
  have hGL : 𝐆𝐋 ⊢ (A 🡒 B).rflSubfmls.conj 🡒 (A 🡒 B) := iff_provable_GL.mp h;
  rw [Formula.rflSubfmls_imp] at hGL;
  have hUnion : 𝐆𝐋 ⊢ (A.rflSubfmls.conj ⋏ B.rflSubfmls.conj) 🡒 (A 🡒 B) :=
    C_trans CKFconjFconjUnion hGL;
  cl_prover [hUnion];

/-- **Craig interpolation property** of `𝐒`.

- [Bek87, Theorem 2] -/
theorem CIP (h : 𝐒 ⊢ A 🡒 B) :
    ∃ C, 𝐒 ⊢ A 🡒 C ∧ 𝐒 ⊢ C 🡒 B ∧ C.atoms ⊆ A.atoms ∩ B.atoms := by
  obtain ⟨C, hC₁, hC₂, hCAtoms⟩ := Logic.GL.CIP (provable_reassoc_of_provable_imp h);
  use C;
  and_intros;
  · exact of_GL (by cl_prover [hC₁]) ⨀ provable_fconj_rflSubfmls A;
  · exact of_GL (by cl_prover [hC₂]) ⨀ provable_fconj_rflSubfmls B;
  · have hA' : (A.rflSubfmls.conj ⋏ A).atoms ⊆ A.atoms := by
      rw [Formula.atoms_and];
      exact Finset.union_subset
        ((FormulaFinset.atoms_conj_subset _).trans (atoms_rflSubfmls_subset A)) subset_rfl;
    have hB' : (B.rflSubfmls.conj 🡒 B).atoms ⊆ B.atoms := by
      rw [Formula.atoms_imp];
      exact Finset.union_subset
        ((FormulaFinset.atoms_conj_subset _).trans (atoms_rflSubfmls_subset B)) subset_rfl;
    exact hCAtoms.trans <| Finset.inter_subset_inter hA' hB';

end Logic.S

end FFL.ProvabilityLogic

end
