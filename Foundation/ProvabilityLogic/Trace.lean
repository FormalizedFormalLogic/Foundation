module

public import Foundation.ProvabilityLogic.GLAlpha.Basic
public import Foundation.ProvabilityLogic.GLBetaMinus.Basic
public import Foundation.ProvabilityLogic.Kripke.Graft
public import Foundation.ProvabilityLogic.S.Basic

/-!
# Traces of formulas and logics

The trace of a formula is the set of heights of finite rooted `GL` models whose root refutes it,
and the trace of a logic is the union of the traces of its members. On letterless formulas it
agrees with `LetterlessFormula.trace`. A logic is bounded above by `GLα` or `GLβ⁻` of its trace,
according as the complement of its trace is infinite or finite.

## References

- [AB05]
- [Bek90]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World

universe u

lemma Kripke.Model.forces_TBB_iff {κ α : Type*} [Nonempty κ] {M : Model κ α} [Fintype M.World]
    [M.IsGL] {x : M.World} {n : ℕ} : x ⊩[M] TBB n ↔ x.rank ≠ n := by
  grind [TBB, forces_boxItr_bot_iff];

namespace Formula

variable {α : Type u} {A B : Formula α} {n : ℕ}

/-- The trace of `A`: the heights of the finite rooted `GL` models whose root does not force `A`.

- [AB05]
-/
def trace (A : Formula α) : Set ℕ :=
  {n | ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : Fintype M.World) (_ : M.IsGL),
    M.height = n ∧ M.root ⊮[M.toModel] A}

lemma root_forces_of_not_mem_trace {κ : Type u} [Nonempty κ] {M : RootedModel κ α}
    [Fintype M.World] [M.IsGL] (h : M.height ∉ A.trace) : M.root ⊩[M.toModel] A := by
  by_contra hA;
  exact h ⟨κ, _, M, _, _, rfl, hA⟩;

lemma GL_imp_of_height_not_mem_trace
    (h : ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsGL],
      M.root ⊩[M.toModel] B → M.height ∉ A.trace) : 𝐆𝐋 ⊢ B 🡒 A := by
  apply Logic.GL.iff_root_forces.mpr;
  intro _ _ M _ hB;
  have : Fintype M.World := Fintype.ofFinite _;
  exact root_forces_of_not_mem_trace (h M hB);

lemma trace_lift (B : LetterlessFormula) : (B.lift : Formula α).trace = B.trace := by
  ext n;
  constructor;
  · rintro ⟨κ, _, M, _, _, rfl, h⟩ hB;
    exact h (LetterlessFormula.forces_lift_iff.mpr hB);
  · intro hn;
    by_contra hn';
    have h : 𝐆𝐋 ⊢ ∼TBB n 🡒 (B.lift : Formula α) :=
      GL_imp_of_height_not_mem_trace fun M _ _ hM ↦ by
        have : Model.World.rank (M := M.toModel) M.root = n := by
          simpa [forces_neg, forces_TBB_iff] using hM;
        rwa [show M.height = n from this];
    rw [← LetterlessFormula.lift_TBB] at h;
    have := Set.eq_univ_iff_forall.mp ((Logic.GL.lift_mem_iff (A := ∼TBB n 🡒 B)).mp h) n;
    simp_all;

@[simp] lemma trace_top : (⊤ : Formula α).trace = ∅ := by
  sorry

@[simp] lemma trace_bot : (⊥ : Formula α).trace = Set.univ := by
  simpa [LetterlessFormula.trace] using trace_lift (α := α) ⊥;

@[simp] lemma trace_TBB : (TBB n : Formula α).trace = {n} := by
  simpa using trace_lift (α := α) (TBB n);

@[simp] lemma trace_and : (A ⋏ B).trace = A.trace ∪ B.trace := by
  ext n;
  simp only [trace, Set.mem_ofPred_eq, Set.mem_union, forces_and, not_and_or];
  grind;

@[simp] lemma trace_conj [DecidableEq α] {Γ : FormulaFinset α} :
    Γ.conj.trace = ⋃ B ∈ Γ, B.trace := by
  ext n;
  simp only [trace, Set.mem_ofPred_eq, Set.mem_iUnion, forces_conj];
  grind;

lemma trace_subst_subset {s : Substitution α α} : (A⟦s⟧).trace ⊆ A.trace := by
  sorry

/-- - [AB05, Lemma 12] -/
theorem trace_finite_or_compl_finite (A : Formula α) : A.trace.Finite ∨ A.traceᶜ.Finite := by
  sorry

end Formula

namespace Logic

variable {α : Type u} {L : Logic α} {A : Formula α}

/-- The trace of a logic: the union of the traces of its members. -/
def trace (L : Logic α) : Set ℕ := ⋃ A ∈ L, A.trace

lemma trace_subset_of_mem (h : A ∈ L) : A.trace ⊆ L.trace := by
  sorry

namespace GL

lemma exists_finset_trace_subset_of_mem_sumQuasiNormal {X : Logic α} (h : A ∈ 𝐆𝐋 +ᴸ X) :
    ∃ Y : Finset (Formula α), ↑Y ⊆ X ∧ A.trace ⊆ ⋃ B ∈ Y, B.trace := by
  sorry

theorem trace_sumQuasiNormal (X : Logic α) : (𝐆𝐋 +ᴸ X).trace = X.trace := by
  sorry

end GL

namespace GLAlpha

variable {X Y : Set ℕ}

theorem mem_iff : A ∈ (𝐆𝐋α X : Logic α) ↔ A.trace.Finite ∧ A.trace ⊆ X := by
  sorry

@[simp] theorem trace_eq : (𝐆𝐋α X : Logic α).trace = X := by
  sorry

lemma mono (h : X ⊆ Y) : (𝐆𝐋α X : Logic α) ⊆ 𝐆𝐋α Y := by
  sorry

lemma subset_S : (𝐆𝐋α X : Logic α) ⊆ 𝐒 := by
  sorry

end GLAlpha

namespace GLBetaMinus

variable {X : Set ℕ} {hX : Xᶜ.Finite}

theorem mem_iff : A ∈ (𝐆𝐋β⁻ X hX : Logic α) ↔ A.trace ⊆ X := by
  sorry

@[simp] theorem trace_eq : (𝐆𝐋β⁻ X hX : Logic α).trace = X := by
  sorry

/-- - [AB05, Lemma 49] -/
lemma bot_mem_univ {hX : (Set.univ : Set ℕ)ᶜ.Finite} : (⊥ : Formula α) ∈ 𝐆𝐋β⁻ Set.univ hX := by
  sorry

end GLBetaMinus

namespace GLAlpha

variable {X : Set ℕ} (hX : Xᶜ.Finite)

lemma subset_GLBetaMinus : (𝐆𝐋α X : Logic α) ⊆ 𝐆𝐋β⁻ X hX := by
  sorry

theorem eq_inter_GLBetaMinus : (𝐆𝐋α X : Logic α) = 𝐆𝐋α Set.univ ∩ 𝐆𝐋β⁻ X hX := by
  sorry

end GLAlpha

/-- - [AB05, Lemma 45] -/
theorem subset_GLAlpha_trace (hL : L.traceᶜ.Infinite) : L ⊆ 𝐆𝐋α L.trace := by
  sorry

/-- - [AB05, Lemma 45] -/
theorem subset_GLBetaMinus_trace (hL : L.traceᶜ.Finite) : L ⊆ 𝐆𝐋β⁻ L.trace hL := by
  sorry

end Logic

end FFL.ProvabilityLogic

end
