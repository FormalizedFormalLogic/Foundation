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

@[simp] lemma trace_lift (B : LetterlessFormula) : (B.lift : Formula α).trace = B.trace := by
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
  simp [trace];

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
  rintro n ⟨κ, _, M, _, _, rfl, h⟩;
  exact ⟨κ, _, { M.toModel.subst s with root := M.root, root_rel := M.root_rel }, _,
    inferInstanceAs (M.toModel.subst s).IsGL, rfl, fun h' ↦ h (forces_subst.mp h')⟩;

/-- - [AB05, Lemma 12] -/
theorem trace_finite_or_compl_finite (A : Formula α) : A.trace.Finite ∨ A.traceᶜ.Finite := by
  classical
  rw [or_iff_not_imp_left];
  intro hinf;
  obtain ⟨_, ⟨κ, _, M, _, _, rfl, hA⟩, hm⟩ := Set.Infinite.exists_gt hinf A.subfmls.prebox.card;
  obtain ⟨u, Rru, hu⟩ := exists_isReflexiveOf_of_card_lt_rank hm;
  have hne : u ≠ M.root := by rintro rfl; exact Std.Irrefl.irrefl (r := M.Rel) _ Rru;
  have := RootedModel.rank_lt_height Rru;
  apply (Set.finite_Iio M.height).subset;
  intro n hn;
  by_contra hle;
  replace hle : M.height ≤ n := by simpa using hle;
  apply hn;
  exact ⟨_, _, M.graft ⟨u, hne⟩ (Fin (n - u.rank - 1)), inferInstance, inferInstance,
    by simp only [RootedModel.graft.height_eq]; omega,
    fun h ↦ hA <| ((RootedModel.graft.forces_iff (X := A.subfmls) (fun _ ↦ subfmls_trans)
      (fun B hB ↦ hu B (FormulaFinset.mem_prebox.mpr hB)) mem_subfmls_self).1 M.root).mp h⟩;

end Formula

namespace Logic

variable {α : Type u} {L : Logic α} {A : Formula α}

/-- The trace of a logic: the union of the traces of its members. -/
def trace (L : Logic α) : Set ℕ := ⋃ A ∈ L, A.trace

lemma trace_subset_of_mem (h : A ∈ L) : A.trace ⊆ L.trace := Set.subset_biUnion_of_mem h

namespace GL

lemma exists_finset_trace_subset_of_mem_sumQuasiNormal {X : Logic α} (h : A ∈ 𝐆𝐋 +ᴸ X) :
    ∃ Y : Finset (Formula α), ↑Y ⊆ X ∧ A.trace ⊆ ⋃ B ∈ Y, B.trace := by
  classical
  induction h with
  | mem₁ h =>
    exact ⟨∅, by simp, fun _ ⟨_, _, M, _, _, _, hA⟩ ↦ (hA (sound M.toModel h M.root)).elim⟩;
  | mem₂ h => exact ⟨{_}, by simpa, by simp⟩;
  | @mdp C _ _ _ ih₁ ih₂ =>
    obtain ⟨Y₁, hY₁, h₁⟩ := ih₁;
    obtain ⟨Y₂, hY₂, h₂⟩ := ih₂;
    use Y₁ ∪ Y₂;
    and_intros;
    · simp [hY₁, hY₂];
    · rintro n ⟨κ, _, M, _, _, rfl, hB⟩;
      by_cases hC : M.root ⊩[M.toModel] C;
      · exact Set.biUnion_subset_biUnion_left (by simp) <|
          h₁ (show M.height ∈ _ from ⟨κ, _, M, _, _, rfl, fun h ↦ hB (h hC)⟩);
      · exact Set.biUnion_subset_biUnion_left (by simp) <|
          h₂ (show M.height ∈ _ from ⟨κ, _, M, _, _, rfl, hC⟩);
  | subst _ ih =>
    obtain ⟨Y, hY, h⟩ := ih;
    exact ⟨Y, hY, trace_subst_subset.trans h⟩;

theorem trace_sumQuasiNormal (X : Logic α) : (𝐆𝐋 +ᴸ X).trace = X.trace := by
  apply subset_antisymm;
  · apply Set.iUnion₂_subset;
    intro A hA;
    obtain ⟨Y, hY, h⟩ := exists_finset_trace_subset_of_mem_sumQuasiNormal hA;
    exact h.trans (Set.biUnion_subset_biUnion_left hY);
  · exact Set.biUnion_subset_biUnion_left sumQuasiNormal.subset_right;

end GL

namespace GLAlpha

variable {X Y : Set ℕ}

theorem mem_iff : A ∈ (𝐆𝐋α X : Logic α) ↔ A.trace.Finite ∧ A.trace ⊆ X := by
  classical
  constructor;
  · intro h;
    obtain ⟨Y, hY, hA⟩ := GL.exists_finset_trace_subset_of_mem_sumQuasiNormal h;
    have hYX : ⋃ B ∈ Y, B.trace ⊆ X := by
      apply Set.iUnion₂_subset;
      intro B hB;
      obtain ⟨n, hn, rfl⟩ := hY hB;
      simpa using hn;
    have hfin : (⋃ B ∈ Y, B.trace).Finite := Y.finite_toSet.biUnion fun B hB ↦ by
      obtain ⟨n, -, rfl⟩ := hY hB;
      simp;
    exact ⟨hfin.subset hA, hA.trans hYX⟩;
  · rintro ⟨hfin, hX⟩;
    apply GL.sumQuasiNormal_of_conj (Γ := hfin.toFinset.image TBB);
    · simp only [Finset.mem_image, Set.Finite.mem_toFinset, forall_exists_index, and_imp];
      rintro _ n hn rfl;
      exact .mem₂ ⟨n, hX hn, rfl⟩;
    · apply Formula.GL_imp_of_height_not_mem_trace;
      intro _ _ M _ _ hM hn;
      exact forces_TBB_iff.mp (forces_conj.mp hM _ (Finset.mem_image_of_mem _
        (hfin.mem_toFinset.mpr hn))) rfl;

@[simp] theorem trace_eq : (𝐆𝐋α X : Logic α).trace = X := by
  rw [GL.trace_sumQuasiNormal];
  simp [trace];

lemma mono (h : X ⊆ Y) : (𝐆𝐋α X : Logic α) ⊆ 𝐆𝐋α Y :=
  sumQuasiNormal.subset_iff.mpr fun _ ⟨n, hn, e⟩ ↦ .mem₂ ⟨n, h hn, e⟩

lemma subset_S : (𝐆𝐋α X : Logic α) ⊆ 𝐒 :=
  sumQuasiNormal.subset_iff.mpr fun _ ⟨n, _, e⟩ ↦ e ▸ .mem₂ ⟨□^[n]⊥, by simp [TBB]⟩

end GLAlpha

namespace GLBetaMinus

variable {X : Set ℕ} {hX : Xᶜ.Finite}

@[simp] theorem trace_eq : (𝐆𝐋β⁻ X hX : Logic α).trace = X := by
  rw [GL.trace_sumQuasiNormal];
  simp [trace];

theorem mem_iff : A ∈ (𝐆𝐋β⁻ X hX : Logic α) ↔ A.trace ⊆ X := by
  constructor;
  · exact fun h ↦ trace_eq (hX := hX) ▸ trace_subset_of_mem h;
  · intro h;
    have : 𝐆𝐋 ⊢ (LetterlessFormula.betaMinus X hX).lift 🡒 A :=
      Formula.GL_imp_of_height_not_mem_trace fun M _ _ hM hn ↦ by
        have : rank (M := M.toModel) M.root ∉ X := by
          simpa using LetterlessFormula.forces_lift_iff.mp hM;
        exact this (h hn);
    exact sumQuasiNormal.mdp (.mem₁ this) (.mem₂ rfl);

/-- - [AB05, Lemma 49] -/
lemma bot_mem_univ {hX : (Set.univ : Set ℕ)ᶜ.Finite} : (⊥ : Formula α) ∈ 𝐆𝐋β⁻ Set.univ hX :=
  mem_iff.mpr (Set.subset_univ _)

end GLBetaMinus

namespace GLAlpha

variable {X : Set ℕ} (hX : Xᶜ.Finite)

lemma subset_GLBetaMinus : (𝐆𝐋α X : Logic α) ⊆ 𝐆𝐋β⁻ X hX :=
  fun _ h ↦ GLBetaMinus.mem_iff.mpr (mem_iff.mp h).2

theorem eq_inter_GLBetaMinus : (𝐆𝐋α X : Logic α) = 𝐆𝐋α Set.univ ∩ 𝐆𝐋β⁻ X hX := by
  ext A;
  simp [mem_iff, GLBetaMinus.mem_iff];

end GLAlpha

/-- - [AB05, Lemma 45] -/
theorem subset_GLAlpha_trace (hL : L.traceᶜ.Infinite) : L ⊆ 𝐆𝐋α L.trace := by
  intro A hA;
  have h := trace_subset_of_mem hA;
  exact GLAlpha.mem_iff.mpr ⟨A.trace_finite_or_compl_finite.resolve_right fun hA ↦
    hL (hA.subset (Set.compl_subset_compl.mpr h)), h⟩;

/-- - [AB05, Lemma 45] -/
theorem subset_GLBetaMinus_trace (hL : L.traceᶜ.Finite) : L ⊆ 𝐆𝐋β⁻ L.trace hL :=
  fun _ hA ↦ GLBetaMinus.mem_iff.mpr (trace_subset_of_mem hA)

end Logic

end FFL.ProvabilityLogic

end
