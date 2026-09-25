module

public import Foundation.ProvabilityLogic.A.Basic
public import Foundation.ProvabilityLogic.S.Arithmetic
public import Foundation.ProvabilityLogic.Trace

/-!
# Traces of provability logics

The provability logic of `T` relative to `U` contains `TBB n` for every `n` in its trace. Hence it
is `GLα` of its trace when the complement of its trace is infinite, and `GLβ⁻` of its trace when
it is not contained in `S`.

## References

- [AB05]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction Kripke Kripke.Model Kripke.Model.World
open Kripke.RootedModel Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁]

/-! ### Closure properties -/

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] {A : Formula α} {X : Logic α}

lemma provabilityLogic_of_GL (h : 𝐆𝐋 ⊢ A) : A ∈ T.provabilityLogicRelativeTo U :=
  fun _ ↦ WeakerThan.pbl (Logic.GL.arithmetical_soundness h)

lemma sumQuasiNormal_subset_provabilityLogic (h : X ⊆ T.provabilityLogicRelativeTo U) :
    (𝐆𝐋 +ᴸ X) ⊆ T.provabilityLogicRelativeTo U := by
  intro A hA;
  induction hA with
  | mem₁ hA => exact provabilityLogic_of_GL hA;
  | mem₂ hA => exact h hA;
  | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
  | subst _ ih => exact provabilityLogic_subst ih;

lemma provabilityLogic_conj [DecidableEq α] {Γ : FormulaFinset α}
    (h : ∀ B ∈ Γ, B ∈ T.provabilityLogicRelativeTo U) : Γ.conj ∈ T.provabilityLogicRelativeTo U :=
  sumQuasiNormal_subset_provabilityLogic h <|
    (FConj_iff_forall_provable (𝓢 := 𝐆𝐋 +ᴸ (Γ : Logic α))).mpr fun _ ↦ .mem₂

end

lemma LetterlessFormula.lift_mem_provabilityLogic {A : LetterlessFormula} (f : Realization α ℒₒᵣ)
    (h : U ⊢ f T A.lift) : A.lift ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun g ↦ by simpa only [standardInterpret, interpret_lift] using h

/-! ### Realizations from Solovay sentences -/

section

variable [𝗜𝚺₁ ⪯ T] {A : Formula α}

/-- - [AB05, Lemma 46] -/
lemma exists_realization_provable_imp_TBB {κ : Type*} [Nonempty κ] (M : RootedModel κ α)
    [Fintype M.World] [M.IsGL] (hA : M.root ⊮[M.toModel] A) :
    ∃ f : Realization α ℒₒᵣ, 𝗜𝚺₁ ⊢ f T (A 🡒 TBB M.height) := by
  let S := standardSolovaySentences T M.extendRoot;
  use S.realization;
  have h : ∀ i, 𝗜𝚺₁ ⊢ S.σ i 🡒 S.realization T (A 🡒 TBB M.height) := by
    rintro (_ | x);
    · have h₁ : 𝗜𝚺₁ ⊢ S.σ (some M.root) 🡒 ∼S.realization T (□^[M.height]⊥) :=
        S.mainlemma_neg (Option.some_ne_none _).symm <|
          extendRoot.forces_some.not.mpr <| by simp [root_forces_boxItr_bot_iff];
      have h₂ := contra <| T.standardProvability.mono' <| CN_of_CN_right h₁;
      simp only [standardInterpret, interpret, TBB, interpret_boxItr,
        Function.iterate_succ_apply'] at h₂ ⊢;
      cl_prover [S.SC2 none (some M.root) trivial, h₂];
    · apply S.mainlemma (Option.some_ne_none x).symm;
      apply extendRoot.forces_some.mpr;
      by_cases hx : x = M.root;
      · exact hx ▸ fun h ↦ absurd h hA;
      · exact fun _ ↦ forces_TBB_iff.mpr (rank_lt_height (M.root_rel x hx)).ne;
  cl_prover [left_Udisj_intro _ h, S.SC4];

/-- - [AB05, Lemma 49] -/
lemma exists_realization_provable_neg_of_not_S (hA : 𝐒 ⊬ A) :
    ∃ n, ∃ f : Realization α ℒₒᵣ,
      𝗜𝚺₁ ⊢ ∼f T (A ⋏ lift (⩕ i ∈ Finset.range n, TBB i)) := by
  classical
  obtain ⟨κ, _, M, _, h₁, h₂⟩ := Logic.S.exists_countermodel hA;
  have : Fintype M.World := Fintype.ofFinite _;
  let S := standardSolovaySentences T M.extendRoot;
  use M.height, S.realization;
  have h : ∀ i, 𝗜𝚺₁ ⊢ S.σ i 🡒
      ∼S.realization T (A ⋏ lift (⩕ i ∈ Finset.range M.height, TBB i)) := by
    rintro (_ | x);
    · have := (S.rfl_mainlemma h₂ mem_subfmls_self).2 h₁;
      simp only [standardInterpret, interpret] at this ⊢;
      cl_prover [this];
    · apply S.mainlemma_neg (Option.some_ne_none x).symm;
      apply extendRoot.forces_some.not.mpr;
      by_cases hx : x = M.root;
      · exact hx ▸ fun h ↦ h₁ (forces_and.mp h).1;
      · intro h;
        have h₃ : ∀ i < M.height, rank (M := M.toModel) x ≠ i := by
          simpa using forces_lift_iff.mp (forces_and.mp h).2;
        exact h₃ _ (rank_lt_height (M.root_rel x hx)) rfl;
  cl_prover [left_Udisj_intro _ h, S.SC4];

end

/-! ### Traces of provability logics -/

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] {n : ℕ}

/-- - [AB05, Lemma 46, Corollary 47] -/
theorem TBB_mem_provabilityLogic_of_mem_trace
    (h : n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace) :
    TBB n ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  obtain ⟨A, hA, κ, _, M, _, _, rfl, hM⟩ := Set.mem_iUnion₂.mp h;
  obtain ⟨f, hf⟩ := exists_realization_provable_imp_TBB (T := T) M hM;
  simpa using lift_mem_provabilityLogic (A := TBB M.height) f
    (by simpa using WeakerThan.pbl hf ⨀ hA f);

/-- - [AB05, Corollary 47] -/
theorem mem_trace_provabilityLogic_iff :
    n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace ↔
      TBB n ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  ⟨TBB_mem_provabilityLogic_of_mem_trace, fun h ↦ Logic.trace_subset_of_mem h (by simp)⟩

/-- - [AB05, Corollary 48] -/
theorem provabilityLogic_eq_GLAlpha
    (h : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Infinite) :
    (T.provabilityLogicRelativeTo U : Logic α) =
      𝐆𝐋α (T.provabilityLogicRelativeTo U : Logic α).trace :=
  subset_antisymm (Logic.subset_GLAlpha_trace h) <| sumQuasiNormal_subset_provabilityLogic <| by
    rintro _ ⟨n, hn, rfl⟩;
    exact TBB_mem_provabilityLogic_of_mem_trace hn

lemma exists_neg_conj_TBB_mem_provabilityLogic
    (h : ¬T.provabilityLogicRelativeTo U ⊆ 𝐒@α) :
    ∃ m, lift (∼⩕ i ∈ Finset.range m, TBB i) ∈
      (T.provabilityLogicRelativeTo U : Logic α) := by
  obtain ⟨A, hA, hAS⟩ := Set.not_subset.mp h;
  obtain ⟨m, f, hf⟩ := exists_realization_provable_neg_of_not_S (T := T) hAS;
  use m;
  apply lift_mem_provabilityLogic f;
  have h₁ : U ⊢ ∼f T (A ⋏ lift (⩕ i ∈ Finset.range m, TBB i)) := WeakerThan.pbl hf;
  have h₂ := hA f;
  simp only [standardInterpret, interpret] at h₁ h₂ ⊢;
  cl_prover [h₁, h₂];

/-- - [AB05, Lemma 49] -/
theorem provabilityLogic_trace_compl_finite
    (h : ¬T.provabilityLogicRelativeTo U ⊆ 𝐒@α) :
    (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite := by
  obtain ⟨m, hm⟩ := exists_neg_conj_TBB_mem_provabilityLogic h;
  exact (Set.finite_Iio m).subset fun n hn ↦
    not_le.mp fun hnm ↦ hn <| Logic.trace_subset_of_mem hm <| by simpa using hnm;

/-- - [AB05, Lemma 49] -/
theorem betaMinus_mem_provabilityLogic (h : ¬T.provabilityLogicRelativeTo U ⊆ 𝐒@α) :
    (betaMinus _ (provabilityLogic_trace_compl_finite h)).lift ∈
      (T.provabilityLogicRelativeTo U : Logic α) := by
  classical
  obtain ⟨m, hm⟩ := exists_neg_conj_TBB_mem_provabilityLogic h;
  apply provabilityLogic_mdp (A := Finset.conj <| insert (lift (∼⩕ i ∈ Finset.range m, TBB i)) <|
    ((Finset.range m).filter (· ∈ (T.provabilityLogicRelativeTo U).trace)).image TBB);
  · apply provabilityLogic_of_GL;
    apply GL_imp_of_height_not_mem_trace;
    intro κ _ M _ _ hM hn;
    have h₁ : M.height < m := by
      simpa [height] using forces_lift_iff.mp (forces_conj.mp hM _ (Finset.mem_insert_self _ _));
    exact forces_TBB_iff.mp (forces_conj.mp hM (TBB M.height) <| Finset.mem_insert_of_mem <|
      Finset.mem_image_of_mem _ <| Finset.mem_filter.mpr ⟨by simpa, by simpa using hn⟩) rfl;
  · exact provabilityLogic_conj <| Finset.forall_mem_insert _ _ _ |>.mpr ⟨hm,
      Finset.forall_mem_image.mpr fun _ hi ↦
        TBB_mem_provabilityLogic_of_mem_trace (Finset.mem_filter.mp hi).2⟩;

/-- - [AB05, Lemma 49] -/
theorem provabilityLogic_eq_GLBetaMinus (h : ¬T.provabilityLogicRelativeTo U ⊆ 𝐒@α) :
    (T.provabilityLogicRelativeTo U : Logic α) =
      𝐆𝐋β⁻ (T.provabilityLogicRelativeTo U : Logic α).trace
        (provabilityLogic_trace_compl_finite h) :=
  subset_antisymm (Logic.subset_GLBetaMinus_trace _) <| sumQuasiNormal_subset_provabilityLogic <|
    Set.singleton_subset_iff.mpr (betaMinus_mem_provabilityLogic h)

/-- - [AB05, Corollary 50] -/
theorem A_subset_provabilityLogic (h : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ) :
    𝐀@α ⊆ T.provabilityLogicRelativeTo U :=
  sumQuasiNormal_subset_provabilityLogic <| by
    rintro _ ⟨n, -, rfl⟩;
    exact TBB_mem_provabilityLogic_of_mem_trace (h ▸ Set.mem_univ n)

end

end FFL.ProvabilityLogic

end
