module

public import Foundation.ProvabilityLogic.A.Basic
public import Foundation.ProvabilityLogic.GLBeta.Basic
public import Foundation.ProvabilityLogic.Kripke.Graft
public import Foundation.ProvabilityLogic.S.Arithmetic

/-!
# Traces of formulas and logics

The trace of a formula is the set of heights of finite rooted `GL` models whose root refutes it,
and the trace of a logic is the union of the traces of its members. On letterless formulas it
agrees with `LetterlessFormula.trace`. A logic is bounded above by `GLα` or `GLβ` of its trace,
according as the complement of its trace is infinite or finite.

The provability logic of `T` relative to `U` contains `alpha n` for every `n` in its trace. Hence it
is `GLα` of its trace when the complement of its trace is infinite, and `GLβ` of its trace when
it is not contained in `S`.

## References

- [AB05]
- [Bek90]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World

universe u

lemma Kripke.Model.forces_alpha_iff {κ α : Type*} [Nonempty κ] {M : Model κ α} [Fintype M.World]
    [M.IsGL] {x : M.World} {n : ℕ} : x ⊩ alpha n ↔ x.rank ≠ n := by
  grind [alpha, forces_boxItr_bot_iff];

namespace Formula

variable {α : Type u} {A B : Formula α} {n : ℕ}

/-- The trace of `A`: the heights of the finite rooted `GL` models whose root does not force `A`.

- [AB05]
-/
def trace (A : Formula α) : Set ℕ :=
  {n | ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : Fintype M.World) (_ : M.IsGL),
    M.height = n ∧ M.root ⊮ A}

lemma GL_imp_of_height_not_mem_trace
    (h : ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsGL],
      M.root ⊩ B → M.height ∉ A.trace) : 𝐆𝐋 ⊢ B 🡒 A := by
  apply Logic.GL.iff_root_forces.mpr;
  intro _ _ M _ hB;
  have : Fintype M.World := Fintype.ofFinite _;
  by_contra hA;
  exact h M hB ⟨_, _, M, _, _, rfl, hA⟩;

@[simp] lemma trace_lift (B : LetterlessFormula) : (↑B : Formula α).trace = B.trace := by
  ext n;
  constructor;
  · rintro ⟨κ, _, M, _, _, rfl, h⟩ hB;
    exact h (LetterlessFormula.forces_lift_iff.mpr hB);
  · intro hn;
    by_contra hn';
    have h : LetterlessFormula.lift (α := α) (∼alpha n 🡒 B) ∈ 𝐆𝐋 :=
      GL_imp_of_height_not_mem_trace fun M _ _ hM ↦ by
        simp_all [LetterlessFormula.forces_lift_iff, RootedModel.height];
    exact hn <| by simpa using Set.eq_univ_iff_forall.mp (Logic.GL.lift_mem_iff.mp h) n;

@[simp] lemma trace_top : (⊤ : Formula α).trace = ∅ := by
  simp [trace];

@[simp] lemma trace_bot : (⊥ : Formula α).trace = Set.univ := by
  simpa [LetterlessFormula.trace] using trace_lift ⊥;

@[simp] lemma trace_alpha : (alpha n : Formula α).trace = {n} := by
  simpa using trace_lift (alpha n);

@[simp] lemma trace_beta {X : Set ℕ} {hX : Xᶜ.Finite} : (beta X hX : Formula α).trace = X := by
  simpa using trace_lift (beta X hX);

@[simp] lemma trace_and : (A ⋏ B).trace = A.trace ∪ B.trace := by
  ext n;
  grind [trace];

@[simp] lemma trace_conj [DecidableEq α] {Γ : FormulaFinset α} :
    Γ.conj.trace = ⋃ B ∈ Γ, B.trace := by
  ext n;
  grind [trace, forces_conj, Set.mem_iUnion];

lemma trace_subst_subset {s : Substitution α α} : (A⟦s⟧).trace ⊆ A.trace := by
  rintro n ⟨κ, _, M, _, _, rfl, h⟩;
  exact ⟨κ, _, { M.toModel.subst s with root := M.root, root_rel := M.root_rel }, _,
    inferInstance, rfl, fun h' ↦ h (forces_subst.mp h')⟩;

/-- - [AB05, Lemma 12] -/
theorem trace_finite_or_compl_finite (A : Formula α) : A.trace.Finite ∨ A.traceᶜ.Finite := by
  classical
  apply or_iff_not_imp_left.mpr;
  intro hinf;
  obtain ⟨_, ⟨κ, _, M, _, _, rfl, hA⟩, hm⟩ := Set.Infinite.exists_gt hinf A.subfmls.prebox.card;
  obtain ⟨u, Rru, hu⟩ := exists_isReflexiveOf_of_card_lt_rank hm;
  have hne : u ≠ M.root := fun h ↦ Std.Irrefl.irrefl _ (h ▸ Rru);
  have := RootedModel.rank_lt_height Rru;
  apply (Set.finite_Iio M.height).subset;
  intro n hn;
  by_contra! hle;
  exact hn ⟨_, _, M.graft ⟨u, hne⟩ (Fin (n - u.rank - 1)), inferInstance, inferInstance,
    by grind [RootedModel.graft.height_eq],
    fun h ↦ hA <| ((RootedModel.graft.forces_iff (fun _ ↦ subfmls_trans)
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
      by_cases hC : M.root ⊩ C;
      · exact Set.biUnion_subset_biUnion_left (by simp) <|
          h₁ ⟨κ, _, M, _, _, rfl, fun h ↦ hB (h hC)⟩;
      · exact Set.biUnion_subset_biUnion_left (by simp) <| h₂ ⟨κ, _, M, _, _, rfl, hC⟩;
  | subst _ ih =>
    obtain ⟨Y, hY, h⟩ := ih;
    exact ⟨Y, hY, trace_subst_subset.trans h⟩;

lemma trace_sumQuasiNormal (X : Logic α) : (𝐆𝐋 +ᴸ X).trace = X.trace := by
  apply subset_antisymm;
  · apply Set.iUnion₂_subset;
    intro A hA;
    obtain ⟨Y, hY, h⟩ := exists_finset_trace_subset_of_mem_sumQuasiNormal hA;
    exact h.trans (Set.biUnion_subset_biUnion_left hY);
  · exact Set.biUnion_subset_biUnion_left sumQuasiNormal.subset_right;

end GL

namespace GLAlpha

variable {X Y : Set ℕ}

theorem mem_iff : A ∈ 𝐆𝐋α X ↔ A.trace.Finite ∧ A.trace ⊆ X := by
  classical
  constructor;
  · intro h;
    obtain ⟨Y, hY, hA⟩ := GL.exists_finset_trace_subset_of_mem_sumQuasiNormal h;
    have h' : ∀ B ∈ Y, B.trace.Finite ∧ B.trace ⊆ X := fun B hB ↦ by
      obtain ⟨n, hn, rfl⟩ := hY hB;
      simpa;
    exact ⟨(Y.finite_toSet.biUnion fun B hB ↦ (h' B hB).1).subset hA,
      hA.trans <| Set.iUnion₂_subset fun B hB ↦ (h' B hB).2⟩;
  · rintro ⟨hfin, hX⟩;
    apply GL.sumQuasiNormal_of_conj (Γ := hfin.toFinset.image alpha);
    · exact Finset.forall_mem_image.mpr fun n hn ↦ .mem₂ ⟨n, hX (hfin.mem_toFinset.mp hn), rfl⟩;
    · exact Formula.GL_imp_of_height_not_mem_trace fun _ _ _ hM hn ↦ forces_alpha_iff.mp
        (forces_conj.mp hM _ <| Finset.mem_image_of_mem _ <| hfin.mem_toFinset.mpr hn) rfl;

@[simp] lemma trace_eq : (𝐆𝐋α X : Logic α).trace = X :=
  (GL.trace_sumQuasiNormal _).trans <| by simp [trace]

lemma mono (h : X ⊆ Y) : (𝐆𝐋α X : Logic α) ⪯ 𝐆𝐋α Y :=
  weakerThan_iff.mpr <| sumQuasiNormal.subset_iff.mpr fun _ ⟨n, hn, e⟩ ↦ .mem₂ ⟨n, h hn, e⟩

instance : (𝐆𝐋α X : Logic α) ⪯ 𝐒 :=
  weakerThan_iff.mpr <| sumQuasiNormal.subset_iff.mpr fun _ ⟨n, _, e⟩ ↦
    e ▸ .mem₂ ⟨□^[n]⊥, by simp [alpha]⟩

instance : Consistent (𝐆𝐋α X : Logic α) := .of_le (𝓢 := 𝐒) inferInstance inferInstance

end GLAlpha

namespace GLBeta

variable {X : Set ℕ} {hX : Xᶜ.Finite}

@[simp] lemma trace_eq : (𝐆𝐋β X hX : Logic α).trace = X :=
  (GL.trace_sumQuasiNormal _).trans <| by simp [trace]

theorem mem_iff : A ∈ 𝐆𝐋β X hX ↔ A.trace ⊆ X := by
  constructor;
  · exact fun h ↦ (trace_subset_of_mem h).trans_eq trace_eq;
  · intro h;
    have : 𝐆𝐋 ⊢ beta X hX 🡒 A :=
      Formula.GL_imp_of_height_not_mem_trace fun _ _ _ hM hn ↦ absurd (h hn) <| by
        simpa [RootedModel.height] using
          LetterlessFormula.forces_lift_iff (A := beta X hX) |>.mp (by simpa using hM);
    exact sumQuasiNormal.mdp (.mem₁ this) (.mem₂ rfl);

/-- - [AB05, Lemma 49] -/
theorem bot_mem_univ : (⊥ : Formula α) ∈ 𝐆𝐋β Set.univ (by simp) :=
  mem_iff.mpr (Set.subset_univ _)

end GLBeta

namespace GLAlpha

variable {X : Set ℕ} (hX : Xᶜ.Finite)

instance : (𝐆𝐋α X : Logic α) ⪯ 𝐆𝐋β X hX :=
  ⟨fun _ h ↦ GLBeta.mem_iff.mpr (mem_iff.mp h).2⟩

lemma eq_inter_GLBeta : (𝐆𝐋α X : Logic α) = 𝐆𝐋α Set.univ ∩ 𝐆𝐋β X hX := by
  ext A;
  simp [mem_iff, GLBeta.mem_iff];

end GLAlpha

/-- - [AB05, Lemma 45] -/
theorem weakerThan_GLAlpha_trace (hL : L.traceᶜ.Infinite) : L ⪯ 𝐆𝐋α L.trace := by
  apply weakerThan_iff.mpr;
  intro A hA;
  have h := trace_subset_of_mem hA;
  exact GLAlpha.mem_iff.mpr ⟨A.trace_finite_or_compl_finite.resolve_right fun hA ↦
    hL <| hA.subset <| Set.compl_subset_compl.mpr h, h⟩;

/-- - [AB05, Lemma 45] -/
theorem weakerThan_GLBeta_trace (hL : L.traceᶜ.Finite) : L ⪯ 𝐆𝐋β L.trace hL :=
  ⟨fun _ hA ↦ GLBeta.mem_iff.mpr (trace_subset_of_mem hA)⟩

end Logic

section

open FirstOrder FirstOrder.ProvabilityAbstraction RootedModel LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁]

/-! ### Closure properties -/

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] {A : Formula α} {X : Logic α}

lemma provabilityLogic_of_GL (h : 𝐆𝐋 ⊢ A) : A ∈ T.provabilityLogicRelativeTo U :=
  fun _ ↦ WeakerThan.pbl (Logic.GL.arithmetical_soundness h)

lemma sumQuasiNormal_weakerThan_provabilityLogic (h : X ⊆ T.provabilityLogicRelativeTo U) :
    (𝐆𝐋 +ᴸ X) ⪯ T.provabilityLogicRelativeTo U := by
  apply Logic.weakerThan_iff.mpr;
  intro A hA;
  induction hA with
  | mem₁ hA => exact provabilityLogic_of_GL hA;
  | mem₂ hA => exact h hA;
  | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
  | subst _ ih => exact provabilityLogic_subst ih;

lemma provabilityLogic_conj [DecidableEq α] {Γ : FormulaFinset α}
    (h : ∀ B ∈ Γ, B ∈ T.provabilityLogicRelativeTo U) : Γ.conj ∈ T.provabilityLogicRelativeTo U :=
  (sumQuasiNormal_weakerThan_provabilityLogic h).wk <|
    (FConj_iff_forall_provable (𝓢 := 𝐆𝐋 +ᴸ (Γ : Logic α))).mpr fun _ ↦ .mem₂

end

lemma LetterlessFormula.lift_mem_provabilityLogic {A : LetterlessFormula} (f : Realization α ℒₒᵣ)
    (h : U ⊢ f T ↑A) : ↑A ∈ T.provabilityLogicRelativeTo U (α := α) :=
  fun g ↦ by simpa only [standardInterpret, interpret_lift] using h

/-! ### Realizations from Solovay sentences -/

section

variable [𝗜𝚺₁ ⪯ T] {A : Formula α}

/-- - [AB05, Lemma 46] -/
lemma exists_realization_provable_imp_alpha {κ : Type*} [Nonempty κ] (M : RootedModel κ α)
    [Fintype M.World] [M.IsGL] (hA : M.root ⊮ A) :
    ∃ f : Realization α ℒₒᵣ, 𝗜𝚺₁ ⊢ f T (A 🡒 alpha M.height) := by
  let S := standardSolovaySentences T M.extendRoot;
  use S.realization;
  have h : ∀ i, 𝗜𝚺₁ ⊢ S.σ i 🡒 S.realization T (A 🡒 alpha M.height) := by
    rintro (_ | x);
    · have h₁ : 𝗜𝚺₁ ⊢ S.σ (some M.root) 🡒 ∼S.realization T (□^[M.height]⊥) :=
        S.mainlemma_neg (Option.some_ne_none _).symm <|
          extendRoot.forces_some.not.mpr <| by simp [root_forces_boxItr_bot_iff];
      have h₂ := contra <| T.standardProvability.mono' <| CN_of_CN_right h₁;
      simp only [standardInterpret, interpret, alpha, interpret_boxItr,
        Function.iterate_succ_apply'] at h₂ ⊢;
      cl_prover [S.SC2 none (some M.root) trivial, h₂];
    · apply S.mainlemma (Option.some_ne_none x).symm;
      apply extendRoot.forces_some.mpr;
      by_cases hx : x = M.root;
      · exact hx ▸ fun h ↦ absurd h hA;
      · exact fun _ ↦ forces_alpha_iff.mpr (rank_lt_height (M.root_rel x hx)).ne;
  cl_prover [left_Udisj_intro _ h, S.SC4];

/-- - [AB05, Lemma 49] -/
lemma exists_realization_provable_neg_of_not_S (hA : 𝐒 ⊬ A) :
    ∃ n, ∃ f : Realization α ℒₒᵣ,
      𝗜𝚺₁ ⊢ ∼f T (A ⋏ lift (⩕ i ∈ Finset.range n, alpha i)) := by
  classical
  obtain ⟨κ, _, M, _, h₁, h₂⟩ := Logic.S.exists_countermodel hA;
  have : Fintype M.World := Fintype.ofFinite _;
  let S := standardSolovaySentences T M.extendRoot;
  use M.height, S.realization;
  have h : ∀ i, 𝗜𝚺₁ ⊢ S.σ i 🡒
      ∼S.realization T (A ⋏ lift (⩕ i ∈ Finset.range M.height, alpha i)) := by
    rintro (_ | x);
    · have := (S.rfl_mainlemma h₂ mem_subfmls_self).2 h₁;
      simp only [standardInterpret, interpret] at this ⊢;
      cl_prover [this];
    · apply S.mainlemma_neg (Option.some_ne_none x).symm;
      apply extendRoot.forces_some.not.mpr;
      by_cases hx : x = M.root;
      · exact hx ▸ fun h ↦ h₁ (forces_and.mp h).1;
      · by_contra h;
        have h₃ : ∀ i < M.height, rank (M := M.toModel) x ≠ i := by
          simpa using forces_lift_iff.mp (forces_and.mp h).2;
        exact h₃ _ (rank_lt_height (M.root_rel x hx)) rfl;
  cl_prover [left_Udisj_intro _ h, S.SC4];

end

/-! ### Traces of provability logics -/

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] {n : ℕ}

/-- - [AB05, Lemma 46, Corollary 47] -/
theorem alpha_mem_provabilityLogic_of_mem_trace
    (h : n ∈ (T.provabilityLogicRelativeTo U (α := α)).trace) :
    alpha n ∈ T.provabilityLogicRelativeTo U (α := α) := by
  obtain ⟨A, hA, κ, _, M, _, _, rfl, hM⟩ := Set.mem_iUnion₂.mp h;
  obtain ⟨f, hf⟩ := exists_realization_provable_imp_alpha (T := T) M hM;
  simpa using lift_mem_provabilityLogic (A := alpha M.height) f
    (by simpa using WeakerThan.pbl hf ⨀ hA f);

/-- - [AB05, Corollary 47] -/
theorem mem_trace_provabilityLogic_iff :
    n ∈ (T.provabilityLogicRelativeTo U (α := α)).trace ↔
      alpha n ∈ T.provabilityLogicRelativeTo U (α := α) :=
  ⟨alpha_mem_provabilityLogic_of_mem_trace, fun h ↦ Logic.trace_subset_of_mem h (by simp)⟩

/-- - [AB05, Corollary 48] -/
theorem provabilityLogic_eq_GLAlpha
    (h : (T.provabilityLogicRelativeTo U (α := α)).traceᶜ.Infinite) :
    T.provabilityLogicRelativeTo U (α := α) =
      𝐆𝐋α (T.provabilityLogicRelativeTo U (α := α)).trace :=
  Logic.weakerThan_antisymm (Logic.weakerThan_GLAlpha_trace h) <|
    sumQuasiNormal_weakerThan_provabilityLogic <| by
    rintro _ ⟨n, hn, rfl⟩;
    exact alpha_mem_provabilityLogic_of_mem_trace hn

lemma exists_neg_conj_alpha_mem_provabilityLogic
    (h : ¬T.provabilityLogicRelativeTo U (α := α) ⪯ 𝐒) :
    ∃ m, lift (∼⩕ i ∈ Finset.range m, alpha i) ∈
      T.provabilityLogicRelativeTo U (α := α) := by
  obtain ⟨A, hA, hAS⟩ := not_weakerThan_iff.mp h;
  obtain ⟨m, f, hf⟩ := exists_realization_provable_neg_of_not_S (T := T) hAS;
  use m;
  apply lift_mem_provabilityLogic f;
  have h₁ : U ⊢ ∼f T (A ⋏ lift (⩕ i ∈ Finset.range m, alpha i)) := WeakerThan.pbl hf;
  have h₂ := hA f;
  simp only [standardInterpret, interpret] at h₁ h₂ ⊢;
  cl_prover [h₁, h₂];

/-- - [AB05, Lemma 49] -/
theorem provabilityLogic_trace_compl_finite
    (h : ¬T.provabilityLogicRelativeTo U (α := α) ⪯ 𝐒) :
    (T.provabilityLogicRelativeTo U (α := α)).traceᶜ.Finite := by
  obtain ⟨m, hm⟩ := exists_neg_conj_alpha_mem_provabilityLogic h;
  exact (Set.finite_Iio m).subset fun n hn ↦
    not_le.mp fun hnm ↦ hn <| Logic.trace_subset_of_mem hm <| by simpa using hnm;

/-- - [AB05, Lemma 49] -/
theorem provabilityLogic_eq_GLBeta (h : ¬T.provabilityLogicRelativeTo U (α := α) ⪯ 𝐒) :
    T.provabilityLogicRelativeTo U (α := α) =
      𝐆𝐋β (T.provabilityLogicRelativeTo U).trace
        (provabilityLogic_trace_compl_finite h) := by
  classical
  suffices beta _ (provabilityLogic_trace_compl_finite h) ∈
      T.provabilityLogicRelativeTo U (α := α) from
    Logic.weakerThan_antisymm (Logic.weakerThan_GLBeta_trace _) <|
      sumQuasiNormal_weakerThan_provabilityLogic <| Set.singleton_subset_iff.mpr this;
  obtain ⟨m, hm⟩ := exists_neg_conj_alpha_mem_provabilityLogic h;
  apply provabilityLogic_mdp (A := Finset.conj <| insert (lift (∼⩕ i ∈ Finset.range m, alpha i)) <|
    ((Finset.range m).filter (· ∈ (T.provabilityLogicRelativeTo U).trace)).image alpha);
  · apply provabilityLogic_of_GL;
    apply GL_imp_of_height_not_mem_trace;
    intro κ _ M _ _ hM hn;
    have h₁ : M.height < m := by
      simpa [height] using forces_lift_iff.mp (forces_conj.mp hM _ (Finset.mem_insert_self _ _));
    exact forces_alpha_iff.mp (forces_conj.mp hM (alpha M.height) <| Finset.mem_insert_of_mem <|
      Finset.mem_image_of_mem _ <| Finset.mem_filter.mpr ⟨by simpa, by simpa using hn⟩) rfl;
  · exact provabilityLogic_conj <| Finset.forall_mem_insert _ _ _ |>.mpr ⟨hm,
      Finset.forall_mem_image.mpr fun _ hi ↦
        alpha_mem_provabilityLogic_of_mem_trace (Finset.mem_filter.mp hi).2⟩;

/-- - [AB05, Corollary 50] -/
theorem A_weakerThan_provabilityLogic
    (h : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ) :
    𝐀 ⪯ T.provabilityLogicRelativeTo U (α := α) :=
  sumQuasiNormal_weakerThan_provabilityLogic <| by
    rintro _ ⟨n, -, rfl⟩;
    exact alpha_mem_provabilityLogic_of_mem_trace (h ▸ Set.mem_univ n)

end

end

end FFL.ProvabilityLogic

end
