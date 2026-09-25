module

public import Foundation.ProvabilityLogic.Classification.UnivTrace

/-!
# Truth provability logics

The provability logic `PL(T, 𝗧𝗔)` of `T` relative to `𝗧𝗔` is `𝐒`, `𝐃`, `𝐀`, or `𝐆𝐋β⁻ {n}ᶜ`,
according to whether `T` is sound, `𝚺₁`-sound but not sound, not `𝚺₁`-sound and of characteristic
`ω`, or of characteristic `n`.

## References

- [AB05, Corollary 41]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction Formula

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁]

/-! ### Soundness and characteristic -/

lemma models_standardProvability_iff {σ : ArithmeticSentence} :
    ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ ↔ T ⊢ σ :=
  ⟨T.standardProvability.sound_on,
    fun h ↦ models_of_provable inferInstance (T.standardProvability.D1 h)⟩

lemma soundOnHierarchy_iff_models_reflection :
    T.SoundOnHierarchy 𝚺 1 ↔
      ∀ σ : ArithmeticSentence, Arithmetic.Hierarchy 𝚺 1 σ →
        ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ 🡒 σ :=
  ⟨fun _ _ hσ ↦ Semantics.Imp.models_imply.mpr fun h ↦
      T.soundOnHierarchy 𝚺 1 (models_standardProvability_iff.mp h) hσ,
    fun h ↦ ⟨fun hσ hσ' ↦
      Semantics.Imp.models_imply.mp (h _ hσ') (models_standardProvability_iff.mpr hσ)⟩⟩

variable [𝗜𝚺₁ ⪯ T] {n : ℕ}

lemma models_boxBot_iff : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability^[n + 1] ⊥ ↔ T.height ≤ n := by
  simpa [Function.iterate_succ_apply', models_standardProvability_iff] using
    Provability.height_le_iff_boxBot.symm

lemma models_TBB_iff (f : Realization α ℒₒᵣ) : ℕ↓[ℒₒᵣ] ⊧ f T (TBB n) ↔ T.height ≠ n := by
  suffices T.height ≤ n → ℕ↓[ℒₒᵣ] ⊧ T.standardProvability^[n] ⊥ ↔ T.height ≠ n by
    simpa only [TBB, standardInterpret, interpret, interpret_boxItr, Semantics.Imp.models_imply,
      models_boxBot_iff];
  rcases n with _ | n;
  · simp;
  · suffices T.height ≤ ↑(n + 1) → T.height ≤ n ↔ T.height ≠ ↑(n + 1) by
      simpa only [models_boxBot_iff];
    cases T.height using ENat.recTopCoe with
    | top => simpa using ENat.top_ne_natCast (n + 1);
    | coe m => norm_cast; omega;

/-! ### Truth provability logics -/

lemma TBB_mem_provabilityLogic_TA_iff :
    TBB n ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ↔ T.height ≠ n :=
  ⟨fun h ↦ (models_TBB_iff ⟨fun _ ↦ ⊥⟩).mp <| Arithmetic.TA.provable_iff.mp <| h _,
    fun h f ↦ Arithmetic.TA.provable_iff.mpr <| (models_TBB_iff f).mpr h⟩

lemma mem_trace_provabilityLogic_TA_iff :
    n ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace ↔ T.height ≠ n :=
  mem_trace_provabilityLogic_iff.trans TBB_mem_provabilityLogic_TA_iff

lemma trace_provabilityLogic_TA_eq_univ_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = .univ ↔ T.height = ⊤ := by
  simp [Set.eq_univ_iff_forall, mem_trace_provabilityLogic_TA_iff, ENat.eq_top_iff_forall_ne,
    ne_comm]

lemma trace_provabilityLogic_TA_eq_compl_singleton_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = {n}ᶜ ↔ T.height = n := by
  suffices (∀ m : ℕ, T.height ≠ m ↔ m ≠ n) ↔ T.height = n by
    simpa only [Set.ext_iff, mem_trace_provabilityLogic_TA_iff, Set.mem_compl_singleton_iff];
  exact ⟨fun h ↦ by simpa using h n, fun h m ↦ by simp [h, eq_comm]⟩

omit [𝗜𝚺₁ ⪯ T] in
lemma bot_notMem_provabilityLogic_TA : ⊥ ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) :=
  fun h ↦ by
    simpa [standardInterpret, interpret] using Arithmetic.TA.provable_iff.mp <| h ⟨fun _ ↦ ⊥⟩

lemma provabilityLogic_TA_subset_S (h : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = .univ) :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ 𝐒 := by
  by_contra hS;
  exact bot_notMem_provabilityLogic_TA <| (provabilityLogic_eq_GLBetaMinus hS).symm.subset <|
    Logic.GLBetaMinus.mem_iff.mpr <| by simp [h];

/-- - [AB05, Corollary 41(ii)] -/
theorem D_subset_provabilityLogic_TA [T.SoundOnHierarchy 𝚺 1] :
    𝐃 ⊆ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
  have h := soundOnHierarchy_iff_models_reflection.mp (inferInstance : T.SoundOnHierarchy 𝚺 1);
  apply sumQuasiNormal_subset_provabilityLogic;
  rintro _ (rfl | ⟨B, C, rfl⟩) f <;> apply Arithmetic.TA.provable_iff.mpr;
  · simpa [standardInterpret, interpret] using h ⊥ (by simp);
  · exact h _ <| by simp [interpret, Arithmetic.standardProvability_def];

/-- - [AB05, Corollary 41(ii)] -/
theorem soundOnHierarchy_of_axiomD_mem_provabilityLogic_TA {a : α}
    (hT : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = .univ)
    (h : □(□#a ⋎ □#a) 🡒 □#a ⋎ □#a ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α)) :
    T.SoundOnHierarchy 𝚺 1 :=
  soundOnHierarchy_iff_models_reflection.mpr fun _ hσ ↦ Arithmetic.TA.provable_iff.mp <|
    provable_sigma1_reflection_of_mem_of_not_A hT h Logic.A.not_axiomD hσ

/-- - [AB05, Corollary 41(iv)] -/
theorem provabilityLogic_TA_eq_GLBetaMinus_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐆𝐋β⁻ {n}ᶜ (by simp) ↔ T.height = n := by
  constructor;
  · exact fun h ↦ trace_provabilityLogic_TA_eq_compl_singleton_iff.mp <|
      h ▸ Logic.GLBetaMinus.trace_eq;
  · intro hn;
    have h : ∼TBB n ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := fun f ↦
      Arithmetic.TA.provable_iff.mpr <| by
        simp [standardInterpret, interpret, models_TBB_iff f, hn];
    have hS : ¬(T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ 𝐒 :=
      fun hS ↦ Logic.S.consistent <| hS h ⨀ Logic.S.provable_TBB;
    exact (provabilityLogic_eq_GLBetaMinus hS).trans <| by
      congr 1; exact trace_provabilityLogic_TA_eq_compl_singleton_iff.mpr hn;

variable [Nonempty α]

/-- - [AB05, Corollary 41(i)] -/
theorem provabilityLogic_TA_eq_S_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐒 ↔ ℕ↓[ℒₒᵣ] ⊧* T := by
  constructor;
  · intro h;
    obtain ⟨p⟩ := ‹Nonempty α›;
    apply Semantics.modelsSet_iff.mpr;
    intro φ hφ;
    have h₁ : □#p 🡒 #p ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := h ▸ Logic.S.axiomT;
    exact Semantics.Imp.models_imply.mp (Arithmetic.TA.provable_iff.mp (h₁ ⟨fun _ ↦ φ⟩)) <|
      models_standardProvability_iff.mpr <| by_axm hφ;
  · exact fun _ ↦ Logic.S.eq_provabilityLogicRelativeTo_TA.symm;

/-- - [AB05, Corollary 41(ii)] -/
theorem provabilityLogic_TA_eq_D_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐃 ↔
      T.SoundOnHierarchy 𝚺 1 ∧ ¬ℕ↓[ℒₒᵣ] ⊧* T := by
  inhabit α;
  constructor;
  · intro h;
    and_intros;
    · exact soundOnHierarchy_of_axiomD_mem_provabilityLogic_TA (a := default)
        (Set.eq_univ_of_forall fun _ ↦
          mem_trace_provabilityLogic_iff.mpr <| h ▸ Logic.D.provable_TBB)
        (h ▸ Logic.D.axiomD);
    · exact fun hs ↦ Logic.D.ssubset_S.ne <| h.symm.trans <| provabilityLogic_TA_eq_S_iff.mpr hs;
  · rintro ⟨_, hs⟩;
    have hT := trace_provabilityLogic_TA_eq_univ_iff (α := α).mpr <|
      Arithmetic.height_eq_top_of_sigma1_sound T;
    rcases provabilityLogic_eq_A_or_eq_D_or_eq_S hT (provabilityLogic_TA_subset_S hT)
      with h | h | h;
    · exact absurd (h ▸ D_subset_provabilityLogic_TA) Logic.A.ssubset_D.not_subset;
    · exact h;
    · exact absurd (provabilityLogic_TA_eq_S_iff.mp h) hs;

/-- - [AB05, Corollary 41(iii)] -/
theorem provabilityLogic_TA_eq_A_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐀 ↔
      ¬T.SoundOnHierarchy 𝚺 1 ∧ T.height = ⊤ := by
  inhabit α;
  constructor;
  · intro h;
    and_intros;
    · exact fun _ ↦ Logic.A.ssubset_D.not_subset <| h ▸ D_subset_provabilityLogic_TA;
    · exact ENat.eq_top_iff_forall_ne.mpr fun _ ↦
        (TBB_mem_provabilityLogic_TA_iff.mp <| h ▸ Logic.A.provable_TBB).symm;
  · rintro ⟨hs₁, hT⟩;
    replace hT := trace_provabilityLogic_TA_eq_univ_iff (α := α).mpr hT;
    rcases provabilityLogic_eq_A_or_eq_D_or_eq_S hT (provabilityLogic_TA_subset_S hT)
      with h | h | h;
    · exact h;
    · exact absurd (soundOnHierarchy_of_axiomD_mem_provabilityLogic_TA (a := default) hT
        (h ▸ Logic.D.axiomD)) hs₁;
    · have := provabilityLogic_TA_eq_S_iff.mp h;
      exact (hs₁ inferInstance).elim;

/-- Exactly one of the following holds: `T` is sound and `PL(T, 𝗧𝗔) = 𝐒`; `T` is `𝚺₁`-sound but
not sound and `PL(T, 𝗧𝗔) = 𝐃`; `T` is not `𝚺₁`-sound, `T` has characteristic `ω`, and
`PL(T, 𝗧𝗔) = 𝐀`; `T` has characteristic `n` and `PL(T, 𝗧𝗔) = 𝐆𝐋β⁻ {n}ᶜ` for some `n`.

- [AB05, Corollary 41]
-/
theorem provabilityLogic_TA_classification :
    ∃! i : Fin 4, ![
      ℕ↓[ℒₒᵣ] ⊧* T ∧ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐒,
      T.SoundOnHierarchy 𝚺 1 ∧ ¬ℕ↓[ℒₒᵣ] ⊧* T ∧ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐃,
      ¬T.SoundOnHierarchy 𝚺 1 ∧ T.height = ⊤ ∧ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐀,
      ∃ n : ℕ, T.height = n ∧
        (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐆𝐋β⁻ {n}ᶜ (by simp)] i := by
  apply existsUnique_of_exists_of_unique;
  · by_cases hs : ℕ↓[ℒₒᵣ] ⊧* T;
    · use 0;
      simpa [hs] using (Logic.S.eq_provabilityLogicRelativeTo_TA (α := α) (T := T)).symm;
    by_cases hs₁ : T.SoundOnHierarchy 𝚺 1;
    · use 1;
      simpa [hs, hs₁] using provabilityLogic_TA_eq_D_iff.mpr ⟨hs₁, hs⟩;
    by_cases h : T.height = ⊤;
    · use 2;
      simpa [hs₁, h] using provabilityLogic_TA_eq_A_iff.mpr ⟨hs₁, h⟩;
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h;
      use 3;
      exact ⟨n, hn.symm, provabilityLogic_TA_eq_GLBetaMinus_iff.mpr hn.symm⟩;
  · have h₁ : ℕ↓[ℒₒᵣ] ⊧* T → T.SoundOnHierarchy 𝚺 1 := fun _ ↦ inferInstance;
    have h₂ : T.SoundOnHierarchy 𝚺 1 → T.height = ⊤ :=
      fun _ ↦ Arithmetic.height_eq_top_of_sigma1_sound T;
    simp +contextual [Fin.forall_fin_succ, h₁, h₂, mt h₁, mt h₂];

end FFL.ProvabilityLogic

end
