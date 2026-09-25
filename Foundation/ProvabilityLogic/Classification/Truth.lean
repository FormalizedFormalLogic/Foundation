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
        ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ 🡒 σ := by
  simp only [Semantics.Imp.models_imply, models_standardProvability_iff];
  exact ⟨fun _ σ hσ h ↦ T.soundOnHierarchy 𝚺 1 h hσ, fun h ↦ ⟨fun hσ hσ' ↦ h _ hσ' hσ⟩⟩

variable [𝗜𝚺₁ ⪯ T] {n : ℕ}

lemma models_boxBot_iff : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability^[n + 1] ⊥ ↔ T.height ≤ n := by
  simpa [Function.iterate_succ_apply', models_standardProvability_iff] using
    Provability.height_le_iff_boxBot.symm

lemma models_TBB_iff (f : Realization α ℒₒᵣ) : ℕ↓[ℒₒᵣ] ⊧ f T (TBB n) ↔ T.height ≠ n := by
  simp only [TBB, standardInterpret, interpret, interpret_boxItr, Semantics.Imp.models_imply,
    models_boxBot_iff];
  rcases n with _ | n;
  · simp;
  · simp only [models_boxBot_iff];
    generalize T.height = m;
    cases m using ENat.recTopCoe with
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
  simp only [Set.ext_iff, mem_trace_provabilityLogic_TA_iff, Set.mem_compl_singleton_iff];
  exact ⟨fun h ↦ by simpa using h n, fun h m ↦ by simp [h, eq_comm]⟩

omit [𝗜𝚺₁ ⪯ T] in
lemma bot_notMem_provabilityLogic_TA : ⊥ ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
  sorry

lemma provabilityLogic_TA_subset_S (h : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = .univ) :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ 𝐒 := by
  sorry

/-- - [AB05, Corollary 41(ii)] -/
theorem D_subset_provabilityLogic_TA [T.SoundOnHierarchy 𝚺 1] :
    𝐃 ⊆ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
  sorry

/-- - [AB05, Corollary 41(ii)] -/
theorem soundOnHierarchy_of_axiomD_mem_provabilityLogic_TA {a : α}
    (hT : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = .univ)
    (h : □(□#a ⋎ □#a) 🡒 □#a ⋎ □#a ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α)) :
    T.SoundOnHierarchy 𝚺 1 := by
  sorry

/-- - [AB05, Corollary 41(iv)] -/
theorem provabilityLogic_TA_eq_GLBetaMinus_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐆𝐋β⁻ {n}ᶜ (by simp) ↔ T.height = n := by
  sorry

variable [Nonempty α]

/-- - [AB05, Corollary 41(i)] -/
theorem provabilityLogic_TA_eq_S_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐒 ↔ ℕ↓[ℒₒᵣ] ⊧* T := by
  sorry

/-- - [AB05, Corollary 41(ii)] -/
theorem provabilityLogic_TA_eq_D_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐃 ↔
      T.SoundOnHierarchy 𝚺 1 ∧ ¬ℕ↓[ℒₒᵣ] ⊧* T := by
  sorry

/-- - [AB05, Corollary 41(iii)] -/
theorem provabilityLogic_TA_eq_A_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = 𝐀 ↔
      ¬T.SoundOnHierarchy 𝚺 1 ∧ T.height = ⊤ := by
  sorry

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
  sorry

end FFL.ProvabilityLogic

end
