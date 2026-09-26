module

public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.Vorspiel.List.OAOO

/-!
# Truth provability logics

The provability logic `PL(T, 𝗧𝗔)` of `T` relative to `𝗧𝗔` is `𝐒`, `𝐃`, `𝐀`, or `𝐆𝐋β {n}ᶜ`,
according to whether `T` is sound, `𝚺₁`-sound but not sound, not `𝚺₁`-sound and of characteristic
`ω`, or of characteristic `n`.

## References

- [AB05, Corollary 41]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder ProvabilityAbstraction Formula

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {n : ℕ} {a : α}

/-! ### Truth provability logics -/

lemma alpha_mem_provabilityLogic_TA_iff :
    alpha n ∈ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) ↔ T.height ≠ n :=
  ⟨fun h ↦ (models_alpha_iff ⟨fun _ ↦ ⊥⟩).mp <| Arithmetic.TA.provable_iff.mp <| h _,
    fun h f ↦ Arithmetic.TA.provable_iff.mpr <| (models_alpha_iff f).mpr h⟩

lemma mem_trace_provabilityLogic_TA_iff :
    n ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 (α := α)).trace ↔ T.height ≠ n :=
  mem_trace_provabilityLogic_iff.trans alpha_mem_provabilityLogic_TA_iff

lemma trace_provabilityLogic_TA_eq_univ_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 (α := α)).trace = .univ ↔ T.height = ⊤ := by
  simp [Set.eq_univ_iff_forall, mem_trace_provabilityLogic_TA_iff, ENat.eq_top_iff_forall_ne,
    ne_comm]

lemma trace_provabilityLogic_TA_eq_compl_singleton_iff :
    (T.provabilityLogicRelativeTo 𝗧𝗔 (α := α)).trace = {n}ᶜ ↔ T.height = n := by
  suffices (∀ m : ℕ, T.height ≠ m ↔ m ≠ n) ↔ T.height = n by
    simpa only [Set.ext_iff, mem_trace_provabilityLogic_TA_iff, Set.mem_compl_singleton_iff];
  exact ⟨fun h ↦ by simpa using h n, fun h m ↦ by simp [h, eq_comm]⟩

lemma provabilityLogic_TA_weakerThan_S
    (h : (T.provabilityLogicRelativeTo 𝗧𝗔 (α := α)).trace = .univ) :
    T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) ⪯ 𝐒 := by
  by_contra hS;
  have h₁ : ⊥ ∈ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) :=
    (provabilityLogic_eq_GLBeta hS).symm.subset <|
      Logic.GLBeta.mem_iff.mpr <| by simp [h];
  simpa [standardInterpret, interpret] using Arithmetic.TA.provable_iff.mp <| h₁ ⟨fun _ ↦ ⊥⟩;

/-- - [AB05, Corollary 41(ii)] -/
theorem D_weakerThan_provabilityLogic_TA [T.SoundOnHierarchy 𝚺 1] :
    𝐃 ⪯ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) := by
  have h := Arithmetic.soundOnHierarchy_iff_models_reflection.mp ‹T.SoundOnHierarchy 𝚺 1›;
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ (rfl | ⟨B, C, rfl⟩) f <;> apply Arithmetic.TA.provable_iff.mpr;
  · simpa [standardInterpret, interpret] using h ⊥ (by simp);
  · exact h _ <| by simp [interpret, Arithmetic.standardProvability_def];

/-- - [AB05, Corollary 41(ii)] -/
theorem soundOnHierarchy_of_axiomD_mem_provabilityLogic_TA
    (hT : (T.provabilityLogicRelativeTo 𝗧𝗔 (α := α)).trace = .univ)
    (h : □(□#a ⋎ □#a) 🡒 □#a ⋎ □#a ∈ T.provabilityLogicRelativeTo 𝗧𝗔) :
    T.SoundOnHierarchy 𝚺 1 :=
  Arithmetic.soundOnHierarchy_iff_models_reflection.mpr fun _ hσ ↦
    Arithmetic.TA.provable_iff.mp <|
      provable_sigma1_reflection_of_mem_of_not_A hT h Logic.A.not_axiomD hσ

/-- - [AB05, Corollary 41(iv)] -/
theorem provabilityLogic_TA_eq_GLBeta_iff :
    T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐆𝐋β {n}ᶜ (by simp) ↔ T.height = n := by
  constructor;
  · exact fun h ↦ trace_provabilityLogic_TA_eq_compl_singleton_iff.mp <|
      h ▸ Logic.GLBeta.trace_eq;
  · intro hn;
    have h : ∼alpha n ∈ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) := fun f ↦
      Arithmetic.TA.provable_iff.mpr <| by
        simp [standardInterpret, interpret, models_alpha_iff f, hn];
    have hS : ¬T.provabilityLogicRelativeTo 𝗧𝗔 ⪯ 𝐒 :=
      fun hS ↦ unprovable_bot <| hS.wk h ⨀ Logic.S.provable_alpha;
    exact (provabilityLogic_eq_GLBeta hS).trans <| by
      congr 1; exact trace_provabilityLogic_TA_eq_compl_singleton_iff.mpr hn;

variable [Nonempty α]

/-- - [AB05, Corollary 41(i)] -/
theorem provabilityLogic_TA_eq_S_iff :
    T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐒 ↔ ℕ↓[ℒₒᵣ] ⊧* T := by
  constructor;
  · intro h;
    obtain ⟨p⟩ := ‹Nonempty α›;
    apply Semantics.modelsSet_iff.mpr;
    intro φ hφ;
    have h₁ : □#p 🡒 #p ∈ T.provabilityLogicRelativeTo 𝗧𝗔 := h ▸ Logic.S.axiomT;
    exact Semantics.Imp.models_imply.mp (Arithmetic.TA.provable_iff.mp (h₁ ⟨fun _ ↦ φ⟩)) <|
      Arithmetic.models_standardProvability_iff.mpr <| by_axm hφ;
  · exact fun _ ↦ Logic.S.eq_provabilityLogicRelativeTo_TA.symm;

/-- - [AB05, Corollary 41(ii)] -/
theorem provabilityLogic_TA_eq_D_iff :
    T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐃 ↔
      T.SoundOnHierarchy 𝚺 1 ∧ ¬ℕ↓[ℒₒᵣ] ⊧* T := by
  inhabit α;
  constructor;
  · intro h;
    and_intros;
    · exact soundOnHierarchy_of_axiomD_mem_provabilityLogic_TA (a := default)
        (Set.eq_univ_of_forall fun _ ↦
          mem_trace_provabilityLogic_iff.mpr <| h ▸ Logic.D.provable_alpha)
        (h ▸ Logic.D.axiomD);
    · exact fun hs ↦ (Logic.strictlyWeakerThan_iff.mp inferInstance).ne <|
        h.symm.trans <| provabilityLogic_TA_eq_S_iff.mpr hs;
  · rintro ⟨_, hs⟩;
    have hT := trace_provabilityLogic_TA_eq_univ_iff (α := α).mpr <|
      Arithmetic.height_eq_top_of_sigma1_sound T;
    rcases provabilityLogic_eq_A_or_eq_D_or_eq_S hT (provabilityLogic_TA_weakerThan_S hT)
      with h | h | h;
    · exact absurd (h ▸ D_weakerThan_provabilityLogic_TA) StrictlyWeakerThan.notWT;
    · exact h;
    · exact absurd (provabilityLogic_TA_eq_S_iff.mp h) hs;

/-- - [AB05, Corollary 41(iii)] -/
theorem provabilityLogic_TA_eq_A_iff :
    T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐀 ↔
      ¬T.SoundOnHierarchy 𝚺 1 ∧ T.height = ⊤ := by
  inhabit α;
  constructor;
  · intro h;
    and_intros;
    · exact fun _ ↦ StrictlyWeakerThan.notWT <| h ▸ D_weakerThan_provabilityLogic_TA;
    · exact ENat.eq_top_iff_forall_ne.mpr fun _ ↦
        (alpha_mem_provabilityLogic_TA_iff.mp <| h ▸ Logic.A.provable_alpha).symm;
  · rintro ⟨hs₁, hT⟩;
    replace hT := trace_provabilityLogic_TA_eq_univ_iff (α := α).mpr hT;
    rcases provabilityLogic_eq_A_or_eq_D_or_eq_S hT (provabilityLogic_TA_weakerThan_S hT)
      with h | h | h;
    · exact h;
    · exact absurd (soundOnHierarchy_of_axiomD_mem_provabilityLogic_TA (a := default) hT
        (h ▸ Logic.D.axiomD)) hs₁;
    · have := provabilityLogic_TA_eq_S_iff.mp h;
      exact (hs₁ inferInstance).elim;

/-- Exactly one of the following holds.

1. `T` is sound and `PL(T, 𝗧𝗔) = 𝐒`.
2. `T` is `𝚺₁`-sound but not sound, and `PL(T, 𝗧𝗔) = 𝐃`.
3. `T` is not `𝚺₁`-sound, `T` has characteristic `ω`, and `PL(T, 𝗧𝗔) = 𝐀`.
4. For some `n`, `T` has characteristic `n` and `PL(T, 𝗧𝗔) = 𝐆𝐋β {n}ᶜ`.

- [AB05, Corollary 41]
-/
theorem provabilityLogic_TA_classification : [
    ℕ↓[ℒₒᵣ] ⊧* T ∧ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐒,
    T.SoundOnHierarchy 𝚺 1 ∧ ¬ℕ↓[ℒₒᵣ] ⊧* T ∧ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐃,
    ¬T.SoundOnHierarchy 𝚺 1 ∧ T.height = ⊤ ∧ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐀,
    ∃ n : ℕ, T.height = n ∧ T.provabilityLogicRelativeTo 𝗧𝗔 (α := α) = 𝐆𝐋β {n}ᶜ (by simp)
  ].OAOO := by
  have h₁ : ℕ↓[ℒₒᵣ] ⊧* T → T.SoundOnHierarchy 𝚺 1 := fun _ ↦ inferInstance;
  have h₂ : T.SoundOnHierarchy 𝚺 1 → T.height = ⊤ :=
    fun _ ↦ Arithmetic.height_eq_top_of_sigma1_sound T;
  oaoo_split;
  · by_cases hs : ℕ↓[ℒₒᵣ] ⊧* T;
    · exact .inl ⟨hs, Logic.S.eq_provabilityLogicRelativeTo_TA.symm⟩;
    by_cases hs₁ : T.SoundOnHierarchy 𝚺 1;
    · exact .inr <| .inl ⟨hs₁, hs, provabilityLogic_TA_eq_D_iff.mpr ⟨hs₁, hs⟩⟩;
    by_cases h : T.height = ⊤;
    · exact .inr <| .inr <| .inl ⟨hs₁, h, provabilityLogic_TA_eq_A_iff.mpr ⟨hs₁, h⟩⟩;
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h;
      exact .inr <| .inr <| .inr ⟨n, hn.symm, provabilityLogic_TA_eq_GLBeta_iff.mpr hn.symm⟩;
  all_goals simp +contextual [h₁, h₂];

end FFL.ProvabilityLogic

end
