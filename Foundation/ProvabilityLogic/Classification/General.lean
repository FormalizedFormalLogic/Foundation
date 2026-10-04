module

public import Foundation.ProvabilityLogic.Classification.AD
public import Foundation.ProvabilityLogic.Classification.DS
public import Foundation.FirstOrder.Incompleteness.Reflection.IteratedConsistency
public import Foundation.FirstOrder.Incompleteness.Reflection.SigmaReflection

/-!
# Classification of provability logics

A provability logic of trace `ω` contained in `𝐒` is one of `𝐀`, `𝐃`, and `𝐒`. In general, the
provability logic of `T` relative to `U` is one of `GLα X`, `GLβ X`, `D ∩ GLβ X`, and
`S ∩ GLβ X`, where `X` is its trace.

## References

- [AB05, Theorem 40]
- [Bek90, Assertion 3, Assertion 6]
-/

@[expose] public section

namespace FFL

open Entailment

namespace ProvabilityLogic

open FirstOrder FirstOrder.Arithmetic Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁] {N : Set ℕ} {A : Formula α}

lemma alpha_mem_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    ∀ n, alpha n (α := α) ∈ T.provabilityLogicRelativeTo U := by
  intro n f;
  simpa [alpha, standardInterpret, interpret, interpret_boxItr, Function.iterate_succ_apply'] using
    h ⟨_, hierarchy_iterate_standardProvability_bot n, rfl⟩

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/-- A provability logic of trace `ω` contained in `𝐒` is one of `𝐀`, `𝐃`, and `𝐒`.

- [Bek90, Assertion 3]
-/
theorem provabilityLogic_eq_A_or_eq_D_or_eq_S :
    letI L := T.provabilityLogicRelativeTo U (α := α);
    L.trace = .univ → L ⪯ 𝐒 → L = 𝐀 ∨ L = 𝐃 ∨ L = 𝐒 := by
  intro hT hS;
  rcases Logic.eq_or_strictlyWeakerThan (A_weakerThan_provabilityLogic hT) with h | h₁;
  · grind;
  · rcases Logic.eq_or_strictlyWeakerThan (D_weakerThan_provabilityLogic hT h₁) with h | h₂;
    · grind;
    · simp [Logic.weakerThan_antisymm hS <| S_weakerThan_provabilityLogic hT h₂];

lemma provabilityLogic_equiv_A_or_equiv_D_or_equiv_S :
    letI L := T.provabilityLogicRelativeTo U (α := α);
    L.trace = .univ → L ⪯ 𝐒 → L ≊ 𝐀 ∨ L ≊ 𝐃 ∨ L ≊ 𝐒 := by
  intro hT hS;
  simpa only [Logic.equiv_iff] using provabilityLogic_eq_A_or_eq_D_or_eq_S hT hS

lemma imp_mem_provabilityLogic_of_mem_add_localReflectionOn (hN : N.Finite)
    (h : A ∈ T.provabilityLogicRelativeTo (U ∪ 𝗥𝗳𝗻[(T.standardProvability^[·] ⊥) '' N] T)) :
    (⩕ n ∈ hN.toFinset, alpha n : LetterlessFormula).lift 🡒 A ∈ T.provabilityLogicRelativeTo U := by
  intro f;
  obtain ⟨⟨s, hs⟩, h₁⟩ := Theory.compact_add_right (h f);
  apply C_trans _ h₁;
  apply right_Fconj_intro;
  intro σ hσ;
  obtain ⟨_, ⟨n, hn, rfl⟩, rfl⟩ := hs hσ;
  have h₂ : U ⊢ f T ((⩕ n ∈ hN.toFinset, alpha n) 🡒 alpha n : LetterlessFormula).lift :=
    provabilityLogic_of_GL (Logic.GL.lift_mem_iff.mpr <| by
      ext k; simpa using (em (k = n)).imp (· ▸ hn) id) f;
  simpa [alpha, standardInterpret, interpret_lift, interpret, interpret_boxItr,
    Function.iterate_succ_apply'] using h₂;

lemma trace_provabilityLogic_add_localReflectionOn_eq_univ :
    letI L := T.provabilityLogicRelativeTo U (α := α);
    (T.provabilityLogicRelativeTo (U ∪ 𝗥𝗳𝗻[(T.standardProvability^[·] ⊥) '' L.traceᶜ] T)
      (α := α)).trace = .univ := by
  set L := T.provabilityLogicRelativeTo U (α := α);
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_provabilityLogic_iff.mpr;
  by_cases hn : n ∈ L.trace;
  · exact provabilityLogic_weakerThan_of_weakerThan.wk <|
      alpha_mem_provabilityLogic_of_mem_trace hn;
  · intro f;
    apply by_axm;
    apply Set.mem_union_right;
    exact ⟨_, ⟨n, hn, rfl⟩, by simp [alpha, standardInterpret, interpret, interpret_boxItr]⟩;

/-- The provability logic of `T` relative to `U` is one of `GLα X`, `GLβ X`, `D ∩ GLβ X`, and
`S ∩ GLβ X`, where `X` is its trace.

- [AB05, Theorem 40]
- [Bek90, Assertion 6]
-/
theorem provabilityLogic_classification :
    letI L := T.provabilityLogicRelativeTo U (α := α);
    L = 𝐆𝐋α L.trace ∨
    ∃ hL : L.traceᶜ.Finite, L = 𝐆𝐋β _ hL ∨ L = 𝐃 ∩ 𝐆𝐋β _ hL ∨ L = 𝐒 ∩ 𝐆𝐋β _ hL := by
  set L := T.provabilityLogicRelativeTo U (α := α);
  rcases L.traceᶜ.finite_or_infinite with hL | hL;
  · by_cases h : L ⪯ 𝐒;
    · set L' :=
        T.provabilityLogicRelativeTo (U ∪ 𝗥𝗳𝗻[(T.standardProvability^[·] ⊥) '' L.traceᶜ] T)
          (α := α);
      have h₁ : L' ⪯ 𝐒 := by
        by_contra h₁;
        have h₂ : 𝐒 ⊢ (⩕ n ∈ hL.toFinset, alpha n : LetterlessFormula).lift (α := α) :=
          WeakerThan.pbl (𝓢 := 𝐆𝐋α Set.univ) <| Logic.GLAlpha.mem_iff.mpr
            ⟨by simpa [LetterlessFormula.trace] using hL.biUnion fun _ _ ↦ Set.finite_singleton _,
              Set.subset_univ _⟩;
        exact unprovable_bot <| h.wk (imp_mem_provabilityLogic_of_mem_add_localReflectionOn hL <|
          (provabilityLogic_eq_GLBeta h₁).symm.subset <| Logic.GLBeta.mem_iff.mpr <| by
            simp [L, trace_provabilityLogic_add_localReflectionOn_eq_univ]) ⨀ h₂;
      have h₂ : L = L' ∩ 𝐆𝐋β _ hL := by
        apply subset_antisymm;
        · exact Set.subset_inter provabilityLogic_weakerThan_of_weakerThan.subset
            (Logic.weakerThan_GLBeta_trace hL).subset;
        · rintro A ⟨hA₁, hA₂⟩;
          have h₃ : 𝐆𝐋 ⊢ ∼(⩕ n ∈ hL.toFinset, alpha n : LetterlessFormula).lift 🡒 A :=
            GL_imp_of_height_not_mem_trace fun _ _ _ hM hn ↦
              absurd (Logic.GLBeta.mem_iff.mp hA₂ hn)
                (by simpa [Kripke.RootedModel.height] using forces_lift_iff (A := ∼_) |>.mp hM);
          exact provabilityLogic_mdp (provabilityLogic_of_GL <| by cl_prover [h₃])
            (imp_mem_provabilityLogic_of_mem_add_localReflectionOn hL hA₁);
      rcases provabilityLogic_eq_A_or_eq_D_or_eq_S
          trace_provabilityLogic_add_localReflectionOn_eq_univ h₁ with h | h | h <;>
      grind [Logic.GLAlpha.eq_inter_GLBeta hL];
    · grind [provabilityLogic_eq_GLBeta h];
  · grind [provabilityLogic_eq_GLAlpha hL];

lemma provabilityLogic_classification_equiv :
    letI L := T.provabilityLogicRelativeTo U (α := α);
    L ≊ 𝐆𝐋α L.trace ∨
    ∃ hL : L.traceᶜ.Finite, L ≊ 𝐆𝐋β _ hL ∨ L ≊ 𝐃 ∩ 𝐆𝐋β _ hL ∨ L ≊ 𝐒 ∩ 𝐆𝐋β _ hL := by
  simpa only [Logic.equiv_iff] using provabilityLogic_classification

lemma trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    (T.provabilityLogicRelativeTo U (α := α)).trace = .univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  exact mem_trace_provabilityLogic_iff.mpr
    <| alpha_mem_provabilityLogic_of_provable_localReflectionOn_Sigma1 h _

lemma D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    𝐃 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ (rfl | ⟨B, C, rfl⟩);
  · exact (A_weakerThan_provabilityLogic
      (trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1 h)).wk
      (Logic.A.neg_boxItr_bot (n := 1));
  · intro f;
    exact h <| T.standardProvability.mem_localReflectionOn_iff.mpr
      ⟨_, by simp [interpret, standardProvability_def], rfl⟩;

lemma S_weakerThan_provabilityLogic_of_provable_localReflection
    (h : U ⊢* 𝗥𝗳𝗻[Set.univ] T) :
    𝐒 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ ⟨C, rfl⟩ f;
  exact h ⟨_, trivial, rfl⟩;

end

section

variable [U.Δ₁] [𝗜𝚺₁ ⪯ T]

variable (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
  (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T)

include hTU hU

lemma trace_provabilityLogic_add_con_eq_univ :
    (T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α)).trace = .univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_provabilityLogic_iff.mpr;
  intro f;
  have h₁ : T ∪ U.Con ⊢ ∼U.standardProvability ⊥ := by_axm <| Set.mem_union_right _ rfl;
  have h₂ : T ∪ U.Con ⊢ T.standardProvability^[n + 1] ⊥ 🡒 U.standardProvability ⊥ :=
    WeakerThan.pbl <| provable_iterate_standardProvability_bot_imp hTU hU n;
  simp only [alpha, standardInterpret, interpret, interpret_boxItr];
  cl_prover [h₁, h₂];

lemma A_weakerThan_provabilityLogic_add_con :
    𝐀 ⪯ T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) :=
  A_weakerThan_provabilityLogic <| trace_provabilityLogic_add_con_eq_univ hTU hU

/-- - [AB05, Example 63] -/
theorem provabilityLogic_add_con_eq_A (hC : Consistent (T ∪ U.Con)) :
    T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) = 𝐀 := by
  apply Logic.weakerThan_antisymm;
  · by_contra! h;
    obtain ⟨-, A, hAA, hAL⟩ :=
      strictlyWeakerThan_iff.mp ⟨A_weakerThan_provabilityLogic_add_con hTU hU, h⟩;
    have h₁ : T ∪ U.Con ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T :=
      provable_localReflectionOn_sigma1_of_mem_of_not_A
        (trace_provabilityLogic_add_con_eq_univ hTU hU) hAL hAA;
    rw [Set.union_singleton] at h₁ hC;
    exact (T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
      (fun _ hσ ↦ by simpa using hσ)
      (by simp : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1 _) h₁).not_con hC;
  · exact A_weakerThan_provabilityLogic_add_con hTU hU;

lemma provabilityLogic_add_con_equiv_A (hC : Consistent (T ∪ U.Con)) :
    T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) ≊ 𝐀 :=
  Logic.equiv_of_eq <| provabilityLogic_add_con_eq_A hTU hU hC

end

section

variable [𝗜𝚺₁ ⪯ T]

lemma trace_provabilityLogic_turingOmega_eq_univ :
    (T.provabilityLogicRelativeTo (T ∪ T.Conω) (α := α)).trace = .univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_provabilityLogic_iff.mpr;
  intro f;
  have h : T ∪ T.Conω ⊢ T.standardProvability.conItr (n + 1) :=
    by_axm <| Set.mem_union_right _ ⟨n + 1, rfl⟩;
  simp only [alpha, standardInterpret, interpret, interpret_boxItr, Function.iterate_succ_apply',
    ProvabilityAbstraction.Provability.conItr] at h ⊢;
  cl_prover [h];

/-- - [AB05, Example 59] -/
theorem provabilityLogic_turingOmega_eq_A (hC : Consistent (T ∪ T.Conω)) :
    T.provabilityLogicRelativeTo (T ∪ T.Conω) (α := α) = 𝐀 := by
  have hT := trace_provabilityLogic_turingOmega_eq_univ (T := T) (α := α);
  apply Logic.weakerThan_antisymm;
  · by_contra! h;
    obtain ⟨-, A, hAA, hAL⟩ := strictlyWeakerThan_iff.mp ⟨A_weakerThan_provabilityLogic hT, h⟩;
    obtain ⟨U, _, hU, e⟩ := exists_prenex_axiomatization_turingOmega (T := T);
    exact (inconsistent_of_provable_localReflectionOn_union (n := 0) hU e <|
      provable_localReflectionOn_sigma1_of_mem_of_not_A hT hAL hAA).not_con hC;
  · exact A_weakerThan_provabilityLogic hT;

lemma provabilityLogic_turingOmega_equiv_A (hC : Consistent (T ∪ T.Conω)) :
    T.provabilityLogicRelativeTo (T ∪ T.Conω) (α := α) ≊ 𝐀 :=
  Logic.equiv_of_eq <| provabilityLogic_turingOmega_eq_A hC

lemma provabilityLogic_turingOmega_eq_A_of_sigma1Sound [T.SoundOnHierarchy 𝚺 1] :
    T.provabilityLogicRelativeTo (T ∪ T.Conω) (α := α) = 𝐀 := by
  apply provabilityLogic_turingOmega_eq_A;
  apply Consistent.of_le (inferInstance : Consistent (T ∪ 𝗥𝗳𝗻[Set.univ] T));
  apply WeakerThan.ofAxm!;
  rintro σ (hσ | ⟨n, rfl⟩);
  · exact by_axm <| Set.mem_union_left _ hσ;
  · exact provable_neg_iterate_standardProvability_bot (fun hσ ↦ by_axm <| Set.mem_union_right _ <|
      T.standardProvability.localReflectionOn_mono (Γ' := Set.univ) (fun _ _ ↦ trivial) hσ) n;

end

section

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

lemma trace_provabilityLogic_add_con_self_eq :
    (T.provabilityLogicRelativeTo (T ∪ T.Con) (α := α)).trace = {0} := by
  ext n;
  rw [mem_trace_provabilityLogic_iff, Set.mem_singleton_iff];
  constructor;
  · intro h;
    have h₁ : T ⊢ ∼T.standardProvability ⊥ 🡒
        T.standardProvability (T.standardProvability^[n] ⊥) 🡒 T.standardProvability^[n] ⊥ := by
      have := h ⟨fun _ ↦ ⊥⟩;
      rw [Set.union_singleton] at this;
      have := deduction this;
      simp only [alpha, standardInterpret, interpret, interpret_boxItr,
        Function.iterate_succ_apply'] at this;
      exact this;
    have h₂ : 𝐆𝐋 ⊢ (∼□⊥ 🡒 alpha n : LetterlessFormula) :=
      Logic.GL.arithmetical_completeness_iff (T := T).mpr fun f ↦ by
        simp only [alpha, standardInterpret, interpret, interpret_boxItr,
          Function.iterate_succ_apply'];
        cl_prover [h₁];
    by_contra hn;
    have h₃ : ∀ i, n ≤ i := by
      simpa using Set.eq_univ_iff_forall.mp (Logic.GL.mem_iff_spectrum_eq_univ.mp h₂) n;
    exact hn <| Nat.le_zero.mp <| h₃ 0;
  · rintro rfl f;
    have h : T ∪ T.Con ⊢ ∼T.standardProvability ⊥ := by_axm <| Set.mem_union_right _ rfl;
    simp only [alpha, standardInterpret, interpret, interpret_boxItr];
    cl_prover [h];

/-- `PL(T, T + Con(T)) = 𝐆𝐋 + ¬□⊥` for a `𝚺₁`-sound `T`. -/
theorem provabilityLogic_add_con_self_eq_GLAlpha :
    T.provabilityLogicRelativeTo (T ∪ T.Con) (α := α) = 𝐆𝐋α {0} :=
  have h := trace_provabilityLogic_add_con_self_eq (T := T) (α := α);
  h ▸ provabilityLogic_eq_GLAlpha (h ▸ (Set.finite_singleton 0).infinite_compl)

end

section

variable {n : ℕ} [NeZero n] [𝗜𝚺₁ ⪯ T] [𝗕𝚺n ⪯ T]

theorem provabilityLogic_add_localReflectionOn_Sigma_eq_D :
    letI T' := T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T;
    Consistent T' → T.provabilityLogicRelativeTo T' (α := α) = 𝐃 := by
  set T' := T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T;
  intro hC;
  have hR : T' ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T := by
    intro _ hσ;
    exact by_axm
      <| Set.mem_union_right _
      <| T.standardProvability.localReflectionOn_mono
      (fun _ h ↦ h.mono NeZero.one_le) hσ;
  have hD := D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1 (α := α) hR;
  apply Logic.weakerThan_antisymm;
  · by_contra! h;
    obtain ⟨-, A, hAD, hA⟩ := strictlyWeakerThan_iff.mp ⟨hD, h⟩;
    obtain ⟨U, _, hU, e⟩ := exists_prenex_axiomatization_localReflectionOn_Sigma (T := T) (n := n);
    have hrfn : T' ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 1)] T := by
      rintro _ ⟨σ, -, rfl⟩;
      exact provable_reflection_of_not_D
        (trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1 hR) hA hAD;
    exact (inconsistent_of_provable_localReflectionOn_union hU e hrfn).not_con hC;
  · exact hD;

lemma provabilityLogic_add_localReflectionOn_Sigma_equiv_D :
    letI T' := T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T;
    Consistent T' → T.provabilityLogicRelativeTo T' (α := α) ≊ 𝐃 :=
  fun hC ↦ Logic.equiv_of_eq <| provabilityLogic_add_localReflectionOn_Sigma_eq_D hC

lemma provabilityLogic_add_localReflectionOn_Sigma_eq_D_of_sigma1Sound
    [T.SoundOnHierarchy 𝚺 1] :
    T.provabilityLogicRelativeTo (T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] T) (α := α) = 𝐃 :=
  provabilityLogic_add_localReflectionOn_Sigma_eq_D <|
    Consistent.of_le inferInstance <| WeakerThan.ofSubset <| Set.union_subset_union_right T <|
      T.standardProvability.localReflectionOn_mono (Γ' := Set.univ) fun _ _ ↦ trivial

end

/-- - [AB05, Example 60] -/
theorem provabilityLogic_add_localReflectionOn_Sigma1_eq_D [𝗜𝚺₁ ⪯ T] :
    letI T' := T ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T;
    Consistent T' → T.provabilityLogicRelativeTo T' (α := α) = 𝐃 :=
  have : 𝗕𝚺 1 ⪯ T := BSigma_weakerThan_ISigma.trans inferInstance;
  provabilityLogic_add_localReflectionOn_Sigma_eq_D

end ProvabilityLogic

end FFL

end
