module

public import Foundation.ProvabilityLogic.Classification.AD
public import Foundation.ProvabilityLogic.Classification.DS
public import Foundation.FirstOrder.Incompleteness.Reflection.Local

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

namespace FirstOrder.ArithmeticTheory

open ProvabilityLogic Formula

variable (T U : ArithmeticTheory) [T.Δ₁] (N : Set ℕ)

noncomputable def addAlpha : ArithmeticTheory :=
  U ∪ (fun n ↦ (alpha n : LetterlessFormula).interpret ⟨Empty.elim⟩ T.standardProvability) '' N

variable {T U N}

lemma weakerThan_addAlpha : U ⪯ T.addAlpha U N := WeakerThan.ofSubset Set.subset_union_left

instance [𝗜𝚺₁ ⪯ U] : 𝗜𝚺₁ ⪯ T.addAlpha U N := (inferInstance : 𝗜𝚺₁ ⪯ U).trans weakerThan_addAlpha

end FirstOrder.ArithmeticTheory

namespace ProvabilityLogic

open FirstOrder Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁] {N : Set ℕ} {A : Formula α}

lemma provabilityLogic_weakerThan_addAlpha :
    T.provabilityLogicRelativeTo U (α := α) ⪯ T.provabilityLogicRelativeTo (T.addAlpha U N) :=
  ⟨fun _ hA f ↦ ArithmeticTheory.weakerThan_addAlpha.pbl (hA f)⟩

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/-- A provability logic of trace `ω` contained in `𝐒` is one of `𝐀`, `𝐃`, and `𝐒`.

- [Bek90, Assertion 3]
-/
theorem provabilityLogic_eq_A_or_eq_D_or_eq_S
    (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ)
    (hS : T.provabilityLogicRelativeTo U (α := α) ⪯ 𝐒) :
    T.provabilityLogicRelativeTo U (α := α) = 𝐀 ∨
      T.provabilityLogicRelativeTo U (α := α) = 𝐃 ∨
      T.provabilityLogicRelativeTo U (α := α) = 𝐒 := by
  rcases Logic.eq_or_strictlyWeakerThan (A_weakerThan_provabilityLogic hT) with h | h₁;
  · grind;
  rcases Logic.eq_or_strictlyWeakerThan (D_weakerThan_provabilityLogic hT h₁) with h | h₂;
  · grind;
  · simp [Logic.weakerThan_antisymm hS <| S_weakerThan_provabilityLogic hT h₂];

lemma provabilityLogic_equiv_A_or_equiv_D_or_equiv_S
    (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ)
    (hS : T.provabilityLogicRelativeTo U (α := α) ⪯ 𝐒) :
    T.provabilityLogicRelativeTo U (α := α) ≊ 𝐀 ∨
      T.provabilityLogicRelativeTo U (α := α) ≊ 𝐃 ∨
      T.provabilityLogicRelativeTo U (α := α) ≊ 𝐒 := by
  simpa only [Logic.equiv_iff] using provabilityLogic_eq_A_or_eq_D_or_eq_S hT hS

lemma imp_mem_provabilityLogic_of_mem_addAlpha (hN : N.Finite)
    (h : A ∈ T.provabilityLogicRelativeTo (T.addAlpha U N)) :
    (⩕ n ∈ hN.toFinset, alpha n : LetterlessFormula).lift 🡒 A ∈ T.provabilityLogicRelativeTo U := by
  intro f;
  obtain ⟨⟨s, hs⟩, h₁⟩ := Theory.compact_add_right (h f);
  apply C_trans _ h₁;
  apply right_Fconj_intro;
  intro σ hσ;
  obtain ⟨n, hn, rfl⟩ := hs hσ;
  have h₂ : U ⊢ f T ((⩕ n ∈ hN.toFinset, alpha n) 🡒 alpha n : LetterlessFormula).lift :=
    provabilityLogic_of_GL (Logic.GL.lift_mem_iff.mpr <| by
      ext k; simpa using (em (k = n)).imp (· ▸ hn) id) f;
  simpa only [standardInterpret, interpret_lift, interpret] using h₂;

lemma trace_provabilityLogic_addAlpha :
    (T.provabilityLogicRelativeTo
      (T.addAlpha U (T.provabilityLogicRelativeTo U (α := α)).traceᶜ) (α := α)).trace = .univ :=
  Set.eq_univ_of_forall fun n ↦ mem_trace_provabilityLogic_iff.mpr <| by
    by_cases hn : n ∈ (T.provabilityLogicRelativeTo U (α := α)).trace;
    · exact provabilityLogic_weakerThan_addAlpha.wk <| alpha_mem_provabilityLogic_of_mem_trace hn;
    · exact fun f ↦ by_axm <| Set.mem_union_right U
        ⟨n, hn, by simpa using (interpret_lift (A := alpha n)).symm⟩;

/-- The provability logic of `T` relative to `U` is one of `GLα X`, `GLβ X`, `D ∩ GLβ X`, and
`S ∩ GLβ X`, where `X` is its trace.

- [AB05, Theorem 40]
- [Bek90, Assertion 6]
-/
theorem provabilityLogic_classification :
    T.provabilityLogicRelativeTo U (α := α) =
        𝐆𝐋α (T.provabilityLogicRelativeTo U (α := α)).trace ∨
      ∃ hL : (T.provabilityLogicRelativeTo U (α := α)).traceᶜ.Finite,
        T.provabilityLogicRelativeTo U (α := α) = 𝐆𝐋β _ hL ∨
        T.provabilityLogicRelativeTo U (α := α) = 𝐃 ∩ 𝐆𝐋β _ hL ∨
        T.provabilityLogicRelativeTo U (α := α) = 𝐒 ∩ 𝐆𝐋β _ hL := by
  rcases (T.provabilityLogicRelativeTo U (α := α)).traceᶜ.finite_or_infinite with hL | hL;
  · by_cases h : T.provabilityLogicRelativeTo U (α := α) ⪯ 𝐒;
    · let V := T.addAlpha U (T.provabilityLogicRelativeTo U (α := α)).traceᶜ;
      have h₁ : T.provabilityLogicRelativeTo V (α := α) ⪯ 𝐒 := by
        by_contra h₁;
        have h₂ : 𝐒 ⊢ (⩕ n ∈ hL.toFinset, alpha n : LetterlessFormula).lift (α := α) :=
          WeakerThan.pbl (𝓢 := 𝐆𝐋α Set.univ) <| Logic.GLAlpha.mem_iff.mpr
            ⟨by simpa [LetterlessFormula.trace] using hL.biUnion fun _ _ ↦ Set.finite_singleton _,
              Set.subset_univ _⟩;
        exact unprovable_bot <| h.wk (imp_mem_provabilityLogic_of_mem_addAlpha hL <|
          (provabilityLogic_eq_GLBeta h₁).symm.subset <| Logic.GLBeta.mem_iff.mpr <| by
            simp [V, trace_provabilityLogic_addAlpha]) ⨀ h₂;
      have h₂ : T.provabilityLogicRelativeTo U (α := α) =
          T.provabilityLogicRelativeTo V ∩ 𝐆𝐋β _ hL := by
        apply subset_antisymm;
        · exact Set.subset_inter provabilityLogic_weakerThan_addAlpha.subset
            (Logic.weakerThan_GLBeta_trace hL).subset;
        · rintro A ⟨hA₁, hA₂⟩;
          have h₃ : 𝐆𝐋 ⊢ ∼(⩕ n ∈ hL.toFinset, alpha n : LetterlessFormula).lift 🡒 A :=
            GL_imp_of_height_not_mem_trace fun _ _ _ hM hn ↦
              absurd (Logic.GLBeta.mem_iff.mp hA₂ hn)
                (by simpa [Kripke.RootedModel.height] using forces_lift_iff (A := ∼_) |>.mp hM);
          exact provabilityLogic_mdp (provabilityLogic_of_GL <| by cl_prover [h₃])
            (imp_mem_provabilityLogic_of_mem_addAlpha hL hA₁);
      rcases provabilityLogic_eq_A_or_eq_D_or_eq_S trace_provabilityLogic_addAlpha h₁
        with h | h | h <;>
      grind [Logic.GLAlpha.eq_inter_GLBeta hL];
    · grind [provabilityLogic_eq_GLBeta h];
  · grind [provabilityLogic_eq_GLAlpha hL];

lemma provabilityLogic_classification_equiv :
    T.provabilityLogicRelativeTo U (α := α) ≊
        𝐆𝐋α (T.provabilityLogicRelativeTo U (α := α)).trace ∨
      ∃ hL : (T.provabilityLogicRelativeTo U (α := α)).traceᶜ.Finite,
        T.provabilityLogicRelativeTo U (α := α) ≊ 𝐆𝐋β _ hL ∨
        T.provabilityLogicRelativeTo U (α := α) ≊ 𝐃 ∩ 𝐆𝐋β _ hL ∨
        T.provabilityLogicRelativeTo U (α := α) ≊ 𝐒 ∩ 𝐆𝐋β _ hL := by
  simpa only [Logic.equiv_iff] using provabilityLogic_classification

end

section

open FirstOrder.Arithmetic

lemma alpha_mem_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    ∀ n, alpha n (α := α) ∈ T.provabilityLogicRelativeTo U := by
  intro n f;
  simpa [alpha, standardInterpret, interpret, interpret_boxItr, Function.iterate_succ_apply'] using
    h ⟨_, hierarchy_iterate_standardProvability_bot n, rfl⟩

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

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
  · exact fun f ↦ h <| T.standardProvability.mem_localReflectionOn_iff.mpr
      ⟨_, by simp [interpret, standardProvability_def], rfl⟩;

lemma S_weakerThan_provabilityLogic_of_provable_localReflection
    (h : U ⊢* 𝗥𝗳𝗻[Set.univ] T) :
    𝐒 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ ⟨C, rfl⟩ f;
  exact h ⟨_, trivial, rfl⟩;

end

section

open FirstOrder.Arithmetic

variable [U.Δ₁] [𝗜𝚺₁ ⪯ T]

omit [T.Δ₁] in
local instance : 𝗜𝚺₁ ⪯ T ∪ U.Con := (inferInstance : 𝗜𝚺₁ ⪯ T).trans inferInstance

lemma trace_provabilityLogic_add_con_eq_univ
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
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

lemma A_weakerThan_provabilityLogic_add_con
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    𝐀 ⪯ T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) :=
  A_weakerThan_provabilityLogic <| trace_provabilityLogic_add_con_eq_univ hTU hU

/-- - [AB05, Example 63] -/
theorem provabilityLogic_add_con_eq_A
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) (hC : Consistent (T ∪ U.Con)) :
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

end

end ProvabilityLogic

end FFL

end
