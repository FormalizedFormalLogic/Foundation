module

public import Foundation.ProvabilityLogic.Classification.AD
public import Foundation.ProvabilityLogic.Classification.DS

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

end ProvabilityLogic

end FFL

end
