module

public import Foundation.ProvabilityLogic.Classification.DS.Modal
public import Foundation.ProvabilityLogic.Classification.ProvabilityLogicTrace

/-!
# No provability logic of trace `ω` lies strictly between `𝐃` and `𝐒`

If the provability logic of `T` relative to `U` has trace `ω` and contains a formula outside `𝐃`,
then `U` proves the local reflection schema for `T`, so the logic contains `𝐒`.

## References

- [AB05, Lemma 56, Lemma 57, Corollary 58]
- [Bek90, Theorem 1, Assertion 1]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁]

lemma LetterlessFormula.lift_mem_provabilityLogic_iff {β : Type*} {A : LetterlessFormula} :
    A.lift ∈ (T.provabilityLogicRelativeTo U : Logic α) ↔
      A.lift ∈ (T.provabilityLogicRelativeTo U : Logic β) := by
  constructor <;> intro h f <;> simpa only [standardInterpret, interpret_lift] using h ⟨fun _ ↦ ⊥⟩;

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

lemma A_subset_provabilityLogic_of_trace {β : Type*}
    (h : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ) :
    𝐀 ⊆ (T.provabilityLogicRelativeTo U : Logic β) :=
  sumQuasiNormal_subset_provabilityLogic <| by
    rintro _ ⟨i, -, rfl⟩;
    simpa using (lift_mem_provabilityLogic_iff (α := α) (A := TBB i)).mp <| by
      simpa using TBB_mem_provabilityLogic_of_mem_trace (h ▸ Set.mem_univ i)

/-- If the provability logic of `T` relative to `U` has trace `ω` and contains a formula outside
`𝐃`, then `U` proves `Pr_T(σ) 🡒 σ` for every sentence `σ`.

- [Bek90, Theorem 1]
- [AB05, Lemma 57]
-/
theorem provable_reflection_of_not_D
    (hT : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ) {A : Formula α}
    (hA : A ∈ (T.provabilityLogicRelativeTo U : Logic α)) (hAD : 𝐃 ⊬ A)
    (σ : ArithmeticSentence) : U ⊢ T.standardProvability σ 🡒 σ := by
  classical
  have h₁ : (𝐀 +ᴸ {A⟦fun a ↦ #(some a)⟧}) ⊆
      (T.provabilityLogicRelativeTo U : Logic (Option α)) := by
    intro C hC;
    induction hC with
    | mem₁ hC => exact A_subset_provabilityLogic_of_trace hT hC;
    | mem₂ hC =>
      obtain rfl := hC;
      intro g;
      simpa [interpret_subst, interpret] using hA ⟨fun a ↦ g.val (some a)⟩;
    | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
    | subst _ ih => exact provabilityLogic_subst ih;
  obtain ⟨B, hBS, hB, hB₂⟩ :=
    Logic.D.exists_A_add_provable_or_boxImp (Logic.D.not_provable_subst_some hAD) none;
  obtain ⟨n, f, hf⟩ := exists_realization_provable_neg_of_not_S (T := T) hBS;
  have h₂ : U ⊢ f T (lift (⩕ i ∈ Finset.range n, TBB i)) :=
    (lift_mem_provabilityLogic_iff (β := Empty)).mpr (by
      simpa using A_subset_provabilityLogic_of_trace hT <|
        FConj'_iff_forall_provable.mpr fun _ _ ↦ Logic.A.provable_TBB) f;
  have h₃ : U ⊢ (⟨Function.update f.val none σ⟩ : Realization _ _) T (B ⋎ (□#none 🡒 #none)) :=
    h₁ hB₂ _;
  have e : (⟨Function.update f.val none σ⟩ : Realization _ _) T B = f T B :=
    interpret_congr_atoms fun a ha ↦
      Function.update_of_ne (by grind [atoms_subst_subset (hB ha)]) _ _;
  have h₄ : U ⊢ ∼f T (B ⋏ lift (⩕ i ∈ Finset.range n, TBB i)) := WeakerThan.pbl hf;
  simp only [standardInterpret, interpret, e] at h₃ h₄;
  cl_prover [h₂, h₃, h₄];

/-- A provability logic of trace `ω` strictly containing `𝐃` contains `𝐒`.

- [Bek90, Assertion 1]
- [AB05, Lemma 56, Lemma 57]
-/
theorem S_subset_provabilityLogic
    (hT : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ)
    (h : 𝐃 ⊂ (T.provabilityLogicRelativeTo U : Logic α)) :
    𝐒 ⊆ (T.provabilityLogicRelativeTo U : Logic α) := by
  obtain ⟨A, hA, hAD⟩ := Set.exists_of_ssubset h;
  apply sumQuasiNormal_subset_provabilityLogic;
  rintro _ ⟨C, rfl⟩ _;
  exact provable_reflection_of_not_D hT hA hAD _;

/-- No provability logic of trace `ω` lies strictly between `𝐃` and `𝐒`.

- [AB05, Corollary 58]
-/
theorem not_D_ssubset_provabilityLogic_ssubset_S
    (hT : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ) :
    ¬(𝐃 ⊂ (T.provabilityLogicRelativeTo U : Logic α) ∧
      (T.provabilityLogicRelativeTo U : Logic α) ⊂ 𝐒) :=
  fun ⟨h₁, h₂⟩ ↦ h₂.not_subset (S_subset_provabilityLogic hT h₁)

end FFL.ProvabilityLogic

end
