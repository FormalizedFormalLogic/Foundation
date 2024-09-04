import Arithmetization.Incompleteness.D1

namespace LO.FirstOrder

namespace Semiformula

variable {L : Language}

lemma coe_substs_eq_substs_coe (σ : Semisentence L k) (v : Fin k → Semiterm L Empty n) :
    (((Rew.substs v).hom σ) : SyntacticSemiformula L n) =
    (Rew.substs (fun x ↦ Rew.emb (v x))).hom (↑σ : SyntacticSemiformula L k) := by
  simp [embedding, ←Rew.hom_comp_app]; congr 2
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

lemma coe_substs_eq_substs_coe₁ (σ : Semisentence L 1) (t : Semiterm L Empty n) :
    (σ/[t] : SyntacticSemiformula L n) =
    (↑σ : SyntacticSemiformula L 1)/[(↑t : Semiterm L ℕ n)] := by
  simpa using coe_substs_eq_substs_coe σ ![t]

end Semiformula

namespace Arith

open LO.Arith LO.System LO.Arith.Formalized

variable (T : Theory ℒₒᵣ) [𝐑₀ ≼ T] [ℕ ⊧ₘ* T] [T.Delta1Definable]

theorem incomplete : ¬System.Complete T  := by
  let D : ℕ → Prop := fun n : ℕ ↦ ∃ p : SyntacticSemiformula ℒₒᵣ 1, n = ⌜p⌝ ∧ T ⊢! ~p/[⌜p⌝]
  have D_re : RePred D := by
    have : 𝚺₁-Predicate fun p : ℕ ↦
      ⌜ℒₒᵣ⌝.IsSemiformula 1 p ∧ (T.codeIn ℕ).Provable (⌜ℒₒᵣ⌝.neg <| ⌜ℒₒᵣ⌝.substs ?[numeral p] p) := by definability
    exact (re_iff_sigma1.mpr this).of_eq <| by
      intro p; constructor
      · rintro ⟨hp, b⟩
        rcases hp.sound with ⟨p, rfl⟩
        refine ⟨p, rfl, Language.Theory.Provable.sound (by simpa)⟩
      · rintro ⟨p, rfl, b⟩
        exact ⟨by simp, by simpa using provable_of_provable (V := ℕ) b⟩
  let σ : SyntacticSemiformula ℒₒᵣ 1 := codeOfRePred (D)
  let ρ : SyntacticFormula ℒₒᵣ := σ/[⌜σ⌝]
  have : ∀ n : ℕ, D n ↔ T ⊢! σ/[‘↑n’] := fun n ↦ by
    simpa [Semiformula.coe_substs_eq_substs_coe₁] using re_complete (T := T) (D_re) (x := n)
  have : T ⊢! ~ρ ↔ T ⊢! ρ := by
    simpa [D, goedelNumber'_def, quote_eq_encode] using this ⌜σ⌝
  have con : System.Consistent T := Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩
  refine LO.System.incomplete_iff_exists_undecidable.mpr ⟨↑ρ, ?_, ?_⟩
  · intro h
    have : T ⊢! ~↑ρ := by simpa [provable₀_iff] using this.mpr h
    exact LO.System.not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable h this) inferInstance
  · intro h
    have : T ⊢! ↑ρ := this.mp (by simpa [provable₀_iff] using h)
    exact LO.System.not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable this h) inferInstance

end LO.FirstOrder.Arith
