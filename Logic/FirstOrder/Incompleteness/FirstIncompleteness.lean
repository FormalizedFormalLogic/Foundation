import Logic.FirstOrder.Arith.Representation
import Logic.FirstOrder.Computability.Calculus

namespace LO

namespace FirstOrder

section

variable {L : Language}

lemma provable_iff_of_consistent_of_complete {T : Theory L}
  (consis : System.Consistent T) (comp : System.Complete T) :
    T ⊢! σ ↔ ¬T ⊢! ~σ :=
  ⟨by rintro ⟨b₁⟩ ⟨b₂⟩; exact Gentzen.inconsistent_of_provable_and_refutable b₁ b₂ consis,
   by intro h; exact or_iff_not_imp_right.mp (comp σ) h⟩

end

namespace Arith

namespace FirstIncompleteness

variable {T : Theory ℒₒᵣ} [𝐄𝐪 ≾ T] [𝐏𝐀⁻ ≾ T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

variable (T)

/-- Set $D \coloneqq \{\sigma\ |\ T \vdash \lnot\sigma(\ulcorner \sigma \urcorner)\}$ is r.e. -/
lemma diagRefutation_re : RePred (fun σ ↦ T ⊢! ~σ/[⸢σ⸣]) := by
  have : Partrec fun σ : Semisentence ℒₒᵣ 1 ↦ (provableFn T (~σ/[⸢σ⸣])).map (fun _ ↦ ()) :=
    Partrec.map
      ((provableFn_partrec T).comp <| Primrec.to_comp
        <| (Semiformula.neg_primrec (L := ℒₒᵣ)).comp
        <| (Semiformula.substs₁_primrec (L := ℒₒᵣ)).comp
          ((Semiterm.Operator.const_primrec (L := ℒₒᵣ)).comp
            <| (Semiterm.Operator.numeral_primrec (L := ℒₒᵣ)).comp .encode) .id)
      (.const ())
  exact this.of_eq <| by intro σ; ext; simp[←provable_iff_provableFn]

noncomputable def diagRefutation : Semisentence ℒₒᵣ 1 := pred (fun σ => T ⊢! ~σ/[⸢σ⸣])

local notation "ρ" => diagRefutation T

/-- Define sentence $\gamma := \rho(\ulcorner \rho \urcorner)$ -/
noncomputable def undecidable : Sentence ℒₒᵣ := ρ/[⸢ρ⸣]

local notation "γ" => undecidable T

/-- ρ is a sentence that represents $D$ -/
lemma diagRefutation_spec (σ : Semisentence ℒₒᵣ 1) :
    T ⊢! ρ/[⸢σ⸣] ↔ T ⊢! ~σ/[⸢σ⸣] := by
  simpa[diagRefutation] using pred_representation T (diagRefutation_re T) (x := σ)

/-- It is obvious that $T \vdash \gamma \iff T \vdash \lnot \gamma$. Since
 $T$ is consistent, $\gamma$ is independent from $T$ -/
lemma independent : System.Independent T γ := by
  have h : T ⊢! γ ↔ T ⊢! ~γ := by simpa using diagRefutation_spec T ρ
  exact
    ⟨System.unprovable_iff_not_provable.mpr
       (fun b => Gentzen.inconsistent_of_provable_and_refutable' b (h.mp b) (consistent_of_sigmaOneSound T)),
     System.unprovable_iff_not_provable.mpr
       (fun b => Gentzen.inconsistent_of_provable_and_refutable' (h.mpr b) b (consistent_of_sigmaOneSound T))⟩

theorem main : ¬System.Complete T := System.incomplete_iff_exists_independent.mpr ⟨γ, independent T⟩

end FirstIncompleteness

variable (T : Theory ℒₒᵣ) [DecidablePred T] [𝐄𝐪 ≾ T] [𝐏𝐀⁻ ≾ T] [SigmaOneSound T] [Theory.Computable T]
open FirstIncompleteness

/- Gödel's First incompleteness theorem -/
theorem first_incompleteness : ¬System.Complete T := FirstIncompleteness.main T

lemma undecidable : T ⊬ undecidable T ∧ T ⊬ ~undecidable T :=
  FirstIncompleteness.independent T

end Arith

end FirstOrder

end LO
