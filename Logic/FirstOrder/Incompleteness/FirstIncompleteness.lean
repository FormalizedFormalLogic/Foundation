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

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

variable (T)

private lemma diagRefutation_re : RePred (fun σ => T ⊢! ~σ/[⸢σ⸣]) := by
  have : Partrec fun σ : Subsentence ℒₒᵣ 1 => (provableFn T (~σ/[⸢σ⸣])).map (fun _ => ()) :=
    Partrec.map
      ((provableFn_partrec T).comp <| Primrec.to_comp
        <| (Subformula.neg_primrec (L := ℒₒᵣ)).comp
        <| (Subformula.substs₁_primrec (L := ℒₒᵣ)).comp
          ((Subterm.Operator.const_primrec (L := ℒₒᵣ)).comp
            <| (Subterm.Operator.numeral_primrec (L := ℒₒᵣ)).comp .encode) .id)
      (.const ())
  exact this.of_eq <| by intro σ; ext; simp[←provable_iff_provableFn]

noncomputable def diagRefutation : Subsentence ℒₒᵣ 1 := pred (fun σ => T ⊢! ~σ/[⸢σ⸣])

local notation "ρ" => diagRefutation T

noncomputable def undecidable : Sentence ℒₒᵣ := ρ/[⸢ρ⸣]

local notation "γ" => undecidable T

lemma diagRefutation_spec (σ : Subsentence ℒₒᵣ 1) :
    T ⊢! ρ/[⸢σ⸣] ↔ T ⊢! ~σ/[⸢σ⸣] := by
  simpa[diagRefutation] using pred_representation T (diagRefutation_re T) (x := σ)

lemma independent : System.Independent T γ := by
  have h : T ⊢! γ ↔ T ⊢! ~γ := by simpa using diagRefutation_spec T ρ
  exact
    ⟨System.unprovable_iff_not_provable.mpr
       (fun b => Gentzen.inconsistent_of_provable_and_refutable' b (h.mp b) (consistent_of_sigmaOneSound T)),
     System.unprovable_iff_not_provable.mpr
       (fun b => Gentzen.inconsistent_of_provable_and_refutable' (h.mpr b) b (consistent_of_sigmaOneSound T))⟩

theorem main : ¬System.Complete T := System.incomplete_iff_exists_independent.mpr ⟨γ, independent T⟩

end FirstIncompleteness

variable (T : Theory ℒₒᵣ) [DecidablePred T] [EqTheory T] [PAminus T] [SigmaOneSound T] [Theory.Computable T]
open FirstIncompleteness

/- Gödel's First incompleteness theorem -/
theorem first_incompleteness : ¬System.Complete T := FirstIncompleteness.main T

lemma undecidable : T ⊬ undecidable T ∧ T ⊬ ~undecidable T :=
  FirstIncompleteness.independent T

end Arith

end FirstOrder

end LO
