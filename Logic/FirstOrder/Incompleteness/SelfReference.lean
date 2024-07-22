import Logic.FirstOrder.Arith.Representation
import Logic.FirstOrder.Computability.Calculus
import Logic.Logic.HilbertStyle.Gentzen
import Logic.Logic.Disjunctive

namespace LO.FirstOrder.Arith.FirstIncompleteness

namespace SelfReference

section

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ≼ T] [𝐏𝐀⁻ ≼ T] [SigmaOneSound T]

open Encodable Semiformula

noncomputable def ssbs : Semisentence ℒₒᵣ 3 :=
  graphTotal₂ (fun (σ π : Semisentence ℒₒᵣ 1) ↦ σ/[(⌜π⌝ : Semiterm ℒₒᵣ Empty 0)])

lemma ssbs_spec (σ π : Semisentence ℒₒᵣ 1) :
    T ⊢! “∀ x, !ssbs x !!⌜σ⌝ !!⌜π⌝ ↔ x = !!⌜σ/[(⌜π⌝ : Semiterm ℒₒᵣ Empty 0)]⌝” :=
  representation_computable₂ T (f := fun (σ π : Semisentence ℒₒᵣ 1) ↦ σ/[(⌜π⌝ : Semiterm ℒₒᵣ Empty 0)])
    (Primrec₂.to_comp <| (Semiformula.substs₁_primrec (L := ℒₒᵣ)).comp₂
      ((Semiterm.Operator.const_primrec (L := ℒₒᵣ)).comp₂ <|
        (Semiterm.Operator.numeral_primrec (L := ℒₒᵣ)).comp₂ $ Primrec.encode.comp₂ .right) <|
        .left) σ π

noncomputable def diag (θ : Semisentence ℒₒᵣ 1) : Semisentence ℒₒᵣ 1 :=
  “x | ∀ y, !ssbs y x x → !θ y”

noncomputable def fixpoint (θ : Semisentence ℒₒᵣ 1) : Sentence ℒₒᵣ :=
  (diag θ)/[⌜diag θ⌝]

lemma substs_diag (θ σ : Semisentence ℒₒᵣ 1) :
    “!(diag θ) !!(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)” = “∀ x, !ssbs x !!⌜σ⌝ !!⌜σ⌝ → !θ x” := by
  simp [goedelNumber'_def, diag, Rew.q_substs, ←Rew.hom_comp_app, Rew.substs_comp_substs]

lemma fixpoint_eq (θ : Semisentence ℒₒᵣ 1) :
    fixpoint θ = “∀ x, !ssbs x !!⌜diag θ⌝ !!⌜diag θ⌝ → !θ x” := by
  simp [fixpoint, substs_diag]

variable (T)

open LO.Arith
/-- Fixpoint Lemma -/
theorem main (θ : Semisentence ℒₒᵣ 1) :
    T ⊢! fixpoint θ ⟷ θ/[⌜fixpoint θ⌝] :=
  complete (oRing_consequence_of _ _ (fun M _ _ _ _ _ _ => by
    haveI : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_provably_subtheory M 𝐏𝐀⁻ T inferInstance (by assumption)
    have hssbs : ∀ σ π : Semisentence ℒₒᵣ 1, ∀ z,
        Evalbm M ![z, encode σ, encode π] ssbs ↔ z = encode (σ/[(⌜π⌝ : Semiterm ℒₒᵣ Empty 0)]) := by
      simpa [goedelNumber'_def, Arith.numeral_eq_natCast, models_iff, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      fun σ π => consequence_iff'.mp (sound₀! (ssbs_spec (T := T) σ π)) M
    simp[models_iff, Semiformula.eval_substs, Matrix.comp_vecCons']
    suffices Evalbm M ![] (fixpoint θ) ↔ Evalbm M ![encode (fixpoint θ)] θ by
      simpa [goedelNumber'_def, Arith.numeral_eq_natCast, Matrix.constant_eq_singleton] using this
    calc
      Evalbm M ![] (fixpoint θ)
      ↔ ∀ z, Evalbm M ![z, encode (diag θ), encode (diag θ)] ssbs → Evalbm M ![z] θ := by simp [goedelNumber'_def,
                                                                                            fixpoint_eq, Semiformula.eval_rew,
                                                                                            Function.comp, Matrix.comp_vecCons',
                                                                                            Matrix.constant_eq_vec₂,
                                                                                            Arith.numeral_eq_natCast,
                                                                                            Matrix.constant_eq_singleton]
    _ ↔ Evalbm M ![encode “!(diag θ) !!(⌜diag θ⌝ : Semiterm ℒₒᵣ Empty 0)”] θ        := by simp [hssbs]
    _ ↔ Evalbm M ![encode (fixpoint θ)] θ                                           := by rfl))

end

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ≼ T] [𝐏𝐀⁻ ≼ T] [SigmaOneSound T]

section ProvableSentence

variable {L : Language.{u}} [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]
  [(k : ℕ) → Primcodable (L.Func k)] [(k : ℕ) → Primcodable (L.Rel k)]
  [UniformlyPrimcodable L.Func] [UniformlyPrimcodable L.Rel]

noncomputable def provableSentence (U : Theory L) : Semisentence ℒₒᵣ 1 := pred (U ⊢! ·)

theorem provableSentence_representation {U : Theory L} [DecidablePred U] [Theory.Computable U] {σ : Sentence L} :
    T ⊢! (provableSentence U)/[⌜σ⌝] ↔ U ⊢! σ := by
  simpa using pred_representation (T := T) (provable_RePred U) (x := σ)

end ProvableSentence

open SelfReference

variable (T)

/-- Gödel Sentence $G$ -/
noncomputable def goedel : Sentence ℒₒᵣ := fixpoint (~provableSentence T)

local notation "G" => goedel T

lemma goedel_spec : T ⊢! G ⟷ ~(provableSentence T)/[⌜G⌝] := by
  simpa using SelfReference.main T (~provableSentence T)

variable [DecidablePred T] [Theory.Computable T]

open LO.System

theorem godel_independent : System.Undecidable T G := by
  suffices ¬(T ⊢! G ∨ T ⊢! ~G) by
    simpa[System.Undecidable, not_or] using this
  rintro (H | H)
  · have h₁ : T ⊢! ~(provableSentence T)/[⌜G⌝] := System.and_left! (goedel_spec T) ⨀ H
    have h₂ : T ⊢! (provableSentence T)/[⌜G⌝]  := by simpa using (provableSentence_representation (L := ℒₒᵣ)).mpr H
    exact (Gentzen.inconsistent_of_provable_and_refutable! h₂ h₁).not_con (consistent_of_sigmaOneSound T)
  · have : T ⊢! ~G ⟷ (provableSentence T)/[⌜G⌝] := Gentzen.not_contra! (goedel_spec T)
    have : T ⊢! (provableSentence T)/[⌜G⌝] := System.and_left! this ⨀ H
    have : T ⊢! G := (provableSentence_representation (L := ℒₒᵣ)).mp this
    exact (Gentzen.inconsistent_of_provable_and_refutable! this H).not_con (consistent_of_sigmaOneSound T)

theorem incomplete : ¬System.Complete T := System.incomplete_iff_exists_undecidable.mpr ⟨G, godel_independent T⟩

lemma not_disjunctive : ¬Disjunctive T := by apply iff_complete_disjunctive.not.mp $ incomplete T

end SelfReference

end LO.FirstOrder.Arith.FirstIncompleteness
