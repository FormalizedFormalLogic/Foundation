--import Logic.Logic.HilbertStyle
import Logic.FirstOrder.Arith.Representation
import Logic.FirstOrder.Computability.Calculus
import Logic.AutoProver.Prover

namespace LO

namespace FirstOrder

namespace Arith

namespace SelfReference

variable {T : Theory ℒₒᵣ} [𝐄𝐪 ≾ T] [𝐏𝐀⁻ ≾ T] [SigmaOneSound T]

open Encodable Semiformula

noncomputable def ssbs : Semisentence ℒₒᵣ 3 :=
  graphTotal₂ (fun (σ π : Semisentence ℒₒᵣ 1) ↦ σ/[(⸢π⸣ : Semiterm ℒₒᵣ Empty 0)])

lemma ssbs_spec (σ π : Semisentence ℒₒᵣ 1) :
    T ⊢! ∀' (ssbs/[#0, ⸢σ⸣, ⸢π⸣] ⟷ “#0 = !!⸢σ/[(⸢π⸣ : Semiterm ℒₒᵣ Empty 0)]⸣”) :=
  representation_computable₂ T (f := fun (σ π : Semisentence ℒₒᵣ 1) ↦ σ/[(⸢π⸣ : Semiterm ℒₒᵣ Empty 0)])
    (Primrec₂.to_comp <| (Semiformula.substs₁_primrec (L := ℒₒᵣ)).comp₂
      ((Semiterm.Operator.const_primrec (L := ℒₒᵣ)).comp₂ <|
        (Semiterm.Operator.numeral_primrec (L := ℒₒᵣ)).comp₂ $ Primrec.encode.comp₂ .right) <|
        .left) σ π

noncomputable def diag (θ : Semisentence ℒₒᵣ 1) : Semisentence ℒₒᵣ 1 :=
  ∀' (ssbs/[#0, #1, #1] ⟶ θ/[#0])

noncomputable def fixpoint (θ : Semisentence ℒₒᵣ 1) : Sentence ℒₒᵣ :=
  ∀' (ssbs/[#0, ⸢diag θ⸣, ⸢diag θ⸣] ⟶ θ/[#0])

lemma substs_diag (θ σ : Semisentence ℒₒᵣ 1) :
    (diag θ)/[(⸢σ⸣ : Semiterm ℒₒᵣ Empty 0)] = ∀' (ssbs/[#0, ⸢σ⸣, ⸢σ⸣] ⟶ θ/[#0]) := by
  simp[diag, Rew.q_substs, ←Rew.hom_comp_app, Rew.substs_comp_substs]

variable (T)

/-- Fixpoint Lemma -/
theorem main (θ : Semisentence ℒₒᵣ 1) :
    T ⊢! fixpoint θ ⟷ θ/[⸢fixpoint θ⸣] :=
  Complete.consequence_iff_provable.mp (oRing_consequence_of _ _ (fun M _ _ _ _ _ _ => by
    haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_subtheory (T₁ := T) M (Semantics.ofSystemSubtheory _ _)
    have hssbs : ∀ σ π : Semisentence ℒₒᵣ 1, ∀ z,
        PVal! M ![z, encode σ, encode π] ssbs ↔ z = encode (σ/[(⸢π⸣ : Semiterm ℒₒᵣ Empty 0)]) := by
      simpa[models_iff, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      fun σ π => consequence_iff'.mp (Sound.sound! (ssbs_spec (T := T) σ π)) M
    simp[models_iff, Semiformula.eval_substs, Matrix.comp_vecCons']
    suffices : PVal! M ![] (fixpoint θ) ↔ PVal! M ![encode (fixpoint θ)] θ
    · simpa[Matrix.constant_eq_singleton] using this
    calc
      PVal! M ![] (fixpoint θ)
      ↔ ∀ z, PVal! M ![z, encode (diag θ), encode (diag θ)] ssbs → PVal! M ![z] θ := by simp[fixpoint, Semiformula.eval_rew,
                                                                                            Function.comp, Matrix.comp_vecCons',
                                                                                            Matrix.constant_eq_vec₂,
                                                                                            Matrix.constant_eq_singleton]
    _ ↔ PVal! M ![encode $ (diag θ)/[(⸢diag θ⸣ : Semiterm ℒₒᵣ Empty 0)]] θ         := by simp[hssbs]
    _ ↔ PVal! M ![encode $ ∀' (ssbs/[#0, ⸢diag θ⸣, ⸢diag θ⸣] ⟶ θ/[#0])] θ         := by rw[substs_diag]
    _ ↔ PVal! M ![encode (fixpoint θ)] θ                                           := by rfl))

end SelfReference

namespace FirstIncompletenessBySelfReference

variable {T : Theory ℒₒᵣ} [𝐄𝐪 ≾ T] [𝐏𝐀⁻ ≾ T] [SigmaOneSound T]

section ProvableSentence

variable {L : Language.{u}} [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]
  [(k : ℕ) → Primcodable (L.Func k)] [(k : ℕ) → Primcodable (L.Rel k)]
  [UniformlyPrimcodable L.Func] [UniformlyPrimcodable L.Rel]

noncomputable def provableSentence (U : Theory L) : Semisentence ℒₒᵣ 1 := pred (U ⊢! ·)

theorem provableSentence_representation {U : Theory L} [DecidablePred U] [Theory.Computable U] {σ : Sentence L} :
    T ⊢! (provableSentence U)/[⸢σ⸣] ↔ U ⊢! σ := by
  simpa using pred_representation (T := T) (provable_RePred U) (x := σ)

end ProvableSentence

open SelfReference

variable (T)

/-- Gödel Sentence $G$ -/
noncomputable def goedel : Sentence ℒₒᵣ := fixpoint (~provableSentence T)

local notation "G" => goedel T

lemma goedel_spec : T ⊢! G ⟷ ~(provableSentence T)/[⸢G⸣] := by
  simpa using SelfReference.main T (~provableSentence T)

variable [DecidablePred T] [Theory.Computable T]

theorem godel_independent : System.Independent T G := by
  suffices : ¬(T ⊢! G ∨ T ⊢! ~G)
  · simpa[System.Independent, not_or] using this
  rintro (H | H)
  · have h₁ : T ⊢! ~(provableSentence T)/[⸢G⸣] := by prover [goedel_spec T, H]
    have h₂ : T ⊢! (provableSentence T)/[⸢G⸣]  := by simpa using (provableSentence_representation (L := ℒₒᵣ)).mpr H
    exact Gentzen.inconsistent_of_provable_and_refutable' h₂ h₁ (consistent_of_sigmaOneSound T)
  · have : T ⊢! ~G ⟷ (provableSentence T)/[⸢G⸣] := by prover [goedel_spec T]
    have : T ⊢! (provableSentence T)/[⸢G⸣] := by prover [this, H]
    have : T ⊢! G := (provableSentence_representation (L := ℒₒᵣ)).mp this
    exact Gentzen.inconsistent_of_provable_and_refutable' this H (consistent_of_sigmaOneSound T)

theorem main : ¬System.Complete T := System.incomplete_iff_exists_independent.mpr ⟨G, godel_independent T⟩

end FirstIncompletenessBySelfReference

end Arith

end FirstOrder

end LO
