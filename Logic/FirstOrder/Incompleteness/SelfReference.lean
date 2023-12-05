import Logic.Logic.HilbertStyle
import Logic.FirstOrder.Arith.Representation
import Logic.FirstOrder.Computability.Calculus

namespace LO

namespace FirstOrder

namespace Arith

namespace SelfReference

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [SigmaOneSound T]

open Encodable Subformula

noncomputable def ssbs : Subsentence ℒₒᵣ 3 :=
  graphTotal₂ (fun (σ π : Subsentence ℒₒᵣ 1) => σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)])

lemma ssbs_spec (σ π : Subsentence ℒₒᵣ 1) :
    T ⊢! ∀' (ssbs/[#0, ⸢σ⸣, ⸢π⸣] ⟷ “#0 = !!⸢σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)]⸣”) :=
  representation_computable₂ T (f := fun (σ π : Subsentence ℒₒᵣ 1) => σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)])
    (Primrec₂.to_comp <| (Subformula.substs₁_primrec (L := ℒₒᵣ)).comp₂
      ((Subterm.Operator.const_primrec (L := ℒₒᵣ)).comp₂ <|
        (Subterm.Operator.numeral_primrec (L := ℒₒᵣ)).comp₂ $ Primrec.encode.comp₂ .right) <|
        .left) σ π

noncomputable def diag (θ : Subsentence ℒₒᵣ 1) : Subsentence ℒₒᵣ 1 :=
  ∀' (ssbs/[#0, #1, #1] ⟶ θ/[#0])

noncomputable def fixpoint (θ : Subsentence ℒₒᵣ 1) : Sentence ℒₒᵣ :=
  ∀' (ssbs/[#0, ⸢diag θ⸣, ⸢diag θ⸣] ⟶ θ/[#0])

lemma substs_diag (θ σ : Subsentence ℒₒᵣ 1) :
    (diag θ)/[(⸢σ⸣ : Subterm ℒₒᵣ Empty 0)] = ∀' (ssbs/[#0, ⸢σ⸣, ⸢σ⸣] ⟶ θ/[#0]) := by
  simp[diag, Rew.q_substs, ←Rew.hom_comp_app, Rew.substs_comp_substs]

variable (T)

theorem main (θ : Subsentence ℒₒᵣ 1) :
    T ⊢! fixpoint θ ⟷ θ/[⸢fixpoint θ⸣] :=
  Complete.consequence_iff_provable.mp (consequence_of _ _ (fun M _ _ _ _ _ => by
    haveI : Theory.Mod M (Theory.PAminus ℒₒᵣ) :=
      Theory.Mod.of_subtheory (T₁ := T) M (Semantics.ofSystemSubtheory _ _)
    have hssbs : ∀ σ π : Subsentence ℒₒᵣ 1, ∀ z,
        PVal! M ![z, encode σ, encode π] ssbs ↔ z = encode (σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)]) := by
      simpa[models_iff, Subformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      fun σ π => consequence_iff'.mp (Sound.sound' (ssbs_spec (T := T) σ π)) M
    simp[models_iff, Subformula.eval_substs, Matrix.comp_vecCons']
    suffices : PVal! M ![] (fixpoint θ) ↔ PVal! M ![encode (fixpoint θ)] θ
    · simpa[Matrix.constant_eq_singleton] using this
    calc
      PVal! M ![] (fixpoint θ)
      ↔ ∀ z, PVal! M ![z, encode (diag θ), encode (diag θ)] ssbs → PVal! M ![z] θ := by simp[fixpoint, Subformula.eval_rew,
                                                                                            Function.comp, Matrix.comp_vecCons',
                                                                                            Matrix.constant_eq_vec₂,
                                                                                            Matrix.constant_eq_singleton]
    _ ↔ PVal! M ![encode $ (diag θ)/[(⸢diag θ⸣ : Subterm ℒₒᵣ Empty 0)]] θ         := by simp[hssbs]
    _ ↔ PVal! M ![encode $ ∀' (ssbs/[#0, ⸢diag θ⸣, ⸢diag θ⸣] ⟶ θ/[#0])] θ         := by rw[substs_diag]
    _ ↔ PVal! M ![encode (fixpoint θ)] θ                                           := by rfl))

end SelfReference

namespace FirstIncompletenessBySelfReference

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [SigmaOneSound T]

section ProvableSentence

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
  [(k : ℕ) → Primcodable (L.func k)] [(k : ℕ) → Primcodable (L.rel k)]
  [UniformlyPrimcodable L.func] [UniformlyPrimcodable L.rel]

noncomputable def provableSentence (U : Theory L) : Subsentence ℒₒᵣ 1 := pred (U ⊢! ·)

theorem provableSentence_representation {U : Theory L} [DecidablePred U] [Theory.Computable U] {σ : Sentence L} :
    T ⊢! (provableSentence U)/[⸢σ⸣] ↔ U ⊢! σ := by
  simpa using pred_representation (T := T) (provable_RePred U) (x := σ)

end ProvableSentence

open SelfReference

variable (T)

noncomputable def goedel : Sentence ℒₒᵣ := fixpoint (~provableSentence T)

local notation "G" => goedel T

lemma goedel_spec : T ⊢! G ⟷ ~(provableSentence T)/[⸢G⸣] := by
  simpa using SelfReference.main T (~provableSentence T)

-- TODO: proof this via (T ⊢ p ⟷ q) → (T ⊢ ~p ⟷ ~q)
lemma goedel_spec' : T ⊢! ~G ⟷ (provableSentence T)/[⸢G⸣] :=
  Complete.consequence_iff_provable.mp (consequence_of _ _ (fun M _ _ _ _ _ => by
    have : M ⊧ G ↔ ¬M ⊧ ((provableSentence T)/[⸢G⸣]) :=
      by simpa using consequence_iff'.mp (Sound.sound' (goedel_spec T)) M
    simp[this]))

variable [DecidablePred T] [Theory.Computable T]
open System.Intuitionistic

theorem godel_independent : System.Independent T G := by
  suffices : ¬(T ⊢! G ∨ T ⊢! ~G)
  · simpa[System.Independent, not_or] using this
  rintro (H | H)
  · have h₁ : T ⊢! ~(provableSentence T)/[⸢G⸣] := by simpa using and_left (goedel_spec T) ⨀ H
    have h₂ : T ⊢! (provableSentence T)/[⸢G⸣]  := by simpa using (provableSentence_representation (L := ℒₒᵣ)).mpr H
    exact inconsistent_of_provable_and_refutable' h₂ h₁ (consistent_of_sigmaOneSound T)
  · have : T ⊢! (provableSentence T)/[⸢G⸣] := by simpa using and_left (goedel_spec' T) ⨀ H
    have : T ⊢! G := (provableSentence_representation (L := ℒₒᵣ)).mp this
    exact inconsistent_of_provable_and_refutable' this H (consistent_of_sigmaOneSound T)

theorem main : ¬System.Complete T := System.incomplete_iff_exists_independent.mpr ⟨G, godel_independent T⟩

end FirstIncompletenessBySelfReference

end Arith

end FirstOrder

end LO
