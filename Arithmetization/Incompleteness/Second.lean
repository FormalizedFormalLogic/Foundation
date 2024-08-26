import Arithmetization.Incompleteness.D3
import Logic.Logic.HilbertStyle.Gentzen
import Logic.Logic.HilbertStyle.Supplemental

namespace LO.System

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [System F S] {𝓢 : S} [System.Classical 𝓢]

lemma inconsistent_of_provable_of_unprovable {p : F}
    (hp : 𝓢 ⊢! p) (hn : 𝓢 ⊢! ~p) : Inconsistent 𝓢 := by
  have : 𝓢 ⊢! p ⟶ ⊥ := neg_equiv'!.mp hn
  intro q; exact efq! ⨀ (this ⨀ hp)

end LO.System

noncomputable section

open Classical

namespace LO.Arith.Formalized

open LO.FirstOrder LO.FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

def substNumeral (p x : V) : V := ⌜ℒₒᵣ⌝.substs₁ (numeral x) p

lemma substNumeral_app_quote (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
    substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[‘↑n’] : Sentence ℒₒᵣ)⌝ := by
  simp [substNumeral]
  let w : Fin 1 → Semiterm ℒₒᵣ Empty 0 := ![‘↑n’]
  have : ?[numeral (n : V)] = (⌜fun i : Fin 1 ↦ ⌜w i⌝⌝ : V) := nth_ext' 1 (by simp) (by simp) (by simp)
  rw [Language.substs₁, this, substs_quote' (L := ℒₒᵣ)]

lemma substNumeral_app_quote_quote (σ π : Semisentence ℒₒᵣ 1) :
    substNumeral (⌜σ⌝ : V) ⌜π⌝ = ⌜(σ/[⌜π⌝] : Sentence ℒₒᵣ)⌝ := by
  simpa [coe_quote, quote_eq_encode] using substNumeral_app_quote σ ⌜π⌝

section

def _root_.LO.FirstOrder.Arith.ssnum : 𝚺₁.Semisentence 3 := .mkSigma
  “y p x | ∃ n, !numeralDef n x ∧ !p⌜ℒₒᵣ⌝.substs₁Def y n p” (by simp)

lemma substNumeral_defined : 𝚺₁-Function₂ (substNumeral : V → V → V) via ssnum := by
  intro v; simp [ssnum, ⌜ℒₒᵣ⌝.substs₁_defined.df.iff, substNumeral]

@[simp] lemma eval_ssnum (v) :
    Semiformula.Evalbm V v ssnum.val ↔ v 0 = substNumeral (v 1) (v 2) := substNumeral_defined.df.iff v

end

end LO.Arith.Formalized

namespace LO.FirstOrder.Arith

open LO.Arith LO.Arith.Formalized

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ≼ T] [𝐈𝚺₁ ≼ T]

section Diagonalization

def diag (θ : Semisentence ℒₒᵣ 1) : Semisentence ℒₒᵣ 1 := “x | ∀ y, !ssnum y x x → !θ y”

def fixpoint (θ : Semisentence ℒₒᵣ 1) : Sentence ℒₒᵣ := (diag θ)/[⌜diag θ⌝]

lemma substs_diag (θ σ : Semisentence ℒₒᵣ 1) :
    “!(diag θ) !!(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)” = “∀ x, !ssnum x !!⌜σ⌝ !!⌜σ⌝ → !θ x” := by
  simp [goedelNumber'_def, diag, Rew.q_substs, ←Rew.hom_comp_app, Rew.substs_comp_substs]

lemma fixpoint_eq (θ : Semisentence ℒₒᵣ 1) :
    fixpoint θ = “∀ x, !ssnum x !!⌜diag θ⌝ !!⌜diag θ⌝ → !θ x” := by
  simp [fixpoint, substs_diag]

theorem diagonal (θ : Semisentence ℒₒᵣ 1) :
    T ⊢! fixpoint θ ⟷ θ/[⌜fixpoint θ⌝] :=
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ T inferInstance inferInstance
    simp [models_iff]
    let Θ : V → Prop := fun x ↦ Semiformula.Evalbm V ![x] θ
    calc
      V ⊧/![] (fixpoint θ)
      ↔ Θ (substNumeral ⌜diag θ⌝ ⌜diag θ⌝) := by simp [fixpoint_eq]
    _ ↔ Θ ⌜fixpoint θ⌝                     := by simp [substNumeral_app_quote_quote]; rfl

end Diagonalization

section

variable (U : Theory ℒₒᵣ) [U.Delta1Definable]

abbrev _root_.LO.FirstOrder.Theory.bewₐ (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := U.provableₐ/[⌜σ⌝]

abbrev _root_.LO.FirstOrder.Theory.consistentₐ : Sentence ℒₒᵣ := ~U.bewₐ ⊥

def _root_.LO.FirstOrder.Theory.goedelₐ : Sentence ℒₒᵣ := fixpoint (~U.provableₐ)

end

section

variable {U : Theory ℒₒᵣ} [U.Delta1Definable]

theorem provableₐ_D1 {σ} : U ⊢! σ → T ⊢! U.bewₐ σ := by
  intro h
  apply complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance inferInstance
    simpa [models_iff] using provableₐ_of_provable h

theorem provableₐ_D2 {σ π} : T ⊢! U.bewₐ (σ ⟶ π) ⟶ U.bewₐ σ ⟶ U.bewₐ π :=
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance inferInstance
    simp [models_iff]
    intro hσπ hσ
    exact provableₐ_iff.mpr <| (by simpa using provableₐ_iff.mp hσπ) ⨀ provableₐ_iff.mp hσ

lemma provableₐ_sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    T ⊢! σ ⟶ U.bewₐ σ :=
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance inferInstance
    simpa [models_iff] using sigma₁_complete hσ

theorem provableₐ_D3 {σ : Sentence ℒₒᵣ} :
    T ⊢! U.bewₐ σ ⟶ U.bewₐ (U.bewₐ σ) := provableₐ_sigma₁_complete (by simp)

lemma goedel_iff_unprovable_goedel : T ⊢! U.goedelₐ ⟷ ~U.bewₐ U.goedelₐ := by
  simpa [Theory.goedelₐ, Theory.bewₐ] using diagonal (~U.provableₐ)

open LO.System LO.System.FiniteContext

lemma provableₐ_D2_context {Γ σ π} (hσπ : Γ ⊢[T]! U.bewₐ (σ ⟶ π)) (hσ : Γ ⊢[T]! U.bewₐ σ) :
    Γ ⊢[T]! U.bewₐ π := of'! provableₐ_D2 ⨀ hσπ ⨀ hσ

lemma provableₐ_D3_context {Γ σ} (hσπ : Γ ⊢[T]! U.bewₐ σ) : Γ ⊢[T]! U.bewₐ (U.bewₐ σ) := of'! provableₐ_D3 ⨀ hσπ


end

section

variable [T.Delta1Definable] (consistent : System.Consistent T)

open LO.System LO.System.FiniteContext

local notation "𝗚" => T.goedelₐ

local notation "𝗖𝗼𝗻" => T.consistentₐ

local prefix:max "□" => T.bewₐ

lemma goedel_unprovable : T ⊬! 𝗚 := by
  intro h
  have hp : T ⊢! □𝗚 := provableₐ_D1 h
  have hn : T ⊢! ~□𝗚 := and_left! goedel_iff_unprovable_goedel ⨀ h
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable hp hn) consistent

lemma consistent_iff_goedel : T ⊢! 𝗖𝗼𝗻 ⟷ 𝗚 := by
  apply iff_intro!
  · have bew_G : [~𝗚] ⊢[T]! □𝗚 := deductInv'! <| contra₂'! <| and_right! goedel_iff_unprovable_goedel
    have bew_not_bew_G : [~𝗚] ⊢[T]! □(~□𝗚) := by
      have : T ⊢! □(𝗚 ⟶ ~□𝗚) := provableₐ_D1 <| and_left! goedel_iff_unprovable_goedel
      exact provableₐ_D2_context (of'! this) bew_G
    have bew_bew_G : [~𝗚] ⊢[T]! □□𝗚 := provableₐ_D3_context bew_G
    have : [~𝗚] ⊢[T]! □⊥ :=
      provableₐ_D2_context (provableₐ_D2_context (of'! <| provableₐ_D1 <| efq_imply_not₁!) bew_not_bew_G) bew_bew_G
    exact contra₂'! (deduct'! this)
  · have : [□⊥] ⊢[T]! □𝗚 := by
      have : T ⊢! □(⊥ ⟶ 𝗚) := provableₐ_D1 efq!
      exact provableₐ_D2_context (of'! this) (by simp)
    have : [□⊥] ⊢[T]! ~𝗚 :=
      of'! (contra₁'! <| and_left! <| goedel_iff_unprovable_goedel) ⨀ this
    exact contra₁'! (deduct'! this)

lemma consistent_unprovable : T ⊬! 𝗖𝗼𝗻 := fun h ↦
  goedel_unprovable consistent <| and_left! consistent_iff_goedel ⨀ h

end

end LO.FirstOrder.Arith

end
