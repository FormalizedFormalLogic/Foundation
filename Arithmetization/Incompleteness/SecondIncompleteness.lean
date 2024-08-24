import Arithmetization.Incompleteness.D3

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

variable {B : Theory ℒₒᵣ} [𝐄𝐐 ≼ B] [𝐈𝚺₁ ≼ B]

section Diagonalization

def diag (θ : Semisentence ℒₒᵣ 1) : Semisentence ℒₒᵣ 1 := “x | ∀ y, !ssnum y x x → !θ y”

def fixpoint (θ : Semisentence ℒₒᵣ 1) : Sentence ℒₒᵣ := (diag θ)/[⌜diag θ⌝]

lemma substs_diag (θ σ : Semisentence ℒₒᵣ 1) :
    “!(diag θ) !!(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)” = “∀ x, !ssnum x !!⌜σ⌝ !!⌜σ⌝ → !θ x” := by
  simp [goedelNumber'_def, diag, Rew.q_substs, ←Rew.hom_comp_app, Rew.substs_comp_substs]

lemma fixpoint_eq (θ : Semisentence ℒₒᵣ 1) :
    fixpoint θ = “∀ x, !ssnum x !!⌜diag θ⌝ !!⌜diag θ⌝ → !θ x” := by
  simp [fixpoint, substs_diag]

theorem main (θ : Semisentence ℒₒᵣ 1) :
    B ⊢! fixpoint θ ⟷ θ/[⌜fixpoint θ⌝] :=
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ B inferInstance inferInstance
    simp [models_iff]
    let Θ : V → Prop := fun x ↦ Semiformula.Evalbm V ![x] θ
    calc
      V ⊧/![] (fixpoint θ)
      ↔ Θ (substNumeral ⌜diag θ⌝ ⌜diag θ⌝) := by simp [fixpoint_eq]
    _ ↔ Θ ⌜fixpoint θ⌝ := by simp [substNumeral_app_quote_quote]; rfl

end Diagonalization

section

variable (T : Theory ℒₒᵣ) [T.Δ₁Definable]

abbrev _root_.LO.FirstOrder.Theory.boxₐ (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := T.provableₐ/[⌜σ⌝]

abbrev _root_.LO.FirstOrder.Theory.consistentₐ : Sentence ℒₒᵣ := ~T.boxₐ ⊥

def _root_.LO.FirstOrder.Theory.goedel : Sentence ℒₒᵣ := fixpoint (~T.provableₐ)

end

section

variable {B : Theory ℒₒᵣ} [𝐄𝐐 ≼ B] [𝐈𝚺₁ ≼ B] {T : Theory ℒₒᵣ} [T.Δ₁Definable]

theorem provableₐ_D1 {σ} : T ⊢! σ → B ⊢! T.boxₐ σ := by
  intro h
  apply complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ B inferInstance inferInstance
    simpa [models_iff] using provableₐ_of_provable h

theorem provable_D2 {σ π} : B ⊢! T.boxₐ (σ ⟶ π) ⟶ T.boxₐ σ ⟶ T.boxₐ π :=
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ B inferInstance inferInstance
    simp [models_iff]
    intro hσπ hσ
    exact provableₐ_iff.mpr <| (by simpa using provableₐ_iff.mp hσπ) ⨀ provableₐ_iff.mp hσ

theorem provableₐ_sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    B ⊢! σ ⟶ T.boxₐ σ :=
  complete <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ B inferInstance inferInstance
    simpa [models_iff] using sigma₁_complete hσ

theorem provableₐ_D3 {σ : Sentence ℒₒᵣ} :
    B ⊢! T.boxₐ σ ⟶ T.boxₐ (T.boxₐ σ) := provableₐ_sigma₁_complete (by simp)

end

end LO.FirstOrder.Arith

end
