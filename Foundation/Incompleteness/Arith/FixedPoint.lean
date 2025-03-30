import Foundation.Incompleteness.Arith.D3
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Incompleteness.ToFoundation.Basic

noncomputable section

open Classical

namespace LO.Arith.Formalized

open LO.FirstOrder LO.FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

def substNumeral (φ x : V) : V := ⌜ℒₒᵣ⌝.substs₁ (numeral x) φ

lemma substNumeral_app_quote (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
    substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[‘↑n’] : Sentence ℒₒᵣ)⌝ := by
  dsimp [substNumeral]
  let w : Fin 1 → Semiterm ℒₒᵣ Empty 0 := ![‘↑n’]
  have : ?[numeral (n : V)] = (⌜fun i : Fin 1 ↦ ⌜w i⌝⌝ : V) := nth_ext' 1 (by simp) (by simp) (by simp [w])
  rw [Language.substs₁, this, quote_substs' (L := ℒₒᵣ)]

lemma substNumeral_app_quote_quote (σ π : Semisentence ℒₒᵣ 1) :
    substNumeral (⌜σ⌝ : V) ⌜π⌝ = ⌜(σ/[⌜π⌝] : Sentence ℒₒᵣ)⌝ := by
  simpa [coe_quote, quote_eq_encode] using substNumeral_app_quote σ ⌜π⌝

def substNumerals (φ : V) (v : Fin k → V) : V := ⌜ℒₒᵣ⌝.substs ⌜fun i ↦ numeral (v i)⌝ φ

lemma substNumerals_app_quote (σ : Semisentence ℒₒᵣ k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.substs (fun i ↦ ‘↑(v i)’)) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  dsimp [substNumerals]
  let w : Fin k → Semiterm ℒₒᵣ Empty 0 := fun i ↦ ‘↑(v i)’
  have : ⌜fun i ↦ numeral (v i : V)⌝ = (⌜fun i : Fin k ↦ ⌜w i⌝⌝ : V) := by
    apply nth_ext' (k : V) (by simp) (by simp)
    intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simp [w]
  rw [this, quote_substs' (L := ℒₒᵣ)]

lemma substNumerals_app_quote_quote (σ : Semisentence ℒₒᵣ k) (π : Fin k → Semisentence ℒₒᵣ k) :
    substNumerals (⌜σ⌝ : V) (fun i ↦ ⌜π i⌝) = ⌜((Rew.substs (fun i ↦ ⌜π i⌝)) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  simpa [coe_quote, quote_eq_encode] using substNumerals_app_quote σ (fun i ↦ ⌜π i⌝)

section

def _root_.LO.FirstOrder.Arith.ssnum : 𝚺₁.Semisentence 3 := .mkSigma
  “y p x. ∃ n, !numeralDef n x ∧ !p⌜ℒₒᵣ⌝.substs₁Def y n p” (by simp)

lemma substNumeral_defined : 𝚺₁-Function₂ (substNumeral : V → V → V) via ssnum := by
  intro v; simp [ssnum, ⌜ℒₒᵣ⌝.substs₁_defined.df.iff, substNumeral]

@[simp] lemma eval_ssnum (v) :
    Semiformula.Evalbm V v ssnum.val ↔ v 0 = substNumeral (v 1) (v 2) := substNumeral_defined.df.iff v

def _root_.LO.FirstOrder.Arith.ssnums : 𝚺₁.Semisentence (k + 2) := .mkSigma
  “y p. ∃ n, !lenDef ↑k n ∧
    (⋀ i, ∃ z, !nthDef z n ↑(i : Fin k) ∧ !numeralDef z #i.succ.succ.succ.succ) ∧
    !p⌜ℒₒᵣ⌝.substsDef y n p” (by simp)

lemma substNumerals_defined :
    Arith.HierarchySymbol.DefinedFunction (fun v ↦ substNumerals (v 0) (v ·.succ) : (Fin (k + 1) → V) → V) ssnums := by
  intro v
  suffices
    (v 0 = ⌜ℒₒᵣ⌝.substs ⌜fun (i : Fin k) ↦ numeral (v i.succ.succ)⌝ (v 1)) ↔
      ∃ x, ↑k = len x ∧ (∀ (i : Fin k), x.[↑↑i] = numeral (v i.succ.succ)) ∧ v 0 = ⌜ℒₒᵣ⌝.substs x (v 1) by
    simpa [ssnums, ⌜ℒₒᵣ⌝.substs_defined.df.iff, substNumerals, numeral_eq_natCast] using this
  constructor
  · intro e
    refine ⟨_, by simp, by intro i; simp, e⟩
  · rintro ⟨w, hk, h, e⟩
    have : w = ⌜fun (i : Fin k) ↦ numeral (v i.succ.succ)⌝ := nth_ext' (k : V) hk.symm (by simp)
      (by intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩; simp [h])
    rcases this; exact e

@[simp] lemma eval_ssnums (v : Fin (k + 2) → V) :
    Semiformula.Evalbm V v ssnums.val ↔ v 0 = substNumerals (v 1) (fun i ↦ v i.succ.succ) := substNumerals_defined.df.iff v

end

end LO.Arith.Formalized

namespace LO.FirstOrder.Arith

open LO.Arith LO.Arith.Formalized

variable {T : Theory ℒₒᵣ} [𝐈𝚺₁ ⪯ T]

section Diagonalization

def diag (θ : Semisentence ℒₒᵣ 1) : Semisentence ℒₒᵣ 1 := “x. ∀ y, !ssnum y x x → !θ y”

def fixpoint (θ : Semisentence ℒₒᵣ 1) : Sentence ℒₒᵣ := (diag θ)/[⌜diag θ⌝]

lemma substs_diag (θ σ : Semisentence ℒₒᵣ 1) :
    “!(diag θ) !!(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)” = (“∀ x, !ssnum x !!⌜σ⌝ !!⌜σ⌝ → !θ x” : Sentence ℒₒᵣ) := by
  simp [goedelNumber'_def, diag, Rew.q_substs, ← TransitiveRewriting.comp_app, Rew.substs_comp_substs]

lemma fixpoint_eq (θ : Semisentence ℒₒᵣ 1) :
    fixpoint θ = (“∀ x, !ssnum x !!⌜diag θ⌝ !!⌜diag θ⌝ → !θ x” : Sentence ℒₒᵣ) := by
  simp [fixpoint, substs_diag]

theorem diagonal (θ : Semisentence ℒₒᵣ 1) :
    T ⊢!. fixpoint θ ⭤ θ/[⌜fixpoint θ⌝] :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ T inferInstance
    simp [models_iff]
    let Θ : V → Prop := fun x ↦ Semiformula.Evalbm V ![x] θ
    calc
      V ⊧/![] (fixpoint θ)
      ↔ Θ (substNumeral ⌜diag θ⌝ ⌜diag θ⌝) := by simp [Θ, fixpoint_eq]
    _ ↔ Θ ⌜fixpoint θ⌝                     := by simp [substNumeral_app_quote_quote]; rfl

end Diagonalization

section Multidiagonalization

/-- $\mathrm{diag}_i(\vec{x}) := (\forall \vec{y})\left[ \left(\bigwedge_j \mathrm{ssnums}(y_j, x_j, \vec{x})\right) \to \theta_i(\vec{y}) \right]$ -/
def multidiag (θ : Semisentence ℒₒᵣ k) : Semisentence ℒₒᵣ k :=
  ∀^[k] (
    (Matrix.conj fun j : Fin k ↦ (Rew.substs <| #(j.addCast k) :> #(j.addNat k) :> fun l ↦ #(l.addNat k)) ▹ ssnums.val) ➝
    (Rew.substs fun j ↦ #(j.addCast k)) ▹ θ)

def multifixpoint (θ : Fin k → Semisentence ℒₒᵣ k) (i : Fin k) : Sentence ℒₒᵣ := (Rew.substs fun j ↦ ⌜multidiag (θ j)⌝) ▹ (multidiag (θ i))

theorem multidiagonal (θ : Fin k → Semisentence ℒₒᵣ k) :
    T ⊢!. multifixpoint θ i ⭤ (Rew.substs fun j ↦ ⌜multifixpoint θ j⌝) ▹ (θ i) :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ T inferInstance
    suffices V ⊧/![] (multifixpoint θ i) ↔ V ⊧/(fun i ↦ ⌜multifixpoint θ i⌝) (θ i) by simpa [models_iff]
    let t : Fin k → V := fun i ↦ ⌜multidiag (θ i)⌝
    have ht : ∀ i, substNumerals (t i) t = ⌜multifixpoint θ i⌝ := by
      intro i; simp [t, multifixpoint, substNumerals_app_quote_quote]
    calc
      V ⊧/![] (multifixpoint θ i) ↔ V ⊧/t (multidiag (θ i))                 := by simp [t, multifixpoint]
      _                      ↔ V ⊧/(fun i ↦ substNumerals (t i) t) (θ i) := by simp [multidiag, ← funext_iff]
      _                      ↔ V ⊧/(fun i ↦ ⌜multifixpoint θ i⌝) (θ i) := by simp [ht]

end Multidiagonalization

end LO.FirstOrder.Arith
