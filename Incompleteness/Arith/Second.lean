import Incompleteness.Arith.D3
import Foundation.Logic.HilbertStyle.Supplemental
import Incompleteness.ToFoundation.Basic

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

section

variable (U : Theory ℒₒᵣ) [U.Delta1Definable]

abbrev _root_.LO.FirstOrder.Theory.bewₐ (σ : Sentence ℒₒᵣ) : Sentence ℒₒᵣ := U.provableₐ/[⌜σ⌝]

abbrev _root_.LO.FirstOrder.Theory.consistentₐ : Sentence ℒₒᵣ := ∼U.bewₐ ⊥

def _root_.LO.FirstOrder.Theory.goedelₐ : Sentence ℒₒᵣ := fixpoint (∼U.provableₐ)

end

section

variable {U : Theory ℒₒᵣ} [U.Delta1Definable]

theorem provableₐ_D1 {σ} : U ⊢!. σ → T ⊢!. U.bewₐ σ := by
  intro h
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  apply complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using provableₐ_of_provable (T := U) (V := V) h

theorem provableₐ_D2 {σ π} : T ⊢!. U.bewₐ (σ ➝ π) ➝ U.bewₐ σ ➝ U.bewₐ π :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simp [models_iff]
    intro hσπ hσ
    exact provableₐ_iff.mpr <| (by simpa using provableₐ_iff.mp hσπ) ⨀ provableₐ_iff.mp hσ

lemma provableₐ_sigma₁_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    T ⊢!. σ ➝ U.bewₐ σ :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete (T := T) <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V _ T inferInstance
    simpa [models_iff] using sigma₁_complete (T := U) (V := V) hσ

theorem provableₐ_D3 {σ : Sentence ℒₒᵣ} :
    T ⊢!. U.bewₐ σ ➝ U.bewₐ (U.bewₐ σ) := provableₐ_sigma₁_complete (by simp)

lemma goedel_iff_unprovable_goedel : T ⊢!. U.goedelₐ ⭤ ∼U.bewₐ U.goedelₐ := by
  simpa [Theory.goedelₐ, Theory.bewₐ] using diagonal (∼U.provableₐ)

open LO.Entailment LO.Entailment.FiniteContext

lemma provableₐ_D2_context {Γ σ π} (hσπ : Γ ⊢[T.alt]! (U.bewₐ (σ ➝ π))) (hσ : Γ ⊢[T.alt]! U.bewₐ σ) :
    Γ ⊢[T.alt]! U.bewₐ π := of'! provableₐ_D2 ⨀ hσπ ⨀ hσ

lemma provableₐ_D3_context {Γ σ} (hσπ : Γ ⊢[T.alt]! U.bewₐ σ) : Γ ⊢[T.alt]! U.bewₐ (U.bewₐ σ) := of'! provableₐ_D3 ⨀ hσπ

variable [ℕ ⊧ₘ* T] [𝐑₀ ⪯ U]

omit [𝐈𝚺₁ ⪯ T] in
lemma provableₐ_sound {σ} : T ⊢!. U.bewₐ σ → U ⊢! ↑σ := by
  intro h
  have : U.Provableₐ (⌜σ⌝ : ℕ) := by simpa [models₀_iff] using consequence_iff.mp (sound! (T := T) h) ℕ inferInstance
  have : U + 𝐑₀' ⊢! ↑σ := Language.Theory.Provable.sound₀ this
  exact add_cobhamR0'.mpr this

lemma provableₐ_complete {σ} : U ⊢! ↑σ ↔ T ⊢!. U.bewₐ σ := ⟨provableₐ_D1, provableₐ_sound⟩

end

section

variable (T)

variable [T.Delta1Definable]

open LO.Entailment LO.Entailment.FiniteContext

local notation "𝗚" => T.goedelₐ

local notation "𝗖𝗼𝗻" => T.consistentₐ

local prefix:max "□" => T.bewₐ

lemma goedel_unprovable [Entailment.Consistent T] : T ⊬ ↑𝗚 := by
  intro h
  have hp : T ⊢! ↑□𝗚 := provableₐ_D1 h
  have hn : T ⊢! ∼↑□𝗚 := by simpa [provable₀_iff] using and_left! goedel_iff_unprovable_goedel ⨀ h
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable hp hn) inferInstance

lemma not_goedel_unprovable [ℕ ⊧ₘ* T] : T ⊬ ∼↑𝗚 := fun h ↦ by
  haveI : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  have : T ⊢!. □𝗚 := Entailment.contra₂'! (and_right! goedel_iff_unprovable_goedel) ⨀ (by simpa [provable₀_iff] using h)
  have : T ⊢! ↑𝗚 := provableₐ_sound this
  exact not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable this h)
    (Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩)

lemma consistent_iff_goedel : T ⊢! ↑𝗖𝗼𝗻 ⭤ ↑𝗚 := by
  apply iff_intro!
  · have bew_G : [∼𝗚] ⊢[T.alt]! □𝗚 := deductInv'! <| contra₂'! <| and_right! goedel_iff_unprovable_goedel
    have bew_not_bew_G : [∼𝗚] ⊢[T.alt]! □(∼□𝗚) := by
      have : T ⊢!. □(𝗚 ➝ ∼□𝗚) := provableₐ_D1 <| and_left! goedel_iff_unprovable_goedel
      exact provableₐ_D2_context (of'! this) bew_G
    have bew_bew_G : [∼𝗚] ⊢[T.alt]! □□𝗚 := provableₐ_D3_context bew_G
    have : [∼𝗚] ⊢[T.alt]! □⊥ :=
      provableₐ_D2_context (provableₐ_D2_context (of'! <| provableₐ_D1 <| efq_imply_not₁!) bew_not_bew_G) bew_bew_G
    simpa [provable₀_iff] using contra₂'! (deduct'! this)
  · have : [□⊥] ⊢[T.alt]! □𝗚 := by
      have : T ⊢!. □(⊥ ➝ 𝗚) := provableₐ_D1 efq!
      exact provableₐ_D2_context (of'! this) (by simp)
    have : [□⊥] ⊢[T.alt]! ∼𝗚 :=
      of'! (contra₁'! <| and_left! <| goedel_iff_unprovable_goedel) ⨀ this
    simpa [provable₀_iff] using  contra₁'! (deduct'! this)

/-- Gödel's Second Incompleteness Theorem-/
theorem goedel_second_incompleteness [Entailment.Consistent T] : T ⊬ ↑𝗖𝗼𝗻 := fun h ↦
  goedel_unprovable T <| and_left! (consistent_iff_goedel T) ⨀ h

theorem inconsistent_unprovable [ℕ ⊧ₘ* T] : T ⊬ ∼↑𝗖𝗼𝗻 := fun h ↦
  not_goedel_unprovable T <| contra₀'! (and_right! (consistent_iff_goedel T)) ⨀ h

theorem inconsistent_undecidable [ℕ ⊧ₘ* T] : Entailment.Undecidable T ↑𝗖𝗼𝗻 := by
  haveI : Consistent T := Sound.consistent_of_satisfiable ⟨_, (inferInstance : ℕ ⊧ₘ* T)⟩
  constructor
  · exact goedel_second_incompleteness T
  · exact inconsistent_unprovable T

end

end LO.FirstOrder.Arith

end
