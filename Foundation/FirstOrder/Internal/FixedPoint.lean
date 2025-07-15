import Foundation.FirstOrder.Internal.D1
import Foundation.Logic.HilbertStyle.Supplemental

open Classical

namespace LO.ISigma1.Metamath.InternalArithmetic

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

/-
lemma substNumeral_app_quote (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
    substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[↑n] : Sentence ℒₒᵣ)⌝ := by
  simp [substNumeral, Semiformula.empty_typed_quote_def,
    Rewriting.embedding_substs_eq_substs_coe₁, Matrix.constant_eq_singleton]

lemma substNumeral_app_quote_quote (σ π : Semisentence ℒₒᵣ 1) :
    substNumeral ⌜σ⌝ (⌜π⌝ : V) = ⌜(σ/[↑(⌜π⌝ : ℕ)] : Sentence ℒₒᵣ)⌝ := by
  simpa [Semiformula.coe_empty_quote_eq_quote] using substNumeral_app_quote (V := V) σ ⌜π⌝

noncomputable def substNumerals (φ : Semiformula V ℒₒᵣ k) (v : Fin k → V) : Formula V ℒₒᵣ :=
    φ.substs ((𝕹 ·)⨟ v)

lemma substNumerals_app_quote (σ : Semisentence ℒₒᵣ k) (v : Fin k → ℕ) :
    substNumerals (V := V) ⌜σ⌝ (v ·) = ⌜((Rew.substs (v ·)) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  simp [substNumerals, Semiformula.empty_typed_quote_def, Rewriting.embedding_substitute_eq_substitute_embedding]
  simp [Matrix.map, Function.comp_def]

lemma substNumerals_app_quote_quote (σ : Semisentence ℒₒᵣ k) (π : Fin k → Semisentence ℒₒᵣ k) :
    substNumerals (V := V) ⌜σ⌝ (fun i ↦ ↑(⌜π i⌝ : ℕ)) = ⌜((Rew.substs (fun i ↦ ↑(⌜π i⌝ : ℕ))) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  simpa [Semiformula.coe_empty_quote_eq_quote] using substNumerals_app_quote (V := V) σ (fun i ↦ ⌜π i⌝)


-/

noncomputable def substNumeral (φ x : V) : V := substs ℒₒᵣ ?[numeral x] φ

lemma substNumeral_app_quote (σ : Semisentence ℒₒᵣ 1) (n : ℕ) :
    substNumeral ⌜σ⌝ (n : V) = ⌜(σ/[↑n] : Sentence ℒₒᵣ)⌝ := by
  simp [substNumeral, Semiformula.empty_quote_def, Semiformula.quote_def,
    Rewriting.embedding_substs_eq_substs_coe₁]

lemma substNumeral_app_quote_quote (σ π : Semisentence ℒₒᵣ 1) :
    substNumeral ⌜σ⌝ (⌜π⌝ : V) = ⌜(σ/[↑(⌜π⌝ : ℕ)] : Sentence ℒₒᵣ)⌝ := by
  simpa [Semiformula.coe_empty_quote_eq_quote] using substNumeral_app_quote (V := V) σ ⌜π⌝

noncomputable def substNumerals (φ : V) (v : Fin k → V) : V := substs ℒₒᵣ (matrixToVec (fun i ↦ numeral (v i))) φ

lemma substNumerals_app_quote (σ : Semisentence ℒₒᵣ k) (v : Fin k → ℕ) :
    (substNumerals ⌜σ⌝ (v ·) : V) = ⌜((Rew.substs (fun i ↦ ↑(v i))) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  simp [substNumerals, Semiformula.empty_quote_def, Semiformula.quote_def,
    Rewriting.embedding_substitute_eq_substitute_embedding]
  rfl

lemma substNumerals_app_quote_quote (σ : Semisentence ℒₒᵣ k) (π : Fin k → Semisentence ℒₒᵣ k) :
    substNumerals (⌜σ⌝ : V) (fun i ↦ ⌜π i⌝) = ⌜((Rew.substs (fun i ↦ ↑(⌜π i⌝ : ℕ))) ▹ σ : Sentence ℒₒᵣ)⌝ := by
  simpa [Semiformula.coe_empty_quote_eq_quote] using substNumerals_app_quote (V := V) σ (fun i ↦ ⌜π i⌝)

section

def ssnum : 𝚺₁.Semisentence 3 := .mkSigma
  “y p x. ∃ n, !numeralGraph n x ∧ ∃ v, !consDef v n 0 ∧ !(substsGraph ℒₒᵣ) y v p”

lemma substNumeral.defined : 𝚺₁-Function₂ (substNumeral : V → V → V) via ssnum := by
  intro v; simp [ssnum, (substs.defined (L := ℒₒᵣ)).df.iff, substNumeral]

@[simp] lemma substNumeral.eval (v) :
    Semiformula.Evalbm V v ssnum.val ↔ v 0 = substNumeral (v 1) (v 2) := substNumeral.defined.df.iff v

def ssnums : 𝚺₁.Semisentence (k + 2) := .mkSigma
  “y p. ∃ n, !lenDef ↑k n ∧
    (⋀ i, ∃ z, !nthDef z n ↑(i : Fin k).val ∧ !numeralGraph z #i.succ.succ.succ.succ) ∧
    !(substsGraph ℒₒᵣ) y n p”

lemma substNumerals.defined :
    Arithmetic.HierarchySymbol.DefinedFunction (fun v ↦ substNumerals (v 0) (v ·.succ) : (Fin (k + 1) → V) → V) ssnums := by
  intro v
  unfold ssnums
  suffices
      v 0 = substs ℒₒᵣ (matrixToVec fun i ↦ numeral (v i.succ.succ)) (v 1) ↔
      ∃ x, ↑k = len x ∧ (∀ i : Fin k, x.[↑↑i] = numeral (v i.succ.succ)) ∧ v 0 = substs ℒₒᵣ x (v 1) by
    simpa [ssnums, substNumerals, (substs.defined (L := ℒₒᵣ)).df.iff, numeral_eq_natCast]
  constructor
  · intro h
    refine ⟨matrixToVec fun i ↦ numeral (v i.succ.succ), ?_⟩
    simpa
  · rintro ⟨x, hx, h, e⟩
    suffices (matrixToVec fun i ↦ numeral (v i.succ.succ)) = x by simpa [this]
    apply nth_ext' (k : V)
    · simp
    · simp [hx]
    · intro i hi
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simp [h]

@[simp] lemma substNumerals.eval (v : Fin (k + 2) → V) :
    Semiformula.Evalbm V v ssnums.val ↔ v 0 = substNumerals (v 1) (fun i ↦ v i.succ.succ) := substNumerals.defined.df.iff v

end

end LO.ISigma1.Metamath.InternalArithmetic

namespace LO.ISigma1

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 Metamath InternalArithmetic

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

lemma val_fixpoint (θ : Semisentence ℒₒᵣ 1) {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁] :
    V ⊧/![] (fixpoint θ) ↔ Semiformula.Evalbm V ![(substNumeral ⌜diag θ⌝ ⌜diag θ⌝ : V)] θ := by
  have E1 : ∀ x y z : V, (![x, y, z] 1) = y := fun x y z ↦ by simp
  have E2 : ∀ x y z : V, (![x, y, z] 2) = z := fun x y z ↦ by simp
  have e1 : ∀ x : V, (![x, ⌜diag θ⌝, ⌜diag θ⌝] 1) = ⌜diag θ⌝ := fun x ↦ E1 _ _ _
  have e2 : ∀ x : V, (![x, ⌜diag θ⌝, ⌜diag θ⌝] 2) = ⌜diag θ⌝ := fun x ↦ E2 _ _ _
  simp only [Nat.reduceAdd, Fin.isValue, fixpoint_eq, Nat.succ_eq_add_one, Fin.isValue, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Matrix.comp_vecCons',
    Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiformula.val_empty_quote, Matrix.constant_eq_singleton,
    LogicalConnective.Prop.arrow_eq, substNumeral.eval, Matrix.cons_val_zero, e1, e2, forall_eq]

theorem diagonal (θ : Semisentence ℒₒᵣ 1) :
    T ⊢!. fixpoint θ ⭤ θ/[⌜fixpoint θ⌝] :=
  haveI : 𝐄𝐐 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ T inferInstance
    let Θ : V → Prop := fun x ↦ Semiformula.Evalbm V ![x] θ
    suffices V ⊧/![] (fixpoint θ) ↔ Θ ⌜fixpoint θ⌝ by
      simpa [Θ, models_iff, Matrix.constant_eq_singleton]
    calc
      V ⊧/![] (fixpoint θ)
      ↔ Θ (substNumeral ⌜diag θ⌝ ⌜diag θ⌝) := val_fixpoint θ --simp [Θ, fixpoint_eq]
    _ ↔ Θ ⌜fixpoint θ⌝                     := by
      simp [substNumeral_app_quote_quote, fixpoint]
      have := Semiformula.coe_empty_quote (L := ℒₒᵣ) (σ := diag θ) (ξ := Empty)
      apply iff_of_eq
      have := congr_arg (fun x : FirstOrder.Semiterm ℒₒᵣ Empty 0 ↦ Θ ⌜(diag θ)/[x]⌝) this --???????????????????????????????/


/--/
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
  complete₀ <| oRing_consequence_of _ _ fun (V : Type) _ _ ↦ by
    haveI : V ⊧ₘ* 𝐈𝚺₁ := ModelsTheory.of_provably_subtheory V 𝐈𝚺₁ T inferInstance
    suffices V ⊧/![] (multifixpoint θ i) ↔ V ⊧/(fun i ↦ ⌜multifixpoint θ i⌝) (θ i) by simpa [models_iff]
    let t : Fin k → V := fun i ↦ ⌜multidiag (θ i)⌝
    have ht : ∀ i, substNumerals (t i) t = ⌜multifixpoint θ i⌝ := by
      intro i; simp [t, multifixpoint, substNumerals_app_quote_quote]
    calc
      V ⊧/![] (multifixpoint θ i) ↔ V ⊧/t (multidiag (θ i))              := by simp [t, multifixpoint]
      _                      ↔ V ⊧/(fun i ↦ substNumerals (t i) t) (θ i) := by simp [multidiag, ← funext_iff]
      _                      ↔ V ⊧/(fun i ↦ ⌜multifixpoint θ i⌝) (θ i)   := by simp [ht]

def exclusiveMultifixpoint (θ : Fin k → Semisentence ℒₒᵣ k) (i : Fin k) : Sentence ℒₒᵣ :=
  multifixpoint (fun j ↦ (θ j).padding j) i

@[simp] lemma exclusiveMultifixpoint_inj_iff (θ : Fin k → Semisentence ℒₒᵣ k) :
    exclusiveMultifixpoint θ i = exclusiveMultifixpoint θ j ↔ i = j := by
  constructor
  · unfold exclusiveMultifixpoint multifixpoint
    suffices ∀ ω : Rew ℒₒᵣ Empty k Empty 0, ω ▹ multidiag ((θ i).padding i) = ω ▹ multidiag ((θ j).padding j) → i = j by exact this _
    intro
    simp [multidiag, Fin.val_inj]
  · rintro rfl; rfl

theorem exclusiveMultidiagonal (θ : Fin k → Semisentence ℒₒᵣ k) :
    T ⊢!. exclusiveMultifixpoint θ i ⭤ (Rew.substs fun j ↦ ⌜exclusiveMultifixpoint θ j⌝) ▹ (θ i) := by
  have : T ⊢!. exclusiveMultifixpoint θ i ⭤ ((Rew.substs fun j ↦ ⌜exclusiveMultifixpoint θ j⌝) ▹ θ i).padding ↑i := by
    simpa using multidiagonal (T := T) (fun j ↦ (θ j).padding j) (i := i)
  exact Entailment.E!_trans this (Entailment.padding_iff _ _)

lemma multifixpoint_pi {θ : Fin k → Semisentence ℒₒᵣ k} (h : ∀ i, Hierarchy 𝚷 (m + 1) (θ i)) :
    Hierarchy 𝚷 (m + 1) (multifixpoint θ i) := by
  simpa [multifixpoint, multidiag, h] using fun _ ↦ Hierarchy.mono (s := 1) (by simp) (by simp)

lemma exclusiveMultifixpoint_pi {θ : Fin k → Semisentence ℒₒᵣ k} (h : ∀ i, Hierarchy 𝚷 (m + 1) (θ i)) :
    Hierarchy 𝚷 (m + 1) (exclusiveMultifixpoint θ i) := by
  apply multifixpoint_pi; simp [h]

end Multidiagonalization

end LO.ISigma1
