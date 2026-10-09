module

public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-!
# Provably total functions

Provably total and provably functional functions, their graph formulas, and closure under
composition.

## References

- [HP98, Definition I.1.51, Definition I.1.51(2), Lemma I.1.53, Theorem I.2.5(3), Lemma I.2.9,
  Definition IV.3.1, Lemma IV.3.4]
- [AB05, §10.2]
- [Bek99, §1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder

namespace Arithmetic

section
variable {k l : ℕ} {V : Type*} [ORingStructure V]

def totalitySentence (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : ArithmeticSentence := ∀¹* ∃¹ φ.val

@[simp] lemma hierarchy_totalitySentence (φ : 𝚺ᴬ₁.Semisentence (k + 1)) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 (totalitySentence φ) := by
  have : ∀ {n : ℕ} (ψ : ArithmeticSemiformula Empty n),
      ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 ψ → ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 (∀¹* ψ) := by
    intro n
    induction n with
    | zero => exact fun _ h ↦ h
    | succ n ih => exact fun ψ h ↦ ih _ h.all
  exact this _ (φ.sigma_prop.exs.accum 𝚷)

lemma models_totalitySentence_iff {φ : 𝚺ᴬ₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ totalitySentence φ ↔ ∀ v : Fin k → V, ∃ y, φ.val.Evalb (y :> v) := by
  simp [totalitySentence, models_iff]

def functionalitySentence (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : ArithmeticSentence :=
  ∀¹* ∀¹ ∀¹ (((Rew.subst (#1 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val) ⋏
    (Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val)) 🡒 “#1 = #0”)

lemma models_functionalitySentence_iff {φ : 𝚺ᴬ₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ functionalitySentence φ ↔ ∀ (v : Fin k → V) (y y'),
      φ.val.Evalb (y :> v) → φ.val.Evalb (y' :> v) → y = y' := by
  simp [functionalitySentence, models_iff, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Empty.eq_elim]

def compGraph (ψ : 𝚺ᴬ₁.Semisentence (l + 1)) (χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)) :
    𝚺ᴬ₁.Semisentence (k + 1) :=
  .mkSigma
    (Rew.bind ![] (#·) ▹ (∃¹* ((Rew.bind (&0 :> (#·)) Empty.elim ▹ ψ.val) ⋏
      Matrix.conj fun i ↦ Rew.bind (#i :> (&·.succ)) Empty.elim ▹ (χ i).val)))
    (Bounding.Hierarchy.rew _ (Bounding.Hierarchy.exsClosure (by simp)))

@[simp] lemma eval_compGraph (ψ : 𝚺ᴬ₁.Semisentence (l + 1))
    (χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)) (w : Fin (k + 1) → V) :
    (compGraph ψ χ).val.Evalb w ↔
      ∃ z : Fin l → V, ψ.val.Evalb (w 0 :> z) ∧ ∀ i, (χ i).val.Evalb (z i :> (w ·.succ)) := by
  simp [compGraph, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
    Matrix.comp_vecCons', Empty.eq_elim]

lemma definedFunction_compGraph {ψ : 𝚺ᴬ₁.Semisentence (l + 1)}
    {χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)} {f : (Fin l → V) → V} {g : Fin l → (Fin k → V) → V}
    (hf : 𝚺ᴬ₁.DefinedFunction f ψ) (hg : ∀ i, 𝚺ᴬ₁.DefinedFunction (g i) (χ i)) :
    𝚺ᴬ₁.DefinedFunction (fun v ↦ f fun i ↦ g i v) (compGraph ψ χ) :=
  .mk fun w ↦ by
    simp only [eval_compGraph, hf.iff, (hg _).iff, Matrix.cons_val_zero, Matrix.cons_val_succ]
    exact ⟨fun ⟨z, hz, hχ⟩ ↦ by simpa [funext hχ] using hz,
      fun e ↦ ⟨_, by simpa using e, fun _ ↦ rfl⟩⟩

lemma definablePred_evalb (φ : 𝚺ᴬ₁.Semisentence (k + 1)) (v : Fin k → V) :
    𝚺ᴬ₁-Predicate fun y ↦ φ.val.Evalb (y :> v) :=
  HierarchySymbol.Definable.mkPolarity (Γ := 𝚺) (m := 1)
    (Rew.bind (#0 :> fun i ↦ &(v i)) Empty.elim ▹ φ.val)
    (Bounding.Hierarchy.rew _ (by simp)) fun w ↦ by
      simp [Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

def leastGraph (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : ArithmeticSemisentence (k + 1) :=
  φ.val ⋏ (∀¹[“#0 < #1”] ∼(Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val))

@[simp] lemma eval_leastGraph (φ : 𝚺ᴬ₁.Semisentence (k + 1)) (w : Fin (k + 1) → V) :
    (leastGraph φ).Evalb w ↔ φ.val.Evalb w ∧ ∀ y < w 0, ¬φ.val.Evalb (y :> (w ·.succ)) := by
  simp [leastGraph, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

noncomputable def minimalGraphMatrix (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : 𝚺ᴬ₀.Semisentence (k + 2) :=
  .mkSigma (Classical.choose (Bounding.Prenex.models_exists_prenex.{0, 0} (Γ := 𝚺) (Γ' := 𝚺)
    (s := 1) φ.sigma_prop)).matrix.val (by simp)

lemma provable_iff_exists_minimalGraphMatrix (T : ArithmeticTheory) [𝗕𝚺₁ ⪯ T]
    (φ : 𝚺ᴬ₁.Semisentence (k + 1)) :
    T ⊢ ∀¹* (φ.val 🡘 ∃¹ (minimalGraphMatrix φ).val) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := 1)
  apply provable_iff_of_models_iff
  intro V _ _ e
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺₁ := models_of_subtheory (T := 𝗕𝚺₁) (U := T) inferInstance
  simpa [minimalGraphMatrix, Bounding.Prenex.val] using
    Classical.choose_spec (Bounding.Prenex.models_exists_prenex.{0, 0} (Γ := 𝚺) (Γ' := 𝚺)
      (s := 1) φ.sigma_prop) V e Empty.elim

lemma evalb_iff_exists_minimalGraphMatrix [V↓[ℒₒᵣ] ⊧* 𝗕𝚺₁] (φ : 𝚺ᴬ₁.Semisentence (k + 1))
    (v : Fin (k + 1) → V) : φ.val.Evalb v ↔ ∃ z, (minimalGraphMatrix φ).val.Evalb (z :> v) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗕𝚺₁ := eq_weakerThan_of_BSigma (s := 1)
  have : ∀ v : Fin (k + 1) → V,
      φ.val.Evalb v ↔ ∃ z, (minimalGraphMatrix φ).val.Evalb (z :> v) := by
    simpa [models_iff] using consequence_iff'.mp
      (Theory.Proof.sound (provable_iff_exists_minimalGraphMatrix 𝗕𝚺₁ φ)) V
  exact this v

def pairGraph (θ : 𝚺ᴬ₀.Semisentence (k + 2)) : ArithmeticSemisentence (k + 2) :=
  (“(#0 + #2) = #1” ⋏
    (Rew.subst (#0 :> #2 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ θ.val)).bexsLTSucc
    (#0 : ArithmeticSemiterm Empty (k + 2))

@[simp] lemma eval_pairGraph [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (θ : 𝚺ᴬ₀.Semisentence (k + 2)) (w : Fin (k + 2) → V) :
    (pairGraph θ).Evalb w ↔
      ∃ z ≤ w 0, z + w 1 = w 0 ∧ θ.val.Evalb (z :> w 1 :> (w ·.succ.succ)) := by
  simp [pairGraph, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim,
    Matrix.constant_eq_singleton]

def existsAtSum (θ : 𝚺ᴬ₀.Semisentence (k + 2)) : ArithmeticSemisentence (k + 1) :=
  ((“(#0 + #1) = #2” ⋏
    (Rew.subst (#0 :> #1 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ θ.val)).bexsLTSucc
      (#1 : ArithmeticSemiterm Empty (k + 2))).bexsLTSucc (#0 : ArithmeticSemiterm Empty (k + 1))

@[simp] lemma eval_existsAtSum [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (θ : 𝚺ᴬ₀.Semisentence (k + 2))
    (w : Fin (k + 1) → V) :
    (existsAtSum θ).Evalb w ↔
      ∃ y' ≤ w 0, ∃ z' ≤ w 0, z' + y' = w 0 ∧ θ.val.Evalb (z' :> y' :> (w ·.succ)) := by
  simp [existsAtSum, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim,
    Matrix.constant_eq_singleton]

def minimalPairGraph (θ : 𝚺ᴬ₀.Semisentence (k + 2)) : ArithmeticSemisentence (k + 1) :=
  ∃¹ (pairGraph θ ⋏
    (∀¹[“#0 < #1”] ∼(Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ existsAtSum θ)) ⋏
    (∀¹[“#0 < #2”] ∼(Rew.subst (#1 :> #0 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ pairGraph θ)))

@[simp] lemma eval_minimalPairGraph [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (θ : 𝚺ᴬ₀.Semisentence (k + 2))
    (w : Fin (k + 1) → V) :
    (minimalPairGraph θ).Evalb w ↔
      ∃ n, (∃ z ≤ n, z + w 0 = n ∧ θ.val.Evalb (z :> w 0 :> (w ·.succ))) ∧
        (∀ n' < n, ¬∃ y' ≤ n', ∃ z' ≤ n', z' + y' = n' ∧ θ.val.Evalb (z' :> y' :> (w ·.succ))) ∧
        (∀ y' < w 0, ¬∃ z' ≤ n, z' + y' = n ∧ θ.val.Evalb (z' :> y' :> (w ·.succ))) := by
  simp [minimalPairGraph, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons',
    Empty.eq_elim]

noncomputable def minimalGraph (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : 𝚺ᴬ₁.Semisentence (k + 1) :=
  .mkSigma (minimalPairGraph (minimalGraphMatrix φ)) (by
    unfold minimalPairGraph pairGraph existsAtSum
    apply Bounding.Hierarchy.exs
    simp)

private lemma definablePred_existsAtSum (θ : 𝚺ᴬ₀.Semisentence (k + 2)) (v : Fin k → V) :
    𝚺ᴬ₀-Predicate fun n ↦ (existsAtSum θ).Evalb (n :> v) :=
  HierarchySymbol.Definable.mkPolarity (Γ := 𝚺) (m := 0)
    (Rew.bind (#0 :> fun i ↦ &(v i)) Empty.elim ▹ existsAtSum θ)
    (Bounding.Hierarchy.rew _ (by simp [existsAtSum])) fun w ↦ by
      simp [Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

private lemma definablePred_pairGraph (θ : 𝚺ᴬ₀.Semisentence (k + 2)) (n₀ : V) (v : Fin k → V) :
    𝚺ᴬ₀-Predicate fun y ↦ (pairGraph θ).Evalb (n₀ :> y :> v) :=
  HierarchySymbol.Definable.mkPolarity (Γ := 𝚺) (m := 0)
    (Rew.bind (&n₀ :> #0 :> fun i ↦ &(v i)) Empty.elim ▹ pairGraph θ)
    (Bounding.Hierarchy.rew _ (by simp [pairGraph])) fun w ↦ by
      simp [Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

private lemma models_existsUnique_minimalPairGraph {θ : 𝚺ᴬ₀.Semisentence (k + 2)}
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {v : Fin k → V} (hex : ∃ y z : V, θ.val.Evalb (z :> y :> v)) :
    (∃ y, (minimalPairGraph θ).Evalb (y :> v)) ∧
      ∀ y y', (minimalPairGraph θ).Evalb (y :> v) → (minimalPairGraph θ).Evalb (y' :> v) →
        y = y' := by
  obtain ⟨y₀, z₀, hz₀⟩ := hex
  have hP : (existsAtSum θ).Evalb ((z₀ + y₀) :> v) :=
    (eval_existsAtSum θ _).mpr ⟨y₀, by simp, z₀, by simp, by simp, by simpa using hz₀⟩
  obtain ⟨n₀, hn₀, hnmin⟩ := InductionOnHierarchy.least_number 𝚺 0
    (definablePred_existsAtSum θ v) hP
  obtain ⟨y₁, hy₁len, z₁, hz₁len, hsum₁, hθ₁⟩ := (eval_existsAtSum θ _).mp hn₀
  have hPy : (pairGraph θ).Evalb (n₀ :> y₁ :> v) :=
    (eval_pairGraph θ _).mpr ⟨z₁, hz₁len, hsum₁, hθ₁⟩
  obtain ⟨ymin, hymin, hyminmin⟩ := InductionOnHierarchy.least_number 𝚺 0
    (definablePred_pairGraph θ n₀ v) hPy
  have toExistsAtSum : ∀ {n y : V}, (∃ z ≤ n, z + y = n ∧ θ.val.Evalb (z :> y :> v)) →
      ∃ y' ≤ n, ∃ z' ≤ n, z' + y' = n ∧ θ.val.Evalb (z' :> y' :> v) := by
    rintro n y ⟨z, hzn, hsum, hθ⟩
    exact ⟨y, by rw [← hsum]; simp, z, hzn, hsum, hθ⟩
  constructor
  · use ymin
    simp only [eval_minimalPairGraph]
    exact ⟨n₀, by simpa using hymin, by simpa using hnmin, by simpa using hyminmin⟩
  · rintro y y' hy hy'
    simp only [eval_minimalPairGraph] at hy hy'
    obtain ⟨n, hyA, hyB, hyC⟩ := hy
    obtain ⟨n', hy'A, hy'B, hy'C⟩ := hy'
    have hnn' : n = n' := by
      rcases lt_trichotomy n n' with hlt | rfl | hlt
      · exact absurd (toExistsAtSum hyA) (hy'B n hlt)
      · rfl
      · exact absurd (toExistsAtSum hy'A) (hyB n' hlt)
    subst hnn'
    rcases lt_trichotomy y y' with hlt | rfl | hlt
    · exact absurd hyA (hy'C y hlt)
    · rfl
    · exact absurd hy'A (hyC y' hlt)

def uniqueTotalitySentence (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : ArithmeticSentence :=
  ∀¹* ((∃¹ leastGraph φ) ⋏ (∀¹ ∀¹
    (((Rew.subst (#1 :> fun i : Fin k ↦ #i.succ.succ) ▹ leastGraph φ) ⋏
      (Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ) ▹ leastGraph φ)) 🡒 “#1 = #0”)))

lemma models_uniqueTotalitySentence_iff {φ : 𝚺ᴬ₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ uniqueTotalitySentence φ ↔ ∀ v : Fin k → V,
      (∃ y, (leastGraph φ).Evalb (y :> v)) ∧
        ∀ y y', (leastGraph φ).Evalb (y :> v) → (leastGraph φ).Evalb (y' :> v) → y = y' := by
  simp [uniqueTotalitySentence, models_iff, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Empty.eq_elim]

end

end Arithmetic

open Arithmetic

namespace ArithmeticTheory

variable {T U : ArithmeticTheory} {k : ℕ} {f : (Fin k → ℕ) → ℕ} {φ : 𝚺ᴬ₁.Semisentence (k + 1)}

structure ProvablyTotalVia (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ)
    (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : Prop where
  defined : HierarchySymbol.DefinedFunction (V := ℕ) f φ
  total : T ⊢ totalitySentence φ

structure ProvablyFunctionalVia (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ)
    (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : Prop extends T.ProvablyTotalVia f φ where
  functional : T ⊢ functionalitySentence φ

def ProvablyTotal (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ φ, T.ProvablyTotalVia f φ

def ProvablyFunctional (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ φ, T.ProvablyFunctionalVia f φ

def provablyTotalFunctions (T : ArithmeticTheory) (k : ℕ) : Set ((Fin k → ℕ) → ℕ) :=
  {f | T.ProvablyTotal f}

@[simp] lemma mem_provablyTotalFunctions :
    f ∈ T.provablyTotalFunctions k ↔ T.ProvablyTotal f := .rfl

namespace ProvablyTotalVia

lemma graph_iff (h : T.ProvablyTotalVia f φ) {v : Fin (k + 1) → ℕ} :
    φ.val.Evalb v ↔ v 0 = f (v ·.succ) := h.defined.iff

lemma mono (h : T.ProvablyTotalVia f φ) (hT : T ⪯ U) : U.ProvablyTotalVia f φ :=
  ⟨h.defined, hT.pbl h.total⟩

/-- Provable totality depends only on the $\Pi_2$ consequences of the theory.
- [AB05, §10.2] -/
lemma of_Pi2_conservative (h : T.ProvablyTotalVia f φ)
    (H : T ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ] U) :
    U.ProvablyTotalVia f φ :=
  ⟨h.defined, H _ (by simp) h.total⟩

lemma models (h : T.ProvablyTotalVia f φ)
    (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (v : Fin k → V) : ∃ y, φ.val.Evalb (y :> v) :=
  models_totalitySentence_iff.mp (consequence_iff'.mp (Theory.Proof.sound h.total) V) v

lemma of_models [𝗘𝗤 ℒₒᵣ ⪯ T] (hf : HierarchySymbol.DefinedFunction (V := ℕ) f φ)
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T], ∀ v : Fin k → V,
      ∃ y, φ.val.Evalb (y :> v)) : T.ProvablyTotalVia f φ :=
  ⟨hf, Arithmetic.complete T _ fun V _ _ ↦ models_totalitySentence_iff.mpr (H V)⟩

lemma leastGraph_iff (h : T.ProvablyTotalVia f φ) {v : Fin (k + 1) → ℕ} :
    (leastGraph φ).Evalb v ↔ v 0 = f (v ·.succ) := by
  simp [h.graph_iff]
  omega

lemma exists_unique [𝗟𝚺1 ⪯ T] (h : T.ProvablyTotalVia f φ) : T ⊢ uniqueTotalitySentence φ := by
  have : 𝗣𝗔⁻ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗟𝚺1) inferInstance inferInstance
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  have : 𝗟𝚺⁺1 ⪯ T := (LSigma_equiv_LBroadSigma 1).symm.le.trans inferInstance
  apply Arithmetic.complete.{0}
  intro (V : Type) _ _
  have : V↓[ℒₒᵣ] ⊧* 𝗟𝚺⁺1 := ModelsTheory.of_provably_subtheory V 𝗟𝚺⁺1 T inferInstance
  apply models_uniqueTotalitySentence_iff.mpr
  intro v
  constructor
  · obtain ⟨y, hy⟩ := h.models V v
    obtain ⟨y₀, h₀, hmin⟩ := LeastNumberOnHierarchy.least_number 𝚺 1 (definablePred_evalb φ v) hy
    use y₀
    simp_all
  · intro y y' hy hy'
    simp only [eval_leastGraph, Matrix.cons_val_zero, Matrix.cons_val_succ] at hy hy'
    grind

lemma models_existsUnique_minimalGraph {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗕𝚺₁] {φ : 𝚺ᴬ₁.Semisentence (k + 1)} {v : Fin k → V}
    (hex : ∃ y, φ.val.Evalb (y :> v)) :
    (∃ y, (minimalGraph φ).val.Evalb (y :> v)) ∧
      ∀ y y', (minimalGraph φ).val.Evalb (y :> v) → (minimalGraph φ).val.Evalb (y' :> v) →
        y = y' := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₀ 𝗕𝚺₁ inferInstance
  obtain ⟨y, hy⟩ := hex
  obtain ⟨z, hz⟩ := (evalb_iff_exists_minimalGraphMatrix φ (y :> v)).mp hy
  exact models_existsUnique_minimalPairGraph ⟨y, z, hz⟩

lemma provablyFunctionalVia_minimalGraph [𝗕𝚺₁ ⪯ T] (h : T.ProvablyTotalVia f φ) :
    T.ProvablyFunctionalVia f (minimalGraph φ) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := 1)
  have hforce : ∀ {y} {x : Fin k → ℕ}, (minimalGraph φ).val.Evalb (y :> x) → y = f x :=
    fun {y x} hy ↦ by
      obtain ⟨_, ⟨z, _, _, hθ⟩, _, _⟩ := (eval_minimalPairGraph _ _).mp hy
      simpa using h.graph_iff.mp ((evalb_iff_exists_minimalGraphMatrix φ (y :> x)).mpr ⟨z, hθ⟩)
  have hdef : HierarchySymbol.DefinedFunction (V := ℕ) f (minimalGraph φ) := .mk fun v ↦ by
    obtain ⟨y₀, x, rfl⟩ : ∃ y x, v = y :> x := ⟨v 0, _, (Fin.cons_self_tail v).symm⟩
    obtain ⟨⟨y₁, hy₁⟩, -⟩ := models_existsUnique_minimalGraph (V := ℕ) (φ := φ) (v := x)
      ⟨f x, h.graph_iff.mpr (by simp)⟩
    constructor
    · exact fun hv ↦ hforce hv
    · intro e
      obtain rfl : y₀ = f x := e
      rwa [hforce hy₁] at hy₁
  have hT : T ⊢ totalitySentence (minimalGraph φ) := by
    apply Arithmetic.complete.{0}
    intro (V : Type) _ _
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗕𝚺₁ T inferInstance
    apply models_totalitySentence_iff.mpr
    intro v
    obtain ⟨y, hy⟩ := h.models V v
    exact (models_existsUnique_minimalGraph ⟨y, hy⟩).1
  have hF : T ⊢ functionalitySentence (minimalGraph φ) := by
    apply Arithmetic.complete.{0}
    intro (V : Type) _ _
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗕𝚺₁ T inferInstance
    apply models_functionalitySentence_iff.mpr
    intro v y y' hy hy'
    obtain ⟨y₀, hy₀⟩ := h.models V v
    exact (models_existsUnique_minimalGraph ⟨y₀, hy₀⟩).2 y y' hy hy'
  exact ⟨⟨hdef, hT⟩, hF⟩

section
variable {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
  {ψ : 𝚺ᴬ₁.Semisentence (l + 1)} {χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)}

lemma comp [𝗘𝗤 ℒₒᵣ ⪯ T] (hg : T.ProvablyTotalVia g ψ) (hh : ∀ i, T.ProvablyTotalVia (h i) (χ i)) :
    T.ProvablyTotalVia (fun v ↦ g fun i ↦ h i v) (compGraph ψ χ) := by
  apply of_models (definedFunction_compGraph hg.defined fun i ↦ (hh i).defined)
  intro V _ _ v
  choose z hz using fun i ↦ (hh i).models V v
  obtain ⟨y, hy⟩ := hg.models V z
  exact ⟨y, by simpa using ⟨z, hy, hz⟩⟩

end

end ProvablyTotalVia

namespace ProvablyFunctionalVia

lemma models (h : T.ProvablyFunctionalVia f φ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] :
    ∃ F : (Fin k → V) → V, 𝚺ᴬ₁.DefinedFunction F φ := by
  have h₁ := models_functionalitySentence_iff.mp
    (consequence_iff'.mp (Theory.Proof.sound h.functional) V)
  choose F hF using h.toProvablyTotalVia.models V
  exact ⟨F, .mk fun v ↦ ⟨fun hv ↦ by simpa using h₁ _ _ _ (by simpa using hv) (hF _),
    fun e ↦ by simpa [← e] using hF (v ·.succ)⟩⟩

lemma of_models [𝗘𝗤 ℒₒᵣ ⪯ T] (hf : HierarchySymbol.DefinedFunction (V := ℕ) f φ)
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T],
      ∃ F : (Fin k → V) → V, 𝚺ᴬ₁.DefinedFunction F φ) : T.ProvablyFunctionalVia f φ where
  toProvablyTotalVia := .of_models hf fun V _ _ v ↦ have ⟨F, hF⟩ := H V; ⟨F v, by simp [hF.iff]⟩
  functional := Arithmetic.complete T _ fun V _ _ ↦
    models_functionalitySentence_iff.mpr fun v y y' hy hy' ↦ by
      obtain ⟨F, hF⟩ := H V
      simp_all [hF.iff]

end ProvablyFunctionalVia

namespace ProvablyTotal

lemma mono (hT : T ⪯ U) : T.ProvablyTotal f → U.ProvablyTotal f :=
  fun ⟨_, h⟩ ↦ ⟨_, h.mono hT⟩

/-- Provable totality depends only on the $\Pi_2$ consequences of the theory.
- [AB05, §10.2] -/
lemma of_Pi2_conservative
    (H : T ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ] U) :
    T.ProvablyTotal f → U.ProvablyTotal f :=
  fun ⟨_, h⟩ ↦ ⟨_, h.of_Pi2_conservative H⟩

section
variable [𝗘𝗤 ℒₒᵣ ⪯ T] {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}

lemma comp (hg : T.ProvablyTotal g) (hh : ∀ i, T.ProvablyTotal (h i)) :
    T.ProvablyTotal fun v ↦ g fun i ↦ h i v :=
  have ⟨_, hg⟩ := hg
  have ⟨_, hh⟩ := Classical.skolem.mp hh
  ⟨_, hg.comp hh⟩

end

lemma exists_unique [𝗟𝚺1 ⪯ T] :
    T.ProvablyTotal f → ∃ φ, T.ProvablyTotalVia f φ ∧ T ⊢ uniqueTotalitySentence φ :=
  fun ⟨_, h⟩ ↦ ⟨_, h, h.exists_unique⟩

end ProvablyTotal

lemma provablyTotalFunctions_subset (h : T ⪯ U) :
    T.provablyTotalFunctions k ⊆ U.provablyTotalFunctions k := fun _ hf ↦ hf.mono h

/-- The class of provably total functions depends only on the $\Pi_2$ consequences of the theory.
- [AB05, §10.2] -/
lemma provablyTotalFunctions_subset_of_Pi2_conservative
    (H : T ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ] U) :
    T.provablyTotalFunctions k ⊆ U.provablyTotalFunctions k := fun _ hf ↦ hf.of_Pi2_conservative H

namespace ProvablyFunctional

lemma toProvablyTotal : T.ProvablyFunctional f → T.ProvablyTotal f :=
  fun ⟨_, h⟩ ↦ ⟨_, h.toProvablyTotalVia⟩

end ProvablyFunctional

theorem provablyTotal_iff_provablyFunctional [𝗕𝚺₁ ⪯ T] :
    T.ProvablyTotal f ↔ T.ProvablyFunctional f :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h.provablyFunctionalVia_minimalGraph⟩,
    fun ⟨_, h⟩ ↦ ⟨_, h.toProvablyTotalVia⟩⟩

end ArithmeticTheory

end FFL.FirstOrder
