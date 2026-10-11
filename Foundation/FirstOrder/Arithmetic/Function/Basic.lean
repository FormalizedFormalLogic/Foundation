module

public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-!
# Provably total functions

Provably total functions, the minimal graph of a `𝚺₁` formula, and closure under composition.

## References

- [HP98]
- [AB05]
- [Bek99]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder

namespace Arithmetic

variable {k : ℕ} {V : Type*} [ORingStructure V]

def provablyTotality (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : ArithmeticSentence :=
  ∀¹* ((∃¹ φ.val) ⋏ (∀¹ ∀¹ (((Rew.subst (#1 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val) ⋏
    (Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val)) 🡒 “#1 = #0”)))

lemma models_provablyTotality_iff {φ : 𝚺ᴬ₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ provablyTotality φ ↔ ∀ v : Fin k → V, (∃ y, φ.val.Evalb (y :> v)) ∧
      ∀ y y', φ.val.Evalb (y :> v) → φ.val.Evalb (y' :> v) → y = y' := by
  simp [provablyTotality, models_iff, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Empty.eq_elim]

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

end Arithmetic

open Arithmetic

namespace ArithmeticTheory

variable {T U : ArithmeticTheory} {k : ℕ} {f : (Fin k → ℕ) → ℕ} {φ : 𝚺ᴬ₁.Semisentence (k + 1)}

structure ProvablyTotalVia (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ)
    (φ : 𝚺ᴬ₁.Semisentence (k + 1)) : Prop where
  defined : HierarchySymbol.DefinedFunction (V := ℕ) f φ
  total : T ⊢ provablyTotality φ

def ProvablyTotal (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ φ, T.ProvablyTotalVia f φ

def provablyTotalFunctions (T : ArithmeticTheory) (k : ℕ) : Set ((Fin k → ℕ) → ℕ) :=
  {f | T.ProvablyTotal f}

@[simp] lemma mem_provablyTotalFunctions :
    f ∈ T.provablyTotalFunctions k ↔ T.ProvablyTotal f := .rfl

namespace ProvablyTotalVia

lemma graph_iff (h : T.ProvablyTotalVia f φ) {v : Fin (k + 1) → ℕ} :
    φ.val.Evalb v ↔ v 0 = f (v ·.succ) := h.defined.iff

lemma mono (h : T.ProvablyTotalVia f φ) (hT : T ⪯ U) : U.ProvablyTotalVia f φ :=
  ⟨h.defined, hT.pbl h.total⟩

lemma models (h : T.ProvablyTotalVia f φ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] :
    ∃ F : (Fin k → V) → V, 𝚺ᴬ₁.DefinedFunction F φ := by
  have h₁ := models_provablyTotality_iff.mp (consequence_iff'.mp (Theory.Proof.sound h.total) V)
  choose hex hu using h₁
  choose F hF using hex
  exact ⟨F, .mk fun v ↦ ⟨fun hv ↦ hu _ _ _ (by simpa using hv) (hF _),
    fun e ↦ by simpa [← e] using hF (v ·.succ)⟩⟩

lemma of_models [𝗘𝗤 ℒₒᵣ ⪯ T] (hf : HierarchySymbol.DefinedFunction (V := ℕ) f φ)
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T],
      ∃ F : (Fin k → V) → V, 𝚺ᴬ₁.DefinedFunction F φ) : T.ProvablyTotalVia f φ :=
  ⟨hf, Arithmetic.complete T _ fun V _ _ ↦ models_provablyTotality_iff.mpr fun v ↦ by
    obtain ⟨F, hF⟩ := H V
    exact ⟨⟨F v, by simp [hF.iff]⟩, by simp_all [hF.iff]⟩⟩

lemma exists_minimalGraph {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗕𝚺₁]
    {φ : 𝚺ᴬ₁.Semisentence (k + 1)} {v : Fin k → V} (hex : ∃ y, φ.val.Evalb (y :> v)) :
    ∃ y, (minimalGraph φ).val.Evalb (y :> v) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₀ 𝗕𝚺₁ inferInstance
  obtain ⟨y₀, hy₀⟩ := hex
  obtain ⟨z₀, hz₀⟩ := (evalb_iff_exists_minimalGraphMatrix φ (y₀ :> v)).mp hy₀
  have hP : (existsAtSum (minimalGraphMatrix φ)).Evalb ((z₀ + y₀) :> v) :=
    (eval_existsAtSum _ _).mpr ⟨y₀, by simp, z₀, by simp, by simp, by simpa using hz₀⟩
  obtain ⟨n₀, hn₀, hnmin⟩ := InductionOnHierarchy.least_number 𝚺 0
    (definablePred_existsAtSum _ v) hP
  obtain ⟨y₁, -, z₁, hz₁len, hsum₁, hθ₁⟩ := (eval_existsAtSum _ _).mp hn₀
  have hPy : (pairGraph (minimalGraphMatrix φ)).Evalb (n₀ :> y₁ :> v) :=
    (eval_pairGraph _ _).mpr ⟨z₁, hz₁len, hsum₁, hθ₁⟩
  obtain ⟨ymin, hymin, hyminmin⟩ := InductionOnHierarchy.least_number 𝚺 0
    (definablePred_pairGraph _ n₀ v) hPy
  refine ⟨ymin, ?_⟩
  change (minimalPairGraph _).Evalb _
  simp only [eval_minimalPairGraph]
  exact ⟨n₀, by simpa using hymin, by simpa using hnmin, by simpa using hyminmin⟩

lemma of_exists [𝗕𝚺₁ ⪯ T] (hf : HierarchySymbol.DefinedFunction (V := ℕ) f φ)
    (h : T ⊢ ∀¹* ∃¹ φ.val) : T.ProvablyTotalVia f (minimalGraph φ) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := 1)
  have hforce : ∀ {y} {x : Fin k → ℕ}, (minimalGraph φ).val.Evalb (y :> x) → y = f x :=
    fun {y x} hy ↦ by
      obtain ⟨_, ⟨z, _, _, hθ⟩, _, _⟩ := (eval_minimalPairGraph _ _).mp hy
      simpa using hf.iff.mp ((evalb_iff_exists_minimalGraphMatrix φ (y :> x)).mpr ⟨z, hθ⟩)
  have hdef : HierarchySymbol.DefinedFunction (V := ℕ) f (minimalGraph φ) := .mk fun v ↦ by
    obtain ⟨y₀, x, rfl⟩ : ∃ y x, v = y :> x := ⟨v 0, _, (Fin.cons_self_tail v).symm⟩
    obtain ⟨y₁, hy₁⟩ := exists_minimalGraph (V := ℕ) (φ := φ) (v := x)
      ⟨f x, hf.iff.mpr (by simp)⟩
    constructor
    · exact fun hv ↦ hforce hv
    · intro e
      obtain rfl : y₀ = f x := e
      rwa [hforce hy₁] at hy₁
  refine of_models hdef fun V _ _ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗕𝚺₁ T inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := ModelsTheory.of_provably_subtheory V 𝗣𝗔⁻ 𝗕𝚺₁ inferInstance
  have hex : ∀ v : Fin k → V, ∃ y, φ.val.Evalb (y :> v) := by
    simpa [models_iff] using consequence_iff'.mp (Theory.Proof.sound h) V
  have hu : ∀ (v : Fin k → V) (y y'), (minimalGraph φ).val.Evalb (y :> v) →
      (minimalGraph φ).val.Evalb (y' :> v) → y = y' := by
    intro v y y' hy hy'
    have toExistsAtSum : ∀ {n y : V}, (∃ z ≤ n, z + y = n ∧
        (minimalGraphMatrix φ).val.Evalb (z :> y :> v)) →
        ∃ y' ≤ n, ∃ z' ≤ n, z' + y' = n ∧ (minimalGraphMatrix φ).val.Evalb (z' :> y' :> v) := by
      rintro n y ⟨z, hzn, hsum, hθ⟩
      exact ⟨y, by rw [← hsum]; simp, z, hzn, hsum, hθ⟩
    change (minimalPairGraph _).Evalb _ at hy hy'
    simp only [eval_minimalPairGraph] at hy hy'
    obtain ⟨n, hyA, hyB, hyC⟩ := hy
    obtain ⟨n', hy'A, hy'B, hy'C⟩ := hy'
    obtain rfl : n = n' := by
      rcases lt_trichotomy n n' with hlt | rfl | hlt
      · exact absurd (toExistsAtSum hyA) (hy'B n hlt)
      · rfl
      · exact absurd (toExistsAtSum hy'A) (hyB n' hlt)
    rcases lt_trichotomy y y' with hlt | rfl | hlt
    · exact absurd hyA (hy'C y hlt)
    · rfl
    · exact absurd hy'A (hyC y' hlt)
  choose F hF using fun v ↦ exists_minimalGraph (hex v)
  exact ⟨F, .mk fun v ↦ ⟨fun hv ↦ hu _ _ _ (by simpa using hv) (hF _),
    fun e ↦ by simpa [← e] using hF (v ·.succ)⟩⟩

lemma exists_sentence [𝗘𝗤 ℒₒᵣ ⪯ T] (h : T.ProvablyTotalVia f φ) : T ⊢ ∀¹* ∃¹ φ.val :=
  Arithmetic.complete T _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using fun v ↦ (models_provablyTotality_iff.mp
      (consequence_iff'.mp (Theory.Proof.sound h.total) V) v).1

lemma of_Pi2_conservative [𝗕𝚺₁ ⪯ T] [𝗕𝚺₁ ⪯ U] (h : T.ProvablyTotalVia f φ)
    (H : T ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ] U) : U.ProvablyTotalVia f (minimalGraph φ) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := 1)
  have hP : ∀ {n : ℕ} (ψ : ArithmeticSemiformula Empty n),
      ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 ψ → ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 (∀¹* ψ) := by
    intro n
    induction n with
    | zero => exact fun _ h ↦ h
    | succ n ih => exact fun ψ h ↦ ih _ h.all
  exact of_exists h.defined (H _ (hP _ (φ.sigma_prop.exs.accum 𝚷)) h.exists_sentence)

end ProvablyTotalVia

namespace ProvablyTotal

lemma mono (hT : T ⪯ U) : T.ProvablyTotal f → U.ProvablyTotal f :=
  fun ⟨_, h⟩ ↦ ⟨_, h.mono hT⟩

lemma of_Pi2_conservative [𝗕𝚺₁ ⪯ T] [𝗕𝚺₁ ⪯ U]
    (H : T ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ] U) :
    T.ProvablyTotal f → U.ProvablyTotal f :=
  fun ⟨_, h⟩ ↦ ⟨_, h.of_Pi2_conservative H⟩

end ProvablyTotal

lemma provablyTotalFunctions_subset (h : T ⪯ U) :
    T.provablyTotalFunctions k ⊆ U.provablyTotalFunctions k := fun _ hf ↦ hf.mono h

lemma provablyTotalFunctions_subset_of_Pi2_conservative [𝗕𝚺₁ ⪯ T] [𝗕𝚺₁ ⪯ U]
    (H : T ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ] U) :
    T.provablyTotalFunctions k ⊆ U.provablyTotalFunctions k := fun _ hf ↦ hf.of_Pi2_conservative H

theorem provablyTotal_iff [𝗕𝚺₁ ⪯ T] :
    T.ProvablyTotal f ↔ ∃ φ : 𝚺ᴬ₁.Semisentence (k + 1),
      HierarchySymbol.DefinedFunction (V := ℕ) f φ ∧ T ⊢ ∀¹* ∃¹ φ.val :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := 1)
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h.defined, h.exists_sentence⟩,
    fun ⟨_, hf, h⟩ ↦ ⟨_, .of_exists hf h⟩⟩

end ArithmeticTheory

/-! ### Composition -/

section
variable {T : ArithmeticTheory} {k l : ℕ} {V : Type*} [ORingStructure V]

def Arithmetic.compGraph (ψ : 𝚺ᴬ₁.Semisentence (l + 1)) (χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)) :
    𝚺ᴬ₁.Semisentence (k + 1) :=
  .mkSigma
    (Rew.bind ![] (#·) ▹ (∃¹* ((Rew.bind (&0 :> (#·)) Empty.elim ▹ ψ.val) ⋏
      Matrix.conj fun i ↦ Rew.bind (#i :> (&·.succ)) Empty.elim ▹ (χ i).val)))
    (Bounding.Hierarchy.rew _ (Bounding.Hierarchy.exsClosure (by simp)))

@[simp] lemma Arithmetic.eval_compGraph (ψ : 𝚺ᴬ₁.Semisentence (l + 1))
    (χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)) (w : Fin (k + 1) → V) :
    (compGraph ψ χ).val.Evalb w ↔
      ∃ z : Fin l → V, ψ.val.Evalb (w 0 :> z) ∧ ∀ i, (χ i).val.Evalb (z i :> (w ·.succ)) := by
  simp [compGraph, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
    Matrix.comp_vecCons', Empty.eq_elim]

lemma Arithmetic.definedFunction_compGraph {ψ : 𝚺ᴬ₁.Semisentence (l + 1)}
    {χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)} {f : (Fin l → V) → V} {g : Fin l → (Fin k → V) → V}
    (hf : 𝚺ᴬ₁.DefinedFunction f ψ) (hg : ∀ i, 𝚺ᴬ₁.DefinedFunction (g i) (χ i)) :
    𝚺ᴬ₁.DefinedFunction (fun v ↦ f fun i ↦ g i v) (compGraph ψ χ) :=
  .mk fun w ↦ by
    simp only [eval_compGraph, hf.iff, (hg _).iff, Matrix.cons_val_zero, Matrix.cons_val_succ]
    exact ⟨fun ⟨z, hz, hχ⟩ ↦ by simpa [funext hχ] using hz,
      fun e ↦ ⟨_, by simpa using e, fun _ ↦ rfl⟩⟩

lemma ArithmeticTheory.ProvablyTotalVia.comp [𝗘𝗤 ℒₒᵣ ⪯ T] {g : (Fin l → ℕ) → ℕ}
    {h : Fin l → (Fin k → ℕ) → ℕ} {ψ : 𝚺ᴬ₁.Semisentence (l + 1)}
    {χ : Fin l → 𝚺ᴬ₁.Semisentence (k + 1)} (hg : T.ProvablyTotalVia g ψ)
    (hh : ∀ i, T.ProvablyTotalVia (h i) (χ i)) :
    T.ProvablyTotalVia (fun v ↦ g fun i ↦ h i v) (compGraph ψ χ) := by
  apply of_models (definedFunction_compGraph hg.defined fun i ↦ (hh i).defined)
  intro V _ _
  obtain ⟨G, hG⟩ := hg.models V
  choose H hH using fun i ↦ (hh i).models V
  exact ⟨_, definedFunction_compGraph hG hH⟩

lemma ArithmeticTheory.ProvablyTotal.comp [𝗘𝗤 ℒₒᵣ ⪯ T] {g : (Fin l → ℕ) → ℕ}
    {h : Fin l → (Fin k → ℕ) → ℕ} (hg : T.ProvablyTotal g) (hh : ∀ i, T.ProvablyTotal (h i)) :
    T.ProvablyTotal fun v ↦ g fun i ↦ h i v :=
  have ⟨_, hg⟩ := hg
  have ⟨_, hh⟩ := Classical.skolem.mp hh
  ⟨_, hg.comp hh⟩

end

end FFL.FirstOrder
