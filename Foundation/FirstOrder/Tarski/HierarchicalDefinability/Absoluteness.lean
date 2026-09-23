module

public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic
public import Foundation.FirstOrder.Tarski.Elementary

/-!
# Absoluteness for bounding hierarchies

Bounded formulas are absolute along embeddings whose image contains every element bounded
by an image element. Sigma-one formulas are upward absolute and Pi-one formulas downward
absolute. These are standard structural-induction facts; the operator-parametric formulation
is specific to this formalization.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding

open scoped Bounding
open Tarski.Structure

variable {L : Language} {ℬ : Bounding L}
variable {R : Semiformula.Operator L 2}
variable {M N ξ : Type*} [Tarski.Structure L M] [Tarski.Structure L N]

/-- An embedding whose image is initial for every bounding operator. -/
class IsInitial (ℬ : Bounding L) (ι : M ↪ₛ[L] N) : Prop where
  operator_iff {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (a b : M) :
    R.val ![a, b] ↔ R.val ![ι a, ι b]
  initial {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (a : M) (b : N) :
    R.val ![b, ι a] → ∃ c : M, ι c = b

variable (ι : M ↪ₛ[L] N)
variable [IsInitial ℬ ι]

private lemma ball_upward {n} {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1))
    (ih : ∀ e ε, φ.Eval e ε → φ.Eval (ι ∘ e) (ι ∘ ε))
    (e : Fin n → M) (ε : ξ → M) :
    (∀¹[R.operator ![#0, Rew.bShift t]] φ).Eval e ε →
      (∀¹[R.operator ![#0, Rew.bShift t]] φ).Eval (ι ∘ e) (ι ∘ ε) := by
  simp only [Semiformula.eval_ball, Semiformula.eval_operator,
    Matrix.comp₂, Semiterm.val_bvar,
    Matrix.cons_val_zero, Semiterm.val_bShift, ← HomClass.val_term ι]
  intro h b hb
  obtain ⟨c, rfl⟩ := IsInitial.initial (ℬ := ℬ) (ι := ι) hR (t.val e ε) b hb
  simpa only [Matrix.comp_vecCons''] using
    ih (c :> e) ε (h c ((IsInitial.operator_iff (ℬ := ℬ) (ι := ι) hR _ _).mpr hb))

private lemma bexs_upward {n} {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1))
    (ih : ∀ e ε, φ.Eval e ε → φ.Eval (ι ∘ e) (ι ∘ ε))
    (e : Fin n → M) (ε : ξ → M) :
    (∃¹[R.operator ![#0, Rew.bShift t]] φ).Eval e ε →
      (∃¹[R.operator ![#0, Rew.bShift t]] φ).Eval (ι ∘ e) (ι ∘ ε) := by
  simp only [Semiformula.eval_bexs, Semiformula.eval_operator,
    Matrix.comp₂, Semiterm.val_bvar,
    Matrix.cons_val_zero, Semiterm.val_bShift, ← HomClass.val_term ι]
  rintro ⟨c, hc, hp⟩
  exact ⟨ι c, (IsInitial.operator_iff (ℬ := ℬ) (ι := ι) hR _ _).mp hc,
    by simpa only [Matrix.comp_vecCons''] using ih (c :> e) ε hp⟩

lemma bounded_absolute {n} {φ : Semiformula L ξ n} (hφ : ℬ.Closure φ)
    (e : Fin n → M) (ε : ξ → M) :
    φ.Eval e ε ↔ φ.Eval (ι ∘ e) (ι ∘ ε) := by
  induction hφ generalizing ε with
  | verum | falsum => simp
  | rel | nrel => simp [Function.comp_def, ← EmbeddingClass.rel ι, HomClass.val_term]
  | and _ _ ihp ihq => simp [ihp, ihq]
  | or _ _ ihp ihq => simp [ihp, ihq]
  | @ball n R φ t hR ht hφ ih =>
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    constructor
    . exact ball_upward ι hR t _ (fun e ε ↦ (ih e ε).mp) e ε
    . simp only [Semiformula.eval_ball, Semiformula.eval_operator,
        Matrix.comp₂, Semiterm.val_bvar,
        Matrix.cons_val_zero, Semiterm.val_bShift, ← HomClass.val_term ι]
      intro h c hc
      apply (ih (c :> e) ε).mpr
      simpa only [Matrix.comp_vecCons''] using
        h (ι c) ((IsInitial.operator_iff (ℬ := ℬ) (ι := ι) hR _ _).mp hc)
  | @bexs n R φ t hR ht hφ ih =>
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    constructor
    . exact bexs_upward ι hR t _ (fun e ε ↦ (ih e ε).mp) e ε
    . simp only [Semiformula.eval_bexs, Semiformula.eval_operator,
        Matrix.comp₂, Semiterm.val_bvar,
        Matrix.cons_val_zero, Semiterm.val_bShift, ← HomClass.val_term ι]
      rintro ⟨b, hb, hp⟩
      obtain ⟨c, rfl⟩ := IsInitial.initial (ℬ := ℬ) (ι := ι) hR (t.val e ε) b hb
      exact ⟨c, (IsInitial.operator_iff (ℬ := ℬ) (ι := ι) hR _ _).mpr hb,
        (ih (c :> e) ε).mpr (by simpa only [Matrix.comp_vecCons''] using hp)⟩

lemma sigma_one_upward {n} {φ : Semiformula L ξ n} (hφ : ℬ.Hierarchy 𝚺 1 φ)
    (e : Fin n → M) (ε : ξ → M) :
    φ.Eval e ε → φ.Eval (ι ∘ e) (ι ∘ ε) := by
  revert e ε
  apply Hierarchy.sigma_succ_induction (s := 0) (P := fun n φ ↦ ∀ (e : Fin n → M) (ε : ξ → M), φ.Eval e ε → φ.Eval (ι ∘ e) (ι ∘ ε)) _ _ _ _ _ _ n φ hφ
  . intro n φ h e ε
    exact (bounded_absolute ι (Hierarchy.zero_iff_bounded.mp h) e ε).mp
  . intro n φ ψ _ _ ihp ihq e ε h
    exact ⟨ihp e ε h.1, ihq e ε h.2⟩
  . intro n φ ψ _ _ ihp ihq e ε
    exact Or.imp (ihp e ε) (ihq e ε)
  . intro R hR n t φ _ ih e ε
    exact ball_upward ι hR t φ ih e ε
  . intro R hR n t φ _ ih e ε
    exact bexs_upward ι hR t φ ih e ε
  . intro n φ _ ih e ε
    simp only [Semiformula.eval_ex]
    rintro ⟨x, hx⟩
    exact ⟨ι x, by simpa only [Matrix.comp_vecCons''] using ih (x :> e) ε hx⟩

lemma pi_one_downward {n} {φ : Semiformula L ξ n} (hφ : ℬ.Hierarchy 𝚷 1 φ)
    (e : Fin n → M) (ε : ξ → M) :
    φ.Eval (ι ∘ e) (ι ∘ ε) → φ.Eval e ε := by
  have h := sigma_one_upward ι hφ.neg e ε
  classical
  have h₁ : ¬φ.Eval e ε → ¬φ.Eval (ι ∘ e) (ι ∘ ε) := by simpa using h
  exact not_imp_not.mp h₁

lemma shigmaZero_absolute {k} (φ : 𝚺₀.Semisentence ℬ k) (v : Fin k → M) :
    φ.val.Evalb v ↔ φ.val.Evalb (ι ∘ v) := by
  simpa [Semiformula.Evalb, Function.comp_def, Empty.eq_elim] using
    bounded_absolute ι (Hierarchy.zero_iff_bounded.mp φ.sigma_prop) v Empty.elim

lemma sigmaOne_upward_absolute {k} (φ : 𝚺₁.Semisentence ℬ k) (v : Fin k → M) :
    φ.val.Evalb v → φ.val.Evalb (ι ∘ v) := by
  simpa [Semiformula.Evalb, Function.comp_def, Empty.eq_elim] using
    sigma_one_upward ι φ.sigma_prop v Empty.elim

lemma piOne_downward_absolute {k} (φ : 𝚷₁.Semisentence ℬ k) (v : Fin k → M) :
    φ.val.Evalb (ι ∘ v) → φ.val.Evalb v := by
  simpa [Semiformula.Evalb, Function.comp_def, Empty.eq_elim] using
    pi_one_downward ι φ.pi_prop v Empty.elim

lemma deltaOne_absolute {k} (φ : 𝚫₁.Semisentence ℬ k)
    (properM : φ.ProperOn M) (properN : φ.ProperOn N) (v : Fin k → M) :
    φ.val.Evalb v ↔ φ.val.Evalb (ι ∘ v) :=
  ⟨by simpa [HierarchySymbol.Semiformula.val_sigma] using
      sigmaOne_upward_absolute ι φ.sigma v,
   by simpa [properM.iff', properN.iff'] using
      piOne_downward_absolute ι φ.pi v⟩

lemma HierarchySymbol.Defined.shigmaZero_absolute {k}
    {R : (Fin k → M) → Prop} {R' : (Fin k → N) → Prop} {φ : 𝚺₀.Semisentence ℬ k}
    (hR : 𝚺₀.Defined R φ) (hR' : 𝚺₀.Defined R' φ) (v : Fin k → M) :
    R v ↔ R' (ι ∘ v) := by
  simpa [hR.iff, hR'.iff] using Bounding.shigmaZero_absolute ι φ v

lemma HierarchySymbol.DefinedFunction.shigmaZero_absolute_func {k}
    {f : (Fin k → M) → M} {f' : (Fin k → N) → N} {φ : 𝚺₀.Semisentence ℬ (k + 1)}
    (hf : 𝚺₀.DefinedFunction f φ) (hf' : 𝚺₀.DefinedFunction f' φ) (v : Fin k → M) :
    ι (f v) = f' (ι ∘ v) := by
  simpa [Function.comp_def] using
    HierarchySymbol.Defined.shigmaZero_absolute ι hf hf' (f v :> v)

lemma HierarchySymbol.Defined.shigmaOne_absolute {k}
    {R : (Fin k → M) → Prop} {R' : (Fin k → N) → Prop} {φ : 𝚫₁.Semisentence ℬ k}
    (hR : 𝚫₁.Defined R φ) (hR' : 𝚫₁.Defined R' φ) (v : Fin k → M) :
    R v ↔ R' (ι ∘ v) := by
  simpa using deltaOne_absolute ι φ hR.proper hR'.proper v

lemma HierarchySymbol.DefinedFunction.shigmaOne_absolute_func {k}
    {f : (Fin k → M) → M} {f' : (Fin k → N) → N} {φ : 𝚺₁.Semisentence ℬ (k + 1)}
    (hf : 𝚺₁.DefinedFunction f φ) (hf' : 𝚺₁.DefinedFunction f' φ) (v : Fin k → M) :
    ι (f v) = f' (ι ∘ v) := by
  have h := sigmaOne_upward_absolute ι φ (f v :> v)
  simpa [hf.iff, hf'.iff, Function.comp_def] using h

lemma models_iff_of_Sigma0 {n} {σ : Semisentence L n}
    (hσ : ℬ.Hierarchy 𝚺 0 σ) {e : Fin n → M} :
    σ.Evalb (ι ∘ e) ↔ σ.Evalb e := by
  simpa [Semiformula.Evalb, Function.comp_def, Empty.eq_elim] using
    (bounded_absolute ι (Hierarchy.zero_iff_bounded.mp hσ) e Empty.elim).symm

lemma models_iff_of_Delta1 {n} {σ : 𝚫₁.Semisentence ℬ n}
    (hσ : σ.ProperOn M) (hσN : σ.ProperOn N) {e : Fin n → M} :
    σ.val.Evalb (ι ∘ e) ↔ σ.val.Evalb e :=
  (deltaOne_absolute ι σ hσ hσN e).symm

end FFL.FirstOrder.Bounding
