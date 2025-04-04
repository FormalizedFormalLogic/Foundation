import Foundation.ProvabilityLogic.S.Basic
import Mathlib.Order.WellFoundedSet

namespace LO

namespace FirstOrder.DerivabilityCondition

namespace ProvabilityPredicate

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] -- [L.DecidableEq]
         -- {M : Type*} [Nonempty M] [Structure L M]
         {T₀ T : FirstOrder.Theory L} -- [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : ProvabilityPredicate T₀ T} -- [𝔅.HBL]

def iterateAux (𝔅 : ProvabilityPredicate T₀ T) (n : ℕ) : Semisentence L 1 :=
  match n with
  | 0 => 𝔅.prov
  | n + 1 =>
    letI 𝔅n : Semisentence L 1 := 𝔅.iterateAux n;
    letI A : Semisentence L 1 := 𝔅.prov/[#0];
    “x. !𝔅n x”

def iterate (𝔅 : ProvabilityPredicate T₀ T) (n : ℕ+) : Semisentence L 1 := iterateAux 𝔅 (n - 1)

notation 𝔅 "^[" n "]" => iterate 𝔅 n

variable {n : ℕ+} {σ : Sentence L}

-- lemma iterate_one : (𝔅^[1] : Semisentence L 1) = 𝔅.prov := rfl

@[simp]
lemma iterate_one : ((𝔅^[1])/[⌜σ⌝] : Sentence L) = 𝔅.prov/[⌜σ⌝] := rfl

@[simp]
lemma iterate_succ :
  letI σn : Sentence L := (𝔅^[n])/[⌜σ⌝];
  ((𝔅^[n + 1])/[⌜σ⌝] : Sentence L) = (𝔅 σn) := by sorry;

end ProvabilityPredicate

end FirstOrder.DerivabilityCondition


namespace Modal

open Logic

variable {n : ℕ+}

/- Logic GL with boxbot -/
protected abbrev Logic.GLBB (n : ℕ+) := addQuasiNormal Logic.GL (□^[n]⊥)
instance : (Logic.GLBB n).QuasiNormal where
  subset_K := by
    intro φ hφ;
    apply Logic.sumQuasiNormal.mem₁;
    exact Logic.of_mem_K hφ;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    apply Logic.sumQuasiNormal.mdp hφψ hφ;
  subst_closed := by
    intro φ hφ s;
    apply Logic.sumQuasiNormal.subst;
    exact hφ;

@[simp]
lemma Logic.GLBB.boxbot : (□^[n]⊥) ∈ Logic.GLBB n := by
  apply Logic.sumQuasiNormal.mem₂;
  tauto;

theorem Logic.GL_ssubset_GLBB : Logic.GL ⊂ Logic.GLBB n := by
  constructor;
  . intro φ hφ;
    apply Logic.sumQuasiNormal.mem₁;
    assumption;
  . suffices ∃ φ, φ ∈ (Logic.GLBB n) ∧ ¬Hilbert.GL ⊢! φ by
      apply Set.setOf_subset_setOf.not.mpr;
      push_neg;
      exact this;
    use (□^[n]⊥);
    constructor;
    . simp;
    . by_contra hC;
      induction n with
      | one =>
        exact Hilbert.GL.Kripke.consistent.not_bot $ Entailment.unnec! hC;
      | succ n ih =>
        simp only [PNat.add_coe, PNat.val_ofNat, Box.multibox_succ] at hC;
        apply ih $ Entailment.unnec! hC;

section

private inductive Logic.GLBB' (n : ℕ+) : Logic
  | mem_GL : ∀ {φ}, φ ∈ Logic.GL → (Logic.GLBB' n) φ
  | boxbot : Logic.GLBB' n (□^[n]⊥)
  | mdp {φ ψ} : Logic.GLBB' n (φ ➝ ψ) → Logic.GLBB' n φ → Logic.GLBB' n ψ

private lemma Logic.eq_GLBB_GLBB' : Logic.GLBB n = Logic.GLBB' n := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact Logic.GLBB'.mem_GL h;
    | mem₂ h => subst h; exact Logic.GLBB'.boxbot;
    | mdp _ _ ihφψ ihφ => exact Logic.GLBB'.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Logic.GLBB'.mem_GL;
        exact Logic.subst h;
      | boxbot =>
        simp only [Formula.subst.subst_multibox, Formula.subst.subst_bot];
        apply Logic.GLBB'.boxbot;
      | mdp _ _ ihφψ ihφ =>
        simp at ihφψ;
        apply Logic.GLBB'.mdp ihφψ ihφ;
  . intro h;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | boxbot => apply sumQuasiNormal.mem₂; tauto;

@[induction_eliminator]
protected def Logic.GLBB.rec'
  {motive : (φ : Formula ℕ) → φ ∈ (Logic.GLBB n) → Prop}
  (mem_GL : ∀ {φ}, (h : φ ∈ Logic.GL) → motive φ (sumQuasiNormal.mem₁ h))
  (boxbot : motive (□^[n]⊥) (sumQuasiNormal.mem₂ (by tauto)))
  (mdp : ∀ {φ ψ}, {hφψ : φ ➝ ψ ∈ (Logic.GLBB n)} → {hφ : φ ∈ (Logic.GLBB n)} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (sumQuasiNormal.mdp hφψ hφ))
  : ∀ {φ}, (h : φ ∈ Logic.GLBB n) → motive φ h := by
  intro φ h;
  rw [Logic.eq_GLBB_GLBB'] at h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | boxbot => exact boxbot;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . rwa [←Logic.eq_GLBB_GLBB'] at hφψ;
    . rwa [←Logic.eq_GLBB_GLBB'] at hφ;

end

open Entailment
lemma Logic.iff_provable_GL_provable_GLBB : (□^[n]⊥ ➝ φ) ∈ Logic.GL ↔ φ ∈ Logic.GLBB n := by
  constructor;
  . intro hφ;
    replace hφ : (□^[n]⊥ ➝ φ) ∈ Logic.GLBB n := GL_ssubset_GLBB.1 hφ;
    apply Logic.mdp hφ;
    apply Logic.sumQuasiNormal.mem₂;
    tauto;
  . intro hφ;
    induction hφ with
    | mem_GL ih => exact imply₁'! ih;
    | boxbot => simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀₁ ihψ;

def Logic.GLₙ : ℕ → Logic
  | 0     => Logic.GL
  | n + 1 => Logic.GLBB ⟨(n + 1), by omega⟩

end Modal


namespace FirstOrder

open DerivabilityCondition

namespace Theory

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T₀ T U : FirstOrder.Theory L}
         {𝔅 : ProvabilityPredicate T₀ T}

def provabilityHeightSet (U : Theory L) (𝔅 : ProvabilityPredicate T₀ T) : Set ℕ+ := { n | U ⊢!. (𝔅^[n])/[⌜(⊥ : Sentence L)⌝] }

lemma provabilityHeightSet.IsWF : (provabilityHeightSet U 𝔅).IsWF := by
  apply Set.wellFoundedOn_iff.mpr;
  sorry;

open Classical in
noncomputable def provabilityHeight (U : Theory L) (𝔅 : ProvabilityPredicate T₀ T) : ℕ :=
  if hH : (provabilityHeightSet U 𝔅).Nonempty then Set.IsWF.min provabilityHeightSet.IsWF hH |>.1 else 0

lemma provabilityHeight.iff_zero : (provabilityHeight U 𝔅) = 0 ↔ ¬(provabilityHeightSet U 𝔅).Nonempty := by
  constructor;
  . contrapose;
    push_neg;
    sorry;
  . simp_all [provabilityHeight]

lemma provabilityHeight.nobot_of_zero : (provabilityHeight U 𝔅) = 0 ↔ ∀ n, U ⊬. (𝔅^[n])/[⌜(⊥ : Sentence L)⌝] := by
  simp_all [iff_zero, provabilityHeightSet, Set.Nonempty];

end Theory

end FirstOrder


namespace ProvabilityLogic

open Classical
open Entailment Entailment.FiniteContext
open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T₀ T : FirstOrder.Theory L}
         {𝔅 : ProvabilityPredicate T₀ T}

protected lemma GL_classification_provabilityHeight.positive (n : ℕ+):
  (Theory.provabilityHeight T 𝔅 = n) ↔ (∀ A, (∀ {f : Realization L}, T ⊢!. (f.interpret 𝔅 A)) ↔ A ∈ Logic.GLBB n) := by
  constructor;
  . intro h;
    sorry;
  . intro h;
    sorry;

protected lemma GL_classification_provabilityHeight.zero :
  (Theory.provabilityHeight T 𝔅 = 0) ↔ (∀ A, (∀ {f : Realization L}, T ⊢!. (f.interpret 𝔅 A)) ↔ A ∈ Logic.GL) := by
  constructor;
  . intro h;
    have := Theory.provabilityHeight.nobot_of_zero.mp h;
    push_neg at this;
    sorry;
  . contrapose;
    intro h;
    replace h : 1 ≤ Theory.provabilityHeight T 𝔅 := Nat.one_le_iff_ne_zero.mpr h;
    let n : ℕ+ := ⟨Theory.provabilityHeight T 𝔅, by omega⟩;
    by_contra H₁;
    have H₂ : (Theory.provabilityHeight T 𝔅 = Theory.provabilityHeight T 𝔅) ↔ (∀ A, (∀ {f : Realization L}, T ⊢!. (f.interpret 𝔅 A)) ↔ A ∈ Logic.GLBB n) :=
      GL_classification_provabilityHeight.positive n;
    simp only [true_iff] at H₂;
    have : Logic.GL = Logic.GLBB n := by ext A; exact Iff.trans (H₁ A |>.symm) $ H₂ A;
    have : Logic.GL ≠ Logic.GLBB n := Set.ssubset_iff_subset_ne.mp (Modal.Logic.GL_ssubset_GLBB (n := n)) |>.2;
    contradiction;

theorem GL_classification_provabilityHeight (n : ℕ):
  (Theory.provabilityHeight T 𝔅 = n) ↔ (∀ A, (∀ {f : Realization L}, T ⊢!. (f.interpret 𝔅 A)) ↔ A ∈ Logic.GLₙ n) := by
  match n with
  | n + 1 => apply GL_classification_provabilityHeight.positive ⟨(n + 1), by omega⟩;
  | 0 => apply GL_classification_provabilityHeight.zero;

end ProvabilityLogic


end LO
