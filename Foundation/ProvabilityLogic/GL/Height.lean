import Foundation.ProvabilityLogic.S.Basic

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

end Modal

end LO
