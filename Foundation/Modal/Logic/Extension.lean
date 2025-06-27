import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Modal.Logic.Basic
import Foundation.Modal.Hilbert.K

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {L L₀ L₁ L₂ L₃ : Logic α}

namespace Logic

inductive sumQuasiNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ}    : L₁ ⊢! φ → sumQuasiNormal L₁ L₂ φ
  | mem₂ {φ}    : L₂ ⊢! φ → sumQuasiNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumQuasiNormal L₁ L₂ (φ ➝ ψ) → sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ ψ
  | subst {φ s} : sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ (φ⟦s⟧)

abbrev addQuasiNormal (L : Logic α) (φ : Formula α) : Logic α := sumQuasiNormal L {φ}

namespace sumQuasiNormal

variable {φ ψ : Formula α}

lemma mem₁! (hφ : L₁ ⊢! φ) : sumQuasiNormal L₁ L₂ ⊢! φ := by
  apply iff_provable.mpr;
  apply sumQuasiNormal.mem₁ hφ;

lemma mem₂! (hφ : L₂ ⊢! φ) : sumQuasiNormal L₁ L₂ ⊢! φ := by
  apply iff_provable.mpr;
  apply sumQuasiNormal.mem₂ hφ;

lemma mdp! (hφψ : (sumQuasiNormal L₁ L₂) ⊢! φ ➝ ψ) (hφ : (sumQuasiNormal L₁ L₂) ⊢! φ) : sumQuasiNormal L₁ L₂ ⊢! ψ := by
  apply iff_provable.mpr;
  apply sumQuasiNormal.mdp;
  . apply iff_provable.mp; exact hφψ;
  . apply iff_provable.mp; exact hφ;


lemma symm : sumQuasiNormal L₁ L₂ = sumQuasiNormal L₂ L₁ := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact sumQuasiNormal.mem₂ h;
    | mem₂ h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | subst _ ihφ => exact sumQuasiNormal.subst ihφ;
  . intro h;
    induction h with
    | mem₁ h => exact sumQuasiNormal.mem₂ h;
    | mem₂ h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | subst _ ihφ => exact sumQuasiNormal.subst ihφ;

variable [DecidableEq α]

instance [L₁.IsQuasiNormal] : Entailment.Lukasiewicz (sumQuasiNormal L₁ L₂) where
  imply₁ _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  imply₂ _ _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  elimContra _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  mdp hφψ hφ := by
    constructor;
    apply sumQuasiNormal.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;

instance [L₁.IsQuasiNormal] : (sumQuasiNormal L₁ L₂).IsQuasiNormal where
  K _ _ := by constructor; apply sumQuasiNormal.mem₁; simp;
  subst s hφ := by
    constructor;
    apply sumQuasiNormal.subst;
    exact PLift.down hφ;

instance [L₂.IsQuasiNormal] : (sumQuasiNormal L₁ L₂).IsQuasiNormal := by
  rw [sumQuasiNormal.symm];
  infer_instance;

instance : L₁ ⪯ sumQuasiNormal L₁ L₂ := by
  apply weakerThan_iff.mpr;
  intro φ hφ;
  apply iff_provable.mpr;
  apply sumQuasiNormal.mem₁ hφ;

instance : L₂ ⪯ sumQuasiNormal L₁ L₂ := by
  rw [sumQuasiNormal.symm];
  infer_instance;

end sumQuasiNormal


inductive sumNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ}    : φ ∈ L₁ → sumNormal L₁ L₂ φ
  | mem₂ {φ}    : φ ∈ L₂ → sumNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumNormal L₁ L₂ (φ ➝ ψ) → sumNormal L₁ L₂ φ → sumNormal L₁ L₂ ψ
  | subst {φ s} : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (φ⟦s⟧)
  | nec {φ}     : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (□φ)

abbrev addNormal (L : Logic α) (φ : Formula α) : Logic α := sumNormal L {φ}

namespace sumNormal

end sumNormal

end Logic




/-
def QuasiNormalExtension (L : Logic) := { L' : Logic // L ⊆ L' ∧ L'.IsQuasiNormal }

namespace QuasiNormalExtension

variable {L₀ : Logic} {L : QuasiNormalExtension L₀}

instance : Membership (Formula ℕ) (QuasiNormalExtension L₀) := ⟨λ L φ => φ ∈ L.1⟩

lemma mem_of_mem_base (h : φ ∈ L₀) : φ ∈ L := L.property.1 h

lemma mem_of_mem_LogicK (h : φ ∈ Logic.K) : φ ∈ L := L.property.2.subset_K h

lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := L.property.2.mdp_closed hφψ hφ

lemma subst (hφ : φ ∈ L) : φ⟦s⟧ ∈ L := L.property.2.subst_closed hφ s

def add (L₁ L₂ : QuasiNormalExtension L₀) : QuasiNormalExtension L₀ where
  val := Logic.sumQuasiNormal L₁.1 L₂.1
  property := by
    constructor;
    . intro φ hφ;
      apply Logic.sumQuasiNormal.mem₁;
      apply mem_of_mem_base hφ;
    . refine ⟨?_, ?_, ?_⟩;
      . intro φ hφ;
        apply Logic.sumQuasiNormal.mem₁;
        apply mem_of_mem_LogicK hφ;
      . intro φ ψ hφ hφψ;
        apply Logic.sumQuasiNormal.mdp hφ hφψ;
      . intro φ hφ s;
        apply Logic.sumQuasiNormal.subst hφ;

instance : Add (QuasiNormalExtension L₀) := ⟨add⟩

/-
instance : Std.IdempotentOp (α := QuasiNormalExtension L₀) (· + ·) where
  idempotent := by
    intro L;
    sorry;

instance : Std.Commutative (α := QuasiNormalExtension L₀) (· + ·) where
  comm := by
    intro L₁ L₂;
    sorry;

instance : Std.Associative (α := QuasiNormalExtension L₀) (· + ·) where
  assoc := by
    intro L₁ L₂ L₃;
    sorry;
-/

def inter (L₁ L₂ : QuasiNormalExtension L₀) : QuasiNormalExtension L₀ where
  val := L₁.1 ∩ L₂.1
  property := by
    constructor;
    . intro φ hφ;
      apply Set.mem_inter <;> exact mem_of_mem_base hφ;
    . refine ⟨?_, ?_, ?_⟩;
      . intro φ hφ;
        apply Set.mem_inter <;> exact mem_of_mem_LogicK hφ;
      . rintro φ ψ ⟨hφψ₁, hφψ₂⟩ ⟨hφ₁, hφ₂⟩;
        apply Set.mem_inter;
        . exact mdp hφψ₁ hφ₁;
        . exact mdp hφψ₂ hφ₂;
      . rintro φ ⟨hφ₁, hφ₂⟩ s;
        apply Set.mem_inter;
        . exact subst hφ₁;
        . exact subst hφ₂;

instance : Inter (QuasiNormalExtension L₀) := ⟨inter⟩

end QuasiNormalExtension


def ExtensionNormal (L : Logic) := { L' : Logic // L'.IsNormal ∧ L ⊆ L' }

namespace ExtensionNormal

end ExtensionNormal
-/

end LO.Modal
