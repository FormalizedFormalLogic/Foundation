import Foundation.Modal.Formula
import Foundation.Modal.Subformulas


namespace LO.Modal


namespace Formula

def complement : Formula α → Formula α
  | ∼φ => φ
  | φ  => ∼φ
prefix:80 "-" => complement

namespace complement

variable {φ ψ : Formula α}

@[simp] lemma neg_def : -(∼φ) = φ := by
  induction φ using Formula.rec' <;> simp_all [complement]

@[simp] lemma bot_def : -(⊥ : Formula α) = ∼(⊥) := by simp only [complement, imp_inj, and_true]; rfl;

@[simp] lemma box_def : -(□φ) = ∼(□φ) := by simp only [complement, imp_inj, and_true]; rfl;

lemma imp_def₁ (hq : ψ ≠ ⊥) : -(φ ➝ ψ) = ∼(φ ➝ ψ) := by
  simp only [complement];
  split;
  . rename_i h; simp [imp_eq, falsum_eq, hq] at h;
  . rfl;

lemma imp_def₂ (hq : ψ = ⊥) : -(φ ➝ ψ) = φ := by
  subst_vars;
  apply neg_def;

lemma resort_box (h : -φ = □ψ) : φ = ∼□ψ := by
  simp [complement] at h;
  split at h;
  . subst_vars; rfl;
  . contradiction;

lemma or [DecidableEq α] (φ : Formula α) : -φ = ∼φ ∨ ∃ ψ, ∼ψ = φ := by
  induction φ using Formula.cases_neg with
  | himp _ _ hn => simp [imp_def₁ hn];
  | hfalsum => simp;
  | hneg => simp;
  | hatom a => simp [complement];
  | hbox φ => simp [complement]; rfl;

end complement

end Formula


namespace FormulaFinset

variable [DecidableEq α]

def complementary (P : FormulaFinset α) : FormulaFinset α := P ∪ (P.image (Formula.complement))
postfix:80 "⁻" => complementary

variable {P P₁ P₂ : FormulaFinset α} {φ ψ χ : Formula α}

lemma complementary_mem (h : φ ∈ P) : φ ∈ P⁻ := by simp_all [complementary];

lemma complementary_comp (h : φ ∈ P) : -φ ∈ P⁻ := by simp [complementary]; tauto;

lemma mem_of (h : φ ∈ P⁻) : φ ∈ P ∨ ∃ ψ ∈ P, -ψ = φ := by simpa [complementary] using h;

lemma complementary_mem_box (hi : ∀ {ψ χ}, ψ ➝ χ ∈ P → ψ ∈ P := by trivial) : □φ ∈ P⁻ → □φ ∈ P := by
  intro h;
  rcases (mem_of h) with (h | ⟨ψ, hq, eq⟩);
  . assumption;
  . replace eq := Formula.complement.resort_box eq;
    subst eq;
    exact hi hq;


class ComplementaryClosed (P : FormulaFinset α) (S : FormulaFinset α) : Prop where
  subset : P ⊆ S⁻
  either : ∀ φ ∈ S, φ ∈ P ∨ -φ ∈ P


def SubformulaeComplementaryClosed (P : FormulaFinset α) (φ : Formula α) : Prop := P.ComplementaryClosed φ.subformulas


end FormulaFinset

end LO.Modal
