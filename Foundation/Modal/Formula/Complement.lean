module

public import Foundation.Modal.Formula.Basic
public import Foundation.Propositional.Entailment.Cl.Basic

@[expose] public section

namespace LO.Modal

namespace Formula

@[grind]
def complement : Formula α → Formula α
  | ∼φ => φ
  | φ  => ∼φ
prefix:80 "-" => complement

namespace complement

variable {φ ψ : Formula α}

@[simp, grind =] lemma neg_def : -(∼φ) = φ := by induction φ <;> simp_all [complement]
@[simp, grind =] lemma bot_def : -(⊥ : Formula α) = ∼⊥ := by simp only [complement];
@[simp, grind =] lemma box_def : -(□φ) = ∼(□φ) := by simp only [complement];

@[grind =>]
lemma imp_def₁ (hq : ψ ≠ ⊥) : -(φ 🡒 ψ) = ∼(φ 🡒 ψ) := by
  dsimp [complement];
  grind [Formula.inj_imp];

@[grind =>]
lemma imp_def₂ (hq : ψ = ⊥) : -(φ 🡒 ψ) = φ := by
  subst hq;
  apply neg_def;

lemma resort_box (h : -φ = □ψ) : φ = ∼□ψ := by
  dsimp [complement] at h;
  split at h;
  . subst h; rfl;
  . contradiction;

lemma or [DecidableEq α] (φ : Formula α) : -φ = ∼φ ∨ ∃ ψ, ∼ψ = φ := by
  induction φ using Formula.cases_neg with
  | himp _ _ hn => simp [imp_def₁ hn];
  | _ => simp [complement];

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

lemma complementary_mem_box (hi : ∀ {ψ χ}, ψ 🡒 χ ∈ P → ψ ∈ P) : □φ ∈ P⁻ → □φ ∈ P := by
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


section

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S} [Entailment.Cl 𝓢] {φ : Formula _}

lemma complement_derive_bot [DecidableEq α] (hp : 𝓢 ⊢ φ) (hcp : 𝓢 ⊢ -φ) : 𝓢 ⊢ ⊥ := by
  induction φ using Formula.cases_neg with
  | hfalsum => assumption;
  | hatom a => unfold Formula.complement at hcp; exact hcp ⨀ hp;
  | hneg => unfold Formula.complement at hcp; exact hp ⨀ hcp;
  | hbox φ => unfold Formula.complement at hcp; exact hcp ⨀ hp;
  | himp φ ψ h =>
    simp only [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;

lemma neg_complement_derive_bot [DecidableEq α] (hp : 𝓢 ⊢ ∼φ) (hcp : 𝓢 ⊢ ∼(-φ)) : 𝓢 ⊢ ⊥ := by
  induction φ using Formula.cases_neg with
  | hfalsum =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;
  | hatom a =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    unfold Formula.complement at hcp;
    exact hp ⨀ hcp;
  | himp φ ψ h =>
    simp only [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox φ =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;

open Entailment

lemma of_imply_complement_bot [DecidableEq α] (h : 𝓢 ⊢ (-φ) 🡒 ⊥) : 𝓢 ⊢ φ := by
  rcases Formula.complement.or (φ := φ) with (hφ | ⟨ψ, rfl⟩);
  . rw [hφ] at h;
    apply of_NN!;
    apply N!_iff_CO!.mp h;
  . simp only [Formula.complement] at h;
    apply N!_iff_CO!.mpr h;

end

end LO.Modal
end
