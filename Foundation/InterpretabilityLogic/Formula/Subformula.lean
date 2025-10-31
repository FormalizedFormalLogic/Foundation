import Foundation.InterpretabilityLogic.Formula.Basic

namespace LO.InterpretabilityLogic

variable {α} [DecidableEq α] {φ ψ χ : Formula α}

namespace Formula

@[grind]
def subformulas : Formula α → Finset (Formula α)
  | atom a => {atom a}
  | ⊥      => {⊥}
  | φ ➝ ψ => {φ ➝ ψ} ∪ subformulas φ ∪ subformulas ψ
  | □φ     => {□φ} ∪ subformulas φ
  | φ ▷ ψ  => {φ ▷ ψ} ∪ subformulas φ ∪ subformulas ψ

namespace subformulas

@[simp, grind]
lemma mem_self : φ ∈ φ.subformulas := by induction φ <;> simp_all [subformulas, Finset.mem_union, Finset.mem_singleton]

@[grind ⇒]
lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ
  | hrhd ψ χ ihψ ihχ => simp_all [subformulas]; grind;
  | _ => simp_all [subformulas];

@[grind ⇒] lemma mem_neg (h : (∼ψ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := (mem_imp h).1

@[grind ⇒]
lemma mem_box (h : (□ψ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ
  | hrhd ψ χ ihψ ihχ => simp_all [subformulas]; grind;
  | hbox ψ ihψ => simp_all [subformulas]; grind;
  | _ => simp_all [subformulas];

@[grind ⇒]
lemma mem_rhd (h : (ψ ▷ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ
  | hrhd ψ χ ihψ ihχ => simp_all [subformulas]; grind;
  | _ => simp_all [subformulas];

@[grind ⇒] lemma mem_or (h : (ψ ⋎ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∨ χ ∈ φ.subformulas := by
  simp only [LukasiewiczAbbrev.or] at h;
  grind;

@[grind ⇒] lemma mem_and (h : (ψ ⋏ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  simp only [LukasiewiczAbbrev.and] at h;
  grind;

end subformulas

end Formula


class FormulaFinset.SubformulaClosed (Φ : FormulaFinset α) where
  subfml_closed : ∀ φ ∈ Φ, φ.subformulas ⊆ Φ

namespace FormulaFinset.SubformulaClosed

variable {Φ : FormulaFinset α} [Φ.SubformulaClosed]

@[grind ⇒]
lemma mem_imp (h : φ ➝ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := by
  constructor <;>
  . apply SubformulaClosed.subfml_closed _ h;
    simp [Formula.subformulas];

@[grind ⇒]
lemma mem_neg (h : ∼φ ∈ Φ) : φ ∈ Φ := (mem_imp h).1

@[grind ⇒]
lemma mem_and (h : φ ⋏ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := by
  simp only [LukasiewiczAbbrev.and] at h;
  grind;

@[grind ⇒]
lemma mem_or (h : φ ⋎ ψ ∈ Φ) : φ ∈ Φ ∨ ψ ∈ Φ := by
  simp only [LukasiewiczAbbrev.or] at h;
  grind;

@[grind ⇒]
lemma mem_box (h : □φ ∈ Φ) : φ ∈ Φ := by
  apply SubformulaClosed.subfml_closed _ h;
  simp [Formula.subformulas];

@[grind ⇒]
lemma mem_rhd (h : φ ▷ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := by
  constructor <;>
  . apply SubformulaClosed.subfml_closed _ h;
    simp [Formula.subformulas];

end FormulaFinset.SubformulaClosed


end LO.InterpretabilityLogic
