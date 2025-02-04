import Foundation.Modal.Formula


namespace LO.Modal

def Formula.subformulas [DecidableEq α] : Formula α → FormulaFinset α
  | atom a => {(atom a)}
  | ⊥      => {⊥}
  | φ ➝ ψ  => insert (φ ➝ ψ) (φ.subformulas ∪ ψ.subformulas)
  | □φ     => insert (□φ) φ.subformulas

namespace Formula.subformulas

variable [DecidableEq α]

@[simp] lemma mem_self {φ : Formula α} : φ ∈ φ.subformulas := by induction φ <;> { simp [subformulas]; try tauto; }

variable {φ ψ χ : Formula α}

lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | himp => simp_all [subformulas]; rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all
  | _ => simp_all [subformulas];

lemma mem_imp₁ (h : (ψ ➝ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := mem_imp h |>.1

lemma mem_imp₂ (h : (ψ ➝ χ) ∈ φ.subformulas) : χ ∈ φ.subformulas := mem_imp h |>.2

lemma mem_box (h : □ψ ∈ φ.subformulas) : ψ ∈ φ.subformulas := by
  induction φ using Formula.rec' <;> {
    simp_all [subformulas];
    try rcases h with (hq | hr); simp_all; simp_all;
  };

-- TODO: add tactic like `subformulas`.
attribute [aesop safe 5 forward]
  mem_imp₁
  mem_imp₂
  mem_box

@[simp]
lemma complexity_lower (h : ψ ∈ φ.subformulas) : ψ.complexity ≤ φ.complexity  := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp_all [subformulas];
    rcases h with _ | h₁ | h₂;
    . subst_vars; simp [Formula.complexity];
    . have := ihp₁ h₁; simp [Formula.complexity]; omega;
    . have := ihp₂ h₂; simp [Formula.complexity]; omega;
  | hbox φ ihp =>
    simp_all [subformulas];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.complexity];
    . have := ihp h₁; simp [Formula.complexity]; omega;
  | hatom => simp_all [subformulas];
  | hfalsum => simp_all [subformulas, Formula.complexity];

/-
@[simp]
lemma degree_lower (h : ψ ∈ φ.subformulas) : ψ.degree ≤ φ.degree := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp_all [subformulas];
    rcases h with rfl | h₁ | h₂;
    . simp_all [Formula.degree];
    . have := ihp₁ h₁; simp [Formula.degree]; omega;
    . have := ihp₂ h₂; simp [Formula.degree]; omega;
  | hbox φ ihp =>
    simp_all [subformulae];
    rcases h with _ | h₁;
    . subst_vars; simp [Formula.degree];
    . have := ihp h₁; simp [Formula.degree]; omega;
  | hatom =>
    simp_all [subformulae];
    rcases h with rfl | rfl <;> simp [Formula.degree];
  | hfalsum => simp_all [subformulae, Formula.degree];
-/

end Formula.subformulas


class FormulaSet.SubformulaClosed (P : FormulaSet α) where
  imp_closed : ∀ {φ ψ}, φ ➝ ψ ∈ P → φ ∈ P ∧ ψ ∈ P
  box_closed : ∀ {φ}, □φ ∈ P → φ ∈ P

namespace FormulaSet.SubformulaClosed

variable {φ : Formula α} {P : FormulaSet α} [hP : P.SubformulaClosed]

lemma mem_imp₁ (h : φ ➝ ψ ∈ P) : φ ∈ P := hP.imp_closed h |>.1
lemma mem_imp₂ (h : φ ➝ ψ ∈ P) : ψ ∈ P := hP.imp_closed h |>.2
lemma mem_box (h : □φ ∈ P) : φ ∈ P := hP.box_closed h

instance {φ : Formula α} [DecidableEq α] : FormulaSet.SubformulaClosed (φ.subformulas).toSet where
  box_closed := by
    intro φ hφ;
    exact Formula.subformulas.mem_box hφ;
  imp_closed := by
    intro φ ψ hφ;
    exact Formula.subformulas.mem_imp hφ;

end FormulaSet.SubformulaClosed

end LO.Modal
