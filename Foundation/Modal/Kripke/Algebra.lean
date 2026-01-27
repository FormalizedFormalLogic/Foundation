module

public import Foundation.Modal.Formula.Basic
public import Foundation.Modal.Logic.Basic
public import Foundation.Modal.Algebra.Basic
public import Foundation.Modal.Kripke.Basic

@[expose] public section

namespace LO.Modal


namespace Kripke

namespace Frame

abbrev dual (F : Kripke.Frame) := Set F.World
postfix:max "⁺" => Frame.dual

variable {F : Kripke.Frame} {A B : F⁺} {x : F.World}

def box (F : Kripke.Frame) : F⁺ → F⁺ := λ A => { x | ∀ y, x ≺ y → y ∈ A }
def dia (F : Kripke.Frame) : F⁺ → F⁺ := λ A => { x | ∃ y, x ≺ y ∧ y ∈ A }

instance : Box F⁺ := ⟨box F⟩
instance : Dia F⁺ := ⟨dia F⟩

@[grind =] lemma mem_def_dia : x ∈ ◇A ↔ ∃ y, x ≺ y ∧ y ∈ A := Iff.rfl
@[grind =] lemma mem_def_box : x ∈ □A ↔ ∀ y, x ≺ y → y ∈ A := Iff.rfl

instance : ModalAlgebra F⁺ where
  box_top := by
    ext x;
    simp [mem_def_box];
  box_meet {A B} := by
    ext x;
    simp [mem_def_box];
    grind;
  dual_dia {A} := by
    ext x;
    simp [mem_def_dia, mem_def_box];

end Frame

variable {F : Kripke.Frame} {A B : F⁺} {x : F.World} {φ ψ : Formula ℕ}

def Valuation.toV (V : Valuation F) : ℕ → F⁺ := λ n x => V x n

open Formula.Kripke

lemma algebraic_lemma (F : Kripke.Frame) (V : Valuation F) (x : F.World) : (Satisfies ⟨F, V⟩ x φ) ↔ x ∈ ((V.toV) ⊩ φ) := by
  induction φ generalizing x with
  | hatom a => simp [Satisfies, Formula.value]; tauto;
  | hfalsum => simp [Satisfies];
  | himp φ ψ ihφ ihψ => simp [Satisfies, ihφ x, ihψ x]; tauto;
  | hbox φ ihφ => simp [Satisfies, ihφ, Frame.mem_def_box];

lemma algebraic_imp : F ⊧ φ ➝ ψ ↔ (∀ V : ℕ → F⁺, (V ⊩ φ) ≤ (V ⊩ ψ)) := by
  constructor;
  . intro H V x h;
    apply algebraic_lemma _ (λ x a => V a x) _ |>.mp;
    apply H;
    apply algebraic_lemma _ (λ x a => V a x) _ |>.mpr;
    exact h;
  . intro H V x h;
    apply algebraic_lemma _ (λ x a => V x a) _ |>.mpr;
    apply H;
    apply algebraic_lemma _ (λ x a => V x a) _ |>.mp;
    exact h;

lemma algebraic_iff : F ⊧ φ ⭤ ψ ↔ (∀ V : ℕ → F⁺, (V ⊩ φ) = (V ⊩ ψ)) := by
  constructor;
  . intro H V;
    apply le_antisymm;
    . apply algebraic_imp.1;
      intro V x;
      apply (Satisfies.iff_def.mp $ H V x).1;
    . apply algebraic_imp.1;
      intro V x;
      apply (Satisfies.iff_def.mp $ H V x).2;
  . intro H V x;
    apply Satisfies.iff_def.mpr;
    constructor;
    . intro h;
      apply algebraic_imp (φ := φ).2;
      . grind;
      . exact h;
    . intro h;
      apply algebraic_imp (φ := ψ).2;
      . grind;
      . exact h;

lemma algebraic : F ⊧ φ ↔ (∀ V : ℕ → F⁺, (V ⊩ φ) = ⊤) := by
  have := algebraic_iff (F := F) (φ := φ) (ψ := ⊤);
  simp_all only [
    ValidOnFrame.models_iff, Formula.eq_value_verum, Set.top_eq_univ,
    Set.eq_univ_iff_forall
  ];
  apply Iff.trans ?_ this;
  constructor;
  . simp [ValidOnFrame, ValidOnModel, Semantics.Models, Satisfies];
  . simp [ValidOnFrame, ValidOnModel, Semantics.Models, Satisfies];

end Kripke

end LO.Modal

end
