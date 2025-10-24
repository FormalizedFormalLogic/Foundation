import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open Entailment

variable {φ ψ : NNFormula ℕ}

namespace NNFormula.Kripke

def Satisfies (M : Kripke.Model) (x : M.World) : NNFormula ℕ → Prop
  | atom a  =>  M x a
  | natom a => ¬M x a
  | ⊤       => True
  | ⊥       => False
  | φ ⋎ ψ   => Satisfies M x φ ∨ Satisfies M x ψ
  | φ ⋏ ψ   => Satisfies M x φ ∧ Satisfies M x ψ
  | □φ      => ∀ y, x ≺ y → (Satisfies M y φ)
  | ◇φ      => ∃ y, x ≺ y ∧ (Satisfies M y φ)

namespace Satisfies

variable {M : Kripke.Model} {x : M.World}

protected instance semantics : Semantics (NNFormula ℕ) (M.World) := ⟨λ x ↦ Satisfies M x⟩

protected lemma iff_models : x ⊧ φ ↔ Satisfies M x φ := iff_of_eq rfl

@[simp]
protected lemma atom_def (a : ℕ) : x ⊧ (atom a) ↔ M x a := by simp [Satisfies.iff_models, Satisfies];

@[simp]
protected lemma natom_def (a : ℕ) : x ⊧ (natom a) ↔ ¬M x a := by simp [Satisfies.iff_models, Satisfies];

protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies.iff_models, Satisfies];

protected lemma bot_def : ¬x ⊧ ⊥ := by simp [Satisfies.iff_models, Satisfies];

protected lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies.iff_models, Satisfies];

protected lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies.iff_models, Satisfies];

protected lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Satisfies.iff_models, Satisfies];

protected lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Satisfies.iff_models, Satisfies];

protected lemma neg_def : x ⊧ ∼φ ↔ ¬x ⊧ φ := by
  induction φ using NNFormula.rec' generalizing x with
  | hOr φ ψ ihφ ihψ =>
    simp only [DeMorgan.or, Satisfies.or_def, not_or];
    constructor;
    . rintro ⟨h₁, h₂⟩;
      exact ⟨ihφ.mp h₁, ihψ.mp h₂⟩;
    . rintro ⟨h₁, h₂⟩;
      exact ⟨ihφ.mpr h₁, ihψ.mpr h₂⟩;
  | hAnd φ ψ ihφ ihψ =>
    simp only [DeMorgan.and, Satisfies.and_def, not_and_or];
    constructor;
    . rintro (h₁ | h₂);
      . left; exact ihφ.mp h₁;
      . right; exact ihψ.mp h₂;
    . rintro (h₁ | h₂);
      . left; exact ihφ.mpr h₁;
      . right; exact ihψ.mpr h₂;
  | hBox φ ihφ =>
    simp only [ModalDeMorgan.box, Satisfies.box_def];
    push_neg;
    constructor;
    . intro h;
      obtain ⟨y, Rxy, hy⟩ := h;
      use y;
      constructor;
      . exact Rxy;
      . apply ihφ.mp;
        exact hy;
    . rintro ⟨y, Rxy, h⟩;
      use y;
      constructor;
      . exact Rxy;
      . apply ihφ.mpr;
        exact h;
  | hDia φ ihφ =>
    simp only [ModalDeMorgan.dia, Satisfies.dia_def, not_exists, not_and];
    constructor;
    . intro h y Rxy;
      apply ihφ.mp;
      exact h y Rxy;
    . intro h y Rxy;
      apply ihφ.mpr;
      exact h y Rxy;
  | _ => simp [Satisfies.iff_models, Satisfies];

protected lemma imp_def : x ⊧ φ ➝ ψ ↔ x ⊧ φ → x ⊧ ψ := by
  simp [Satisfies.or_def, Satisfies.neg_def];
  tauto;

protected instance : Semantics.Tarski (M.World) where
  models_verum := λ _ => Satisfies.top_def
  models_falsum := λ _ => Satisfies.bot_def
  models_or  := Satisfies.or_def
  models_and := Satisfies.and_def
  models_imply := Satisfies.imp_def
  models_not := Satisfies.neg_def



end Satisfies


def ValidOnModel (M : Kripke.Model) := λ φ => ∀ x, Satisfies M x φ

namespace ValidOnModel

instance semantics : Semantics (NNFormula ℕ) (Kripke.Model) := ⟨λ M ↦ ValidOnModel M⟩

@[simp] protected lemma iff_models : M ⊧ φ ↔ ValidOnModel M φ := iff_of_eq rfl

end ValidOnModel


def ValidOnFrame (F : Kripke.Frame) := λ φ => ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics (NNFormula ℕ) (Kripke.Frame) := ⟨λ F ↦ ValidOnFrame F⟩

@[simp] protected lemma iff_models : F ⊧ φ ↔ ValidOnFrame F φ := iff_of_eq rfl

end ValidOnFrame


def ValidOnFrameClass (C : Kripke.FrameClass) := λ φ => ∀ {F}, F ∈ C → ValidOnFrame F φ

namespace ValidOnFrameClass

instance semantics : Semantics (NNFormula ℕ) (Kripke.FrameClass) := ⟨λ C ↦ ValidOnFrameClass C⟩

@[simp] protected lemma iff_models : C ⊧ φ ↔ ValidOnFrameClass C φ := iff_of_eq rfl

end ValidOnFrameClass

end NNFormula.Kripke


namespace NNFormula.Kripke

variable {φ : NNFormula ℕ}

lemma Satisfies.toFormula : NNFormula.Kripke.Satisfies M x φ ↔ Formula.Kripke.Satisfies M x φ.toFormula := by
  induction φ using NNFormula.rec' generalizing x with
  | hOr φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . apply Formula.Kripke.Satisfies.or_def.mpr;
        left;
        exact ihφ.mp hφ;
      . apply Formula.Kripke.Satisfies.or_def.mpr;
        right;
        exact ihψ.mp hψ;
    . rintro h;
      rcases Formula.Kripke.Satisfies.or_def.mp h with (hφ | hψ);
      . left; exact ihφ.mpr hφ;
      . right; exact ihψ.mpr hψ;
  | hAnd φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      apply Formula.Kripke.Satisfies.and_def.mpr;
      constructor;
      . exact ihφ.mp hφ;
      . exact ihψ.mp hψ;
    . rintro h;
      replace ⟨hφ, hψ⟩ := Formula.Kripke.Satisfies.and_def.mp h;
      constructor;
      . apply ihφ.mpr hφ;
      . apply ihψ.mpr hψ;
  | hBox φ ihφ =>
    constructor;
    . intro h y Rxy;
      apply ihφ.mp;
      exact h y Rxy;
    . intro h y Rxy;
      apply ihφ.mpr;
      exact h y Rxy;
  | hDia φ ihφ =>
    constructor;
    . rintro ⟨y, Rxy, hy⟩;
      apply Formula.Kripke.Satisfies.dia_def.mpr;
      use y;
      constructor;
      . exact Rxy;
      . apply ihφ.mp;
        exact hy;
    . rintro h;
      obtain ⟨y, Rxy, hy⟩ := Formula.Kripke.Satisfies.dia_def.mp h;
      use y;
      constructor;
      . exact Rxy;
      . apply ihφ.mpr;
        exact hy;
  | _ => simp [NNFormula.Kripke.Satisfies, Formula.Kripke.Satisfies];

lemma ValidOnModel.toFormula : NNFormula.Kripke.ValidOnModel M φ ↔ Formula.Kripke.ValidOnModel M φ.toFormula := by
  simp only [NNFormula.Kripke.ValidOnModel, Formula.Kripke.ValidOnModel, Satisfies.toFormula];
  exact ⟨λ h x => h x, λ h x => h x⟩;

lemma ValidOnFrame.toFormula : NNFormula.Kripke.ValidOnFrame F φ ↔ Formula.Kripke.ValidOnFrame F φ.toFormula := ⟨
  λ h V => ValidOnModel.toFormula.mp (h V),
  λ h V => ValidOnModel.toFormula.mpr (h V)
⟩

end NNFormula.Kripke


namespace Formula.Kripke

variable {φ : Formula ℕ}

lemma Satisfies.toNNFormula : Formula.Kripke.Satisfies M x φ ↔ NNFormula.Kripke.Satisfies M x φ.toNNFormula := by
  induction φ generalizing x with
  | hbox φ ihφ =>
    constructor;
    . intro h y Rxy;
      apply ihφ.mp;
      exact h y Rxy;
    . intro h y Rxy;
      apply ihφ.mpr;
      exact h y Rxy;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . rintro h;
      apply NNFormula.Kripke.Satisfies.imp_def.mpr;
      intro hφ;
      apply ihψ.mp;
      apply h;
      apply ihφ.mpr;
      exact hφ;
    . intro h hφ;
      apply ihψ.mpr;
      apply NNFormula.Kripke.Satisfies.imp_def.mp h;
      apply ihφ.mp;
      exact hφ;
  | _ => simp [Formula.Kripke.Satisfies, NNFormula.Kripke.Satisfies];

lemma ValidOnModel.toNNFormula : Formula.Kripke.ValidOnModel M φ ↔ NNFormula.Kripke.ValidOnModel M φ.toNNFormula := ⟨
  fun h x => Satisfies.toNNFormula.mp (h x),
  fun h x => Satisfies.toNNFormula.mpr (h x)
⟩

lemma ValidOnFrame.toNNFormula : Formula.Kripke.ValidOnFrame F φ ↔ NNFormula.Kripke.ValidOnFrame F φ.toNNFormula := ⟨
  fun h V => ValidOnModel.toNNFormula.mp (h V),
  fun h V => ValidOnModel.toNNFormula.mpr (h V)
⟩

end Formula.Kripke


end LO.Modal
