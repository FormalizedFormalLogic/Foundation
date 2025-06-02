import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Kripke.Logic.K

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
  induction φ generalizing x with
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
  simp [←NNFormula.imp_eq, NNFormula.imp, Satisfies.or_def, Satisfies.neg_def];
  tauto;

protected lemma iff_def : x ⊧ φ ⭤ ψ ↔ (x ⊧ φ ↔ x ⊧ ψ) := by
  constructor;
  . intro h;
    have ⟨hφψ, hψφ⟩ := Satisfies.and_def.mp h;
    constructor;
    . exact Satisfies.imp_def.mp hφψ;
    . exact Satisfies.imp_def.mp hψφ;
  . rintro ⟨hφψ, hψφ⟩;
    apply Satisfies.and_def.mpr;
    constructor;
    . apply Satisfies.imp_def.mpr; exact hφψ;
    . apply Satisfies.imp_def.mpr; exact hψφ;

protected instance : Semantics.Tarski (M.World) where
  realize_top := λ _ => Satisfies.top_def
  realize_bot := λ _ => Satisfies.bot_def
  realize_or  := Satisfies.or_def
  realize_and := Satisfies.and_def
  realize_imp := Satisfies.imp_def
  realize_not := Satisfies.neg_def



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


namespace Hilbert.K.NNFormula

open Formula.Kripke

variable {φ ψ : NNFormula _}

lemma iff_neg : Hilbert.K ⊢! ∼(φ.toFormula) ⭤ (∼φ).toFormula := by
  apply Hilbert.K.Kripke.complete.complete;
  intro F _ V x;
  apply Satisfies.iff_def.mpr;
  induction φ generalizing x with
  | hOr φ ψ ihφ ihψ =>
    constructor;
    . intro h;
      replace h := Satisfies.or_def.not.mp $ Satisfies.not_def.mp h;
      push_neg at h;
      apply Satisfies.and_def.mpr;
      constructor;
      . apply ihφ x |>.mp; exact h.1;
      . apply ihψ x |>.mp; exact h.2;
    . intro h;
      replace h := Satisfies.and_def.mp h;
      apply Satisfies.or_def.not.mpr;
      push_neg;
      constructor;
      . apply ihφ x |>.mpr;
        exact h.1;
      . apply ihψ x |>.mpr;
        exact h.2;
  | hAnd φ ψ ihφ ihψ =>
    constructor;
    . intro h;
      replace h := Satisfies.and_def.not.mp $ Satisfies.not_def.mp h;
      set_option push_neg.use_distrib true in push_neg at h;
      apply Satisfies.or_def.mpr;
      rcases h with (hφ | hψ);
      . left; apply ihφ x |>.mp; exact hφ;
      . right; apply ihψ x |>.mp; exact hψ;
    . intro h;
      apply Satisfies.and_def.not.mpr;
      set_option push_neg.use_distrib true in push_neg;
      rcases Satisfies.or_def.mp h with (hφ | hψ);
      . left; apply ihφ x |>.mpr; exact hφ;
      . right; apply ihψ x |>.mpr; exact hψ;
  | hBox φ ih =>
    constructor;
    . intro h;
      replace h := Satisfies.box_def.not.mp $ Satisfies.not_def.mp h;
      push_neg at h;
      obtain ⟨y, Rxy, hy⟩ := h;
      apply Satisfies.dia_def.mpr;
      use y;
      constructor;
      . assumption;
      . apply ih y |>.mp hy;
    . intro h;
      obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use y;
      constructor;
      . assumption;
      . apply ih y |>.mpr hy;
  | hDia φ ih =>
    constructor;
    . intro h;
      replace h := Satisfies.dia_def.not.mp $ Satisfies.not_def.mp h;
      push_neg at h;
      intro y Rxy;
      exact ih y |>.mp $ h _ Rxy;
    . intro h;
      apply Satisfies.dia_def.not.mpr;
      push_neg;
      intro y Rxy;
      exact ih y |>.mpr $ h y Rxy;
  | _ => simp [Satisfies, Semantics.Realize];

lemma exists_CNF_DNF (φ : NNFormula _) :
  (∃ Γ : MNFSegments ℕ, Γ.toMCNF.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ Γ.toMCNF) ∧
  (∃ Δ : MNFSegments ℕ, Δ.toMDNF.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ Δ.toMDNF)
  := by
  sorry;

lemma exists_CNF (φ : NNFormula _) : ∃ Γ : MNFSegments ℕ, Γ.toMCNF.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ Γ.toMCNF := exists_CNF_DNF φ |>.1
lemma exists_DNF (φ : NNFormula _) : ∃ Δ : MNFSegments ℕ, Δ.toMDNF.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ Δ.toMDNF := exists_CNF_DNF φ |>.2

/-
lemma exists_CNF_DNF (φ : NNFormula _) :
  (∃ γ : NNFormula _, γ.isModalCNF ∧ γ.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ γ.toFormula) ∧
  (∃ δ : NNFormula _, δ.isModalDNF ∧ δ.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ δ.toFormula)
  := by
  induction φ with
  | hAtom a   => constructor <;> . use (.atom a); simp;
  | hNatom a  => constructor <;> . use (.natom a); simp;
  | hVerum    => constructor <;> . use ⊤; simp;
  | hFalsum   => constructor <;> . use ⊥; simp;
  | hBox φ ih => constructor <;> . use (□φ); simp;
  | hDia φ ih => constructor <;> . use (◇φ); simp;
  | hAnd φ ψ ihφ ihψ =>
    obtain ⟨⟨γφ, hγφ₁, hγφ₂, hγφ₃⟩, ⟨δφ, hδφ₁, hδφ₂, hδφ₃⟩⟩ := ihφ;
    obtain ⟨⟨γψ, hγψ₁, hγψ₂, hγψ₃⟩, ⟨δψ, hδψ₁, hδψ₂, hδψ₃⟩⟩ := ihψ;
    constructor;
    . use (γφ ⋏ γψ);
      refine ⟨?_, ?_, ?_⟩;
      . tauto;
      . sorry;
      . apply EKK!_of_E!_of_E! <;> assumption;
    . match δφ, δψ with
      | δφ₁ ⋎ δφ₂, δψ₁ ⋎ δψ₂ =>
        use (δφ₁ ⋏ δψ₁) ⋎ (δφ₂ ⋏ δψ₂);
        constructor;
        . simp [NNFormula.isModalDNF] at hδφ₁ hδψ₁;
          constructor;
          . sorry;
          . sorry;
        . simp [NNFormula.toFormula] at hδφ₂ hδψ₂ ⊢;
          sorry;
      | δφ₁ ⋎ δφ₂, δψ =>
        sorry;
      | δφ, δψ₁ ⋎ δψ₂ =>
        sorry;
      | δφ, δψ =>
        sorry;
  | hOr φ ψ ihφ ihψ =>
    obtain ⟨⟨γφ, hγφ₁, hγφ₂, hγφ₃⟩, ⟨δφ, hδφ₁, hδφ₂, hδφ₃⟩⟩ := ihφ;
    obtain ⟨⟨γψ, hγψ₁, hγψ₂, hγψ₃⟩, ⟨δψ, hδψ₁, hδψ₂, hδψ₃⟩⟩ := ihψ;
    constructor;
    . sorry;
    . use (δφ ⋎ δψ);
      refine ⟨?_, ?_, ?_⟩;
      . tauto;
      . sorry;
      . apply EAA!_of_E!_of_E! <;> assumption;

lemma exists_CNF (φ : NNFormula _) : ∃ γ : NNFormula _, γ.isModalCNF ∧ γ.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ γ.toFormula := exists_CNF_DNF φ |>.1
lemma exists_DNF (φ : NNFormula _) : ∃ δ : NNFormula _, δ.isModalDNF ∧ δ.degree = φ.degree ∧ Hilbert.K ⊢! φ.toFormula ⭤ δ.toFormula := exists_CNF_DNF φ |>.2
-/

end Hilbert.K.NNFormula


end LO.Modal
