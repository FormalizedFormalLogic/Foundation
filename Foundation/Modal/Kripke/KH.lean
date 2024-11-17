import Foundation.Modal.Kripke.Semantics
import Foundation.Modal.Kripke.GL.Definability

namespace Set

variable {s t : Set α}

abbrev Cofinite (s : Set α) := sᶜ.Finite

lemma cofinite_compl : sᶜ.Cofinite ↔ s.Finite := by simp [Set.Cofinite];

lemma comp_finite : s.Finite → sᶜ.Cofinite := cofinite_compl.mpr

end Set


namespace LO.Modal

open System
open Kripke
open Formula
open Formula.Kripke


namespace Kripke

variable {F : Kripke.Frame} {a : ℕ}

lemma valid_atomic_H_of_valid_atomic_L : F ⊧ (Axioms.L (atom a)) → F ⊧ (Axioms.H (atom a)) := by
  intro h V x hx;
  have : Satisfies ⟨F, V⟩ x (□(□a ➝ a)) := by
    intro y Rxy;
    exact (Satisfies.and_def.mp $ @hx y Rxy) |>.1;
  exact @h V x this;

lemma valid_atomic_L_of_valid_atomic_H : F ⊧ Axioms.H (atom a) → F ⊧ Axioms.L (atom a) := by
  intro hH V x hx;

  let V' : Valuation F := λ w a => ∀ n : ℕ, Satisfies ⟨F, V⟩ w (□^[n] a);

  have h₁ : Satisfies ⟨F, V'⟩ x (□(□a ⭤ a)) := by
    intro y Rxy;
    have : Satisfies ⟨F, V'⟩ y a ↔ Satisfies ⟨F, V'⟩ y (□a) := calc
      _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (□^[(n + 1)]a) := by
        constructor;
        . intro h n; apply h;
        . intro h n;
          have h₁ : Satisfies ⟨F, V⟩ y (□□^[n](atom a) ➝ □^[n](atom a)) := by
            induction n with
            | zero => apply @hx y Rxy;
            | succ n => intro _; apply h;
          apply h₁;
          simpa using h n;
      _ ↔ ∀ n, ∀ z, y ≺ z → Satisfies ⟨F, V⟩ z (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ z, y ≺ z → ∀ n : ℕ, Satisfies ⟨F, V⟩ z (□^[n]a) := by aesop;
      _ ↔ ∀ z, y ≺ z → Satisfies ⟨F, V'⟩ z (atom a) := by simp [Satisfies];
      _ ↔ Satisfies ⟨F, V'⟩ y (□(atom a)) := by simp [Satisfies];
    apply Satisfies.iff_def.mpr;
    exact this.symm;

  have h₂ : Satisfies ⟨F, V'⟩ x (□atom a) := @hH V' x h₁;

  intro w Rxw;
  exact @h₂ w Rxw 0;

lemma valid_atomic_L_iff_valid_atomic_H : F ⊧ Axioms.L (atom a) ↔ F ⊧ Axioms.H (atom a) := by
  constructor;
  . exact valid_atomic_H_of_valid_atomic_L;
  . exact valid_atomic_L_of_valid_atomic_H;

lemma valid_atomic_4_of_valid_atomic_L (F_trans : Transitive F) : F ⊧ Axioms.L (atom a) → F ⊧ Axioms.Four (atom a) := by
  intro h V x h₂ y Rxy z Ryz;
  refine h₂ z ?_;
  exact F_trans Rxy Ryz;

lemma valid_atomic_4_of_valid_atomic_H (F_trans : Transitive F) : F ⊧ Axioms.H (atom a) → F ⊧ Axioms.Four (atom a) := by
  intro h;
  apply valid_atomic_4_of_valid_atomic_L;
  . assumption;
  . exact valid_atomic_L_of_valid_atomic_H h;

lemma valid_on_frame_Four_of_L (h : F ⊧* 𝗟) : F ⊧* 𝟰 := by
  have trans := trans_of_L h;
  simp_all [Axioms.L, Axioms.Four];
  intro φ V x hx y Rxy;
  apply h φ V y;
  intro z Ryz h₂;
  apply hx;
  exact trans Rxy Ryz;

lemma valid_atomic_Four_of_valid_atomic_H : F ⊧ Axioms.H (atom a) → F ⊧ Axioms.Four (atom a) := by
  intro h V x h₂ y Rxy z Ryz;
  have := valid_atomic_L_iff_valid_atomic_H.mpr h V x;
  sorry;

end Kripke


namespace Hilbert.KH.Kripke

/--
  `0♯ ≺ 1♯ ≺ 2# ≺ ⋯ ≺ n♯ ≺ ⋯ ≺ n♭ ⋯ ≺ 2♭ ≺ 1♭ ≺ 0♭`

  - reflexive in `♯`
  - irreflexive in `♭`
-/
abbrev cresswellFrame : Kripke.Frame where
  World := ℕ × Fin 2
  Rel n m :=
    match n, m with
    | (n, 0), (m, 0) => n ≤ m + 1
    | (n, 1), (m, 1) => n > m
    | (_, 0), (_, 1) => True
    | _, _ => False

namespace cresswellFrame

abbrev Sharp := { w : cresswellFrame.World // w.2 = 0 }
-- instance : LE cresswellFrame.SharpWorld := ⟨λ x y => x.1 ≤ y.1⟩

@[match_pattern]
abbrev sharp (n : ℕ) : Sharp := ⟨(n, 0), rfl⟩
postfix:max "♯" => sharp

lemma sharp_iff {n m : Sharp} : n.1 ≺ m.1 ↔ n.1.1 ≤ m.1.1 + 1 := by aesop;

@[simp]
lemma sharp_refl {n : Sharp} : n.1 ≺ n.1 := by
  obtain ⟨⟨n, _⟩, ⟨_, rfl⟩⟩ := n;
  simp [Frame.Rel'];


abbrev Flat := { w : cresswellFrame.World // w.2 = 1 }
-- instance : LE cresswellFrame.SharpWorld := ⟨λ x y => x.1 ≤ y.1⟩

@[match_pattern]
abbrev flat (n : ℕ) : Flat := ⟨(n, 1), rfl⟩
postfix:max "♭" => flat

lemma flat_iff {n m : Flat} : n.1 ≺ m.1 ↔ n.1.1 > m.1.1 := by aesop;

@[simp]
lemma flat_irrefl {n : Flat} : ¬(n.1 ≺ n.1) := by
  obtain ⟨⟨n, _⟩, ⟨_, rfl⟩⟩ := n;
  simp [Frame.Rel'];


@[simp]
lemma bridge {n : Sharp} {m : Flat} : n.1 ≺ m.1 := by
  obtain ⟨⟨n, _⟩, ⟨_, rfl⟩⟩ := n;
  obtain ⟨⟨m, _⟩, ⟨_, rfl⟩⟩ := m;
  simp [Frame.Rel'];

-- @[simp] lemma cannot_back : ¬(n♭ ≺ m♯) := by simp [Frame.Rel'];

-- lemma sharp_cresc (h : n ≤ m) : n♯ ≺ m♯ := by omega;

lemma is_transitive : Transitive cresswellFrame.Rel := by
  rintro x y z Rxy Ryz;
  match x, y, z with
  | x♯, y♯, z♯ => sorry;
  | x♯, y♯, z♭ => simp;
  | x♯, y♭, z♯ => trivial;
  | x♯, y♭, z♭ => trivial;
  | x♭, y♯, z♯ => trivial;
  | x♭, y♯, z♭ => trivial;
  | x♭, y♭, z♯ => trivial;
  | x♭, y♭, z♭ => omega;

end cresswellFrame


abbrev cresswellModel : Kripke.Model := ⟨cresswellFrame, λ w _ => w ≠ 0♯⟩

@[reducible]
instance : Semantics (Formula ℕ) cresswellModel.World := Formula.Kripke.Satisfies.semantics (M := cresswellModel)

lemma not_satisfies_atomic_Four_on_cresswellModel : ¬(Satisfies (cresswellModel) 2♯ (Axioms.Four (atom a))) := by
  apply Satisfies.imp_def.not.mpr;
  push_neg;
  constructor;
  . intro x h;
    match x with
    | x♯ =>
      apply Satisfies.atom_def.mpr;
      have : 1 ≤ x := by simpa using cresswellFrame.sharp_iff.mp h;
      suffices x ≠ 0 by simpa;
      omega;
    | x♭ =>
      apply Satisfies.atom_def.mpr;
      simp;
  . apply Satisfies.box_def.not.mpr; push_neg;
    use 1♯;
    constructor;
    . apply cresswellFrame.sharp_iff.mpr;
      tauto;
    . apply Satisfies.box_def.not.mpr; push_neg;
      use 0♯;
      constructor;
      . apply cresswellFrame.sharp_iff.mpr;
        tauto;
      . apply Satisfies.atom_def.not.mpr;
        simp;

lemma not_valid_Four_on_cresswellFrame : ¬(cresswellFrame) ⊧* 𝟰 := by
  apply Semantics.RealizeSet.setOf_iff.not.mpr; push_neg;
  use Axioms.Four (atom 0);
  constructor;
  . tauto;
  . apply ValidOnFrame.not_valid_iff_exists_valuation_world.mpr;
    use (cresswellModel), 2♯;
    exact not_satisfies_atomic_Four_on_cresswellModel;

abbrev cresswellModel.truthset (φ) := { w : cresswellModel.World | Satisfies _ w φ }

namespace cresswellModel.truthset

variable {φ ψ : Formula ℕ}

lemma def_top : truthset ⊤ = Set.univ := by simp [truthset, Satisfies];

lemma def_bot : truthset ⊥ = ∅ := by tauto;

lemma def_imp : truthset (φ ➝ ψ) = (truthset φ)ᶜ ∪ truthset ψ := by
  simp_all [truthset, Satisfies, imp_iff_not_or];
  rfl;

lemma either_finite_cofinite : (truthset φ).Finite ∨ (truthset φ).Cofinite := by
  induction φ using Formula.rec' with
  | hatom a =>
    right;
    simp [truthset, cresswellModel, Set.Cofinite, Satisfies];
  | hfalsum => simp [def_bot];
  | himp φ ψ ihφ ihψ =>
    rw [def_imp];
    rcases ihφ with (_ | _) <;> rcases ihψ with (_ | _);
    . right;
      simp only [Set.Cofinite, Set.compl_union, compl_compl];
      apply Set.Finite.inter_of_left;
      assumption;
    . right;
      simp_all only [Set.Cofinite, Set.compl_union, compl_compl];
      apply Set.Finite.inter_of_left;
      assumption;
    . left;
      simp_all [Set.Cofinite, Set.compl_union, compl_compl];
    . right;
      simp_all only [Set.Cofinite, Set.compl_union, compl_compl];
      apply Set.Finite.inter_of_right;
      assumption;
  | hbox φ ihφ =>
    by_cases h : ∃ n : cresswellFrame.Flat, ¬Satisfies cresswellModel n φ;
    . obtain ⟨n, h⟩ := h;
      -- ..., (n+2)♭, (n+1)♭ ∉ truthset φ.
      have h₁ : ∀ m : cresswellFrame.Flat, m.1 ≺ n.1 → ¬Satisfies cresswellModel m (□φ) := by
        intro m hm;
        apply Satisfies.box_def.not.mpr; push_neg;
        use n;
        constructor;
        . assumption;
        . exact h;
      -- 0♯, 1♯, ... ∉ truthset φ.
      have h₂ : ∀ m : cresswellFrame.Sharp, ¬Satisfies cresswellModel m (□φ) := by
        intro m;
        apply Satisfies.box_def.not.mpr; push_neg;
        use n;
        constructor;
        . exact cresswellFrame.bridge;
        . exact h;
      -- so, only n♭, (n-1)♭, ..., 0♭ ∈ truthset φ.
      left;
      sorry;
    . push_neg at h;
      replace ihφ : (truthset φ).Cofinite := by
        apply or_iff_not_imp_left.mp ihφ;
        sorry;
        /-
        apply Set.Infinite.of_image;
        by_contra hC;
        obtain ⟨m, hm⟩ := Set.Finite.exists_not_mem hC;
        sorry;
        -/
      -- obtain ⟨m, hm⟩ := Set.Finite.exists_not_mem ihφ;
      -- take maximal n♯ ¬⊧ φ
      sorry;
      /-
      obtain ⟨m, hm⟩ : ∃ m : cresswellFrame.SharpWorld, m.1 ∈ truthset φ := by
        obtain ⟨m, hm⟩ := Set.Finite.exists_not_mem ihφ;
        use ⟨m, ?_⟩;
        . simp_all;
        . by_contra hC;
          have := h ⟨(m.1, false), by simp⟩;
          simp at hm;
          contradiction;
      simp at hm;
      -/

end cresswellModel.truthset

lemma valid_H_on_cresswellModel : (cresswellModel) ⊧* 𝗛 := by
  simp only [Semantics.RealizeSet.setOf_iff, ValidOnModel.iff_models, forall_exists_index, forall_apply_eq_imp_iff];
  intro φ;
  wlog h : ∃ w : cresswellModel.World, ¬Satisfies cresswellModel w φ;
  . intro x _ y Rxy;
    push_neg at h;
    exact h y;
  obtain ⟨w, h⟩ := h;
  by_cases h : ∃ n, w = n♭;
  . obtain ⟨n, h⟩ := h;
    sorry;
  . push_neg at h;
    have : (cresswellModel.truthset φ).Infinite := by sorry
    have : (cresswellModel.truthset φ).Cofinite := by
      have := cresswellModel.truthset.either_finite_cofinite (φ := φ);
      apply or_iff_not_imp_left.mp this;
      apply Set.not_infinite.not.mp;
      push_neg;
      sorry;
    sorry;

lemma not_provable_atomic_Four : (Hilbert.KH ℕ) ⊬ (Axioms.Four (atom a)) := by
  have := @Kripke.instSound_of_frameClass_definedBy_aux (Axioms.Four a) 𝗛 { F | F ⊧* 𝗛 } (by tauto);
  apply not_imp_not.mpr this;
  simp [ValidOnFrameClass];
  use cresswellModel.toFrame;
  constructor;
  . intro φ;
    sorry;
  . apply ValidOnFrame.not_valid_iff_exists_valuation_world.mpr;
    use cresswellModel.Val, 2♯;
    exact @not_satisfies_atomic_Four_on_cresswellModel a;

-- Incompleteness of KH
theorem not_exists_complete_frameclass : ¬∃ C : FrameClass, ∀ φ : Formula ℕ, (Hilbert.KH ℕ) ⊢! φ ↔ C ⊧ φ := by
  by_contra hC;
  obtain ⟨C, hC⟩ := hC;
  have : C ⊧ Axioms.H (atom 0) := hC (Axioms.H (atom 0)) |>.mp axiomH!;
  have : C ⊧ Axioms.Four (atom 0) := by
    intro F hF;
    exact Kripke.valid_atomic_Four_of_valid_atomic_H $ @this F hF;
  have : Hilbert.KH ℕ ⊢! Axioms.Four (atom 0) := hC (Axioms.Four (atom 0)) |>.mpr this;
  exact not_provable_atomic_Four this;

end Hilbert.KH.Kripke

end LO.Modal
