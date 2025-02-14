import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Hilbert.WellKnown
import Mathlib.Order.Interval.Finset.Nat

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
      _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (□^[n] a) := by simp [Satisfies, V'];
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
      _ ↔ ∀ z, y ≺ z → Satisfies ⟨F, V'⟩ z (atom a) := by simp [Satisfies, V'];
      _ ↔ Satisfies ⟨F, V'⟩ y (□(atom a)) := by simp [Satisfies];
    simp [Satisfies, V'];
    tauto;

  have h₂ : Satisfies ⟨F, V'⟩ x (□atom a) := @hH V' x h₁;

  intro w Rxw;
  exact @h₂ w Rxw 0;

lemma valid_atomic_L_iff_valid_atomic_H : F ⊧ Axioms.L (atom 0) ↔ F ⊧ Axioms.H (atom 0) := by
  constructor;
  . exact valid_atomic_H_of_valid_atomic_L;
  . exact valid_atomic_L_of_valid_atomic_H;

lemma valid_atomic_4_of_valid_atomic_L : F ⊧ Axioms.L (atom 0) → F ⊧ Axioms.Four (atom 0) := by
  intro h V x h₂ y Rxy z Ryz;
  refine h₂ z ?_;
  apply @trans_of_validate_L F h x y z Rxy Ryz;

lemma valid_atomic_Four_of_valid_atomic_H : F ⊧ Axioms.H (atom 0) → F ⊧ Axioms.Four (atom 0) := by
  trans;
  . exact valid_atomic_L_iff_valid_atomic_H.mpr;
  . exact valid_atomic_4_of_valid_atomic_L;

abbrev cresswellFrame : Kripke.Frame where
  World := ℕ × Fin 2
  Rel n m :=
    match n, m with
    | (n, 0), (m, 0) => n ≤ m + 1
    | (n, 1), (m, 1) => n > m
    | (_, 0), (_, 1) => True
    | _, _ => False

namespace cresswellFrame

@[match_pattern] abbrev sharp (n : ℕ) : cresswellFrame.World := (n, 0)
postfix:max "♯" => sharp


@[match_pattern] abbrev flat (n : ℕ) : cresswellFrame.World := (n, 1)
postfix:max "♭" => flat

variable {n m : ℕ} {x y : cresswellFrame.World}

lemma trichonomy : x ≺ y ∨ x = y ∨ y ≺ x := by
  match x, y with
  | x♯, y♯ => simp [cresswellFrame, Frame.Rel']; omega;
  | x♭, y♯ => simp [cresswellFrame, Frame.Rel'];
  | x♯, y♭ => simp [cresswellFrame, Frame.Rel'];
  | x♭, y♭ => simp [cresswellFrame, Frame.Rel']; omega;

@[simp] lemma sharp_to_flat : n♯ ≺ m♭ := by simp [cresswellFrame, Frame.Rel']

@[simp] lemma not_flat_to_sharp : ¬(n♭ ≺ m♯):= by simp [cresswellFrame, Frame.Rel'];

lemma sharp_to_sharp : n♯ ≺ m♯ ↔ n ≤ m + 1 := by simp [cresswellFrame, Frame.Rel']

lemma flat_to_flat : n♭ ≺ m♭ ↔ n > m := by simp [cresswellFrame, Frame.Rel'];

lemma exists_flat_of_from_flat (h : n♭ ≺ x) : ∃ m, x = ⟨m, 1⟩ ∧ n > m := by
  match x with
  | ⟨m, 0⟩ => aesop;
  | ⟨m, 1⟩ => use m;

end cresswellFrame



abbrev cresswellModel : Kripke.Model := ⟨cresswellFrame, λ w _ => w ≠ 0♯⟩

namespace cresswellModel

end cresswellModel


open cresswellFrame cresswellModel

lemma not_valid_axiomFour_in_cresswellModel : ¬(Satisfies cresswellModel 2♯ (Axioms.Four (atom 0))) := by
  apply Satisfies.imp_def.not.mpr;
  push_neg;
  constructor;
  . intro x;
    match x with
    | n♯ =>
      intro h2n;
      suffices n ≠ 0 by simpa [Satisfies];
      omega;
    | n♭ => simp [Satisfies];
  . apply Satisfies.box_def.not.mpr
    push_neg;
    use 1♯;
    constructor;
    . omega;
    . apply Satisfies.box_def.not.mpr;
      push_neg;
      use 0♯;
      constructor;
      . omega;
      . tauto;

abbrev cresswellModel.truthset (φ : Formula _) := { x : cresswellModel.World | Satisfies cresswellModel x φ }
local notation "‖" φ "‖" => cresswellModel.truthset φ

namespace cresswellModel.truthset

lemma infinite_of_all_flat (h : ∀ n, n♭ ∈ ‖φ‖) : (‖φ‖.Infinite) := by
  apply Set.infinite_coe_iff.mp;
  exact Infinite.of_injective (λ n => ⟨n♭, h n⟩) $ by simp [Function.Injective]

-- TODO: need golf
lemma exists_max_sharp (h₁ : ∀ n, n♭ ∈ ‖φ‖) (h₂ : ‖φ‖ᶜ.Finite) (h₃ : ‖φ‖ᶜ.Nonempty) :
  ∃ n, n♯ ∉ ‖φ‖ ∧ (∀ m > n, m♯ ∈ ‖φ‖) := by
  obtain ⟨s, hs⟩ := Set.Finite.exists_finset (s := (λ x => x.1) '' ‖φ‖ᶜ) $ Set.Finite.image _ h₂;
  have se : s.Nonempty := by
    let ⟨x, hx⟩ := h₃;
    use x.1;
    apply hs _ |>.mpr;
    use x;
  use (s.max' se);
  constructor;
  . obtain ⟨f, hx₁⟩ := by simpa using @hs _ |>.mp $ Finset.max'_mem _ se;
    match f with
    | 0 => exact hx₁;
    | 1 =>
      have := hx₁ $ h₁ _;
      contradiction;
  . intro m hm;
    by_contra hC;
    have : m < m := Finset.max'_lt_iff (H := se) |>.mp hm m (by
      apply hs m |>.mpr;
      use m♯;
      simpa;
    );
    simp at this;

lemma either_finite_cofinite : (‖φ‖.Finite) ∨ (‖φ‖ᶜ.Finite) := by
  induction φ using Formula.rec' with
  | hatom a => simp [truthset, Satisfies];
  | hfalsum => simp [truthset, Satisfies];
  | himp φ ψ ihφ ihψ =>
    rw [(show ‖φ ➝ ψ‖ = ‖φ‖ᶜ ∪ ‖ψ‖ by tauto_set), Set.compl_union, compl_compl];
    rcases ihφ with (_ | _) <;> rcases ihψ with (_ | _);
    . right; apply Set.Finite.inter_of_left; assumption;
    . right; apply Set.Finite.inter_of_left; assumption;
    . left;
      rw [Set.finite_union];
      constructor <;> assumption;
    . right; apply Set.Finite.inter_of_right; assumption;
  | hbox φ ihφ =>
    by_cases h : ∀ n, n♭ ∈ ‖φ‖;
    . have tsφc_finite : ‖φ‖ᶜ.Finite := or_iff_not_imp_left.mp ihφ $ truthset.infinite_of_all_flat h;
      wlog tsφc_ne : ‖φ‖ᶜ.Nonempty;
      . have : ‖□φ‖ᶜ = ∅ := by
          simp only [Set.compl_empty_iff, Set.eq_univ_iff_forall, Set.mem_setOf_eq];
          intro x y Rxy;
          match x, y with
          | m♯, k♯ =>
            simp [Set.compl_empty, Set.Nonempty] at tsφc_ne;
            apply tsφc_ne;
          | m♭, k♯ => simp at Rxy;
          | m♯, k♭ => apply h;
          | m♭, k♭ => apply h;
        rw [this];
        simp;
      obtain ⟨n, hn, hn_max⟩ := exists_max_sharp h tsφc_finite tsφc_ne;
      right;
      apply @Set.Finite.subset (s := (·♯) '' Set.Icc 0 (n + 1));
      . apply Set.toFinite
      . intro x hx;
        replace := Satisfies.box_def.not.mp hx;
        push_neg at this;
        obtain ⟨y, Rxy, _⟩ := this;
        match x, y with
        | m♯, k♯ =>
          by_contra hC; simp at hC;
          replace Rxy := sharp_to_sharp.mp Rxy;
          have : k♯ ∈ ‖φ‖ := @hn_max k (by omega);
          contradiction;
        | m♭, k♯ => simp at Rxy;
        | _♯, k♭ => have := h k; contradiction;
        | _♭, k♭ => have := h k; contradiction;
    . left;
      push_neg at h;
      obtain ⟨n, hn⟩ := h;
      apply @Set.Finite.subset (s := (·♭) '' Set.Icc 0 n);
      . apply Set.toFinite
      . intro x hx;
        match x with
        | m♯ =>
          have := hx n♭ sharp_to_flat;
          contradiction;
        | m♭ =>
          by_contra hC;
          have := hx n♭ $ (cresswellFrame.flat_to_flat.mpr $ by simpa using hC);
          contradiction;

end cresswellModel.truthset

open Classical in
lemma valid_axiomH_in_cresswellModel : cresswellModel ⊧ □(□φ ⭤ φ) ➝ □φ := by
  rintro x;
  by_cases h : ∀ n, n♭ ∈ ‖φ‖;
  . have tsφc_fin : ‖φ‖ᶜ.Finite := or_iff_not_imp_left.mp truthset.either_finite_cofinite $ truthset.infinite_of_all_flat h;
    wlog tsφc_ne : ‖φ‖ᶜ.Nonempty;
    . apply Satisfies.imp_def₂.mpr;
      right;
      simp [Set.compl_empty, Set.Nonempty] at tsφc_ne;
      intro y Rxy;
      apply tsφc_ne;
    obtain ⟨n, hn, hn_max⟩ := truthset.exists_max_sharp h tsφc_fin tsφc_ne;
    match x with
    | m♭ =>
      apply Satisfies.imp_def₂.mpr;
      right;
      rintro y Rny;
      obtain ⟨k, ⟨rfl, _⟩⟩ := exists_flat_of_from_flat Rny;
      apply h;
    | m♯ =>
      by_cases hnm : n + 2 ≤ m;
      . apply Satisfies.imp_def₂.mpr;
        right;
        rintro y Rny;
        match y with
        | _♭ => apply h;
        | _♯ => apply hn_max; omega;
      . apply Satisfies.imp_def₂.mpr;
        left;
        apply Satisfies.box_def.not.mpr;
        push_neg;
        use (n + 1)♯;
        constructor;
        . omega;
        . have : Satisfies cresswellModel (n + 1)♯ φ := hn_max (n + 1) (by omega);
          have : ¬Satisfies cresswellModel (n + 1)♯ (□φ) := by
            apply Satisfies.box_def.not.mpr;
            push_neg;
            use n♯;
            constructor;
            . omega;
            . apply hn;
          apply Satisfies.iff_def.not.mpr;
          tauto;
  . push_neg at h;
    obtain ⟨n, hn⟩ := h;
    wlog hn_max : ∀ m < n, m♭ ∈ ‖φ‖;
    . push_neg at hn_max;
      obtain ⟨m, hmn, hm⟩ := hn_max;
      let M := (Finset.Icc 0 m) |>.filter (λ k => k♭ ∉ ‖φ‖ ∧ (∀ l < k, l♭ ∈ ‖φ‖));
      have hM : M.Nonempty := by
        sorry;
        -- TODO: find recursively by 0♭, 1♭, 2♭, ..., m♭;
        /-
        let rec find (x : ℕ) := -- (hx₁ : x ≤ m) (hx₂ : ∀ y < x, y♭ ∈ ‖φ‖) :=
          if h : x♭ ∈ ‖φ‖
          then find (x + 1);
          /-
            (by
              by_contra hC;
              simp at hC;
              have : x = m := by omega;
              rw [this] at h;
              contradiction
            )
            (by
              intro y hy;
              rcases (Nat.lt_succ_iff_lt_or_eq.mp hy) with (h | rfl);
              . exact hx₂ _ h;
              . assumption;
            )
          -/

          else x;
        exact ⟨
          find 0 (by simp) (by omega),
          by
            simp [M];
            refine ⟨?_, ?_, ?_⟩;
            . sorry;
            . sorry;
            . sorry;
        ⟩
        -/
      obtain ⟨h, hx, hy⟩ := Finset.mem_filter.mp $ Finset.min'_mem M $ hM;
      exact this x (M.min' _) hx hy;
    have hn₁ : Satisfies cresswellModel n♭ (□φ) := by
      intro x Rnx;
      obtain ⟨m, ⟨rfl, hnm⟩⟩ := exists_flat_of_from_flat Rnx;
      exact hn_max m hnm;
    have hn₂ : ¬Satisfies cresswellModel n♭ (□φ ⭤ φ) := by
      apply Satisfies.iff_def.not.mpr;
      push_neg;
      tauto;
    match x with
    | m♯ =>
      apply Satisfies.imp_def₂.mpr;
      left;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use n♭;
      constructor;
      . exact sharp_to_flat;
      . assumption;
    | m♭ =>
      by_cases hmn : m > n;
      . intro h;
        have := @h n♭ $ (flat_to_flat.mpr hmn);
        contradiction;
      . apply Satisfies.imp_def₂.mpr;
        right;
        rintro y Rmy;
        obtain ⟨k, ⟨rfl, hk₂⟩⟩ := exists_flat_of_from_flat Rmy;
        apply hn_max;
        omega;

lemma provable_KH_of_valid_cresswellModel : Hilbert.KH ⊢! φ → cresswellModel ⊧ φ := by
  intro h;
  induction h using Hilbert.Deduction.rec! with
  | maxm h =>
    rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact Kripke.ValidOnModel.axiomK;
    . exact valid_axiomH_in_cresswellModel;
  | mdp ihφψ ihφ => exact Kripke.ValidOnModel.mdp ihφψ ihφ;
  | nec ihφ => exact Kripke.ValidOnModel.nec ihφ;
  | imply₁ => exact Kripke.ValidOnModel.imply₁;
  | imply₂ => exact Kripke.ValidOnModel.imply₂;
  | ec => exact Kripke.ValidOnModel.elimContra;

lemma KH_unprov_axiomFour : Hilbert.KH ⊬ Axioms.Four (atom 0) := fun hC =>
  not_valid_axiomFour_in_cresswellModel (provable_KH_of_valid_cresswellModel hC 2♯)

theorem KH_KripkeIncomplete : ¬∃ C : Kripke.FrameClass, ∀ φ, (Hilbert.KH ⊢! φ ↔ C ⊧ φ) := by
  rintro ⟨C, h⟩;
  have : C ⊧ Axioms.H (atom 0) := @h (Axioms.H (atom 0)) |>.mp $ by simp;
  have : C ⊧ Axioms.Four (atom 0) := fun {F} hF => valid_atomic_Four_of_valid_atomic_H (this hF);
  have : Hilbert.KH ⊢! Axioms.Four (atom 0) := @h (Axioms.Four (atom 0)) |>.mpr this;
  exact @KH_unprov_axiomFour this;

end Kripke

end LO.Modal
