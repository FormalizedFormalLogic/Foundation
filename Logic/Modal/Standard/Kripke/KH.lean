import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

variable [DecidableEq α] [Inhabited α]

namespace Kripke

open System
open Kripke
open Formula Formula.Kripke

variable (a : α) {F : Kripke.Frame}

lemma valid_H_of_valid_L : F# ⊧ Axioms.L (atom a) → F# ⊧ Axioms.H (atom a) := by
  simp [Axioms.L, Axioms.H];
  intro h V x hx;
  have : Satisfies ⟨F, V⟩ x (□(□a ⟶ a)) := by intro y Rxy; exact hx Rxy |>.1;
  exact @h V x this;


lemma valid_L_of_valid_H : F# ⊧ Axioms.H (atom a) → F# ⊧ Axioms.L (atom a) := by
  simp [Axioms.L, Axioms.H];
  intro hH V x hx;

  let M : Kripke.Model α := ⟨F#, V⟩;
  let V' : Valuation F α := λ w a => ∀ n : ℕ, Satisfies ⟨F#, V⟩ w (□^[n] a);

  let M' : Kripke.Model α := ⟨F, V'⟩;

  have h₁ : Satisfies M' x (□(□a ⟷ a)) := by
    intro y Rxy;
    have : Satisfies M' y a ↔ Satisfies M' y (□a) := calc
      _ ↔ ∀ n, Satisfies M y (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ n, Satisfies M y (□^[(n + 1)]a) := by
        constructor;
        . intro h n; apply h;
        . intro h n;
          have h₁ : Satisfies M y (□□^[n](atom a) ⟶ □^[n](atom a)) := by
            induction n with
            | zero => apply hx Rxy;
            | succ n => intro _; apply h;
          apply h₁;
          simpa using h n;
      _ ↔ ∀ n, ∀ z, y ≺ z → Satisfies M z (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ z, y ≺ z → ∀ n : ℕ, Satisfies M z (□^[n]a) := by aesop;
      _ ↔ ∀ z, y ≺ z → Satisfies M' z (atom a) := by simp [Satisfies];
      _ ↔ Satisfies M' y (□(atom a)) := by simp [Satisfies];
    exact ⟨this.2, this.1⟩;

  have H : Satisfies M' x (□atom a) := @hH M'.Valuation x h₁;

  intro w hxw;
  exact H hxw 0;

lemma iff_valid_L_valid_H : F# ⊧ Axioms.L (atom a) ↔ F# ⊧ Axioms.H (atom a) := by
  constructor;
  . exact valid_H_of_valid_L a;
  . exact valid_L_of_valid_H a;

lemma _root_.LO.Modal.Standard.KH_not_Four : 𝐊𝐇 ⊬! Axioms.Four (atom a) := by sorry

lemma _root_.LO.Modal.Standard.KH_not_Loeb : 𝐊𝐇 ⊬! Axioms.L (atom a) := by
  by_contra hC;
  have : System.HasAxiomL 𝐊𝐇 := ⟨by
    intro p;
    simpa [subst] using KH_deduct_substitution a p hC |>.some;
  ⟩;
  have : 𝐊𝐇 ⊢! Axioms.Four (atom a) := axiomFour!;
  exact KH_not_Four a this;


notation "Thm(" Λ:90 ")" => System.theory Λ

/-- Set of frame that every theorems of `Λ` are valid on. -/
abbrev TheoremsFrameClass (Λ : DeductionParameter α) : FrameClass.Dep α := { F : Frame | F# ⊧* Thm(Λ) }
notation "𝔽(" Λ:90 ")" => TheoremsFrameClass Λ

variable [Inhabited α]

lemma KH_incompleteAux (𝔽 : FrameClass) (hFH : 𝔽# ⊧* (𝗛 : AxiomSet α)) : ∃ p : Formula α, (𝔽# ⊧ p ∧ 𝐊𝐇 ⊬! p) := by
  by_contra hC;
  push_neg at hC;
  have := hC (Axioms.L (atom default)) ?h;
  have := KH_not_Loeb (α := α) default;
  contradiction;

  intro F hF;
  apply iff_valid_L_valid_H (default) |>.mpr;
  simp at hFH;
  exact hFH _ hF;

theorem KH_incomplete : ∃ p : Formula α, 𝔽(𝐊𝐇) ⊧ p ∧ 𝐊𝐇 ⊬! p := by
  obtain ⟨p, hs, hp⟩ := KH_incompleteAux (α := α) 𝔽(𝐊𝐇) $ by
    simp;
    intro p F hp;
    exact Semantics.realizeSet_iff.mp hp (by simp [System.theory]);
  use p;

/--
  Type class for _"`Λ` is incomplete for Kripke semantics"_
-/
class Incomplete (Λ : DeductionParameter α) : Prop where
  incomplete : ∃ p, 𝔽(Λ) ⊧ p ∧ Λ ⊬! p

instance : Incomplete (α := α) 𝐊𝐇 := ⟨KH_incomplete⟩

end Kripke

end LO.Modal.Standard
