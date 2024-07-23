import Logic.Modal.Standard.Kripke.GL.Completeness

namespace LO.Modal.Standard

variable [DecidableEq α] [Inhabited α]

-- TODO: 結局使わなかった．
namespace Formula

def subst (p : Formula α) (a : α) (t : Formula α) : Formula α :=
  match p with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | atom b => if b = a then t else atom b
  | ~p => ~(p.subst a t)
  | p ⋏ q => (p.subst a t) ⋏ (q.subst a t)
  | p ⋎ q => (p.subst a t) ⋎ (q.subst a t)
  | p ⟶ q => (p.subst a t)  ⟶ (q.subst a t)
  | box p => □(p.subst a t)

end Formula

lemma GL_deduct_substitution {p : Formula α} (a : α) (q : Formula α) : 𝐆𝐋 ⊢! p → 𝐆𝐋 ⊢! (p.subst a q) := by
  intro h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    apply Deduction.maxm!;
    rcases hp with (hAxK | hAxL);
    . obtain ⟨p, q, rfl⟩ := hAxK; simp [Formula.subst];
    . obtain ⟨p, q, rfl⟩ := hAxL; simp [Formula.subst];
  | hMdp ihpq ihp =>
    simp only [Formula.subst] at ihpq ihp;
    exact ihpq ⨀ ihp;
  | hNec ih =>
    simp only [Formula.subst];
    exact System.nec! ih;
  | _ =>
    simp only [Formula.subst];
    trivial;

lemma KH_deduct_substitution {p : Formula α} (a : α) (q : Formula α) : 𝐊𝐇 ⊢! p → 𝐊𝐇 ⊢! (p.subst a q) := by
  intro h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    apply Deduction.maxm!;
    rcases hp with (hAxK | hAxH);
    . obtain ⟨p, q, rfl⟩ := hAxK; simp [Formula.subst];
    . obtain ⟨p, q, rfl⟩ := hAxH; simp [Formula.subst]; rfl;
  | hMdp ihpq ihp => simp only [Formula.subst] at ihpq ihp; exact ihpq ⨀ ihp;
  | hNec ih => simp only [Formula.subst]; exact System.nec! ih;
  | _ => simp only [Formula.subst]; trivial;

namespace Kripke

open System
open Kripke
open Formula Formula.Kripke

variable {a : α} {F : Kripke.Frame}

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
  . exact valid_H_of_valid_L;
  . exact valid_L_of_valid_H;

lemma H_not_Four : 𝐊𝐇 ⊬! □(atom a) ⟶ □□(atom a) := by sorry

end Kripke

end LO.Modal.Standard
