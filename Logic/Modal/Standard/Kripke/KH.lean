import Logic.Modal.Standard.Kripke.GL.Completeness

namespace LO.Modal.Standard

variable [DecidableEq α]

namespace Formula

@[simp] lemma complexity_not (p : Formula α) : p.complexity < (~p).complexity := by simp [Formula.complexity]

abbrev UniformSubstitution (α) := α → Formula α

def subst (p : Formula α) (σ : UniformSubstitution α) : Formula α :=
  match p with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | atom b => σ b
  | ~p => ~(p.subst σ)
  | p ⋏ q => (p.subst σ) ⋏ (q.subst σ)
  | p ⋎ q => (p.subst σ) ⋎ (q.subst σ)
  | p ⟶ q => (p.subst σ)  ⟶ (q.subst σ)
  | box p => □(p.subst σ)

def subst₂ (p : Formula α) (a : α) (t : Formula α) : Formula α :=
  match p with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | atom b => if b = a then t else atom b
  | ~p => ~(p.subst₂ a t)
  | p ⋏ q => (p.subst₂ a t) ⋏ (q.subst₂ a t)
  | p ⋎ q => (p.subst₂ a t) ⋎ (q.subst₂ a t)
  | p ⟶ q => (p.subst₂ a t)  ⟶ (q.subst₂ a t)
  | box p => □(p.subst₂ a t)

lemma Kripke.Satisfies.subst_closed {p : Formula α} {M : Kripke.Model α} {x : M.World} (a : α) (t : Formula α) : x ⊧ p → x ⊧ (p.subst₂ a t) := by
  induction p using Formula.rec' generalizing x with
  | hatom b =>
    simp [Formula.subst₂];
    by_cases h : b = a;
    . simp_all;
      sorry;
    . simp_all;
  | hverum =>
    simp [Formula.subst₂];
  | hfalsum => simp_all [Formula.subst₂];
  | hneg p ih =>
    simp [Formula.subst₂];
    sorry;
  | hand p q ihp ihq => simp_all [Formula.subst₂];
  | hor p q ihp ihq =>
    rintro (hp | hq);
    . left; exact ihp hp;
    . right; exact ihq hq;
  | himp p q ihp ihq =>
    simp [Formula.subst₂];
    rintro hp hq;
    sorry;
  | hbox p ih =>
    simp [Formula.subst₂];
    intro h y Rxy;
    apply ih $ @h y Rxy;

end Formula

-- MEMO: `Ax(Λ)`がきちんと公理図式として要請を満たせば`hMaxm`の証明は一般化できる
lemma GL_deduct_substitution {p : Formula α} (a : α) (q : Formula α) : 𝐆𝐋 ⊢! p → 𝐆𝐋 ⊢! (p.subst₂ a q) := by
  intro h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    apply Deduction.maxm!;
    rcases hp with (hAxK | hAxL);
    . obtain ⟨p, q, rfl⟩ := hAxK; simp [Formula.subst₂];
    . obtain ⟨p, q, rfl⟩ := hAxL; simp [Formula.subst₂];
  | hMdp ihpq ihp =>
    simp only [Formula.subst₂] at ihpq ihp;
    exact ihpq ⨀ ihp;
  | hNec ih =>
    simp only [Formula.subst₂];
    exact System.nec! ih;
  | _ =>
    simp only [Formula.subst₂];
    trivial;

namespace Kripke

open System
open Kripke
open Formula Formula.Kripke

variable {a : α} {F : Kripke.Frame}

/-
lemma valid_H_of_valid_L {F : Kripke.Frame} : F# ⊧* (𝗟 : AxiomSet α) → F# ⊧* (𝗛 : AxiomSet α) := by
  simp [Axioms.L, Axioms.H];
  intro h p V x hx;
  have : Satisfies ⟨F, V⟩ x (□(□p ⟶ p)) := by intro y Rxy; exact hx Rxy |>.1;
  exact @h p V x this;
-/

lemma valid_H_of_valid_L : F# ⊧ Axioms.L (atom a) → F# ⊧ Axioms.H (atom a) := by
  simp [Axioms.L, Axioms.H];
  intro h V x hx;
  have : Satisfies ⟨F, V⟩ x (□(□a ⟶ a)) := by intro y Rxy; exact hx Rxy |>.1;
  exact @h V x this;


lemma valid_L_of_valid_H {a : α} {F : Kripke.Frame} : F# ⊧ Axioms.H (atom a) → F# ⊧ Axioms.L (atom a) := by
  simp [Axioms.L, Axioms.H];
  intro hH V x hx;

  let M : Kripke.Model α := ⟨F#, V⟩;
  let V' : Valuation F α := λ w a => ∀ n : ℕ, Satisfies ⟨F#, V⟩ w (□^[n] a);

  let M' : Kripke.Model α := ⟨F, V'⟩;

  have h₁ : Satisfies M' x (□(□a ⟷ a)) := by
    intro y Rxy;
    have : Satisfies M' y a ↔ Satisfies M' y (□a) := calc
      _ ↔ ∀ n : ℕ, Satisfies M y (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ n : ℕ, Satisfies M y (□^[(n + 1)]a) := by
        constructor;
        . intro h n; apply h;
        . intro h n;
          have h₁ : Satisfies M y (□atom a ⟶ atom a) := @hx y Rxy;
          have h₂ : Satisfies M y ((□atom a ⟶ atom a).subst₂ a (□^[n]atom a)) := Satisfies.subst_closed (a := a) (t := (□^[n](atom a))) h₁;
          simp [Formula.subst₂] at h₂;
          apply h₂;
          aesop;
      _ ↔ ∀ n : ℕ, ∀ z, y ≺ z → Satisfies M z (□^[n] a) := by simp [Satisfies];
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
