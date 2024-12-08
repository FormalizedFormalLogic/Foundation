import Foundation.Modal.Hilbert.ConsistentTheory
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open System
open Formula
open MaximalConsistentTheory
open Hilbert.Deduction
open Kripke

variable {H : Hilbert ℕ} [H.IsNormal] [H.Consistent]

namespace Hilbert

namespace Kripke

abbrev canonicalFrame (H : Hilbert ℕ) [H.IsNormal] [H.Consistent] : Kripke.Frame where
  World := MCT H
  Rel Ω₁ Ω₂ := □''⁻¹Ω₁.theory ⊆ Ω₂.theory

namespace canonicalFrame

variable {Ω₁ Ω₂ : (canonicalFrame H).World}

@[simp] lemma rel_def_box: Ω₁ ≺ Ω₂ ↔ ∀ {φ}, □φ ∈ Ω₁.theory → φ ∈ Ω₂.theory := by simp [Frame.Rel']; aesop;

lemma multirel_def_multibox : Ω₁ ≺^[n] Ω₂ ↔ ∀ {φ}, □^[n]φ ∈ Ω₁.theory → φ ∈ Ω₂.theory := by
  induction n generalizing Ω₁ Ω₂ with
  | zero =>
    simp_all;
    constructor;
    . intro h; subst h; tauto;
    . intro h; apply intro_equality; simpa;
  | succ n ih =>
    constructor;
    . intro h φ hp;
      obtain ⟨⟨Ω₃, _⟩, R₁₃, R₃₂⟩ := h;
      apply ih.mp R₃₂ $ rel_def_box.mp R₁₃ (by simpa using hp);
    . intro h;
      obtain ⟨Ω, hΩ⟩ := lindenbaum (H := H) (T := (□''⁻¹Ω₁.theory ∪ ◇''^[n]Ω₂.theory)) $ by
        apply Theory.intro_union_consistent;
        rintro Γ Δ ⟨hΓ, hΔ⟩ hC;

        replace hΓ : ∀ φ ∈ Γ, □φ ∈ Ω₁.theory := by simpa using hΓ;
        have dΓconj : Ω₁.theory *⊢[H]! □⋀Γ := membership_iff.mp $ iff_mem_box_conj.mpr hΓ;

        have hΔ₂ : ∀ φ ∈ ◇'⁻¹^[n]Δ, φ ∈ Ω₂.theory := by
          intro φ hp;
          exact Set.iff_mem_multidia.mp $ hΔ (◇^[n]φ) (by simpa using hp);

        have hΔconj : ⋀◇'⁻¹^[n]Δ ∈ Ω₂.theory := iff_mem_conj.mpr hΔ₂;

        have : ⋀◇'⁻¹^[n]Δ ∉ Ω₂.theory := by {
          have d₁ : H ⊢! ⋀Γ ➝ ⋀Δ ➝ ⊥ := and_imply_iff_imply_imply'!.mp hC;
          have : H ⊢! ⋀(◇'^[n]◇'⁻¹^[n]Δ) ➝ ⋀Δ := by
            apply conjconj_subset!;
            intro ψ hq;
            obtain ⟨χ, _, _⟩ := hΔ ψ hq;
            subst_vars;
            simpa;
          have : H ⊢! ◇^[n]⋀◇'⁻¹^[n]Δ ➝ ⋀Δ := imp_trans''! iff_conjmultidia_multidiaconj! $ this;
          have : H ⊢! ∼(□^[n](∼⋀◇'⁻¹^[n]Δ)) ➝ ⋀Δ := imp_trans''! (and₂'! multidia_duality!) this;
          have : H ⊢! ∼⋀Δ ➝ □^[n](∼⋀◇'⁻¹^[n]Δ) := contra₂'! this;
          have : H ⊢! (⋀Δ ➝ ⊥) ➝ □^[n](∼⋀◇'⁻¹^[n]Δ) := imp_trans''! (and₂'! neg_equiv!) this;
          have : H ⊢! ⋀Γ ➝ □^[n](∼⋀◇'⁻¹^[n]Δ) := imp_trans''! d₁ this;
          have : H ⊢! □⋀Γ ➝ □^[(n + 1)](∼⋀◇'⁻¹^[n]Δ) := by simpa using imply_box_distribute'! this;
          exact iff_mem_neg.mp $ h $ membership_iff.mpr $ (Context.of! this) ⨀ dΓconj;
        }

        contradiction;
      use Ω;
      constructor;
      . intro φ hp;
        apply hΩ;
        simp_all;
      . apply ih.mpr;
        apply multibox_multidia.mpr;
        intro φ hp;
        apply hΩ;
        simp_all;

lemma multirel_def_multibox' : Ω₁ ≺^[n] Ω₂ ↔ ∀ {φ}, φ ∈ (□''⁻¹^[n]Ω₁.theory) → φ ∈ Ω₂.theory := by
  constructor;
  . intro h φ hp; exact multirel_def_multibox.mp h hp;
  . intro h; apply multirel_def_multibox.mpr; assumption;

lemma multirel_def_multidia : Ω₁ ≺^[n] Ω₂ ↔ ∀ {φ}, (φ ∈ Ω₂.theory → ◇^[n]φ ∈ Ω₁.theory) := Iff.trans multirel_def_multibox multibox_multidia

lemma rel_def_dia : Ω₁ ≺ Ω₂ ↔ ∀ {φ}, φ ∈ Ω₂.theory → ◇φ ∈ Ω₁.theory := by simpa using multirel_def_multidia (n := 1) (Ω₁ := Ω₁) (Ω₂ := Ω₂)

end canonicalFrame


abbrev canonicalModel (H : Hilbert ℕ) [H.IsNormal] [H.Consistent] : Model where
  toFrame := canonicalFrame H
  Val Ω a := (atom a) ∈ Ω.theory

@[reducible]
instance : Semantics (Formula ℕ) (canonicalModel H).World := Formula.Kripke.Satisfies.semantics (M := canonicalModel H)


section lemmata

variable {φ ψ : Formula ℕ}

lemma truthlemma : ∀ {Ω : (canonicalModel H).World}, Ω ⊧ φ ↔ (φ ∈ Ω.theory) := by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    intro Ω;
    constructor;
    . intro h;
      apply iff_mem_box.mpr;
      intro Ω' hΩ';
      apply ih.mp;
      exact h Ω' hΩ';
    . intro h Ω' hΩ';
      apply ih.mpr;
      exact canonicalFrame.rel_def_box.mp hΩ' h;
  | himp φ ψ ihp ihq =>
    intro Ω;
    constructor;
    . intro h;
      apply iff_mem_imp.mpr;
      intro hp; replace hp := ihp.mpr hp;
      exact ihq.mp $ h hp;
    . intro h;
      have := iff_mem_imp.mp h;
      intro hp; replace hp := ihp.mp hp;
      exact ihq.mpr $ this hp
  | _ => simp_all [Semantics.Realize, Kripke.Satisfies];


lemma iff_valid_on_canonicalModel_deducible : (canonicalModel H) ⊧ φ ↔ H ⊢! φ := by
  constructor;
  . contrapose;
    intro h;
    have : Theory.Consistent H ({∼φ}) := by
      apply Theory.def_consistent.mpr;
      intro Γ hΓ;
      by_contra hC;
      have : H ⊢! φ := dne'! $ neg_equiv'!.mpr $ replace_imply_left_conj! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this;
    simp [Kripke.ValidOnModel];
    use Ω;
    exact truthlemma.not.mpr $ iff_mem_neg.mp (show ∼φ ∈ Ω.theory by simp_all);
  . intro h Ω;
    suffices φ ∈ Ω.theory by exact truthlemma.mpr this;
    by_contra hC;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Theory.iff_insert_inconsistent.mp $ (MaximalConsistentTheory.maximal' hC);
    have : Γ ⊢[H]! ⊥ := FiniteContext.provable_iff.mpr $ and_imply_iff_imply_imply'!.mp hΓ₂ ⨀ h;
    have : Γ ⊬[H] ⊥ := Theory.def_consistent.mp Ω.consistent _ hΓ₁;
    contradiction;

lemma realize_axiomset_of_self_canonicalModel : (canonicalModel H) ⊧* H.axioms := by
  apply Semantics.realizeSet_iff.mpr;
  intro φ hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  exact maxm! hp;

lemma realize_theory_of_self_canonicalModel : (canonicalModel H) ⊧* (System.theory H) := by
  apply Semantics.realizeSet_iff.mpr;
  intro φ hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  simpa [System.theory] using hp;

lemma complete_of_canonical {C : FrameClass} (hFC : canonicalFrame H ∈ C) : C ⊧ φ → H ⊢! φ := by
  simp [Semantics.Realize, Kripke.ValidOnFrame];
  contrapose;
  push_neg;
  intro h;
  use (canonicalFrame H);
  constructor;
  . assumption;
  . use (canonicalModel H).Val;
    exact iff_valid_on_canonicalModel_deducible.not.mpr h;

lemma instCompleteOfCanonical {C : FrameClass} (hC : (Kripke.canonicalFrame H) ∈ C) : Complete H C := ⟨complete_of_canonical hC⟩

end lemmata

end Kripke


namespace K

instance Kripke.complete : Complete (Hilbert.K ℕ) (Kripke.AllFrameClass) := Hilbert.Kripke.instCompleteOfCanonical (C := Kripke.AllFrameClass) $ by tauto

end K

end Hilbert

end LO.Modal
