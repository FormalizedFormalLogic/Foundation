import Foundation.Modal.ConsistentTheory
import Foundation.Modal.Kripke.Semantics

namespace LO.Modal

open LO.Kripke
open System
open Formula
open MaximalConsistentTheory
open Hilbert.Deduction

variable {α : Type u} [DecidableEq α]
variable {H : Hilbert α} [H.IsNormal]

namespace Kripke

abbrev CanonicalFrame (H : Hilbert α) [Nonempty (MCT H)] : Kripke.Frame where
  World := MCT H
  Rel Ω₁ Ω₂ := □''⁻¹Ω₁.theory ⊆ Ω₂.theory

namespace CanonicalFrame

variable [Nonempty (MCT H)]
variable {Ω₁ Ω₂ : (CanonicalFrame H).World}

omit [DecidableEq α] [H.IsNormal] in
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

end CanonicalFrame


abbrev CanonicalModel (H : Hilbert α) [Nonempty (MCT H)]  : Model α where
  Frame := CanonicalFrame H
  Valuation Ω a := (atom a) ∈ Ω.theory


namespace CanonicalModel

variable [Nonempty (MCT H)]

@[reducible]
instance : Semantics (Formula α) (CanonicalModel H).World := Formula.Kripke.Satisfies.semantics (M := CanonicalModel H)

-- @[simp] lemma frame_def : (CanonicalModel Ax).Rel' Ω₁ Ω₂ ↔ (□''⁻¹Ω₁.theory : Theory α) ⊆ Ω₂.theory := by rfl
-- @[simp] lemma val_def : (CanonicalModel Ax).Valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel


section

variable [Nonempty (MCT H)] {φ : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel H).World}, Ω ⊧ φ ↔ (φ ∈ Ω.theory) := by
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
      exact CanonicalFrame.rel_def_box.mp hΩ' h;
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
  | hatom a =>
    simp_all [Kripke.Satisfies];
  | _ => simp_all [Kripke.Satisfies];


lemma iff_valid_on_canonicalModel_deducible : (CanonicalModel H) ⊧ φ ↔ H ⊢! φ := by
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

lemma realize_axiomset_of_self_canonicalModel : (CanonicalModel H) ⊧* H.axioms := by
  apply Semantics.realizeSet_iff.mpr;
  intro φ hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  exact maxm! hp;

lemma realize_theory_of_self_canonicalModel : (CanonicalModel H) ⊧* (System.theory H) := by
  apply Semantics.realizeSet_iff.mpr;
  intro φ hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  simpa [System.theory] using hp;

end

lemma complete_of_mem_canonicalFrame [Nonempty (MCT H)] {𝔽 : FrameClass} (hFC : CanonicalFrame H ∈ 𝔽) : 𝔽#α ⊧ φ → (H) ⊢! φ := by
  simp [Semantics.Realize, Kripke.ValidOnFrame];
  contrapose;
  push_neg;
  intro h;
  use (CanonicalFrame H);
  constructor;
  . assumption;
  . use (CanonicalModel H).Valuation;
    exact iff_valid_on_canonicalModel_deducible.not.mpr h;

instance instComplete_of_mem_canonicalFrame [Nonempty (MCT H)] (𝔽 : FrameClass) (hFC : CanonicalFrame H ∈ 𝔽) : Complete (H) (𝔽#α) := ⟨complete_of_mem_canonicalFrame hFC⟩

instance K_complete : Complete (Hilbert.K α) (AllFrameClass.{u}#α) := by
  convert instComplete_of_mem_canonicalFrame (α := α) AllFrameClass trivial;
  rw [Hilbert.ExtK.K_is_extK_of_empty];
  . tauto;
  . infer_instance;

end Kripke

end LO.Modal
