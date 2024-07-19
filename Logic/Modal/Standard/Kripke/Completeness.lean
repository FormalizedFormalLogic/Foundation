import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

open System
open Formula
open MaximalConsistentTheory
open DeductionParameter (Normal)

variable {α : Type*} [DecidableEq α] [Inhabited α]
variable {Λ : DeductionParameter α} [Λ.IsNormal]

namespace Kripke

noncomputable abbrev CanonicalFrame (Λ : DeductionParameter α) [Inhabited (Λ)-MCT] : Frame where
  World := (Λ)-MCT
  World_decEq := Classical.decEq _
  Rel Ω₁ Ω₂ := □''⁻¹Ω₁.theory ⊆ Ω₂.theory

namespace CanonicalFrame

variable [Inhabited (Λ)-MCT]
variable {Ω₁ Ω₂ : (CanonicalFrame Λ).World}

@[simp]
lemma frame_def_box: Ω₁ ≺ Ω₂ ↔ ∀ {p}, □p ∈ Ω₁.theory → p ∈ Ω₂.theory := by simp [Frame.Rel']; aesop;

lemma multiframe_def_multibox : Ω₁ ≺^[n] Ω₂ ↔ ∀ {p}, □^[n]p ∈ Ω₁.theory → p ∈ Ω₂.theory := by
  induction n generalizing Ω₁ Ω₂ with
  | zero =>
    simp_all;
    constructor;
    . intro h; subst h; tauto;
    . intro h; apply intro_equality; simpa;
  | succ n ih =>
    constructor;
    . intro h p hp;
      obtain ⟨⟨Ω₃, _⟩, R₁₃, R₃₂⟩ := h;
      apply ih.mp R₃₂ $ frame_def_box.mp R₁₃ (by simpa using hp);
    . intro h;
      obtain ⟨Ω, hΩ⟩ := lindenbaum (Λ := Λ) (T := (□''⁻¹Ω₁.theory ∪ ◇''^[n]Ω₂.theory)) $ by
        apply Theory.intro_union_consistent;
        intro Γ Δ hΓ hΔ hC;

        replace hΓ : ∀ p ∈ Γ, □p ∈ Ω₁.theory := by simpa using hΓ;
        have dΓconj : Ω₁.theory *⊢[_]! □⋀Γ := membership_iff.mp $ iff_mem_box_conj.mpr hΓ;

        have hΔ₂ : ∀ p ∈ ◇'⁻¹^[n]Δ, p ∈ Ω₂.theory := by
          intro p hp;
          simpa using hΔ (◇^[n]p) (by simp_all);

        have hΔconj : ⋀◇'⁻¹^[n]Δ ∈ Ω₂.theory := iff_mem_conj.mpr hΔ₂;

        have : ⋀◇'⁻¹^[n]Δ ∉ Ω₂.theory := by {
          have d₁ : Λ ⊢! ⋀Γ ⟶ ⋀Δ ⟶ ⊥ := and_imply_iff_imply_imply'!.mp hC;
          have : Λ ⊢! ⋀(◇'^[n]◇'⁻¹^[n]Δ) ⟶ ⋀Δ := by
            apply conjconj_subset!;
            intro q hq;
            obtain ⟨r, _, _⟩ := hΔ q hq;
            subst_vars;
            simpa;
          have : Λ ⊢! ◇^[n]⋀◇'⁻¹^[n]Δ ⟶ ⋀Δ := imp_trans''! iff_conjmultidia_multidiaconj! $ this;
          have : Λ ⊢! ~(□^[n](~⋀◇'⁻¹^[n]Δ)) ⟶ ⋀Δ := imp_trans''! (and₂'! multidia_duality!) this;
          have : Λ ⊢! ~⋀Δ ⟶ □^[n](~⋀◇'⁻¹^[n]Δ) := contra₂'! this;
          have : Λ ⊢! (⋀Δ ⟶ ⊥) ⟶ □^[n](~⋀◇'⁻¹^[n]Δ) := imp_trans''! (and₂'! neg_equiv!) this;
          have : Λ ⊢! ⋀Γ ⟶ □^[n](~⋀◇'⁻¹^[n]Δ) := imp_trans''! d₁ this;
          have : Λ ⊢! □⋀Γ ⟶ □^[(n + 1)](~⋀◇'⁻¹^[n]Δ) := by simpa only [UnaryModalOperator.multimop_succ] using imply_box_distribute'! this;
          exact iff_mem_neg.mp $ h $ membership_iff.mpr $ (Context.of! this) ⨀ dΓconj;
        }

        contradiction;
      use Ω;
      constructor;
      . intro p hp;
        apply hΩ;
        simp_all;
      . apply ih.mpr;
        apply multibox_multidia.mpr;
        intro p hp;
        apply hΩ;
        simp_all;

lemma multiframe_def_multibox' : Ω₁ ≺^[n] Ω₂ ↔ ∀ {p}, p ∈ (□''⁻¹^[n]Ω₁.theory) → p ∈ Ω₂.theory := by
  constructor;
  . intro h p hp; exact multiframe_def_multibox.mp h hp;
  . intro h; apply multiframe_def_multibox.mpr; assumption;

lemma multiframe_def_multidia : Ω₁ ≺^[n] Ω₂ ↔ ∀ {p}, (p ∈ Ω₂.theory → ◇^[n]p ∈ Ω₁.theory) := Iff.trans multiframe_def_multibox multibox_multidia

end CanonicalFrame


noncomputable abbrev CanonicalModel (Λ : DeductionParameter α) [Inhabited (Λ)-MCT]  : Model α where
  Frame := CanonicalFrame Λ
  Valuation Ω a := (atom a) ∈ Ω.theory


namespace CanonicalModel

variable [Inhabited (Λ)-MCT]

@[reducible]
instance : Semantics (Formula α) (CanonicalModel Λ).World := Formula.Kripke.Satisfies.semantics (M := CanonicalModel Λ)

-- @[simp] lemma frame_def : (CanonicalModel Ax).Rel' Ω₁ Ω₂ ↔ (□''⁻¹Ω₁.theory : Theory α) ⊆ Ω₂.theory := by rfl
-- @[simp] lemma val_def : (CanonicalModel Ax).Valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel


section

variable [Inhabited (Λ)-MCT] {p : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel Λ).World}, Ω ⊧ p ↔ (p ∈ Ω.theory) := by
  induction p using Formula.rec' with
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      apply iff_mem_box.mpr;
      intro Ω' hΩ';
      apply ih.mp;
      exact h hΩ';
    . intro h Ω' hΩ';
      apply ih.mpr;
      exact CanonicalFrame.frame_def_box.mp hΩ' h;
  | _ => simp_all [Kripke.Satisfies];

lemma iff_valid_on_canonicalModel_deducible : (CanonicalModel Λ) ⊧ p ↔ Λ ⊢! p := by
  constructor;
  . contrapose;
    intro h;
    have : (Λ)-Consistent ({~p}) := by
      apply Theory.def_consistent.mpr;
      intro Γ hΓ;
      by_contra hC;
      have : Λ ⊢! p := dne'! $ neg_equiv'!.mpr $ replace_imply_left_conj! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this;
    simp [Kripke.ValidOnModel];
    use Ω;
    exact truthlemma.not.mpr $ iff_mem_neg.mp (show ~p ∈ Ω.theory by simp_all);
  . intro h Ω;
    suffices p ∈ Ω.theory by exact truthlemma.mpr this;
    by_contra hC;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Theory.iff_insert_inconsistent.mp $ Ω.maximal' hC;
    have : Γ ⊢[Λ]! ⊥ := FiniteContext.provable_iff.mpr $ and_imply_iff_imply_imply'!.mp hΓ₂ ⨀ h;
    have : Γ ⊬[Λ]! ⊥ := Theory.def_consistent.mp Ω.consistent _ hΓ₁;
    contradiction;

lemma realize_axiomset_of_self_canonicalModel : (CanonicalModel Λ) ⊧* Ax(Λ) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  exact Deduction.maxm! (by assumption);

lemma realize_theory_of_self_canonicalModel : (CanonicalModel Λ) ⊧* (System.theory Λ) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  simpa [System.theory] using hp;

end

lemma complete_of_mem_canonicalFrame [Inhabited (Λ)-MCT] {𝔽 : FrameClass.Dep α} (hFC : CanonicalFrame Λ ∈ 𝔽) : 𝔽 ⊧ p → (Λ) ⊢! p := by
  simp [Kripke.ValidOnFrameClass, Kripke.ValidOnFrame];
  contrapose;
  push_neg;
  intro h;
  use (CanonicalFrame Λ);
  constructor;
  . assumption;
  . use (CanonicalModel Λ).Valuation;
    exact iff_valid_on_canonicalModel_deducible.not.mpr h;

lemma instComplete_of_mem_canonicalFrame [Inhabited (Λ)-MCT] {𝔽 : FrameClass.Dep α} (hFC : CanonicalFrame Λ ∈ 𝔽) : Complete (Λ) 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

instance K_complete : Complete (𝐊 : DeductionParameter α) AllFrameClass# := by
  simpa [←Normal.isK] using instComplete_of_mem_canonicalFrame (Λ := 𝐊) (𝔽 := AllFrameClass#) trivial;

end Kripke

end LO.Modal.Standard
