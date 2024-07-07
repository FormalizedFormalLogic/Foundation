import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α] [Inhabited α]
variable {Ax : AxiomSet α}

open System
open Formula
open MaximalConsistentTheory
open DeductionParameter (Normal)

namespace Kripke

abbrev CanonicalFrame (Ax : AxiomSet α) [Inhabited (𝝂Ax)-MCT] : Frame where
  World := (𝝂Ax)-MCT
  Rel Ω₁ Ω₂ := □''⁻¹Ω₁.theory ⊆ Ω₂.theory

namespace CanonicalFrame

variable [Inhabited (𝝂Ax)-MCT]
variable {Ω₁ Ω₂ : (CanonicalFrame Ax).World}

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
      obtain ⟨Ω, hΩ⟩ := lindenbaum (Λ := 𝝂Ax) (T := (□''⁻¹Ω₁.theory ∪ ◇''^[n]Ω₂.theory)) $ by
        apply Theory.intro_union_consistent;
        intro Γ Δ hΓ hΔ hC;

        replace hΓ : ∀ p ∈ Γ, □p ∈ Ω₁.theory := by simpa using hΓ;
        have dΓconj : Ω₁.theory *⊢[_]! □⋀Γ := membership_iff.mp $ iff_mem_box_conj.mpr hΓ;

        have hΔ₂ : ∀ p ∈ ◇'⁻¹^[n]Δ, p ∈ Ω₂.theory := by
          intro p hp;
          simpa using hΔ (◇^[n]p) (by simp_all);

        have hΔconj : ⋀◇'⁻¹^[n]Δ ∈ Ω₂.theory := iff_mem_conj.mpr hΔ₂;

        have : ⋀◇'⁻¹^[n]Δ ∉ Ω₂.theory := by {
          have d₁ : 𝝂Ax ⊢! ⋀Γ ⟶ ⋀Δ ⟶ ⊥ := and_imply_iff_imply_imply'!.mp hC;
          have : 𝝂Ax ⊢! ⋀(◇'^[n]◇'⁻¹^[n]Δ) ⟶ ⋀Δ := by
            apply conjconj_subset!;
            intro q hq;
            obtain ⟨r, _, _⟩ := hΔ q hq;
            subst_vars;
            simpa;
          have : 𝝂Ax ⊢! ◇^[n]⋀◇'⁻¹^[n]Δ ⟶ ⋀Δ := imp_trans''! iff_conjmultidia_multidiaconj! $ this;
          have : 𝝂Ax ⊢! ~(□^[n](~⋀◇'⁻¹^[n]Δ)) ⟶ ⋀Δ := imp_trans''! (and₂'! multidia_duality!) this;
          have : 𝝂Ax ⊢! ~⋀Δ ⟶ □^[n](~⋀◇'⁻¹^[n]Δ) := contra₂'! this;
          have : 𝝂Ax ⊢! (⋀Δ ⟶ ⊥) ⟶ □^[n](~⋀◇'⁻¹^[n]Δ) := imp_trans''! (and₂'! neg_equiv!) this;
          have : 𝝂Ax ⊢! ⋀Γ ⟶ □^[n](~⋀◇'⁻¹^[n]Δ) := imp_trans''! d₁ this;
          have : 𝝂Ax ⊢! □⋀Γ ⟶ □^[(n + 1)](~⋀◇'⁻¹^[n]Δ) := by simpa only [UnaryModalOperator.multimop_succ] using imply_box_distribute'! this;
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


abbrev CanonicalModel (Ax : AxiomSet α) [Inhabited (𝝂Ax)-MCT] : Model α where
  Frame := CanonicalFrame Ax
  Valuation Ω a := (atom a) ∈ Ω.theory


namespace CanonicalModel

variable [Inhabited (𝝂Ax)-MCT]

@[reducible]
instance : Semantics (Formula α) (CanonicalModel Ax).World := Formula.Kripke.Satisfies.semantics (M := CanonicalModel Ax)

-- @[simp] lemma frame_def : (CanonicalModel Ax).Rel' Ω₁ Ω₂ ↔ (□''⁻¹Ω₁.theory : Theory α) ⊆ Ω₂.theory := by rfl
-- @[simp] lemma val_def : (CanonicalModel Ax).Valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel


section

variable [Inhabited (𝝂Ax)-MCT] {p : Formula α}

lemma truthlemma : ∀ {Ω : (CanonicalModel Ax).World}, Ω ⊧ p ↔ (p ∈ Ω.theory) := by
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

lemma iff_valid_on_canonicalModel_deducible : (CanonicalModel Ax) ⊧ p ↔ ((𝝂Ax) ⊢! p) := by
  constructor;
  . contrapose;
    intro h;
    have : (𝝂Ax)-Consistent ({~p}) := by
      apply Theory.def_consistent.mpr;
      intro Γ hΓ;
      by_contra hC;
      have : 𝝂Ax ⊢! p := dne'! $ neg_equiv'!.mpr $ replace_imply_left_conj! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this;
    simp [Kripke.ValidOnModel];
    use Ω;
    exact truthlemma.not.mpr $ iff_mem_neg.mp (show ~p ∈ Ω.theory by simp_all);
  . intro h Ω;
    suffices p ∈ Ω.theory by exact truthlemma.mpr this;
    by_contra hC;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Theory.iff_insert_inconsistent.mp $ Ω.maximal' hC;
    have : Γ ⊢[𝝂Ax]! ⊥ := FiniteContext.provable_iff.mpr $ and_imply_iff_imply_imply'!.mp hΓ₂ ⨀ h;
    have : Γ ⊬[𝝂Ax]! ⊥ := Theory.def_consistent.mp Ω.consistent _ hΓ₁;
    contradiction;

lemma realize_axiomset_of_self_canonicalModel : (CanonicalModel Ax) ⊧* Ax := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  exact Deduction.maxm! (by aesop);

lemma realize_theory_of_self_canonicalModel : (CanonicalModel Ax) ⊧* (System.theory (𝝂Ax)) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  simpa [System.theory] using hp;

end

lemma complete_of_mem_canonicalFrame [Inhabited (𝝂Ax)-MCT] {𝔽 : FrameClass.Dep α} (hFC : CanonicalFrame Ax ∈ 𝔽) : 𝔽 ⊧ p → (𝝂Ax) ⊢! p := by
  simp [Kripke.ValidOnFrameClass, Kripke.ValidOnFrame];
  contrapose;
  push_neg;
  intro h;
  use (CanonicalFrame Ax);
  constructor;
  . assumption;
  . use (CanonicalModel Ax).Valuation;
    exact iff_valid_on_canonicalModel_deducible.not.mpr h;

lemma instComplete_of_mem_canonicalFrame [Inhabited (𝝂Ax)-MCT] {𝔽 : FrameClass.Dep α} (hFC : CanonicalFrame Ax ∈ 𝔽) : Complete (𝝂Ax) 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

instance K_complete : Complete (𝐊 : DeductionParameter α) AllFrameClass# := by
  simpa [←Normal.isK] using instComplete_of_mem_canonicalFrame (Ax := 𝗞) (𝔽 := AllFrameClass#) trivial;

end Kripke

end LO.Modal.Standard
