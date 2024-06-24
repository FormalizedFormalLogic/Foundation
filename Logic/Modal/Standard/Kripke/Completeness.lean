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

abbrev CanonicalFrame (Ax : AxiomSet α) [Inhabited (Axᴺ)-MCT] : Frame (Axᴺ)-MCT where
  World := Set.univ
  Rel := λ ⟨⟨Ω₁, _⟩, ⟨Ω₂, _⟩⟩ => □''⁻¹Ω₁.theory ⊆ Ω₂.theory

instance [Inhabited (Axᴺ)-MCT] : Coe (Axᴺ)-MCT (CanonicalFrame Ax).World := ⟨λ Ω => ⟨Ω, (by trivial)⟩⟩


namespace CanonicalFrame

variable [Inhabited (Axᴺ)-MCT]
variable {Ω₁ Ω₂ : (Axᴺ)-MCT}

@[simp]
lemma frame_def_box: (CanonicalFrame Ax |>.Rel' Ω₁ Ω₂) ↔ ∀ {p}, □p ∈ Ω₁.theory → p ∈ Ω₂.theory := by simp [Frame.Rel']; aesop;

lemma multiframe_def_multibox : (CanonicalFrame Ax |>.RelItr' n Ω₁ Ω₂) ↔ ∀ {p}, □^[n]p ∈ Ω₁.theory → p ∈ Ω₂.theory := by
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
      obtain ⟨Ω, hΩ⟩ := lindenbaum (𝓓 := Axᴺ) (T := (□''⁻¹Ω₁.theory ∪ ◇''^[n]Ω₂.theory)) $ by
        apply Theory.intro_union_Consistent;
        intro Γ Δ hΓ hΔ hC;

        replace hΓ : ∀ p ∈ Γ, □p ∈ Ω₁.theory := by simpa using hΓ;
        have dΓconj : Ω₁.theory *⊢[_]! □Γ.conj' := membership_iff.mp $ iff_mem_box_conj'.mpr hΓ;

        have hΔ₂ : ∀ p ∈ ◇'⁻¹^[n]Δ, p ∈ Ω₂.theory := by
          intro p hp;
          simpa using hΔ (◇^[n]p) (by simp_all);

        have hΔconj : (◇'⁻¹^[n]Δ).conj' ∈ Ω₂.theory := iff_mem_conj'.mpr hΔ₂;

        have : (Axᴺ) ⊢! Γ.conj' ⟶ □^[n](~(◇'⁻¹^[n]Δ).conj') := imp_trans''! (and_imply_iff_imply_imply'!.mp hC)
          $ contra₂'! $ imp_trans''! (and₂'! multidia_duality!)
          $ imp_trans''! iff_conj'multidia_multidiaconj'! $ by
            apply conj'conj'_subset;
            intro q hq;
            obtain ⟨r, _, _⟩ := by simpa using hΔ q hq;
            subst_vars;
            simpa;
        have : (Axᴺ) ⊢! □Γ.conj' ⟶ □^[(n + 1)](~(◇'⁻¹^[n]Δ).conj') := by simpa only [UnaryModalOperator.multimop_succ] using imply_box_distribute'! this;
        have : (◇'⁻¹^[n]Δ).conj' ∉ Ω₂.theory := iff_mem_neg.mp $ h $ membership_iff.mpr $ (Context.of! this) ⨀ dΓconj;

        contradiction;
      existsi ⟨Ω, (by trivial)⟩;
      constructor;
      . intro p hp;
        apply hΩ;
        simp_all;
      . apply ih.mpr;
        apply multibox_multidia.mpr;
        intro p hp;
        apply hΩ;
        simp_all;

lemma multiframe_def_multibox' : (CanonicalFrame Ax |>.RelItr' n Ω₁ Ω₂) ↔ ∀ {p}, p ∈ (□''⁻¹^[n]Ω₁.theory) → p ∈ Ω₂.theory := by
  constructor;
  . intro h p hp; exact multiframe_def_multibox.mp h hp;
  . intro h; apply multiframe_def_multibox.mpr; assumption;

lemma multiframe_def_multidia : (CanonicalFrame Ax |>.RelItr' n Ω₁ Ω₂) ↔ ∀ {p}, (p ∈ Ω₂.theory → ◇^[n]p ∈ Ω₁.theory) := Iff.trans multiframe_def_multibox multibox_multidia

end CanonicalFrame


abbrev CanonicalModel (Ax : AxiomSet α) [Inhabited (Axᴺ)-MCT] : Model (Axᴺ)-MCT α where
  Frame := CanonicalFrame Ax
  Valuation Ω a := (atom a) ∈ Ω.1.theory


namespace CanonicalModel

variable [Inhabited (Axᴺ)-MCT]

-- @[reducible]
-- instance : Semantics (Formula α) (CanonicalModel Ax).World := Formula.kripke_satisfies.semantics (CanonicalModel Ax)

-- @[simp] lemma frame_def : (CanonicalModel Ax).Rel' Ω₁ Ω₂ ↔ (□''⁻¹Ω₁.theory : Theory α) ⊆ Ω₂.theory := by rfl
-- @[simp] lemma val_def : (CanonicalModel Ax).Valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel


section

variable [Inhabited (Axᴺ)-MCT]

lemma truthlemma : ∀ {Ω : (Axᴺ)-MCT}, (⟨CanonicalModel Ax, Ω⟩ : (M : Model (Axᴺ)-MCT α) × M.World) ⊧ p ↔ (p ∈ Ω.theory) := by
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
  | _ => simp_all [kripke_satisfies];

lemma iff_valid_on_canonicalModel_deducible : (CanonicalModel Ax) ⊧ p ↔ ((Axᴺ) ⊢! p) := by
  constructor;
  . contrapose;
    intro h;
    have : (Axᴺ)-Consistent ({~p}) := by
      intro Γ hΓ;
      by_contra hC;
      have : _ ⊢! p := dne'! $ replace_imply_left_conj'! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this;
    simp [valid_on_KripkeModel];
    existsi Ω, (by trivial);
    exact truthlemma.not.mpr $ iff_mem_neg.mp (show ~p ∈ Ω.theory by simp_all);
  . intro h ⟨Ω, _⟩;
    suffices p ∈ Ω.theory by exact truthlemma.mpr this;
    by_contra hC;
    have := Ω.maximal' hC;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Theory.iff_insert_Inconsistent.mp this;
    exact Ω.consistent hΓ₁ $ and_imply_iff_imply_imply'!.mp hΓ₂ ⨀ h;

lemma realize_axiomset_of_self_canonicalModel : (CanonicalModel Ax) ⊧* Ax := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  exact Deduction.maxm! (by aesop);

lemma realize_theory_of_self_canonicalModel : (CanonicalModel Ax) ⊧* (System.theory (Axᴺ)) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  simpa [System.theory] using hp;

end

lemma complete_of_mem_canonicalFrame [Inhabited (Axᴺ)-MCT] {𝔽 : FrameClass.Dep α} (hFC : ⟨(Axᴺ)-MCT, CanonicalFrame Ax⟩ ∈ 𝔽) : 𝔽 ⊧ p → (Axᴺ) ⊢! p := by
  simp [valid_on_KripkeFrameClass, valid_on_KripkeFrame];
  contrapose;
  push_neg;
  intro h;
  use (Axᴺ)-MCT, (CanonicalFrame Ax);
  constructor;
  . assumption;
  . use (CanonicalModel Ax).Valuation;
    exact iff_valid_on_canonicalModel_deducible.not.mpr h;

instance instComplete_of_mem_canonicalFrame [Inhabited (Axᴺ)-MCT] {𝔽 : FrameClass.Dep α} (hFC : ⟨(Axᴺ)-MCT, CanonicalFrame Ax⟩ ∈ 𝔽) : Complete (Axᴺ) 𝔽 := ⟨complete_of_mem_canonicalFrame hFC⟩

-- LO.Modal.Standard.Kripke.completeness_of_K.{u_1} {α : Type u_1} [DecidableEq α] : Complete 𝐊 (AllFrameClass.Dep α)
instance K_complete : Complete 𝐊 AllFrameClass[α] := by
  simpa [←Normal.isK] using instComplete_of_mem_canonicalFrame (Ax := 𝗞) (𝔽 := AllFrameClass[α]) trivial;

end Kripke

end LO.Modal.Standard
