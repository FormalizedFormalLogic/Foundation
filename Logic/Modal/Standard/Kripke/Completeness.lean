import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α] [Inhabited α]
variable {𝓓 : DeductionParameter α} [𝓓.Normal] [Inhabited (𝓓)-MCT]

open System
open Formula
open MaximalConsistentTheory

namespace Kripke

abbrev CanonicalFrame (𝓓 : DeductionParameter α) [Inhabited (𝓓)-MCT] : Frame' α where
  World := (𝓓)-MCT
  Rel :=  λ Ω₁ Ω₂ => (□''⁻¹Ω₁.theory : Theory α) ⊆ Ω₂.theory

namespace CanonicalFrame

@[simp]
lemma frame_def_box: (CanonicalFrame 𝓓).Rel Ω₁ Ω₂ ↔ (∀ {p : Formula α}, □p ∈ Ω₁.theory → p ∈ Ω₂.theory) := by rfl

lemma multiframe_def_multibox : ((CanonicalFrame 𝓓).RelItr n Ω₁ Ω₂) ↔ ∀ {p : Formula α}, □^[n]p ∈ Ω₁.theory → p ∈ Ω₂.theory := by
  induction n generalizing Ω₁ Ω₂ with
  | zero =>
    simp_all;
    constructor;
    . intro h; subst h; tauto;
    . intro h; apply intro_equality; simpa;
  | succ n ih =>
    constructor;
    . simp;
      intro Ω₃ h₁₃ h₃₂ p h;
      exact ih.mp h₃₂ $ h₁₃ h;
    . intro h;
      obtain ⟨Ω, hΩ⟩ := lindenbaum (𝓓 := 𝓓) (T := (□''⁻¹Ω₁.theory ∪ ◇''^[n]Ω₂.theory)) $ by
        apply Theory.intro_union_Consistent;
        intro Γ Δ hΓ hΔ hC;

        replace hΓ : ∀ p ∈ Γ, □p ∈ Ω₁.theory := by simpa using hΓ;
        have dΓconj : Ω₁.theory *⊢[𝓓]! □Γ.conj' := membership_iff.mp $ iff_mem_box_conj'.mpr hΓ;

        have hΔ₂ : ∀ p ∈ ◇'⁻¹^[n]Δ, p ∈ Ω₂.theory := by
          intro p hp;
          simpa using hΔ (◇^[n]p) (by simp_all);

        have hΔconj : (◇'⁻¹^[n]Δ).conj' ∈ Ω₂.theory := iff_mem_conj'.mpr hΔ₂;

        have : 𝓓 ⊢! Γ.conj' ⟶ □^[n](~(◇'⁻¹^[n]Δ).conj') := imp_trans''! (and_imply_iff_imply_imply'!.mp hC)
          $ contra₂'! $ imp_trans''! (and₂'! multidia_duality!)
          $ imp_trans''! iff_conj'multidia_multidiaconj'! $ by
            apply conj'conj'_subset;
            intro q hq;
            obtain ⟨r, _, _⟩ := by simpa using hΔ q hq;
            subst_vars;
            simpa;
        have : 𝓓 ⊢! □Γ.conj' ⟶ □^[(n + 1)](~(◇'⁻¹^[n]Δ).conj') := by simpa only [UnaryModalOperator.multimop_succ] using imply_box_distribute'! this;
        have : (◇'⁻¹^[n]Δ).conj' ∉ Ω₂.theory := iff_mem_neg.mp $ h $ membership_iff.mpr $ (Context.of! this) ⨀ dΓconj;

        contradiction;
      existsi Ω;
      constructor;
      . intro p hp;
        apply hΩ;
        simp_all;
      . apply ih.mpr;
        apply multibox_multidia.mpr;
        intro p hp;
        apply hΩ;
        simp_all;

lemma multiframe_def_multibox' : ((CanonicalFrame 𝓓).RelItr n Ω₁ Ω₂) ↔ ∀ {p : Formula α}, p ∈ (□''⁻¹^[n]Ω₁.theory) → p ∈ Ω₂.theory := by
  constructor;
  . intro h p hp; exact multiframe_def_multibox.mp h hp;
  . intro h; apply multiframe_def_multibox.mpr; assumption;

lemma multiframe_def_multibox'' : ((CanonicalFrame 𝓓).RelItr n Ω₁ Ω₂) ↔ ∀ {p : Formula α}, p ∈ (□''⁻¹^[n]Ω₁.theory) → p ∈ Ω₂.theory := by
  constructor;
  . intro h p hp; exact multiframe_def_multibox.mp h hp;
  . intro h; apply multiframe_def_multibox.mpr; assumption;

lemma multiframe_def_multidia : (CanonicalFrame 𝓓).RelItr n Ω₁ Ω₂ ↔ ∀ {p : Formula α}, (p ∈ Ω₂.theory → ◇^[n]p ∈ Ω₁.theory) := Iff.trans multiframe_def_multibox multibox_multidia

end CanonicalFrame


abbrev CanonicalModel (𝓓 : DeductionParameter α) [Inhabited (𝓓)-MCT] : Model α where
  Frame := CanonicalFrame 𝓓
  Valuation Ω a := (atom a) ∈ Ω.theory


namespace CanonicalModel

variable [Inhabited (MCT 𝓓)]

@[reducible]
instance : Semantics (Formula α) (CanonicalModel 𝓓).World := instKripkeSemanticsFormulaWorld (CanonicalModel 𝓓)

@[simp] lemma frame_def : (CanonicalModel 𝓓).Frame.Rel Ω₁ Ω₂ ↔ (□''⁻¹Ω₁.theory : Theory α) ⊆ Ω₂.theory := by rfl
@[simp] lemma val_def : (CanonicalModel 𝓓).Valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel


section

lemma truthlemma : ∀ {Ω : (CanonicalModel 𝓓).World}, Ω ⊧ p ↔ (p ∈ Ω.theory) := by
  induction p using Formula.rec' with
  | hatom a => simp [Kripke.Satisfies];
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      apply iff_mem_box.mpr;
      intro Ω' hΩ';
      apply ih.mp;
      exact h Ω' hΩ';
    . intro h Ω' hΩ';
      apply ih.mpr;
      exact CanonicalFrame.frame_def_box.mp hΩ' h;
  | hfalsum => simp [Formula.Kripke.Satisfies.bot_def (M := (CanonicalModel 𝓓))];
  | hVerum => simp [Formula.Kripke.Satisfies.top_def (M := (CanonicalModel 𝓓))];
  | _ => simp_all;

lemma iff_valid_on_canonicalModel_deducible : (CanonicalModel 𝓓) ⊧ p ↔ (𝓓 ⊢! p) := by
  constructor;
  . contrapose;
    intro h;
    have : (𝓓)-Consistent ({~p}) := by
      intro Γ hΓ;
      by_contra hC;
      have : 𝓓 ⊢! p := dne'! $ replace_imply_left_conj'! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this;
    simp [Kripke.ValidOnModel];
    existsi Ω;
    exact truthlemma.not.mpr $ iff_mem_neg.mp (show ~p ∈ Ω.theory by simp_all);
  . intro h Ω;
    suffices p ∈ Ω.theory by exact truthlemma.mpr this;
    by_contra hC;
    have := Ω.maximal' hC;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Theory.iff_insert_Inconsistent.mp this;
    exact Ω.consistent hΓ₁ $ and_imply_iff_imply_imply'!.mp hΓ₂ ⨀ h;

lemma realize_axiomset_of_self_canonicalModel : CanonicalModel 𝓓 ⊧* Ax(𝓓) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  exact ⟨Deduction.maxm hp⟩;

@[simp]
lemma realize_theory_of_self_canonicalModel : CanonicalModel 𝓓 ⊧* (System.theory 𝓓) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  simpa [System.theory] using hp;

end

lemma validOnCanonicalModel_of_subset
  {𝓓₁ 𝓓₂ : DeductionParameter α} [𝓓₁.Normal] [𝓓₂.Normal] [Inhabited (𝓓₁)-MCT] [Inhabited (𝓓₂)-MCT]
  (hRed : 𝓓₁ ≤ₛ 𝓓₂ := by simp) (h : CanonicalModel 𝓓₁ ⊧ p) : CanonicalModel 𝓓₂ ⊧ p :=
  iff_valid_on_canonicalModel_deducible.mpr $ hRed $ iff_valid_on_canonicalModel_deducible.mp h

class Canonical (𝓓 : DeductionParameter α) [Inhabited (𝓓)-MCT] where
  realize : (CanonicalFrame 𝓓) ⊧* Ax(𝓓)

lemma complete!_on_frameclass_of_canonical [System.Consistent 𝓓] [Inhabited (𝓓)-MCT] [Canonical 𝓓] : 𝔽(Ax(𝓓)) ⊧ p → 𝓓 ⊢! p := by
  simp [Kripke.ValidOnFrameClass, Kripke.ValidOnFrame];
  contrapose;
  push_neg;
  intro h;
  use (CanonicalFrame 𝓓);
  constructor;
  . apply Canonical.realize;
  . existsi (CanonicalModel 𝓓).Valuation;
    exact iff_valid_on_canonicalModel_deducible.not.mpr h;

instance instComplete [System.Consistent 𝓓] [Canonical 𝓓] : Complete 𝓓 𝔽(Ax(𝓓)) := ⟨complete!_on_frameclass_of_canonical⟩

def canonical_of_definability [Inhabited (𝓓)-MCT] (definability : Definability Ax(𝓓) P) (h : P (CanonicalFrame 𝓓)) : Canonical 𝓓 where
  realize := definability.defines _ |>.mpr h;

instance : Canonical (𝐊 : DeductionParameter α) := canonical_of_definability AxiomSet.K.definability trivial

-- MEMO: inferInstanceで行けてほしいのだがなぜか通らないので明示的に指定している
instance : Complete (𝐊 : DeductionParameter α) 𝔽(Ax(𝐊)) := instComplete

instance Canonical.union
  {𝓓₁ 𝓓₂ : DeductionParameter α}
  [𝓓₁.Normal] [𝓓₂.Normal]
  [Inhabited (𝓓₁)-MCT] [Inhabited (𝓓₂)-MCT] [Inhabited (𝓓₁ ⊔ 𝓓₂)-MCT]
  (definability₁ : Definability Ax(𝓓₁) P₁)
  (definability₂ : Definability Ax(𝓓₂) P₂)
  (h₁ : P₁ (CanonicalFrame (DeductionParameter.union 𝓓₁ 𝓓₂ (by done))))
  (h₂ : P₂ (CanonicalFrame (DeductionParameter.union 𝓓₁ 𝓓₂ (by done))))
  -- MEMO: `(by done)`としなければならない理由はよくわからない．
  : Canonical (DeductionParameter.union 𝓓₁ 𝓓₂ (by done)) := by
  apply canonical_of_definability;
  apply Definability.union definability₁ definability₂;
  exact ⟨h₁, h₂⟩;

end Kripke

end LO.Modal.Standard
