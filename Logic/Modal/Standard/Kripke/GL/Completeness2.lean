import Logic.Modal.Standard.Complemental
import Logic.Modal.Standard.Kripke.GL.Definability

namespace LO.Modal.Standard

variable {α : Type u} [Inhabited α] [DecidableEq α]
variable {p q : Formula α}

namespace Kripke

open Formula

abbrev GLCompleteFrame (p : Formula α) : Kripke.FiniteFrame where
  World := CCF 𝐆𝐋 (𝒮 p)
  Rel X Y :=
    (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.formulae → (q ∈ Y.formulae ∧ □q ∈ Y.formulae)) ∧
    (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.formulae ∧ □r ∈ Y.formulae)

namespace GLCompleteFrame

lemma irreflexive : Irreflexive (GLCompleteFrame p).Rel := by simp [Irreflexive];

lemma transitive : Transitive (GLCompleteFrame p).Rel := by
  simp;
  rintro X Y Z ⟨RXY, ⟨r, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  . rintro q hq₁ hq₂;
    exact RYZ q hq₁ $ RXY q hq₁ hq₂ |>.2;
  . use r;
    refine ⟨by assumption, by assumption, ?_⟩;
    exact RYZ r (by assumption) (by assumption) |>.2;

end GLCompleteFrame


abbrev GLCompleteModel (p : Formula α) : Kripke.Model α where
  Frame := GLCompleteFrame p
  Valuation X a := (atom a) ∈ X.formulae

open System System.FiniteContext
open Formula.Kripke
open ComplementaryClosedConsistentFormulae

private lemma GL_truthlemma.lemma1
  {X : CCF 𝐆𝐋 (𝒮 p)} (hq₁ : □q ∈ 𝒮 p) (hq₂ : □q ∉ X.formulae)
  : Formulae.Consistent 𝐆𝐋  ((X.formulae.prebox ∪ X.formulae.prebox.box) ∪ {□q, -q}) := by
  apply Formulae.intro_union_consistent;
  intro Γ₁ Γ₂ hΓ₁ hΓ₂;
  by_contra hC;
  have : 𝐆𝐋 ⊢! ⋀Γ₁ ⟶ ⋀Γ₂ ⟶ ⊥ := and_imply_iff_imply_imply'!.mp hC;
  have : Γ₁ ⊢[𝐆𝐋]! ⋀Γ₂ ⟶ ⊥ := provable_iff.mpr this;
  have : Γ₁ ⊢[𝐆𝐋]! (□q ⋏ -q) ⟶ ⊥ := imp_trans''! (by
    suffices Γ₁ ⊢[𝐆𝐋]! ⋀[□q, -q] ⟶ ⋀Γ₂ by simpa;
    apply conjconj_subset!;
    intro p hp;
    have := hΓ₂ p hp;
    simp at this;
    rcases this with (_ | _);
    . simp; left; assumption;
    . simp; right; assumption;
  ) this;
  have : Γ₁ ⊢[𝐆𝐋]! □q ⟶ -q ⟶ ⊥ := and_imply_iff_imply_imply'!.mp this;
  have : Γ₁ ⊢[𝐆𝐋]! □q ⟶ q := by
    rcases Formula.complement.or (p := q) with (hp | ⟨q, rfl⟩);
    . rw [hp] at this;
      exact imp_trans''! this dne!;
    . simpa [complement] using this;
  have : (□'Γ₁) ⊢[𝐆𝐋]! □(□q ⟶ q) := contextual_nec! this;
  have : (□'Γ₁) ⊢[𝐆𝐋]! □q := axiomL! ⨀ this;
  have H₁ : 𝐆𝐋 ⊢! ⋀□'Γ₁ ⟶ □q := provable_iff.mp this;

  let Γ₁' := Γ₁.filter (λ r => r ∈ X.formulae.prebox);
  have hΓ₁' : ∀ r ∈ Γ₁', r ∈ X.formulae.prebox := by intro r hr; simpa using List.of_mem_filter hr;

  have H₂ : 𝐆𝐋 ⊢! ⋀□'Γ₁' ⟶ ⋀□'Γ₁ := conjconj_provable! $ by
    intro r hr; simp at hr;
    obtain ⟨r, hr, rfl⟩ := hr;
    have := hΓ₁ r hr; simp at this;
    rcases this with (_ | ⟨r, hr, rfl⟩);
    . apply by_axm!;
      simp [Γ₁'];
      sorry;
    . apply axiomFour'!;
      apply by_axm!;
      sorry;

  replace H₂ : 𝐆𝐋 ⊢! ⋀□'Γ₁' ⟶ ⋀□'Γ₁ := provable_iff.mp H₂;
  have := imp_trans''! H₂ H₁;

  have : X.formulae *⊢[𝐆𝐋]! □q := by
    apply Context.provable_iff.mpr;
    use (□'Γ₁');
    constructor;
    . intro q hq;
      simp at hq;
      obtain ⟨r, hr, rfl⟩ := hq;
      simpa using hΓ₁' r hr;
    . assumption;

  have : □q ∈ X.formulae := membership_iff hq₁ |>.mpr this;
  contradiction;

private lemma GL_truthlemma.lemma2
  {X : CCF 𝐆𝐋 (𝒮 p)} (hq : □q ∈ 𝒮 p)
  : ((X.formulae.prebox ∪ X.formulae.prebox.box) ∪ {□q, -q}) ⊆ (𝒮 p)⁻ := by
  simp only [Formulae.complementary];
  intro r hr;
  simp [Finset.mem_union] at hr;
  rcases hr with (rfl | hp | ⟨r, hr, rfl⟩ | rfl);
  . apply Finset.mem_union.mpr;
    tauto;
  . have := X.closed.subset hp;
    have := Formulae.complementary_mem_box this;
    apply Finset.mem_union.mpr;
    left; trivial;
  . exact X.closed.subset hr;
  . apply Finset.mem_union.mpr;
    right; simp;
    use q;
    constructor;
    . trivial;
    . rfl;

lemma GL_truthlemma (h : 𝐆𝐋 ⊬! p) {X : CCF 𝐆𝐋 (𝒮 p)} (q_sub : q ∈ 𝒮 p) :
  Satisfies (GLCompleteModel p) X q ↔ q ∈ X.formulae := by
  induction q using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp q r ihq ihr =>
    constructor;
    . contrapose;
      intro h;
      simp [Satisfies];
      constructor;
      . apply ihq (by trivial) |>.mpr;
        exact iff_not_mem_imp q_sub |>.mp h |>.1;
      . apply ihr (by trivial) |>.not.mpr;
        have := iff_not_mem_imp q_sub |>.mp h |>.2;
        exact iff_mem_compl (by trivial) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by trivial) |>.mp hq;
      replace hr := ihr (by trivial) |>.not.mp hr;
      apply iff_not_mem_imp q_sub |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (by trivial) |>.not.mp (by simpa using hr);
  | hbox q ih =>
    constructor;
    . contrapose;
      intro h;
      obtain ⟨Y, hY₁⟩ := lindenbaum (S := 𝒮 p) (GL_truthlemma.lemma2 q_sub) (GL_truthlemma.lemma1 q_sub h);
      simp only [Finset.union_subset_iff] at hY₁;
      have hY₁₁ : □q ∈ Y.formulae := by apply hY₁.2; simp;
      have hY₁₂ : -q ∈ Y.formulae := by apply hY₁.2; simp;
      simp [Satisfies];
      use Y;
      constructor;
      . intro r _ hr_sub;
        constructor;
        . apply hY₁.1.1; simpa;
        . apply hY₁.1.2; simpa;
      . use q;
        refine ⟨q_sub, h, hY₁₁, ?_⟩;
        . apply ih (by trivial) |>.not.mpr;
          exact iff_mem_compl (by trivial) |>.not.mpr (by simpa);
    . intro h Y RXY;
      apply ih (by trivial) |>.mpr;
      simp [Frame.Rel'] at RXY;
      refine RXY.1 q ?_ h |>.1;
      assumption;

private lemma GL_completeAux : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐋 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GLCompleteFrame p);
  constructor;
  . exact ⟨GLCompleteFrame.transitive, GLCompleteFrame.irreflexive⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    obtain ⟨X, hX₁⟩ := lindenbaum (S := 𝒮 p) (X := {-p})
      (by
        simp [Formulae.complementary];
        right; use p; constructor <;> simp;
      )
      (Formulae.unprovable_iff_singleton_compl_consistent.mp h);
    use (GLCompleteModel p).Valuation, X;
    apply GL_truthlemma (by simpa) (by simp) |>.not.mpr;
    exact iff_mem_compl (by simp) |>.not.mpr $ by
      simp;
      apply hX₁;
      tauto;

instance GL_complete : Complete (𝐆𝐋 : DeductionParameter α) TransitiveIrreflexiveFrameClass.{u}ꟳ# := ⟨GL_completeAux⟩

instance : FiniteFrameProperty (α := α) 𝐆𝐋 TransitiveIrreflexiveFrameClass where

end Kripke

end LO.Modal.Standard
