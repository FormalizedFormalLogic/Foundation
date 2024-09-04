import Logic.Modal.Complemental
import Logic.Modal.Kripke.Grz.Definability


namespace LO.Modal

open LO.Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]
variable {p q : Formula α}

namespace Formula

noncomputable abbrev GrzSubformulas (p : Formula α) := (𝒮 p) ∪ ((𝒮 p).prebox.image (λ q => □(q ⟶ □q)))
prefix:70 "𝒮ᴳ " => Formula.GrzSubformulas

namespace GrzSubformulas

@[simp]
lemma mem_self : p ∈ 𝒮ᴳ p := by simp [GrzSubformulas, Subformulas.mem_self]

lemma mem_boximpbox (h : q ∈ (𝒮 p).prebox) : □(q ⟶ □q) ∈ 𝒮ᴳ p := by simp_all [GrzSubformulas];

lemma mem_origin (h : q ∈ 𝒮 p) : q ∈ 𝒮ᴳ p := by simp_all [GrzSubformulas];

lemma mem_imp (h : (q ⟶ r) ∈ 𝒮ᴳ p) : q ∈ 𝒮ᴳ p ∧ r ∈ 𝒮ᴳ p := by
  simp_all [GrzSubformulas];
  aesop;

lemma mem_imp₁ (h : (q ⟶ r) ∈ 𝒮ᴳ p) : q ∈ 𝒮ᴳ p := mem_imp h |>.1

lemma mem_imp₂ (h : (q ⟶ r) ∈ 𝒮ᴳ p) : r ∈ 𝒮ᴳ p := mem_imp h |>.2

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_origin $ by assumption
    | apply mem_imp₁  $ by assumption
    | apply mem_imp₂  $ by assumption
  )

end GrzSubformulas


end Formula

namespace Kripke

open Formula

abbrev GrzCompleteFrame (p : Formula α) : Kripke.FiniteFrame where
  World := CCF 𝐆𝐫𝐳 (𝒮ᴳ p)
  Rel X Y :=
    (∀ q ∈ □''⁻¹(𝒮ᴳ p), □q ∈ X.formulae → □q ∈ Y.formulae) ∧
    ((∀ q ∈ □''⁻¹(𝒮ᴳ p), □q ∈ Y.formulae → □q ∈ X.formulae) → X = Y)

namespace GrzCompleteFrame

lemma reflexive : Reflexive (GrzCompleteFrame p).Rel := by simp [Reflexive];

lemma transitive : Transitive (GrzCompleteFrame p).Rel := by
  simp;
  rintro X Y Z ⟨RXY₁, RXY₂⟩ ⟨RYZ₁, RYZ₂⟩;
  constructor;
  . rintro q hq₁ hq₂;
    exact RYZ₁ q hq₁ $ RXY₁ q hq₁ hq₂;
  . intro h;
    have eXY : X = Y := RXY₂ $ by
      intro q hs hq;
      exact h q hs $ RYZ₁ q hs hq;
    have eYZ : Y = Z := RYZ₂ $ by
      intro q hs hq;
      exact RXY₁ q hs $ h q hs hq;
    subst_vars;
    tauto;

lemma antisymm : Antisymmetric (GrzCompleteFrame p).Rel := by
  rintro X Y ⟨_, h₁⟩ ⟨h₂, _⟩;
  exact h₁ h₂;

end GrzCompleteFrame

abbrev GrzCompleteModel (p : Formula α) : Kripke.Model α where
  Frame := GrzCompleteFrame p
  Valuation X a := (atom a) ∈ X.formulae


open System System.FiniteContext
open Formula.Kripke
open ComplementaryClosedConsistentFormulae


private lemma Grz_truthlemma.lemma1
  {X : CCF 𝐆𝐫𝐳 (𝒮ᴳ p)} (hq : □q ∈ 𝒮 p)
  : ((X.formulae.prebox.box) ∪ {□(q ⟶ □q), -q}) ⊆ (𝒮ᴳ p)⁻ := by
  simp only [Formulae.complementary];
  intro r hr;
  simp [Finset.mem_union] at hr;
  apply Finset.mem_union.mpr;
  rcases hr with (rfl | ⟨r, hr, rfl⟩ | rfl);
  . left;
    simp;
    tauto;
  . have := X.closed.subset hr;
    left;
    exact Formulae.complementary_mem_box GrzSubformulas.mem_imp₁ this;
  . right; simp;
    use q;
    constructor;
    . left; trivial;
    . rfl;

private lemma Grz_truthlemma.lemma2
  {X : CCF 𝐆𝐫𝐳 (𝒮ᴳ p)} (hq₁ : □q ∈ 𝒮 p) (hq₂ : □q ∉ X.formulae)
  : Formulae.Consistent 𝐆𝐫𝐳 ((X.formulae.prebox.box) ∪ {□(q ⟶ □q), -q}) := by
    apply Formulae.intro_union_consistent;
    rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;
    replace hΓ₂ : ∀ r ∈ Γ₂, r = □(q ⟶ □q) ∨ r = -q := by
      intro r hr;
      simpa using hΓ₂ r hr;

    by_contra hC;
    have : Γ₁ ⊢[𝐆𝐫𝐳]! ⋀Γ₂ ⟶ ⊥ := provable_iff.mpr $ and_imply_iff_imply_imply'!.mp hC;
    have : Γ₁ ⊢[𝐆𝐫𝐳]! (□(q ⟶ □q) ⋏ -q) ⟶ ⊥ := imp_trans''! (by
      suffices Γ₁ ⊢[𝐆𝐫𝐳]! ⋀[□(q ⟶ □q), -q] ⟶ ⋀Γ₂ by
        simpa only [ne_eq, List.cons_ne_self, not_false_eq_true, List.conj₂_cons_nonempty, List.conj₂_singleton];
      apply conjconj_subset!;
      simpa using hΓ₂;
    ) this;
    have : Γ₁ ⊢[𝐆𝐫𝐳]! □(q ⟶ □q) ⟶ -q ⟶ ⊥ := and_imply_iff_imply_imply'!.mp this;
    have : Γ₁ ⊢[𝐆𝐫𝐳]! □(q ⟶ □q) ⟶ q := by
      rcases Formula.complement.or (p := q) with (hp | ⟨q, rfl⟩);
      . rw [hp] at this;
        exact imp_trans''! this dne!;
      . simpa only [complement] using this;
    have : (□'Γ₁) ⊢[𝐆𝐫𝐳]! □(□(q ⟶ □q) ⟶ q) := contextual_nec! this;
    have : (□'Γ₁) ⊢[𝐆𝐫𝐳]! q := axiomGrz! ⨀ this;
    have : (□'□'Γ₁) ⊢[𝐆𝐫𝐳]! □q := contextual_nec! this;
    -- TODO: `contextual_axiomFour`
    have : 𝐆𝐫𝐳 ⊢! ⋀□'□'Γ₁ ⟶ □q := provable_iff.mp this;
    have : 𝐆𝐫𝐳 ⊢! □□⋀Γ₁ ⟶ □q := imp_trans''! (imp_trans''! (distribute_multibox_conj! (n := 2)) $ conjconj_subset! (by simp)) this;
    have : 𝐆𝐫𝐳 ⊢! □⋀Γ₁ ⟶ □q := imp_trans''! axiomFour! this;
    have : 𝐆𝐫𝐳 ⊢! ⋀□'Γ₁ ⟶ □q := imp_trans''! collect_box_conj! this;
    have : 𝐆𝐫𝐳 ⊢! ⋀□'(X.formulae.prebox.box |>.toList) ⟶ □q := imp_trans''! (conjconj_subset! (by
      simp;
      intro r hr;
      have := hΓ₁ _ hr; simp at this;
      tauto;
    )) this;
    have : 𝐆𝐫𝐳 ⊢! ⋀□'(X.formulae.prebox.toList) ⟶ □q := imp_trans''! (conjconj_provable! (by
      intro q hq;
      simp at hq;
      obtain ⟨r, hr, rfl⟩ := hq;
      apply axiomFour'!;
      apply FiniteContext.by_axm!;
      simpa;
    )) this;
    have : X.formulae *⊢[𝐆𝐫𝐳]! □q := by
      apply Context.provable_iff.mpr;
      use □'X.formulae.prebox.toList;
      constructor;
      . simp;
      . assumption;
    have : □q ∈ X.formulae := membership_iff (by trivial) |>.mpr this;
    contradiction;

-- TODO: syntactical proof
private lemma Grz_truthlemma.lemma3 : 𝐊𝐓 ⊢! (p ⋏ □(p ⟶ □p)) ⟶ □p := by
  by_contra hC;
  have := (not_imp_not.mpr $ KT_complete (α := α) |>.complete) hC;
  simp at this;
  obtain ⟨F, F_refl, hF⟩ := this;
  simp [ValidOnFrame, ValidOnModel, Satisfies] at hF;
  obtain ⟨V, x, h₁, h₂, ⟨y, Rxy, h₃⟩⟩ := hF;
  have := h₂ x (F_refl x);
  have := (this h₁) _ Rxy;
  contradiction;

lemma Grz_truthlemma {X : (GrzCompleteModel p).World} (q_sub : q ∈ 𝒮 p) :
  Satisfies (GrzCompleteModel p) X q ↔ q ∈ X.formulae := by
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
        exact iff_not_mem_imp
          (hsub_qr := GrzSubformulas.mem_origin q_sub)
          (hsub_q := by simp [GrzSubformulas]; left; trivial)
          (hsub_r := by simp [GrzSubformulas]; left; trivial)
          |>.mp h |>.1;
      . apply ihr (by trivial) |>.not.mpr;
        have := iff_not_mem_imp
          (hsub_qr := GrzSubformulas.mem_origin q_sub)
          (hsub_q := by simp [GrzSubformulas]; left; trivial)
          (hsub_r := by simp [GrzSubformulas]; left; trivial)
          |>.mp h |>.2;
        exact iff_mem_compl (by simp [GrzSubformulas]; left; trivial) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by trivial) |>.mp hq;
      replace hr := ihr (by trivial) |>.not.mp hr;
      apply iff_not_mem_imp
        (hsub_qr := GrzSubformulas.mem_origin q_sub)
        (hsub_q := by simp [GrzSubformulas]; left; trivial)
        (hsub_r := by simp [GrzSubformulas]; left; trivial) |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (by simp [GrzSubformulas]; left; trivial) |>.not.mp (by simpa using hr);
  | hbox q ih =>
    constructor;
    . contrapose;
      by_cases w : q ∈ X.formulae;
      . intro h;
        obtain ⟨Y, hY⟩ := lindenbaum (S := 𝒮ᴳ p) (Grz_truthlemma.lemma1 q_sub) (Grz_truthlemma.lemma2 q_sub h);
        simp only [Finset.union_subset_iff] at hY;
        simp only [Satisfies]; push_neg;
        use Y;
        constructor;
        . constructor;
          . intro r hr hr₂;
            apply hY.1;
            simpa;
          . apply imp_iff_not_or (b := X = Y) |>.mpr;
            left; push_neg;
            use (q ⟶ □q);
            refine ⟨?_, ?_, ?_⟩;
            . simp_all;
            . apply hY.2; simp;
            . by_contra hC;
              have : ↑X.formulae *⊢[𝐆𝐫𝐳]! q := membership_iff (by simp; left; trivial) |>.mp w;
              have : ↑X.formulae *⊢[𝐆𝐫𝐳]! □(q ⟶ □q) := membership_iff (by simp; right; assumption) |>.mp hC;
              have : ↑X.formulae *⊢[𝐆𝐫𝐳]! (q ⋏ □(q ⟶ □q)) ⟶ □q := Context.of! $ KT_weakerThan_Grz Grz_truthlemma.lemma3;
              have : ↑X.formulae *⊢[𝐆𝐫𝐳]! □q := this ⨀ and₃'! (by assumption) (by assumption);
              have : □q ∈ X.formulae := membership_iff (GrzSubformulas.mem_origin (by assumption)) |>.mpr this;
              contradiction;
        . apply ih (by trivial) |>.not.mpr;
          apply iff_mem_compl (GrzSubformulas.mem_origin (by trivial)) |>.not.mpr;
          simp;
          apply hY.2;
          simp;
      . intro _;
        simp only [Satisfies]; push_neg;
        use X;
        constructor;
        . exact GrzCompleteFrame.reflexive X;
        . exact ih (by trivial) |>.not.mpr w;
    . intro h Y RXY;
      apply ih (by trivial) |>.mpr;
      have : ↑Y.formulae *⊢[𝐆𝐫𝐳]! □q ⟶ q := Context.of! $ axiomT!;
      have : ↑Y.formulae *⊢[𝐆𝐫𝐳]! q := this ⨀ (membership_iff (by simp; left; trivial) |>.mp (RXY.1 q (by simp; tauto) h));
      exact membership_iff (by simp; left; trivial) |>.mpr this;

private lemma Grz_completeAux {p : Formula α} : ReflexiveTransitiveAntisymmetricFrameClass.{u}ꟳ#α ⊧ p → 𝐆𝐫𝐳 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GrzCompleteFrame p);
  constructor;
  . refine ⟨GrzCompleteFrame.reflexive, GrzCompleteFrame.transitive, GrzCompleteFrame.antisymm⟩;
  . simp only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models];
    push_neg;
    obtain ⟨X, hX₁⟩ := lindenbaum (S := 𝒮ᴳ p) (X := {-p})
      (by simp; apply Formulae.complementary_comp; simp)
      (Formulae.unprovable_iff_singleton_compl_consistent.mp h);
    use (GrzCompleteModel p).Valuation, X;
    apply Grz_truthlemma (by simp) |>.not.mpr;
    exact iff_mem_compl (by simp) |>.not.mpr $ by
      simp;
      apply hX₁;
      tauto;

instance Grz_complete : Complete (𝐆𝐫𝐳 : Hilbert α) (ReflexiveTransitiveAntisymmetricFrameClass.{u}ꟳ#α) := ⟨Grz_completeAux⟩

instance : FiniteFrameProperty (α := α) 𝐆𝐫𝐳 ReflexiveTransitiveAntisymmetricFrameClass where

end Kripke

end LO.Modal
