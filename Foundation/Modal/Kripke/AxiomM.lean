
import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.K4
import Foundation.Modal.Kripke.Completeness


section

variable {α : Type u} (rel : α → α → Prop)

def McKinseyCondition := ∀ x, ∃ y, rel x y ∧ (∀ z, rel y z → y = z)

class SatisfiesMcKinseyCondition (α) (rel : α → α → Prop) : Prop where
  mckCondition : McKinseyCondition rel

end



namespace LO.Modal

@[simp]
lemma eq_box_toSet_toSet_box {F : Type*} [Box F] [DecidableEq F] {s : Finset F} : s.toSet.box = s.box.toSet := by ext φ; simp;


namespace Hilbert

variable {H : Hilbert _}

noncomputable instance [Hilbert.K4Point1 ⪯ H] : Entailment.Modal.K4Point1 H where
  K _ _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4Point1) (by simp) |>.some
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4Point1) (by simp) |>.some
  M _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4Point1) (by simp) |>.some

end Hilbert


namespace Hilbert.K

open Entailment
open Formula.Kripke

lemma axiomM_DiaCDiaBox! : Hilbert.K ⊢! (□◇φ ➝ ◇□φ) ⭤ ◇(◇φ ➝ □φ) := by
  apply Kripke.complete.complete;
  intro F _ V x;
  apply Satisfies.iff_def.mpr;
  constructor;
  . intro h;
    apply Satisfies.dia_def.mpr;
    by_cases hx : Satisfies _ x (□◇φ);
    . obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp $ h hx;
      use y;
      constructor;
      . assumption;
      . tauto;
    . have := Satisfies.box_def.not.mp hx;
      push_neg at this;
      obtain ⟨y, Rxy, hy⟩ := this;
      use y;
      constructor;
      . assumption;
      . intro h;
        contradiction;
  . intro hx₁ hx₂;
    obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp hx₁;
    apply Satisfies.dia_def.mpr;
    use y;
    constructor
    . assumption;
    . exact hy $ hx₂ _ Rxy;

lemma CKDiaBoxDiaK! : Hilbert.K ⊢! (◇φ ⋏ □ψ) ➝ ◇(φ ⋏ ψ) := by
  apply Kripke.complete.complete;
  intro F _ V x hx;
  have ⟨hx₁, hx₂⟩ := Satisfies.and_def.mp hx;
  have ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp hx₁;
  apply Satisfies.dia_def.mpr;
  use y;
  constructor;
  . assumption;
  . apply Satisfies.and_def.mpr;
    constructor;
    . assumption
    . apply hx₂ _ Rxy;

lemma CKBoxDiaDiaK! : Hilbert.K ⊢! (□φ ⋏ ◇ψ) ➝ ◇(φ ⋏ ψ) := by
  sorry;

end Hilbert.K


namespace Hilbert.K4Point1

open Entailment

variable {φ ψ : Formula _}

lemma CKDiaBoxDiaK! : Hilbert.K4Point1 ⊢! (◇φ ⋏ □ψ) ➝ ◇(φ ⋏ ψ) := K_weakerThan_K4Point1.pbl Hilbert.K.CKDiaBoxDiaK!

lemma CKBoxDiaDiaK! : Hilbert.K4Point1 ⊢! (□φ ⋏ ◇ψ) ➝ ◇(φ ⋏ ψ) := K_weakerThan_K4Point1.pbl Hilbert.K.CKBoxDiaDiaK!

lemma DiaK!_of_CKBoxDia (h : Hilbert.K4Point1 ⊢! ◇φ ⋏ □ψ) : Hilbert.K4Point1 ⊢! ◇(φ ⋏ ψ) := CKDiaBoxDiaK! ⨀ h

lemma DiaCDiaBox! : Hilbert.K4Point1 ⊢! ◇(◇φ ➝ □φ) :=
  (K_weakerThan_K4Point1.pbl $ C_of_E_mp! $ Hilbert.K.axiomM_DiaCDiaBox!) ⨀ (by simp)

lemma DiaConjCDiabox {Γ : List _} (hΓ : Γ ≠ []) : Hilbert.K4Point1 ⊢! ◇(Γ.map (λ φ => ◇φ ➝ □φ)).conj := by
  induction Γ using List.induction_with_singleton' with
  | hnil => tauto;
  | hsingle φ =>
    sorry;
  | hcons φ ψ Γ ih =>
    simp;
    have : Hilbert.K4Point1 ⊢! (List.map (fun φ ↦ ◇(◇φ ➝ □φ)) (φ :: ψ :: Γ)).conj := by
      -- Conj_intro
      sorry;
    have : Hilbert.K4Point1 ⊢! (List.map (fun φ ↦ □◇(◇φ ➝ □φ)) (φ :: ψ :: Γ)).conj := by
      -- Conj_intro
      sorry;
    simp at this;
    have := K!_replace_left this axiomM!;
    have := (C_of_E_mpr! K!_assoc) ⨀ this;
    have := K!_replace_left this CKDiaBoxDiaK!;
    have : Hilbert.K4Point1 ⊢! ◇◇((◇φ ➝ □φ) ⋏ (◇ψ ➝ □ψ)) ⋏ (List.map (fun φ ↦ □◇(◇φ ➝ □φ)) Γ).conj := by sorry;
    have : Hilbert.K4Point1 ⊢! ◇((◇φ ➝ □φ) ⋏ (◇ψ ➝ □ψ)) ⋏ (List.map (fun φ ↦ □◇(◇φ ➝ □φ)) Γ).conj := K!_replace_left this $ by
      sorry;
    have : Hilbert.K4Point1 ⊢! ◇((◇φ ➝ □φ) ⋏ (◇ψ ➝ □ψ)) ⋏ □(List.map (fun φ ↦ ◇(◇φ ➝ □φ)) Γ).conj := K!_replace_right this $ by
      sorry;
    have := DiaK!_of_CKBoxDia this;
    sorry;
    -- have : Hilbert.K4Point1 ⊢! (◇(◇φ ➝ □φ) ⋏ ◇(◇ψ ➝ □ψ)) ⋏ (List.map (fun φ ↦ □◇(◇φ ➝ □φ)) Γ).conj := K!_replace_left this $ by simp;
    -- have := (C_of_E_mp! K!_assoc) ⨀ this;

    /-
    replace ih := ih (by simp);
    simp at ih;
    replace ih := nec! $ ih (by simp);

    have : Hilbert.K4Point1 ⊢! ◇(◇φ ➝ □φ) := DiaCDiaBox!;
    have : Hilbert.K4Point1 ⊢! ◇□(◇φ ➝ □φ) := axiomM! ⨀ nec! this;

    have : Hilbert.K4Point1 ⊢! ◇((◇φ ➝ □φ) ⋏ (◇ψ ➝ □ψ) ⋏ (List.map (fun φ ↦ ◇φ ➝ □φ) Γ).conj) := by
      apply DiaK!_of_CKBoxDia;
      apply K!_intro;
      . sorry;
      . sorry;
    exact this;
    -/

lemma DiaFconjCDiabox {Γ : Finset _} (hΓ : Γ ≠ ∅) : Hilbert.K4Point1 ⊢! ◇(Γ.image (λ φ => ◇φ ➝ □φ)).conj := by
  apply diaK''! ?_ (h₂ := DiaConjCDiabox (Γ := Γ.toList) ?_);
  . apply right_Fconj!_intro;
    intro ψ hψ;
    apply left_Conj!_intro;
    simpa using hψ;
  . simpa;

end Hilbert.K4Point1



open Formula.Kripke

namespace Kripke

section definability

variable {F : Kripke.Frame}

private lemma not_mckinseyCondition_of_not_validate_axiomM' (h : ¬F ⊧ (Axioms.M (.atom 0))) :
  ∃ x : F.World, ∀ y, x ≺ y → (∃ z w, (y ≺ z ∧ y ≺ w ∧ z ≠ w))
  := by
    obtain ⟨V, x, hx⟩ := ValidOnFrame.exists_valuation_world_of_not h;
    have := Satisfies.imp_def₂.not.mp hx;
    push_neg at this;
    obtain ⟨h₁, h₂⟩ := this;
    use x;
    intro y Rxy;
    obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp $ h₁ _ Rxy;
    obtain ⟨w, Ryw, hw⟩ := by
      have := Satisfies.dia_def.not.mp h₂;
      push_neg at this;
      have := Satisfies.box_def.not.mp $ this y Rxy;
      push_neg at this;
      exact this;
    have : z ≠ w := by
      intro h;
      subst h;
      contradiction;
    use z, w;

private lemma not_McKinseyCondition_of_notPseudoMcKinseyCondition
  (hMc : ∃ x : F.World, ∀ y, x ≺ y → (∃ z w, (y ≺ z ∧ y ≺ w ∧ z ≠ w)))
  : ¬McKinseyCondition F.Rel := by
  unfold McKinseyCondition;
  push_neg;
  obtain ⟨x, h⟩ := hMc;
  use x;
  intro y Rxy;
  obtain ⟨u, v, Ryu, Ryv, huv⟩ := h y Rxy;
  by_cases hyu : y = u;
  . subst hyu;
    use v;
  . use u;

lemma not_mckinseyCondition_of_not_validate_axiomM (h : ¬F ⊧ (Axioms.M (.atom 0))) : ¬McKinseyCondition F.Rel := by
  unfold McKinseyCondition;
  push_neg;
  obtain ⟨x, h⟩ := not_mckinseyCondition_of_not_validate_axiomM' h;
  use x;
  intro y Rxy;
  obtain ⟨u, v, Ryu, Ryv, huv⟩ := h y Rxy;
  by_cases hyu : y = u;
  . subst hyu;
    use v;
  . use u;

lemma mckinseyCondition_of_validate_axiomM : McKinseyCondition F → F ⊧ (Axioms.M (.atom 0)) := by
  contrapose!;
  exact not_mckinseyCondition_of_not_validate_axiomM;

/-
lemma validate_M_of_mckinseyan_trans (hTrans : Transitive F) : F ⊧ (Axioms.M (.atom 0)) → McKinseyCondition F := by
  contrapose;
  intro hMc;
  unfold McKinseyCondition at hMc;
  push_neg at hMc;
  obtain ⟨x, h⟩ := hMc;
  by_cases hDead : ∀ y, ¬x ≺ y;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ _ _ => True), x;
    suffices (∀ y, x ≺ y → ∃ x, y ≺ x) ∧ ∀ y, ¬x ≺ y by
      simpa [Satisfies];
    constructor;
    . intro y Rxy;
      have := hDead y Rxy;
      contradiction;
    . assumption;
  . push_neg at hDead;
    obtain ⟨y, Rxy⟩ := hDead;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ z _ =>
      x ≺ z ∧ ∀ u, x ≺ u → ∃ v, (v ≠ z ∧ u ≺ z ∧ u ≺ v)
    ), x;
    apply Satisfies.imp_def₂.not.mpr;
    push_neg;

    constructor;
    . apply Satisfies.box_def.mpr;
      intro w Rxw;
      apply Satisfies.dia_def.mpr;
      obtain ⟨z, Rwz, hwz⟩ := h w Rxw;
      use z;
      constructor;
      . assumption;
      . simp [Semantics.Realize, Satisfies];
        constructor;
        . exact hTrans Rxw Rwz;
        . intro u Rxu;
          use w;
          refine ⟨?_, ?_, ?_⟩;
          . tauto;
          . sorry
          . sorry;
    . apply Satisfies.dia_def.not.mpr
      push_neg;
      intro z Rxz;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      obtain ⟨w, Rzw, hzw⟩ := h z Rxz;
      use w;
      constructor;
      . assumption;
      . simp [Semantics.Realize, Satisfies];
        intro Rxw;
        use z;
        constructor;
        . assumption;
        . intro v hvw _;
          sorry;

abbrev TransitiveMcKinseyConditionFrameClass : FrameClass := { F | Transitive F ∧ McKinseyCondition F }

instance TransitiveMcKinseyConditionFrameClass.DefinedByFourAndM : TransitiveMcKinseyConditionFrameClass.DefinedBy {Axioms.Four (.atom 0), Axioms.M (.atom 0)} := ⟨by
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, ValidOnFrame.models_iff, forall_eq_or_imp, forall_eq];
  intro F;
  constructor;
  . rintro ⟨hT, hM⟩;
    refine ⟨?_, ?_⟩;
    . exact iff_transitive_validate_AxiomFour.mp hT;
    . exact mcKinseyan_of_validate_M_trans hM;
  . rintro ⟨hFour, hM⟩;
    have := iff_transitive_validate_AxiomFour.mpr hFour;
    constructor;
    . assumption;
    . exact validate_M_of_mckinseyan_trans this hM;
⟩

instance : Kripke.TransitiveMcKinseyConditionFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Transitive, McKinseyCondition];
-/

end definability

section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Modal.K 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open MaximalConsistentTableau

namespace Canonical

open Classical in
lemma satisfiesMcKinseyCondition {H : Hilbert ℕ} [Consistent H] [Hilbert.K4Point1 ⪯ H] : SatisfiesMcKinseyCondition _ (canonicalFrame H).Rel := ⟨by
  rintro x;
  have ⟨y, hy⟩ := lindenbaum (𝓢 := H) (t₀ := ⟨x.1.1.prebox ∪ Set.univ.image (λ φ => ◇φ ➝ □φ), ∅⟩) $ by
    intro Γ Δ hΓ hΔ;
    suffices H ⊬ Γ.conj ➝ ⊥ by
      simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΔ;
      subst hΔ;
      simpa;
    by_contra! hC;
    replace hC := FConj_DT.mp hC;

    let Γ' := insert (◇⊤ ➝ □⊤) Γ;
    replace hC : Γ'.toSet *⊢[H]! ⊥ := Context.weakening! (by simp [Γ']) hC;

    let Γ'₁ := { φ ∈ Γ' | φ ∈ x.1.1.prebox };
    let Γ'₂ := { φ ∈ Γ' | ∃ ψ, ◇ψ ➝ □ψ = φ };
    apply MaximalConsistentTableau.neither (t := x) (φ := ◇Γ'₂.conj);
    constructor;
    . apply iff_provable_mem₁.mp;
      apply WeakerThan.pbl (𝓢 := Hilbert.K4Point1);
      convert Hilbert.K4Point1.DiaFconjCDiabox (Γ := Γ'.preimage (λ φ => ◇φ ➝ □φ) (by simp [Set.InjOn])) ?_
      . simp [Γ'₂, Finset.image_preimage];
      . simp [
          Γ',
          (show insert (◇⊤ ➝ □⊤) Γ = {◇⊤ ➝ □⊤} ∪ Γ by ext; simp),
          (show Finset.preimage {◇⊤ ➝ □⊤} (fun φ ↦ ◇φ ➝ □φ) (by simp [Set.InjOn]) = {(⊤ : Formula ℕ)} by ext; simp),
        ];
    . replace hC : (Γ'₁ ∪ Γ'₂).toSet *⊢[H]! ⊥ := by
        convert hC;
        ext φ;
        simp only [Set.mem_preimage, Function.iterate_one, Finset.mem_union, Finset.mem_filter, Finset.mem_insert, Γ'₁, Γ', Γ'₂, hΓ];
        constructor;
        . tauto;
        . rintro (rfl | h);
          . tauto;
          . have := hΓ h;
            simp at this ⊢;
            tauto;
      replace hC : Γ'₁.toSet.box *⊢[H]! □(∼Γ'₂.conj) := Context.nec! $ N!_iff_CO!.mpr $ FConj_DT'.mpr hC;
      replace hC : Γ'₁.box.toSet *⊢[H]! □(∼Γ'₂.conj) := by convert hC; simp;
      replace hC : Γ'₁.box.toSet *⊢[H]! ∼◇(Γ'₂.conj) := by
        apply FConj_DT.mp;
        apply C!_trans $ FConj_DT.mpr hC;
        simp;
      apply iff_mem₁_neg.mp;
      apply iff_provable_include₁.mp hC x;
      intro _;
      simp only [Set.mem_preimage, Function.iterate_one, Finset.coe_image, Finset.coe_filter,
        Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp, Γ'₁];
      rintro χ hχ _ rfl;
      assumption;
  have Rxy : (canonicalFrame H).Rel x y := by
    dsimp [canonicalFrame];
    trans (x.1.1.prebox ∪ Set.univ.image (λ φ => ◇φ ➝ □φ));
    . apply Set.subset_union_left;
    . simpa using hy;
  by_cases hy : ∃ z, (canonicalFrame H).Rel y z;
  . obtain ⟨z, Ryz⟩ := hy;
    use z;
    constructor;
    . exact _root_.trans Rxy Ryz;
    . intro u Rzu;
      by_contra! ezu;
      obtain ⟨ξ, hξ₁, hξ₂⟩ := exists₁₂_of_ne ezu;
      have : □ξ ∈ y.1.1 := iff_mem₁_imp'.mp (by apply hy.1; simp) $ def_rel_dia_mem₁.mp Ryz hξ₁;
      have : ξ ∈ u.1.1 := def_rel_box_mem₁.mp (_root_.trans Ryz Rzu) this;
      exact iff_not_mem₂_mem₁.mpr this hξ₂;
  . use y;
    constructor;
    . assumption;
    . tauto;
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
