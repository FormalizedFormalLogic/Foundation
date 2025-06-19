import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Entailment.K4
import Foundation.Modal.Kripke.Logic.K
import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.Completeness
import Mathlib.Order.Preorder.Finite


namespace LO.Modal

@[simp]
lemma eq_box_toSet_toSet_box {F : Type*} [Box F] [DecidableEq F] {s : Finset F} : s.toSet.box = s.box.toSet := by ext φ; simp;


namespace Hilbert.K

open LO.Entailment Entailment.FiniteContext
open Formula.Kripke

variable {φ ψ : Formula _}

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
  apply Kripke.complete.complete;
  intro F _ V x hx;
  have ⟨hx₁, hx₂⟩ := Satisfies.and_def.mp hx;
  have ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp hx₂;
  apply Satisfies.dia_def.mpr;
  use y;
  constructor;
  . assumption;
  . apply Satisfies.and_def.mpr;
    constructor;
    . apply hx₁ _ Rxy;
    . assumption

end Hilbert.K


namespace Hilbert.K4M

open LO.Entailment Entailment.FiniteContext LO.Modal.Entailment

variable {φ ψ : Formula _}

lemma CKDiaBoxDiaK! : Hilbert.K4M ⊢! (◇φ ⋏ □ψ) ➝ ◇(φ ⋏ ψ) := K_weakerThan_K4M.pbl Hilbert.K.CKDiaBoxDiaK!

lemma CKBoxDiaDiaK! : Hilbert.K4M ⊢! (□φ ⋏ ◇ψ) ➝ ◇(φ ⋏ ψ) := K_weakerThan_K4M.pbl Hilbert.K.CKBoxDiaDiaK!

lemma DiaK!_of_CKBoxDia (h : Hilbert.K4M ⊢! ◇φ ⋏ □ψ) : Hilbert.K4M ⊢! ◇(φ ⋏ ψ) := CKDiaBoxDiaK! ⨀ h
lemma DiaK!_of_CKDiaBox (h : Hilbert.K4M ⊢! □φ ⋏ ◇ψ) : Hilbert.K4M ⊢! ◇(φ ⋏ ψ) := CKBoxDiaDiaK! ⨀ h

lemma DiaCDiaBox! : Hilbert.K4M ⊢! ◇(◇φ ➝ □φ) :=
  (K_weakerThan_K4M.pbl $ C_of_E_mp! $ Hilbert.K.axiomM_DiaCDiaBox!) ⨀ (by simp)

lemma DiaConjCDiabox {Γ : List _} (hΓ : Γ ≠ []) : Hilbert.K4M ⊢! ◇(Γ.map (λ φ => ◇φ ➝ □φ)).conj := by
  induction Γ using List.induction_with_singleton with
  | hnil => tauto;
  | hsingle φ =>
    apply diaK''! ?_ $ DiaCDiaBox! (φ := φ);
    apply right_K!_intro <;> simp;
  | hcons φ Γ _ ih =>
    have : Hilbert.K4M ⊢! ◇□(◇φ ➝ □φ) ⋏ □◇(List.map (fun φ ↦ (◇φ ➝ □φ)) Γ).conj := by
      apply K!_intro;
      . exact axiomM! ⨀ (nec! DiaCDiaBox!);
      . exact nec! $ ih $ by assumption;
    have : Hilbert.K4M ⊢! ◇(□(◇φ ➝ □φ) ⋏ ◇(List.map (fun φ ↦ ◇φ ➝ □φ) Γ).conj) := DiaK!_of_CKBoxDia this;
    replace : Hilbert.K4M ⊢! ◇◇((◇φ ➝ □φ) ⋏ (List.map (fun φ ↦ ◇φ ➝ □φ) Γ).conj) := diaK''! CKBoxDiaDiaK! this;
    replace : Hilbert.K4M ⊢! ◇((◇φ ➝ □φ) ⋏ (List.map (fun φ ↦ ◇φ ➝ □φ) Γ).conj) := diaFour'! this;
    exact this;

lemma DiaFconjCDiabox {Γ : Finset _} (hΓ : Γ ≠ ∅) : Hilbert.K4M ⊢! ◇(Γ.image (λ φ => ◇φ ➝ □φ)).conj := by
  apply diaK''! ?_ (h₂ := DiaConjCDiabox (Γ := Γ.toList) ?_);
  . apply right_Fconj!_intro;
    intro ψ hψ;
    apply left_Conj!_intro;
    simpa using hψ;
  . simpa;

end Hilbert.K4M



open Formula.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.SatisfiesMcKinseyCondition (F : Frame) where
  mckinsey : ∀ x : F, ∃ y, x ≺ y ∧ ∀ z, y ≺ z → y = z

lemma Frame.mckinsey [F.SatisfiesMcKinseyCondition] : ∀ x : F, ∃ y, x ≺ y ∧ ∀ z, y ≺ z → y = z := SatisfiesMcKinseyCondition.mckinsey

instance : whitepoint.SatisfiesMcKinseyCondition := ⟨by
  intro x;
  use x;
  tauto;
⟩

section definability

open Formula (atom)
open Formula.Kripke

lemma validate_axiomM_of_satisfiesMcKinseyCondition [F.SatisfiesMcKinseyCondition] : F ⊧ (Axioms.M (.atom 0)) := by
  have := Frame.SatisfiesMcKinseyCondition.mckinsey (F := F);
  revert this;
  contrapose!;
  intro h;
  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  have ⟨h₁, h₂⟩ := Satisfies.not_imp_def.mp h;
  use x;
  intro y Rxy;
  obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp $ h₁ _ Rxy;
  obtain ⟨w, Ryw, h₂⟩ := Satisfies.not_box_def.mp $ (Satisfies.not_dia_def.mp h₂) y Rxy;
  by_cases eyz : y = z;
  . subst eyz;
    use w;
    constructor;
    . assumption;
    . by_contra hC; subst hC;
      contradiction;
  . tauto;

end definability

section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open LO.Entailment Entailment.FiniteContext LO.Modal.Entailment
open canonicalModel
open MaximalConsistentTableau

namespace Canonical

open Classical in
instance {H : Hilbert ℕ} [Consistent H] [Hilbert.K4M ⪯ H] : (canonicalFrame H).SatisfiesMcKinseyCondition := ⟨by
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
      apply WeakerThan.pbl (𝓢 := Hilbert.K4M);
      convert Hilbert.K4M.DiaFconjCDiabox (Γ := Γ'.preimage (λ φ => ◇φ ➝ □φ) (by simp [Set.InjOn])) ?_
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
    . exact (canonicalFrame H).trans Rxy Ryz;
    . intro u Rzu;
      by_contra! ezu;
      obtain ⟨ξ, hξ₁, hξ₂⟩ := exists₁₂_of_ne ezu;
      have : □ξ ∈ y.1.1 := iff_mem₁_imp'.mp (by apply hy.1; simp) $ def_rel_dia_mem₁.mp Ryz hξ₁;
      have : ξ ∈ u.1.1 := def_rel_box_mem₁.mp ((canonicalFrame H).trans Ryz Rzu) this;
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
