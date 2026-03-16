module

public import Foundation.Logic.Embedding
public import Foundation.Modal.Kripke.Logic.S4
public import Foundation.Modal.Logic.SumNormal
public import Foundation.Propositional.Hilbert.Minimal.Basic
public import Foundation.Propositional.Kripke.Hilbert.Int.Basic

@[expose] public section

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional

namespace Propositional

@[match_pattern]
def Formula.gödelTranslate : Propositional.Formula α → Modal.Formula α
  | .atom a  => □(.atom a)
  | ⊥ => ⊥
  | φ ⋏ ψ => (gödelTranslate φ) ⋏ (gödelTranslate ψ)
  | φ ⋎ ψ => (gödelTranslate φ) ⋎ (gödelTranslate ψ)
  | φ 🡒 ψ => □((gödelTranslate φ) 🡒 (gödelTranslate ψ))
postfix:90 "ᵍ" => Propositional.Formula.gödelTranslate

structure ModalCompanion (IL : Propositional.Logic α) (ML : Modal.Logic α) : Prop where
  companion : ∀ {φ}, φ ∈ IL ↔ ML ⊢ φᵍ

/-
lemma Modal.ModalCompanion.tofaithfullyEmbeddable
    (IL : Propositional.Logic ℕ) (ML : Modal.Logic ℕ) [Modal.ModalCompanion IL ML] : Entailment.FaithfullyEmbeddable IL ML where
  prop := ⟨(·ᵍ), fun _ ↦ Modal.ModalCompanion.companion.symm⟩
-/

namespace Logic

variable {IL : Propositional.Logic ℕ}

abbrev smallestMC (IL : Propositional.Logic ℕ) : Modal.Logic ℕ := Modal.S4.sumNormal ((·ᵍ) '' IL)

instance : Modal.Entailment.S4 IL.smallestMC where
  T φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.sumNormal.mem₁!;
    simp;
  Four φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.sumNormal.mem₁!;
    simp;

@[grind .]
lemma mem_smallestMC_of_mem : φ ∈ IL → IL.smallestMC ⊢ φᵍ := by
  intro h;
  apply Modal.Logic.sumNormal.mem₂!;
  apply Modal.Logic.iff_provable.mpr;
  apply Set.mem_image_of_mem;
  assumption;

lemma smallestMC.mdp_S4 (hφψ : Modal.S4 ⊢ φ 🡒 ψ) (hφ : IL.smallestMC ⊢ φ) : IL.smallestMC ⊢ ψ := by
  exact (Modal.Logic.sumNormal.mem₁! hφψ) ⨀ hφ;

abbrev largestMC (IL : Propositional.Logic ℕ) : Modal.Logic ℕ := Modal.Logic.sumNormal IL.smallestMC ({ Modal.Axioms.Grz φ | φ })

instance : Modal.Entailment.Grz IL.largestMC where
  Grz φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.sumNormal.mem₂!;
    apply Modal.Logic.iff_provable.mpr;
    tauto;

@[grind .]
lemma mem_largestMC_of_mem : φ ∈ IL → IL.largestMC ⊢ φᵍ := fun h => Modal.Logic.sumNormal.mem₁! $ mem_smallestMC_of_mem h

instance : IL.smallestMC ⪯ IL.smallestMC := inferInstance

end Logic

theorem modalCompanion_via_kripkeSemantics
  {L : Propositional.Logic ℕ} {ML : Modal.Logic ℕ}
  (P : ∀ {κ}, (Rel κ κ) → Prop)
  (hLML : ∀ {φ}, φ ∈ L → ML ⊢ φᵍ)
  (complete : ∀ {φ}, (∀ F : Propositional.Kripke.Frame, P F → F ⊧ φ) → φ ∈ L)
  (sound    : ∀ {φ}, φ ∈ ML → (∀ F : Modal.Kripke.Frame, IsPartialOrder _ F → P F → F ⊧ φ))
  : ModalCompanion L ML := by
  constructor;
  intro φ;
  constructor;
  . apply hLML;
  . intro h;
    apply complete;
    intro IF hF IV x;
    have H : ∀ ψ w, Propositional.Formula.Kripke.Satisfies ⟨IF, IV⟩ w ψ ↔ (Modal.Formula.Kripke.Satisfies ⟨⟨IF.World, IF.Rel⟩, IV.Val⟩ w (ψᵍ)) := by
      intro ψ w;
      induction ψ using Propositional.Formula.rec' generalizing w with
      | hatom a =>
        constructor;
        . intro _ _ h;
          exact IV.hereditary h $ by assumption;
        . intro h;
          exact h _ $ refl _;
      | hfalsum => tauto;
      | hor φ ψ ihp ihq =>
        constructor;
        . rintro (hp | hq);
          . apply Modal.Formula.Kripke.Satisfies.or_def.mpr; left;
            exact ihp w |>.mp hp;
          . apply Modal.Formula.Kripke.Satisfies.or_def.mpr; right;
            exact ihq w |>.mp hq;
        . intro h;
          rcases Modal.Formula.Kripke.Satisfies.or_def.mp h with (hp | hq)
          . left; exact ihp w |>.mpr hp;
          . right; exact ihq w |>.mpr hq;
      | _ => simp_all [Propositional.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
    apply H φ x |>.mpr $ sound (by grind) ⟨IF.World, IF.Rel⟩ inferInstance hF IV x;

end Propositional



namespace Modal

open Propositional.Formula (gödelTranslate)

variable {α} [DecidableEq α]
variable {S} [Entailment S (Modal.Formula α)]
variable {𝓢 : S} [Entailment.S4 𝓢]
variable {φ ψ χ : Propositional.Formula α}

@[simp, grind .]
lemma gödelTranslated_axiomTc : 𝓢 ⊢ φᵍ 🡒 □φᵍ := by
  induction φ using Propositional.Formula.rec' with
  | hfalsum => apply efq!;
  | hand φ ψ ihp ihq => exact C!_trans (CKK!_of_C!_of_C! ihp ihq) collect_box_and!
  | hor φ ψ ihp ihq => exact C!_trans (left_A!_intro (right_A!_intro_left ihp) (right_A!_intro_right ihq)) collect_box_or!
  | _ => simp only [gödelTranslate, axiomFour!];

lemma gödelTranslated_axiomImplyK : 𝓢 ⊢ (Axioms.ImplyK φ ψ)ᵍ := by
  exact nec! $ C!_trans gödelTranslated_axiomTc $ axiomK'! $ nec! $ implyK!;

lemma gödelTranslated_axiomImplyS : 𝓢 ⊢ (Axioms.ImplyS φ ψ χ)ᵍ := by
  apply nec! $ C!_trans (C!_trans (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ C!_trans (axiomK'! $ nec! implyS!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [φᵍ, φᵍ 🡒 □(ψᵍ 🡒 χᵍ)] ⊢[𝓢] φᵍ := by_axm!;
  have : [φᵍ, φᵍ 🡒 □(ψᵍ 🡒 χᵍ)] ⊢[𝓢] (φᵍ 🡒 □(ψᵍ 🡒 χᵍ)) := by_axm!;
  have : [φᵍ, φᵍ 🡒 □(ψᵍ 🡒 χᵍ)] ⊢[𝓢] □(ψᵍ 🡒 χᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;

lemma gödelTranslated_axiomAndIntro : 𝓢 ⊢ (Axioms.AndInst φ ψ)ᵍ := by
  exact nec! $ C!_trans gödelTranslated_axiomTc $ axiomK'! $ nec! $ and₃!

lemma gödelTranslated_axiomOrElim : 𝓢 ⊢ (Axioms.OrElim φ ψ χ)ᵍ := by
  exact nec! $ C!_trans axiomFour! $ axiomK'! $ nec! $ C!_trans (axiomK'! $ nec! $ or₃!) axiomK!;

lemma gödelTranslated_axiomOrInst₁ : 𝓢 ⊢ (Axioms.OrInst₁ φ ψ)ᵍ := nec! $ or₁!
lemma gödelTranslated_axiomOrInst₂ : 𝓢 ⊢ (Axioms.OrInst₂ φ ψ)ᵍ := nec! $ or₂!
lemma gödelTranslated_axiomAndElim₁ : 𝓢 ⊢ (Axioms.AndElim₁ φ ψ)ᵍ := nec! $ and₁!
lemma gödelTranslated_axiomAndElim₂ : 𝓢 ⊢ (Axioms.AndElim₂ φ ψ)ᵍ := nec! $ and₂!
lemma gödelTranslated_axiomVerum : 𝓢 ⊢ (Axioms.Verum)ᵍ := nec! $ verum!
lemma gödelTranslated_mdp (h₁ : 𝓢 ⊢ (φ 🡒 ψ)ᵍ) (h₂ : 𝓢 ⊢ φᵍ) : 𝓢 ⊢ ψᵍ := axiomT'! $ axiomK''! h₁ $ nec! $ h₂

attribute [simp, grind .]
  gödelTranslated_axiomOrElim
  gödelTranslated_axiomAndIntro
  gödelTranslated_axiomImplyS
  gödelTranslated_axiomImplyK
  gödelTranslated_axiomOrInst₁
  gödelTranslated_axiomOrInst₂
  gödelTranslated_axiomAndElim₁
  gödelTranslated_axiomAndElim₂
  gödelTranslated_axiomVerum

attribute [grind <=] gödelTranslated_mdp

@[simp, grind .]
lemma gödelTranslated_efq : 𝓢 ⊢ (Axioms.EFQ φ)ᵍ := nec! efq!

lemma gödelTranslated_persistency {M : Modal.Kripke.Model} [M.IsTransitive] {x y : M} {φ : Propositional.Formula ℕ} : x ⊧ φᵍ → x ≺ y → y ⊧ φᵍ := by
  induction φ using Propositional.Formula.rec' with
  | hatom a =>
    intro h Rxy z Ryz;
    apply h z $ M.trans Rxy Ryz;
  | hfalsum => tauto;
  | hand φ ψ ihφ ihψ =>
    simp only [gödelTranslate, Modal.Formula.Kripke.Satisfies.and_def];
    rintro ⟨hφ, hψ⟩ Rxy;
    constructor;
    . apply ihφ hφ Rxy;
    . apply ihψ hψ Rxy;
  | hor φ ψ ihφ ihψ =>
    simp only [gödelTranslate, Modal.Formula.Kripke.Satisfies.or_def];
    rintro (hφ | hψ) Rxy;
    . left; apply ihφ hφ Rxy;
    . right; apply ihψ hψ Rxy;
  | himp φ ψ ihφ ihψ =>
    intro h Rxy z Ryz hφ;
    apply h z (M.trans Rxy Ryz) hφ;

end Modal


namespace Propositional.Hilbert

variable {α} [DecidableEq α]
variable {S} [Entailment S (Modal.Formula α)]
variable {𝓜 : S} [Modal.Entailment.S4 𝓜]

lemma provable_gödelTranslated_of_provable {H : Hilbert α} (h : 𝓜 ⊢* ((·ᵍ) '' H.schema)) : H ⊢ φ → 𝓜 ⊢ φᵍ := by
  rintro ⟨h⟩;
  induction h with
  | @axm φ ih => apply h; use φ; tauto;
  | _ => grind;

lemma provable_gödelTranslated_of_mem_logic {H : Hilbert α} (h : 𝓜 ⊢* ((·ᵍ) '' H.schema)) : φ ∈ H.logic → 𝓜 ⊢ φᵍ := by
  rw [←Hilbert.iff_mem_logic_provable]
  apply provable_gödelTranslated_of_provable h;

end Propositional.Hilbert


/-
lemma dp_of_mdp [ModalDisjunctive mH] [ModalCompanion iH mH] [Entailment.S4 mH] : iH ⊢ φ ⋎ ψ → iH ⊢ φ ∨ iH ⊢ ψ := by
    intro hpq;
    have : mH ⊢ □φᵍ ⋎ □ψᵍ := of_C!_of_C!_of_A! (right_A!_intro_left axiomTc_GTranslate!) (right_A!_intro_right axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mH] [ModalCompanion iH mH] [Entailment.S4 mH] : Disjunctive iH := ⟨dp_of_mdp (iH := iH) (mH := mH)⟩
-/

end LO
end
