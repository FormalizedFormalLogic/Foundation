module

/-
  Jeřábek's proof of boxdot conjecture.

  References:
  - E. Jeřábek - "Cluster Expansion and the Boxdot Conjecture": https://arxiv.org/abs/1308.0994
-/
public import Foundation.Modal.Boxdot.Basic
public import Foundation.Modal.Kripke.Logic.S5
public import Foundation.Modal.Kripke.Logic.S4McK
public import Foundation.Modal.Logic.Global

@[expose] public section

namespace LO.Modal

namespace Kripke

variable {F : Frame}

def Frame.twice (F : Frame) : Frame where
  World := F.World × Bool
  Rel := λ (x, _) (y, _) => x ≺ y

local postfix:100 "×2" => Frame.twice

instance [F.IsReflexive] : F×2.IsReflexive where
  refl := by rintro ⟨x, i⟩; simp [Frame.twice];

instance [F.IsTransitive] : F×2.IsTransitive where
  trans := by
    rintro ⟨x, i⟩ ⟨y, j⟩ ⟨z, k⟩ Rxy Ryj;
    simp only [Frame.twice] at Rxy Ryj;
    exact F.trans Rxy Ryj;

instance [F.IsSymmetric] : F×2.IsSymmetric where
  symm := by
    rintro ⟨x, i⟩ ⟨y, j⟩ Rxy;
    simp only [Frame.twice] at Rxy;
    exact F.symm Rxy;

instance [F.IsPiecewiseStronglyConvergent] : F×2.IsPiecewiseStronglyConvergent := by
  constructor;
  rintro ⟨x, i⟩ ⟨y, j⟩ ⟨z, k⟩ Rxy Rxz;
  simp only [Frame.twice] at Rxy Rxz;
  obtain ⟨u, Ryu, Rzu⟩ := F.ps_convergent Rxy Rxz;
  use (u, i);
  constructor <;> simpa [Frame.twice];

instance [F.IsPiecewiseStronglyConnected] : F×2.IsPiecewiseStronglyConnected := by
  constructor;
  rintro ⟨x, i⟩ ⟨y, j⟩ ⟨z, k⟩ Rxy Rxz;
  simp only [Frame.twice] at Rxy Rxz;
  rcases F.ps_connected Rxy Rxz with (Ryz | Rzy);
  . left; simpa;
  . right; simpa;


def Frame.twice.PMorphism (F : Frame) : F×2 →ₚ F where
  toFun := Prod.fst
  forth := by
    rintro ⟨x, _⟩ ⟨y, _⟩ h;
    simpa using h;
  back := by
    intro ⟨x, i⟩ y Rxy;
    use ⟨y, true⟩;
    constructor;
    . simp;
    . tauto;

class FrameClass.JerabekAssumption (C : FrameClass) where
  twice : ∀ F ∈ C, F×2 ∈ C

instance : FrameClass.KT.JerabekAssumption := by
  constructor;
  intro F hF;
  simp_all only [Set.mem_setOf_eq];
  infer_instance;

instance : FrameClass.KTB.JerabekAssumption := by
  constructor;
  intro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

instance : FrameClass.S4.JerabekAssumption := by
  constructor;
  intro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

instance : FrameClass.S4Point2.JerabekAssumption := by
  constructor;
  intro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

instance : FrameClass.S4Point3.JerabekAssumption := by
  constructor;
  intro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

instance : FrameClass.S5.JerabekAssumption := by
  constructor;
  intro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

end Kripke


namespace Formula

variable {α : Type*} {φ : Formula _}

def flag (φ : Formula α) : Bool → Formula α
  | true  => φ
  | false => ∼φ

@[simp]
lemma atom_flag_boxdotTranslated : (flag (.atom a) b)ᵇ = (flag (.atom a) b) := by
  match b with | true | false => rfl;

end Formula


namespace Logic

variable {α} {L₀ L : Logic α}

def boxdot_preimage (L : Logic α) := { φ ∈ L | L ⊢ φᵇ }
local postfix:100 "ᵇ⁻¹" => boxdot_preimage

def BoxdotProperty (L₀ : Logic α) := ∀ {L : Logic _}, L.IsNormal → Lᵇ⁻¹ = L₀ → L ⊆ L₀

def StrongBoxdotProperty (L₀ : Logic α) := ∀ {L : Logic _}, L.IsNormal → Lᵇ⁻¹ ⊆ L₀ → L ⊆ L₀

lemma BDP_of_SBDP : StrongBoxdotProperty L₀ → BoxdotProperty L₀ := by
  intro hSBDP;
  intro L _ hL;
  apply hSBDP;
  . assumption;
  . rw [hL];

end Logic

section



open LO.Entailment LO.Modal.Entailment
open GlobalConsequence
open Formula (atom flag boxdotTranslate)
open Formula.Kripke
open Kripke


def Formula.Kripke.Satisfies.neither_flag {M : Model} {x : M} {φ : Formula ℕ} : ¬(x ⊧ φ.flag b ∧ x ⊧ φ.flag !b) := by
  match b with
  | true  => simp [Formula.flag];
  | false => simp [Formula.flag];

section

variable {L : Logic ℕ} [L.IsNormal] {n : ℕ} {Γ Δ : Finset (Formula ℕ)} {φ : Formula ℕ} {p} {b}

private lemma jerabek_SBDP.lemma₁ : Modal.K ⊢ (flag (.atom p) b) ⋏ □φᵇ 🡒 ⊡((flag (.atom p) !b) 🡒 φᵇ) := by
  apply Complete.complete (𝓜 := Kripke.FrameClass.K);
  intro F hF V x hx;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply Satisfies.and_def.mpr;
  constructor;
  . intro hx₁;
    by_contra hC;
    apply Satisfies.neither_flag;
    constructor;
    . exact Satisfies.and_def.mp hx |>.1;
    . assumption;
  . replace hx := Satisfies.and_def.mp hx |>.2;
    intro y Rxy h;
    apply hx;
    assumption;

private lemma jerabek_SBDP.lemma₂ : L ⊢ (flag (.atom p) b) ⋏ □φᵇ 🡒 ⊡((flag (.atom p) !b) 🡒 φᵇ) := by
  apply normal_provable_of_K_provable;
  exact lemma₁;

private lemma jerabek_SBDP.lemma₃ : L ⊢ (□^[n]Γ.conj)ᵇ 🡒 □^≤[n](Γ.image (·ᵇ)).conj := by
  apply normal_provable_of_K_provable;
  apply Complete.complete (𝓜 := Kripke.FrameClass.K);
  intro F hF V x h;
  apply Satisfies.fconj_def.mpr;
  simp only [Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
  intro k hk;
  apply Satisfies.boxItr_def.mpr;
  intro y Rxy;
  apply Satisfies.fconj_def.mpr;
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
  intro ξ hξ;
  replace h : Satisfies _ x (□^[k]Γ.conjᵇ) := Satisfies.fconj_def.mp (Satisfies.iff_boxdotTranslateMultibox_boxdotTranslateBoxlt.mp h) _ ?_;
  . apply Satisfies.fconj_def.mp (Satisfies.boxdotTranslate_fconj₂.mp $ Satisfies.boxItr_def.mp h Rxy) _;
    simp only [Finset.mem_image];
    use ξ;
  . simp only [Finset.mem_image, Finset.mem_range];
    use k;

end

/--
  Every Logic `L₀` which is `Modal.KT ⪯ L₀` and sound and complete to frame class `C` satisfies Jeřábek's assumption, has strong boxdot property.
-/
theorem jerabek_SBDP
  (L₀ : Logic ℕ) [hKT : Modal.KT ⪯ L₀]
  (C : Kripke.FrameClass) [C.JerabekAssumption]
  [sound : Sound L₀ C] [complete : Complete L₀ C]
  : L₀.StrongBoxdotProperty := by
  intro L _;
  contrapose!;
  intro hL;
  obtain ⟨φ, hφL, hφL₀⟩ := Set.not_subset.mp hL;
  apply Set.not_subset.mpr;

  let q := Formula.freshAtom φ;
  let X₀ := (□⁻¹'φ.subformulas).image (λ ψ => □((.atom q) 🡒 ψ) 🡒 ψ);
  let X₁ := (□⁻¹'φ.subformulas).image (λ ψ => □(∼(.atom q) 🡒 ψ) 🡒 ψ);
  let X := X₀ ∪ X₁;
  let XB := X.image (·ᵇ);

  have Claim1 : ∀ ψ ∈ (□⁻¹'φ.subformulas), (L, XB.toSet) ⊢ □ψᵇ 🡒 ψᵇ := by
    intro ψ hψ;
    have H₁ : ∀ b, (L, XB.toSet) ⊢ (flag (.atom q) b) ⋏ □ψᵇ 🡒 ⊡((flag (.atom q) !b) 🡒 ψᵇ) := by
      intro b;
      apply GlobalConsequence.thm!;
      apply jerabek_SBDP.lemma₂;
    have H₂ : ∀ b, (L, XB.toSet) ⊢ ⊡((flag (.atom q) b) 🡒 ψᵇ) 🡒 ψᵇ := by
      intro b;
      suffices (L, XB.toSet) ⊢ (□((flag (.atom q) b) 🡒 ψ) 🡒 ψ)ᵇ by
        simpa only [Formula.boxdotTranslate, Formula.atom_flag_boxdotTranslated] using this;
      apply GlobalConsequence.ctx!;
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, XB];
      use (□((flag (atom q) b) 🡒 ψ) 🡒 ψ);
      constructor;
      . match b with
        | true
        | false =>
          simp [X, X₀, X₁, flag, Finset.LO.preboxItr];
          grind;
      . rfl;
    have H₃ : ∀ b, (L, XB.toSet) ⊢ (flag (.atom q) b) 🡒 (□ψᵇ 🡒 ψᵇ) := by
      intro b;
      cl_prover [(H₁ b), (H₂ !b)];
    have H₄ : (L, XB.toSet) ⊢  atom q 🡒 □ψᵇ 🡒 ψᵇ := H₃ true;
    have H₅ : (L, XB.toSet) ⊢ ∼atom q 🡒 □ψᵇ 🡒 ψᵇ := H₃ false;
    cl_prover [H₄, H₅];
  have Claim2 : ∀ ψ ∈ φ.subformulas, (L, XB.toSet) ⊢ ψ 🡘 ψᵇ := by
    intro ψ hψ;
    induction ψ with
    | hfalsum => simp [Formula.boxdotTranslate];
    | hatom a => simp [Formula.boxdotTranslate];
    | himp ψ₁ ψ₂ ihψ₁ ihψ₂ =>
      replace ihψ₁ := ihψ₁ (by grind);
      replace ihψ₂ := ihψ₂ (by grind);
      dsimp [Formula.boxdotTranslate];
      cl_prover [ihψ₁, ihψ₂];
    | hbox ψ ihψ =>
      replace ihψ : (L, XB.toSet) ⊢ ψ 🡘 ψᵇ := ihψ (by grind);
      have H₁ : (L, XB.toSet) ⊢ □ψ 🡘 □ψᵇ := box_congruence! ihψ;
      have H₂ : (L, XB.toSet) ⊢ □ψᵇ 🡘 ⊡ψᵇ := by
        apply Entailment.E!_intro;
        . have : (L, XB.toSet) ⊢ □ψᵇ 🡒 ψᵇ := Claim1 ψ (by simpa [Finset.LO.preboxItr]);
          cl_prover [this];
        . cl_prover;
      cl_prover [H₁, H₂];
  have : (L, XB.toSet) ⊢ φᵇ := by
    have h₁ : (L, XB.toSet) ⊢ φ 🡒 φᵇ := C_of_E_mp! $ Claim2 φ (by grind);
    have h₂ : (L, XB.toSet) ⊢ φ := by
      apply GlobalConsequence.thm!;
      grind;
    exact h₁ ⨀ h₂;
  obtain ⟨Γ, n, hΓ, hφ⟩ := GlobalConsequence.iff_finite_boxLe_provable.mp this;
  replace hφ : L ⊢ (□^≤[n]XB.conj) 🡒 φᵇ := C!_trans (boxLe_fconj_regularity_of_subset hΓ) hφ;
  let χ := (□^[n](X.conj) 🡒 φ);
  have hχ : L ⊢ χᵇ := by apply C!_trans jerabek_SBDP.lemma₃ hφ;
  use χ;
  constructor;
  . constructor;
    . suffices L ⊢ χ by grind;
      apply dhyp!;
      grind;
    . assumption;
  . suffices L₀ ⊬ (□^[n]X.conj) 🡒 φ by grind;
    apply sound.not_provable_of_countermodel;
    apply not_validOnFrameClass_of_exists_model_world;

    have : ¬C ⊧ φ := complete.exists_countermodel_of_not_provable (by grind);
    obtain ⟨M, x, hMC, hF⟩ := Kripke.exists_model_world_of_not_validOnFrameClass this;
    let M₂ : Kripke.Model := {
      toFrame := M.toFrame.twice
      Val := λ a ⟨w, i⟩ =>
        if   a = q then i = true
        else M.Val a w
    }
    have : M.IsReflexive := by
      apply reflexive_of_validate_AxiomT;
      apply sound.sound;
      . apply hKT.pbl;
        simp;
      . assumption;

    -- Memo: BdRV Prop 2.14
    have H2 : ∀ ψ ∈ φ.subformulas, ∀ w : M.World, ∀ b : Bool, Satisfies M₂ (w, b) ψ ↔ Satisfies M w ψ := by
      intro ψ hψ w b;
      induction ψ generalizing w b with
      | hfalsum => simp [Satisfies];
      | hatom a =>
        have : a ≠ q := Formula.ne_freshAtom_of_mem_subformulas hψ |>.symm;
        simp [Satisfies, M₂, this];
      | himp ψ₁ ψ₂ ihψ₁ ihψ₂ =>
        replace ihψ₁ := ihψ₁ (by grind);
        replace ihψ₂ := ihψ₂ (by grind);
        simp [Satisfies, ihψ₁, ihψ₂]
      | hbox ψ ihψ =>
        replace ihψ := ihψ (by grind);
        constructor;
        . intro h v Rwv;
          apply ihψ v _ |>.mp;
          apply h (v, b);
          simpa [Frame.Rel', M₂, Frame.twice]
        . intro h v Rwv;
          apply ihψ v.1 v.2 |>.mpr;
          apply h;
          simpa [Frame.Rel', M₂, Frame.twice] using Rwv;

    use M₂, (x, true);
    constructor;
    . exact Kripke.FrameClass.JerabekAssumption.twice (C := C) _ hMC;
    . apply Satisfies.not_imp_def.mpr;
      constructor;
      . have : M₂ ⊧ X.conj := by
          intro x;
          apply Satisfies.fconj_def.mpr;
          rintro ψ hψ;
          rcases (by simpa [X, X₀, X₁] using hψ) with (⟨ψ, _, rfl⟩ | ⟨ψ, _, rfl⟩);
          . intro hψ₁;
            by_cases hψ : Satisfies M x.1 ψ;
            . exact H2 _ (by grind) _ _ |>.mpr hψ;
            . exfalso;
              apply hψ;
              apply H2 _ (by grind) _ true |>.mp;
              apply hψ₁ (x.1, true);
              . simp [Frame.Rel', M₂, Frame.twice];
              . simp [Satisfies, M₂];
          . intro hψ₁;
            by_cases hψ : Satisfies M x.1 ψ;
            . exact H2 _ (by grind) _ _ |>.mpr hψ;
            . exfalso;
              apply hψ;
              apply H2 _ (by grind) _ false |>.mp;
              apply hψ₁ (x.1, false);
              . simp [Frame.Rel', M₂, Frame.twice];
              . simp [Satisfies, M₂];
        apply ValidOnModel.multinec n this;
      . exact H2 φ (by grind) x _ |>.not.mpr hF;

/--
  Every Logic `L₀` which is `Modal.KT ⪯ L₀` and sound and complete to frame class `C` satisfies Jeřábek's assumption, has boxdot property.
-/
theorem jerabek_BDP
  (L₀ : Logic ℕ) [Modal.KT ⪯ L₀]
  (C : Kripke.FrameClass) [C.JerabekAssumption]
  [Sound L₀ C] [Complete L₀ C]
  : L₀.BoxdotProperty := Logic.BDP_of_SBDP $ jerabek_SBDP L₀ C

/-- `Modal.KT` has boxdot property. This is original boxdot conjecture. -/
theorem KT.BDP : Modal.KT.BoxdotProperty := jerabek_BDP Modal.KT Kripke.FrameClass.KT
alias boxdot_conjecture := KT.BDP

/-- `Modal.KTB` has boxdot property. -/
theorem KTB.BDP : Modal.KTB.BoxdotProperty := jerabek_BDP Modal.KTB Kripke.FrameClass.KTB

/-- `Modal.S4` has boxdot property. -/
theorem S4.BDP : Modal.S4.BoxdotProperty := jerabek_BDP Modal.S4 Kripke.FrameClass.S4

/-- `Modal.S4Point2` has boxdot property. -/
theorem S4Point2.BDP : Modal.S4Point2.BoxdotProperty := jerabek_BDP Modal.S4Point2 Kripke.FrameClass.S4Point2

/-- `Modal.S4Point3` has boxdot property. -/
theorem S4Point3.BDP : Modal.S4Point3.BoxdotProperty := jerabek_BDP Modal.S4Point3 Kripke.FrameClass.S4Point3

/-- `Modal.S5` has boxdot property. -/
theorem S5.BDP : Modal.S5.BoxdotProperty := jerabek_BDP Modal.S5 Kripke.FrameClass.S5

end

end LO.Modal
end
