import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Logic.KTB
import Foundation.Modal.Kripke.Logic.S5
import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Logic.Grz.Completeness
import Foundation.Modal.Kripke.Logic.GrzPoint2
import Foundation.Modal.Logic.Global




namespace LO.Modal

namespace Kripke

variable {F : Frame}

def Frame.twice (F : Frame) : Frame where
  World := F.World × Fin 2
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

def Frame.twice.PMorphism (F : Frame) : F×2 →ₚ F where
  toFun := Prod.fst
  forth := by
    rintro ⟨x, _⟩ ⟨y, _⟩ h;
    simpa using h;
  back := by
    intro ⟨x, i⟩ y Rxy;
    use ⟨y, 0⟩;
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

end Kripke


namespace Formula

variable {α : Type*} {φ : Formula _}

def flag (φ : Formula α) : Bool → Formula α
  | true  => φ
  | false => ∼φ

@[simp]
lemma atom_flag_boxdotTranslated : (flag (.atom a) b)ᵇ = (flag (.atom a) b) := by
  match b with | true | false => rfl;

def freshAtom : Formula ℕ → ℕ
  | ⊥ => 0
  | .atom a => a + 1
  | φ ➝ ψ => max φ.freshAtom ψ.freshAtom
  | □φ => φ.freshAtom

lemma le_max_atoms_of_mem_atoms {a : ℕ} (ha : a ∈ φ.atoms) : a ≤ φ.atoms.max' (⟨a, ha⟩) := by
  induction φ with
  | hfalsum => simp [atoms] at ha;
  | hatom b => simp [atoms] at ha ⊢; omega;
  | hbox φ ihφ => apply ihφ; simpa using ha;
  | himp φ ψ ihφ ihψ =>
    rcases (show a ∈ φ.atoms ∨ a ∈ ψ.atoms by simpa [atoms] using ha) with (hφ | hψ);
    . by_cases hψ : ψ.atoms.Nonempty;
      . simp [atoms, Finset.max'_union ⟨_, hφ⟩ hψ, ihφ hφ];
      . simp [atoms, Finset.not_nonempty_iff_eq_empty.mp hψ, ihφ hφ];
    . by_cases hφ : φ.atoms.Nonempty;
      . simp [atoms, Finset.max'_union hφ ⟨_, hψ⟩, ihψ hψ];
      . simp [atoms, Finset.not_nonempty_iff_eq_empty.mp hφ, ihψ hψ];

lemma le_max_atoms_freshAtom (h : φ.atoms.Nonempty) : Finset.max' φ.atoms h < φ.freshAtom  := by
  induction φ with
  | hfalsum => simp [atoms] at h;
  | hatom a => simp [atoms, freshAtom];
  | hbox φ ihφ =>
    suffices ∀ a ∈ φ.atoms, a < φ.freshAtom by simpa [atoms, freshAtom];
    intro a ha;
    calc
      a ≤ φ.atoms.max' h := by apply le_max_atoms_of_mem_atoms ha;
      _ < φ.freshAtom    := by apply ihφ;
  | himp φ ψ ihφ ihψ =>
    simp [atoms, freshAtom] at h ⊢;
    rcases h with (⟨a, ha⟩ | ⟨a, ha⟩);
    . left;
      rintro b (hb | hb);
      . calc
          b ≤ φ.atoms.max' (⟨a, ha⟩) := by apply le_max_atoms_of_mem_atoms hb;
          _ < φ.freshAtom            := @ihφ ⟨b, hb⟩;
      . have := le_max_atoms_of_mem_atoms ha;
        have := le_max_atoms_of_mem_atoms hb;
        have := @ihφ ⟨a, ha⟩;
        sorry;
    . sorry;

lemma not_mem_freshAtom_atoms : φ.freshAtom ∉ φ.atoms := by
  induction φ with
  | hfalsum => simp [atoms];
  | hatom a => simp [atoms, freshAtom];
  | hbox φ ihφ => simp_all [atoms, freshAtom];
  | himp φ ψ ihφ ihψ =>
    simp [atoms, freshAtom];
    constructor;
    . have : max φ.freshAtom ψ.freshAtom = φ.freshAtom ∨ max φ.freshAtom ψ.freshAtom = ψ.freshAtom := by omega;
      rcases this with (h | h);
      . simpa [h];
      . rw [h];

        sorry;
    . sorry;
    -- rcases (show max φ.freshAtom ψ.freshAtom = φ.freshAtom ∨ max φ.freshAtom ψ.freshAtom = ψ.freshAtom by omega) with (h | h);
    -- . sorry;
    -- . sorry;

end Formula

namespace Logic

variable {α} {L₀ L : Logic α}

def boxdot_preimage (L : Logic α) := { φ ∈ L | L ⊢! φᵇ }
local postfix:100 "ᵇ" => boxdot_preimage

def BoxdotProperty (L₀ : Logic α) := ∀ {L : Logic _}, L.IsNormal → Lᵇ = L₀ → L ⊆ L₀

def StrongBoxdotProperty (L₀ : Logic α) := ∀ {L : Logic _}, L.IsNormal → Lᵇ ⊆ L₀ → L ⊆ L₀

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

private lemma jerabek_SBDP.lemma₁
  {p : ℕ} {φ : Formula ℕ} {b : Bool} : Hilbert.K ⊢! (flag (.atom p) b) ⋏ □φᵇ ➝ ⊡((flag (.atom p) !b) ➝ φᵇ) := by
  apply Complete.complete (𝓜 := Kripke.FrameClass.all);
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

private lemma jerabek_SBDP.lemma₂
  {L : Logic ℕ} [L.IsNormal]
  {p : ℕ} {φ : Formula ℕ} {b : Bool} : L ⊢! (flag (.atom p) b) ⋏ □φᵇ ➝ ⊡((flag (.atom p) !b) ➝ φᵇ) := by
  apply normal_provable_of_K_provable;
  simpa using lemma₁;
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
  let X₀ := φ.subformulas.prebox.image (λ ψ => □((.atom q) ➝ ψ) ➝ ψ);
  let X₁ := φ.subformulas.prebox.image (λ ψ => □(∼(.atom q) ➝ ψ) ➝ ψ);
  let X := X₀ ∪ X₁;
  let XB := X.image (·ᵇ);

  have Claim1 : ∀ ψ ∈ φ.subformulas.prebox, (L, XB.toSet) ⊢! □ψᵇ ➝ ψᵇ := by
    intro ψ hψ;
    have H₁ : ∀ b, (L, XB.toSet) ⊢! (flag (.atom q) b) ⋏ □ψᵇ ➝ ⊡((flag (.atom q) !b) ➝ ψᵇ) := by
      intro b;
      apply GlobalConsequence.thm!;
      apply jerabek_SBDP.lemma₂;
    have H₂ : ∀ b, (L, XB.toSet) ⊢! ⊡((flag (.atom q) b) ➝ ψᵇ) ➝ ψᵇ := by
      intro b;
      suffices (L, XB.toSet) ⊢! (□((flag (.atom q) b) ➝ ψ) ➝ ψ)ᵇ by
        simpa only [Formula.boxdotTranslate, Formula.atom_flag_boxdotTranslated] using this;
      apply GlobalConsequence.ctx!;
      match b with
      | true =>
        simp only [Finset.coe_image, flag, Set.mem_image, Finset.mem_coe, XB];
        use (□(atom q ➝ ψ) ➝ ψ);
        constructor;
        . simpa [X, X₀, X₁] using hψ;
        . rfl;
      | false =>
        simp only [Finset.coe_image, flag, Set.mem_image, Finset.mem_coe, XB];
        use (□(∼(atom q) ➝ ψ) ➝ ψ);
        constructor;
        . simpa [X, X₀, X₁] using hψ;
        . rfl;
    have H₃ : ∀ b, (L, XB.toSet) ⊢! (flag (.atom q) b) ➝ (□ψᵇ ➝ ψᵇ) := by
      intro b;
      cl_prover [(H₁ b), (H₂ !b)];
    have H₄ : (L, XB.toSet) ⊢!  atom q ➝ □ψᵇ ➝ ψᵇ := H₃ true;
    have H₅ : (L, XB.toSet) ⊢! ∼atom q ➝ □ψᵇ ➝ ψᵇ := H₃ false;
    cl_prover [H₄, H₅];
  have Claim2 : ∀ ψ ∈ φ.subformulas, (L, XB.toSet) ⊢! ψ ⭤ ψᵇ := by
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
      replace ihψ : (L, XB.toSet) ⊢! ψ ⭤ ψᵇ := ihψ (by grind);
      have H₁ : (L, XB.toSet) ⊢! □ψ ⭤ □ψᵇ := box_congruence! ihψ;
      have H₂ : (L, XB.toSet) ⊢! □ψᵇ ⭤ ⊡ψᵇ := by
        apply Entailment.E!_intro;
        . have : (L, XB.toSet) ⊢! □ψᵇ ➝ ψᵇ := Claim1 ψ (by simpa);
          cl_prover [this];
        . cl_prover;
      cl_prover [H₁, H₂];
  have : (L, XB.toSet) ⊢! φᵇ := by
    have h₁ : (L, XB.toSet) ⊢! φ ➝ φᵇ := C_of_E_mp! $ Claim2 φ (by grind);
    have h₂ : (L, XB.toSet) ⊢! φ := by
      apply GlobalConsequence.thm!;
      simpa using hφL;
    exact h₁ ⨀ h₂;
  have : L ⊢! XB.conj ➝ φᵇ := by sorry; -- TODO: it's not!
  let χ := X.conj ➝ φ
  have : L ⊢! χᵇ := by sorry;
  use χ;
  constructor;
  . constructor;
    . suffices L ⊢! χ by simpa;
      apply dhyp!;
      simpa using hφL;
    . assumption;
  . have : ¬C ⊧ φ := complete.exists_countermodel_of_not_provable (by simpa using hφL₀);
    obtain ⟨M, x, hMC, hF⟩ := Kripke.exists_model_world_of_not_validOnFrameClass this;

    let M₂ : Kripke.Model := {
      toFrame := M.toFrame.twice
      Val := λ ⟨w, i⟩ a =>
        if   a = q then i = 0
        else M.Val w a
    }
    have : M.IsReflexive := by
      apply reflexive_of_validate_AxiomT;
      apply sound.sound;
      . apply hKT.pbl;
        simp;
      . assumption;

    have H2 : ∀ ψ ∈ φ.subformulas, ∀ w : M.World, ∀ i : Fin 2, Satisfies M₂ (w, i) ψ ↔ Satisfies M w ψ := by sorry; -- BdRV 2.14
    have : ¬Satisfies M₂ (x, 0) φ := @H2 φ (by simp) x 0 |>.not.mpr hF;

    suffices L₀ ⊬ X.conj ➝ φ by simpa;

    apply sound.not_provable_of_countermodel;
    apply not_validOnFrameClass_of_exists_model_world;
    use M₂, (x, 0);
    constructor;
    . exact Kripke.FrameClass.JerabekAssumption.twice (C := C) _ hMC;
    . apply Satisfies.not_imp_def.mpr;
      constructor;
      . apply Satisfies.fconj_def.mpr;
        simp only [
          Finset.mem_union, Finset.mem_image, Finset.mem_preimage, Function.iterate_one,
          Fin.isValue, X, X₀, X₁
        ];
        rintro _ (⟨ξ, _, rfl⟩ | ⟨ξ, _, rfl⟩);
        . rintro hξ₁;
          contrapose! hξ₁;
          apply Satisfies.not_box_def.mpr;
          use (x, 0);
          constructor;
          . simp [M₂, Frame.twice];
          . apply Satisfies.not_imp_def.mpr;
            constructor;
            . simp [Semantics.Realize, Satisfies, M₂];
            . apply H2 ξ (by grind) x 0 |>.not.mpr;
              apply H2 ξ (by grind) x 0 |>.not.mp hξ₁;
        . rintro hξ₁;
          contrapose! hξ₁;
          apply Satisfies.not_box_def.mpr;
          use (x, 1);
          constructor;
          . simp [M₂, Frame.twice];
          . apply Satisfies.not_imp_def.mpr;
            constructor;
            . simp [Semantics.Realize, Satisfies, M₂];
            . apply H2 ξ (by grind) x 1 |>.not.mpr;
              apply H2 ξ (by grind) x 0 |>.not.mp hξ₁;
      . exact @H2 φ (by simp) x 0 |>.not.mpr hF;

/--
  Every Logic `L₀` which is `Modal.KT ⪯ L₀` and sound and complete to frame class `C` satisfies Jeřábek's assumption, has boxdot property.
-/
theorem jerabek_BDP
  (L₀ : Logic ℕ) [Modal.KT ⪯ L₀]
  (C : Kripke.FrameClass) [C.JerabekAssumption]
  [Sound L₀ C] [Complete L₀ C]
  : L₀.BoxdotProperty := Logic.BDP_of_SBDP $ jerabek_SBDP L₀ C

/-- `Modal.KT` has boxdot property. This is originally boxdot conjecture stated. -/
theorem KT.BDP : Modal.KT.BoxdotProperty := jerabek_BDP Modal.KT Kripke.FrameClass.KT
alias boxdot_conjecture := KT.BDP

/-- `Modal.KTB` has boxdot property. -/
theorem KTB.BDP : Modal.KTB.BoxdotProperty := jerabek_BDP Modal.KTB Kripke.FrameClass.KTB

/-- `Modal.S4` has boxdot property. -/
theorem S4.BDP : Modal.S4.BoxdotProperty := jerabek_BDP Modal.S4 Kripke.FrameClass.S4

end

end LO.Modal
