module

public import Foundation.Modal.Logic.GL.Independency
public import Foundation.Modal.Logic.S.Basic
public import Mathlib.Order.WellFoundedSet

@[expose] public section

namespace LO.Modal

open Formula (atom)
open Logic

protected abbrev D := sumQuasiNormal Modal.GL {∼□⊥, □(□(atom 0) ⋎ □(.atom 1)) 🡒 □(atom 0) ⋎ □(.atom 1)}
instance : Modal.D.IsQuasiNormal := inferInstance

instance : Entailment.HasAxiomP Modal.D where
  P := by
    constructor;
    apply Logic.sumQuasiNormal.mem₂;
    apply Logic.iff_provable.mpr;
    simp;

lemma D.mem_axiomDz : Modal.D ⊢ □(□φ ⋎ □ψ) 🡒 □φ ⋎ □ψ := by
  apply Logic.subst (φ := □(□(atom 0) ⋎ □(.atom 1)) 🡒 □(atom 0) ⋎ □(.atom 1)) (s := λ a => if a = 0 then φ else ψ);
  apply Logic.sumQuasiNormal.mem₂!;
  apply Logic.iff_provable.mpr;
  simp;

instance : Modal.GL ⪱ Modal.D := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use ∼□⊥;
    constructor;
    . simp;
    . simpa using GL.unprovable_notbox;

section

private inductive D' : Logic ℕ
  | mem_GL {φ} : Modal.GL ⊢ φ → Modal.D' φ
  | axiomP : Modal.D' (∼□⊥)
  | axiomD (φ ψ) : Modal.D' (□(□φ ⋎ □ψ) 🡒 □φ ⋎ □ψ)
  | mdp  {φ ψ} : Modal.D' (φ 🡒 ψ) → Modal.D' φ → Modal.D' ψ

private lemma D'.eq_D : Modal.D' = Modal.D := by
  ext φ;
  constructor;
  . intro h;
    apply iff_provable.mp;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁! h;
    | mdp _ _ ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | axiomD φ => apply Modal.D.mem_axiomDz;
    | axiomP => simp;
  . intro h;
    induction h with
    | mem₁ h => exact Modal.D'.mem_GL h;
    | mem₂ h =>
      rcases h with (rfl | rfl);
      . apply Modal.D'.axiomP;
      . apply Modal.D'.axiomD;
    | mdp _ _ ihφψ ihφ => exact Modal.D'.mdp ihφψ ihφ;
    | subst hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Modal.D'.mem_GL;
        apply Logic.subst;
        exact h;
      | axiomP => apply Modal.D'.axiomP;
      | axiomD _ _ => apply Modal.D'.axiomD;
      | mdp _ _ ihφψ ihφ => apply Modal.D'.mdp ihφψ ihφ;

-- TODO: Remove `eq_D_D'`?
protected def D.rec'
  {motive  : (φ : Formula ℕ) → (Modal.D ⊢ φ) → Prop}
  (mem_GL  : ∀ {φ}, (h : Modal.GL ⊢ φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomP  : motive (∼□⊥) (by simp))
  (axiomDz : ∀ {φ ψ}, motive (□(□φ ⋎ □ψ) 🡒 □φ ⋎ □ψ) (Modal.D.mem_axiomDz))
  (mdp : ∀ {φ ψ}, {hφψ : Modal.D ⊢ φ 🡒 ψ} → {hφ : Modal.D ⊢ φ} → (motive (φ 🡒 ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Modal.D ⊢ φ) → motive φ h := by
  intro φ h;
  replace h := iff_provable.mp $ Modal.D'.eq_D ▸ h;
  induction h with
  | mem_GL h => apply mem_GL; assumption;
  | axiomP => apply axiomP;
  | axiomD φ ψ => apply axiomDz;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . replace hφψ := iff_provable.mpr hφψ;
      rwa [D'.eq_D] at hφψ;
    . replace hφ := iff_provable.mpr hφ;
      rwa [D'.eq_D] at hφ;

end


section

open LO.Entailment LO.Modal.Entailment

@[simp]
lemma GL.box_disj_Tc {l : List (Formula ℕ)} : Modal.GL ⊢ (□'l).disj 🡒 □(□'l).disj := by
  apply left_Disj!_intro;
  intro ψ hψ;
  obtain ⟨ψ, hψ, rfl⟩ := List.LO.exists_of_mem_box hψ;
  apply C!_trans axiomFour!;
  apply axiomK'!;
  apply nec!;
  apply right_Disj!_intro;
  assumption;

lemma D.ldisj_axiomDz {l : List (Formula ℕ)} : Modal.D ⊢ □((□'l).disj) 🡒 (□'l).disj := by
  induction l with
  | nil => exact axiomP!;
  | cons φ l ih =>
    apply C!_replace ?_ ?_ (D.mem_axiomDz (φ := φ) (ψ := (□'l).disj));
    . apply sumQuasiNormal.mem₁!;
      apply axiomK'!;
      apply nec!;
      suffices Modal.GL ⊢ □φ ⋎ (□'l).disj 🡒 □φ ⋎ □(□'l).disj by simpa;
      have : Modal.GL ⊢ (□'l).disj 🡒 □(□'l).disj := GL.box_disj_Tc;
      cl_prover [this];
    . suffices Modal.D ⊢ □φ ⋎ □(□'l).disj 🡒 □φ ⋎ (□'l).disj by simpa;
      cl_prover [ih];

lemma D.fdisj_axiomDz {s : Finset (Formula ℕ)} : Modal.D ⊢ □((□'s).disj) 🡒 (□'s).disj := by
  apply C!_replace ?_ ?_ $ D.ldisj_axiomDz (l := s.toList);
  . apply sumQuasiNormal.mem₁!;
    apply axiomK'!;
    apply nec!;
    apply left_Fdisj!_intro;
    rintro ψ hψ;
    apply right_Disj!_intro;
    obtain ⟨ψ, hψ, rfl⟩ : ∃ a ∈ s, □a = ψ := Finset.LO.exists_of_mem_box hψ;
    grind;
  . apply left_Disj!_intro;
    intro ψ hψ;
    apply right_Fdisj!_intro;
    obtain ⟨ψ, hψ₂, rfl⟩ := List.LO.exists_of_mem_box hψ;
    grind;

lemma D.axiomFour : Modal.D ⊢ □□φ 🡒 □φ := by
  simpa [Finset.LO.preboxItr, Finset.LO.boxItr] using fdisj_axiomDz (s := {φ});

noncomputable abbrev Formula.dzSubformula (φ : Formula ℕ) := (□⁻¹'φ.subformulas).powerset.image (λ s => □((□'s).disj) 🡒 (□'s).disj)


namespace Kripke

instance {F : Frame} [F.IsFinite] [F.IsIrreflexive] [F.IsTransitive] : F.IsConverseWellFounded := ⟨by
  apply Finite.converseWellFounded_of_trans_irrefl';
  . infer_instance;
  . intro x y z; apply F.trans;
  . intro x; apply F.irrefl;
⟩

namespace Model

/--
  `ω`-extend root model.
  Valuation on `n ∈ ω` is same on `M.root` and on point `ω` is by `o`.
-/
abbrev tailModel₀ (M : Kripke.Model) [M.IsPointRooted] (o : ℕ → Prop) : Kripke.Model where
  World := Unit ⊕ ℕ ⊕ M.World -- `Unit` means `ω`
  Rel x y :=
    match x, y with
    | _            , .inl _        => False -- ¬(x ≺ ω)
    | .inl        _, _             => True  -- ω ≺ x where x is not ω
    | .inr $ .inl x, .inr $ .inl y => x > y -- x ≺ y ↔ x > y where x, y ∈ ω
    | .inr $ .inl _, .inr $ .inr _ => True
    | .inr $ .inr _, .inr $ .inl _ => False
    | .inr $ .inr x, .inr $ .inr y => x ≺ y
  Val p x :=
    match x with
    | .inl _        => o p
    | .inr $ .inl _ => M.Val p M.root.1
    | .inr $ .inr x => M.Val p x

namespace tailModel₀

variable {M : Kripke.Model} [M.IsPointRooted] {o}

instance instPontRooted : (M.tailModel₀ o).IsPointRooted where
  default := ⟨.inl (), by grind⟩
  uniq {r'} := by
    by_contra! hC;
    have := r'.2 (.inl ()) (by grind);
    simp [Frame.Rel'] at this;

instance instTransitive [M.IsTransitive] : (M.tailModel₀ o).IsTransitive := ⟨by grind⟩

@[coe] abbrev embed_nat (n : ℕ) : M.tailModel₀ o := .inr $ .inl n

@[coe] abbrev embed_original (x : M) : M.tailModel₀ o := .inr $ .inr x

instance instCWF [M.IsConverseWellFounded] : (M.tailModel₀ o).IsConverseWellFounded := ⟨by
  apply ConverseWellFounded.iff_has_max.mpr;
  intro s hs;
  let s₁ := { x | (Sum.inr $ Sum.inr x) ∈ s };
  let s₂ := { x | (Sum.inr $ Sum.inl x) ∈ s };
  by_cases hs₁ : s₁.Nonempty;
  . obtain ⟨m, hm₁, hm₂⟩ := ConverseWellFounded.iff_has_max.mp M.cwf s₁ (by simpa);
    use embed_original m;
    grind;
  . by_cases hs₂ : s₂.Nonempty;
    . let m := Set.IsWF.min (s := s₂) (Set.IsWF.of_wellFoundedLT _) (by assumption);
      use embed_nat m;
      constructor;
      . simpa using Set.IsWF.min_mem (s := s₂) _ _;
      . intro x hx;
        match x with
        | .inl _ => grind;
        | .inr $ .inr x =>
          exfalso;
          apply hs₁;
          use x;
          grind;
        | .inr $ .inl n =>
          suffices m ≤ n by grind;
          apply Set.IsWF.min_le;
          grind;
    . use (M.tailModel₀ o).root;
      simp [Set.Nonempty] at hs₁ hs₂;
      constructor;
      . contrapose! hs;
        ext x;
        match x with | .inl _ | .inr $ .inl n | .inr $ .inr x => tauto;
      . simp_all [tailModel₀, s₁, s₂];
⟩

protected def pMorphism_original : M →ₚ (M.tailModel₀ o) where
  toFun := embed_original
  forth := by grind;
  back := by grind;
  atomic := by grind;

lemma modal_equivalent_original {x : M} : ModalEquivalent (M₁ := M) (M₂ := M.tailModel₀ o) x (embed_original x) := by
  apply tailModel₀.pMorphism_original.modal_equivalence;

open Formula.Kripke

lemma satisfies_box_of_satisfies_box_at_root [M.IsTransitive] (h : Satisfies _ (M.tailModel₀ o).root.1 (□φ)) {x : M.tailModel₀ o} : Satisfies _ x (□φ) := by
  intro y Rxy;
  apply h;
  dsimp [Frame.root, default];
  grind;

protected def pMorphism_extendRoot (M : Model) [M.IsPointRooted] (n) : (M.extendRoot n) →ₚ (M.tailModel₀ o) where
  toFun := λ x =>
    match x with
    | .inl i => embed_nat i
    | .inr x => embed_original x
  forth := by
    rintro (x | x) (y | y) Rxy <;>
    simp_all only [Model.extendRoot, Frame.extendRoot, tailModel₀];
    case inl.inl => omega;
  back := by
    rintro (x | x) (y | y | y) Rxy;
    case inl.inr.inl => use Sum.inl ⟨y, by grind⟩; grind;
    all_goals simp_all [Frame.Rel', tailModel₀, Model.extendRoot, Frame.extendRoot];
  atomic := by rintro a (w | w) <;> grind;

lemma modal_equivalent_extendRoot_original {n : ℕ+} {x : M} : ModalEquivalent (M₁ := M.extendRoot n) (M₂ := M.tailModel₀ o) x (embed_original x) := by
  apply tailModel₀.pMorphism_extendRoot M n |>.modal_equivalence;

lemma modal_equivalent_extendRoot_nat {n : ℕ+} {i : Fin n} : ModalEquivalent (M₁ := M.extendRoot n) (M₂ := M.tailModel₀ o) (Sum.inl i) (embed_nat i) := by
  apply tailModel₀.pMorphism_extendRoot M n |>.modal_equivalence;

open Formula.Kripke in
lemma of_provable_rflSubformula_original_root [M.IsTransitive]
  {φ : Formula _}
  (hS : M.root.1 ⊧ ((□⁻¹'φ.subformulas).image (λ ψ => □ψ 🡒 ψ)).conj) :
  ∀ ψ ∈ φ.subformulas, ∀ i : ℕ, M.root.1 ⊧ ψ ↔ Satisfies (M.tailModel₀ o) (embed_nat i) ψ := by
  intro ψ hψ i;
  induction ψ generalizing i with
  | hatom p | hfalsum => simp [Satisfies];
  | himp ψ ξ ihψ ihξ =>
    simp [ihψ (by grind) i, ihξ (by grind) i, Satisfies];
  | hbox ψ ihψ =>
    replace ihψ := ihψ (by grind);
    calc
      _ ↔ (∀ x, M.root.1 ≺ x → x ⊧ ψ) ∧ (M.root.1 ⊧ ψ) := by
        suffices (∀ y, M.root.1 ≺ y → y ⊧ ψ) → M.root.1 ⊧ ψ by simpa [Satisfies];
        apply Satisfies.fconj_def.mp hS (□ψ 🡒 ψ) $ by
          simp only [Finset.LO.preboxItr, Function.iterate_one, Finset.mem_image, Finset.mem_preimage];
          use ψ;
      _ ↔ (∀ x : M, x ⊧ ψ) ∧ (∀ j < i, Satisfies (M.tailModel₀ o) (embed_nat j) ψ) := by grind;
      _ ↔ (∀ x, Satisfies (M.tailModel₀ o) (embed_original x) ψ) ∧ (∀ j < i, Satisfies (M.tailModel₀ o) (embed_nat j) ψ) := by
        apply and_congr_left';
        simp only [@modal_equivalent_original (M := M) (o := o) (φ := ψ)];
        constructor;
        . intro h x;
          apply h;
        . intro h x;
          apply h;
      _ ↔ _ := by
        constructor;
        . rintro ⟨h₁, h₂⟩ (_ | j | y) R <;> grind;
        . rintro h;
          constructor;
          . intro x;
            apply h;
            grind;
          . intro j hj;
            apply h;
            grind;

end tailModel₀


def tailModel (M : Kripke.Model) [M.IsPointRooted] : Kripke.Model := tailModel₀ M (M · M.root.1)


namespace tailModel

variable {M : Kripke.Model} [M.IsPointRooted]

instance instPointRooted : (tailModel M).IsPointRooted := tailModel₀.instPontRooted

end tailModel

end Model


end Kripke


section

open Classical
open Kripke
open Kripke.Model
open Formula.Kripke

theorem GL_D_TFAE :
  [
    Modal.D ⊢ φ,
    ∀ M : Kripke.Model, [M.IsFinite] → [M.IsTransitive] → [M.IsIrreflexive] → [M.IsRooted] → ∀ o, Satisfies _ (M.tailModel₀ o).root.1 φ,
    ∀ M : Kripke.Model, [M.IsFinite] → [M.IsTransitive] → [M.IsIrreflexive] → [M.IsRooted] → M.root.1 ⊧ φ.dzSubformula.conj 🡒 φ,
    Modal.GL ⊢ φ.dzSubformula.conj 🡒 φ,
  ].TFAE := by
    tfae_have 1 → 2 := by
      intro h M _ _ _ _ o;
      induction h using D.rec' with
      | mem_GL h =>
        apply Sound.sound (𝓜 := Kripke.FrameClass.GL) h;
        apply Set.mem_setOf_eq.mpr;
        exact {
          trans {x y z} := by apply (M.tailModel₀ o).trans,
          cwf := by apply (M.tailModel₀ o).cwf,
        }
      | axiomP =>
        apply Satisfies.not_def.mpr;
        apply Satisfies.not_box_def.mpr;
        use tailModel₀.embed_original M.root;
        constructor;
        . grind;
        . tauto;
      | @axiomDz φ ψ =>
        intro h;
        contrapose! h;
        replace h := Satisfies.or_def.not.mp h;
        push Not at h;
        obtain ⟨x, Rrx, hx⟩ := Satisfies.not_box_def.mp h.1;
        obtain ⟨y, Rry, hy⟩ := Satisfies.not_box_def.mp h.2;

        apply Satisfies.not_box_def.mpr;
        let z : M.tailModel₀ o := tailModel₀.embed_nat $
          match x, y with
          | .inr $ .inl x, .inr $ .inl y => (max x y) + 1
          | .inr $ .inr _, .inr $ .inl y => y + 1
          | .inr $ .inl x, .inr $ .inr _ => x + 1
          | .inr $ .inr x, .inr $ .inr y => 0
        have Rzx : z ≺ x := by
          unfold z;
          match x, y with
          | .inr $ .inl _, .inr $ .inl _ => dsimp [tailModel₀]; omega;
          | .inr $ .inr _, .inr $ .inl _
          | .inr $ .inl _, .inr $ .inr _
          | .inr $ .inr _, .inr $ .inr _ => grind;
        have Rzy : z ≺ y := by
          unfold z;
          match x, y with
          | .inr $ .inl _, .inr $ .inl _ => dsimp [tailModel₀]; omega;
          | .inr $ .inr _, .inr $ .inl _
          | .inr $ .inl _, .inr $ .inr _
          | .inr $ .inr _, .inr $ .inr _ => grind;
        use z;
        constructor;
        . grind;
        . apply Satisfies.or_def.not.mpr;
          push Not;
          constructor;
          . apply Satisfies.not_box_def.mpr;
            use x;
          . apply Satisfies.not_box_def.mpr;
            use y;
      | mdp ihφψ ihφ => exact ihφψ ihφ
    tfae_have 2 → 3 := by
      contrapose!;
      rintro ⟨M, _, _, _, _, h⟩;
      have h₁ : ∀ X ⊆ (□⁻¹'φ.subformulas), Satisfies M M.root (□(□'X).disj 🡒 (□'X).disj) := by simpa using Satisfies.not_imp_def.mp h |>.1;
      have h₂ := Satisfies.not_imp_def.mp h |>.2;

      let X := (□⁻¹'φ.subformulas).filter (λ ψ => ¬(M.root.1 ⊧ □ψ));
      obtain ⟨x, Rrx, hx⟩ : ∃ x, M.root.1 ≺ x ∧ ∀ ψ ∈ X, ¬x ⊧ □ψ := by
        have : M.root.1 ⊧ ∼((□'X).disj) := by
          apply Satisfies.not_def.mpr;
          apply Satisfies.fdisj_def.not.mpr;
          simp [X, Finset.LO.preboxItr, Finset.LO.boxItr];
        have : M.root.1 ⊧ ∼□((□'X).disj) := by
          have := h₁ X $ by simp [X];
          tauto;
        obtain ⟨x, Rrx, hx⟩ := Satisfies.not_box_def.mp this;
        use x;
        constructor;
        . assumption;
        . simpa [Finset.LO.preboxItr, Finset.LO.boxItr] using Satisfies.fdisj_def.not.mp hx;

      refine ⟨(M↾x), inferInstance, inferInstance, inferInstance, inferInstance, (M.Val · M.root), ?_⟩;
      exact (show ∀ ψ ∈ φ.subformulas, Satisfies _ _ ψ ↔ Satisfies M M.root ψ by
        intro ψ hψ;
        induction ψ with
        | hatom p | hfalsum => simp [Satisfies];
        | himp φ ψ ihφ ihψ => simp [Satisfies, ihφ (by grind), ihψ (by grind)];
        | hbox ψ ihψ =>
          replace ihψ := ihψ (by grind);
          constructor;
          . intro h;
            have : x ⊧ □ψ :=
              Model.pointGenerate.modal_equivalent _ _ |>.mp
              $ tailModel₀.modal_equivalent_original |>.mpr
              $ tailModel₀.satisfies_box_of_satisfies_box_at_root (x := tailModel₀.embed_original ⟨x, by grind⟩) h
            contrapose! this;
            apply hx;
            simp_all [X, Finset.LO.preboxItr, Finset.LO.boxItr];
          . intro h w Rrw;
            have H₁ : ∀ w : M↾x, Satisfies _ w ψ := by
              intro w;
              apply Model.pointGenerate.modal_equivalent x w |>.mpr;
              apply h;
              grind;
            match w with
            | .inl _ => contradiction;
            | .inr $ .inr w => exact tailModel₀.modal_equivalent_original.mp $ H₁ w;
            | .inr $ .inl n =>
              apply tailModel₀.of_provable_rflSubformula_original_root (M := M↾x) (φ := φ) ?_ ψ (by grind) n |>.mp;
              . apply H₁;
              . apply Model.pointGenerate.modal_equivalent_at_root x |>.mpr;
                apply Satisfies.conj_def.mpr;
                suffices ∀ (ψ : Formula ℕ), □ψ ∈ φ.subformulas → x ⊧ (□ψ 🡒 ψ) by simpa [Finset.LO.preboxItr, Finset.LO.boxItr];
                intro ψ _ hψ;
                have : ψ ∉ X := by
                  contrapose! hψ;
                  apply hx;
                  assumption;
                have : M.root.1 ⊧ (□ψ) := by
                  simp [X, Finset.LO.preboxItr] at this;
                  tauto;
                apply this;
                assumption;
      ) φ (show φ ∈ φ.subformulas by grind) |>.not.mpr $ h₂;
    tfae_have 4 ↔ 3 := GL.Kripke.finite_completeness_TFAE.out 0 3;
    tfae_have 4 → 1 := by
      intro h;
      apply (show Modal.D ⊢ φ.dzSubformula.conj 🡒 φ by exact sumQuasiNormal.mem₁! h) ⨀ ?_;
      apply FConj!_iff_forall_provable.mpr;
      intro ψ hψ;
      obtain ⟨s, _, rfl⟩ : ∃ s ⊆ (□⁻¹'φ.subformulas), □(□'s).disj 🡒 (□'s).disj = ψ := by simpa using hψ;
      exact D.fdisj_axiomDz;
    tfae_finish;

lemma iff_provable_D_provable_GL : Modal.D ⊢ φ ↔ Modal.GL ⊢ φ.dzSubformula.conj 🡒 φ := GL_D_TFAE (φ := φ) |>.out 0 3

lemma D.unprovable_T : Modal.D ⊬ (Axioms.T (.atom 0)) := by
  apply GL_D_TFAE |>.out 0 1 |>.not.mpr;
  push Not;
  let M : Kripke.Model := {
    World := Fin 1,
    Rel := (· < ·),
    Val := λ p i => True,
  }
  use M;
  refine ⟨inferInstance, inferInstance, inferInstance, ⟨0, by grind⟩, λ _ => False, ?_⟩;
  . apply Satisfies.not_imp_def.mpr
    constructor;
    . intro x Rrx;
      match x with
      | .inr $ .inl x => simp [Satisfies, M];
      | .inr $ .inr x => simp [Satisfies, M];
    . tauto;

instance : Modal.D ⪱ Modal.S := by
  constructor;
  . apply weakerThan_iff.mpr;
    intro φ hφ;
    induction hφ using D.rec' with
    | mem_GL h => exact WeakerThan.pbl h;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => exact axiomT!;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.T (.atom 0);
    constructor;
    . simp;
    . exact D.unprovable_T;

end

end

end LO.Modal
end
