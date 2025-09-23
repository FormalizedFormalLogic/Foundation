import Foundation.Modal.Logic.SumNormal
import Foundation.Modal.Logic.Basic
import Foundation.Modal.Logic.GL.Independency
import Foundation.Modal.Kripke.Logic.GL.Soundness
import Foundation.Modal.Logic.S.Basic
import Foundation.Modal.Entailment.GL
import Mathlib.Tactic.TFAE
import Mathlib.Order.WellFoundedSet
import Foundation.Modal.Maximal.Unprovability

namespace LO.Modal

open Formula (atom)
open Logic

protected abbrev D := sumQuasiNormal Modal.GL {∼□⊥, □(□(atom 0) ⋎ □(.atom 1)) ➝ □(atom 0) ⋎ □(.atom 1)}
instance : Modal.D.IsQuasiNormal := inferInstance

instance : Entailment.HasAxiomP Modal.D where
  P := by
    constructor;
    apply Logic.sumQuasiNormal.mem₂;
    apply Logic.iff_provable.mpr;
    simp;

lemma D.mem_axiomDz : Modal.D ⊢! □(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ := by
  apply Logic.subst! (φ := □(□(atom 0) ⋎ □(.atom 1)) ➝ □(atom 0) ⋎ □(.atom 1)) (s := λ a => if a = 0 then φ else ψ);
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
  | mem_GL {φ} : Modal.GL ⊢! φ → Modal.D' φ
  | axiomP : Modal.D' (∼□⊥)
  | axiomD (φ ψ) : Modal.D' (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ)
  | mdp  {φ ψ} : Modal.D' (φ ➝ ψ) → Modal.D' φ → Modal.D' ψ

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
        apply subst!;
        exact h;
      | axiomP => apply Modal.D'.axiomP;
      | axiomD _ _ => apply Modal.D'.axiomD;
      | mdp _ _ ihφψ ihφ => apply Modal.D'.mdp ihφψ ihφ;

-- TODO: Remove `eq_D_D'`?
protected def D.rec'
  {motive  : (φ : Formula ℕ) → (Modal.D ⊢! φ) → Prop}
  (mem_GL  : ∀ {φ}, (h : Modal.GL ⊢! φ) → motive φ (sumQuasiNormal.mem₁! h))
  (axiomP  : motive (∼□⊥) (by simp))
  (axiomDz : ∀ {φ ψ}, motive (□(□φ ⋎ □ψ) ➝ □φ ⋎ □ψ) (Modal.D.mem_axiomDz))
  (mdp : ∀ {φ ψ}, {hφψ : Modal.D ⊢! φ ➝ ψ} → {hφ : Modal.D ⊢! φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (hφψ ⨀ hφ))
  : ∀ {φ}, (h : Modal.D ⊢! φ) → motive φ h := by
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
lemma GL.box_disj_Tc {l : List (Formula ℕ)} : Modal.GL ⊢! l.box.disj ➝ □l.box.disj := by
  apply left_Disj!_intro;
  intro ψ hψ;
  obtain ⟨ψ, hψ, rfl⟩ := List.exists_box_of_mem_box hψ;
  apply C!_trans axiomFour!;
  apply axiomK'!;
  apply nec!;
  apply right_Disj!_intro;
  assumption;

lemma D.ldisj_axiomDz {l : List (Formula ℕ)} : Modal.D ⊢! □(l.box.disj) ➝ l.box.disj := by
  induction l with
  | nil => exact axiomP!;
  | cons φ l ih =>
    apply C!_replace ?_ ?_ (D.mem_axiomDz (φ := φ) (ψ := l.box.disj));
    . apply sumQuasiNormal.mem₁!;
      apply axiomK'!;
      apply nec!;
      suffices Modal.GL ⊢! □φ ⋎ l.box.disj ➝ □φ ⋎ □l.box.disj by simpa;
      have : Modal.GL ⊢! l.box.disj ➝ □l.box.disj := GL.box_disj_Tc;
      cl_prover [this];
    . suffices Modal.D ⊢! □φ ⋎ □l.box.disj ➝ □φ ⋎ l.box.disj by simpa;
      cl_prover [ih];

lemma D.fdisj_axiomDz {s : Finset (Formula ℕ)} : Modal.D ⊢! □(s.box.disj) ➝ s.box.disj := by
  apply C!_replace ?_ ?_ $ D.ldisj_axiomDz (l := s.toList);
  . apply sumQuasiNormal.mem₁!;
    apply axiomK'!;
    apply nec!;
    apply left_Fdisj!_intro;
    rintro ψ hψ;
    apply right_Disj!_intro;
    obtain ⟨ψ, hψ, rfl⟩ : ∃ a ∈ s, □a = ψ := by simpa using hψ;
    apply List.box_mem_of;
    simpa;
  . apply left_Disj!_intro;
    intro ψ hψ;
    apply right_Fdisj!_intro;
    obtain ⟨ψ, hψ₂, rfl⟩ := List.exists_box_of_mem_box hψ;
    simpa using hψ₂;

lemma D.axiomFour : Modal.D ⊢! □□φ ➝ □φ := by
  simpa using Logic.subst! (λ _ => φ) $ fdisj_axiomDz (s := {(.atom 0)});

noncomputable abbrev Formula.dzSubformula (φ : Formula ℕ) := φ.subformulas.prebox.powerset.image (λ s => □(s.box.disj) ➝ s.box.disj)


namespace Kripke

instance {F : Frame} {r : F} [F.IsFiniteTree r] : F.IsConverseWellFounded := ⟨by
  apply Finite.converseWellFounded_of_trans_irrefl';
  . infer_instance;
  . intro x y z; apply F.trans;
  . intro x; apply F.irrefl;
⟩

variable {M : Kripke.Model} {r} [M.IsRootedBy r]

def tailModel₀ (M : Kripke.Model) {r} [M.IsRootedBy r] (o : ℕ → Prop) : Kripke.Model where
  World := Unit ⊕ ℕ ⊕ M.World -- `Unit` means `ω`
  Rel x y :=
    match x, y with
    | _            , .inl _        => False -- ¬(x ≺ ω)
    | .inl        _, _             => True  -- ω ≺ x where x is not ω
    | .inr $ .inl x, .inr $ .inl y => x > y -- x ≺ y ↔ x > y where x, y ∈ ω
    | .inr $ .inl _, .inr $ .inr _ => True
    | .inr $ .inr _, .inr $ .inl _ => False
    | .inr $ .inr x, .inr $ .inr y => x ≺ y
  Val x p :=
    match x with
    | .inl _        => o p
    | .inr $ .inl _ => M.Val r p
    | .inr $ .inr x => M.Val x p

namespace tailModel₀

variable {o}

protected abbrev root {M : Kripke.Model} {r} [M.IsRootedBy r] {o} : tailModel₀ M o := .inl ()

instance : (tailModel₀ M o).IsRootedBy (tailModel₀.root) where
  root_generates := by
    intro x h;
    match x with
    | .inl _ => simp [tailModel₀.root] at h;
    | .inr $ _ =>
      apply Relation.TransGen.single;
      simp [tailModel₀, tailModel₀.root];

instance transitive [M.IsTransitive] : (tailModel₀ M o).IsTransitive where
  trans x y z := by
    match x, y, z with
    | .inl _, _, _ => dsimp [tailModel₀]; aesop;
    | _, .inl _, _ => simp [tailModel₀];
    | _, _, .inl _ => simp [tailModel₀];
    | .inr $ .inl x, .inr $ .inl y, .inr $ .inl z => dsimp [tailModel₀]; omega;
    | .inr $ .inr x, .inr $ .inr y, .inr $ .inr z => dsimp [tailModel₀]; apply Frame.trans;
    | .inr $ .inr _, .inr _, .inr $ .inl _ => dsimp [tailModel₀]; aesop;
    | .inr $ .inl _, .inr $ .inr _, _ => dsimp [tailModel₀]; aesop;
    | .inr $ .inl _, .inr $ .inl _, .inr $ .inr _ => simp [tailModel₀];
    | .inr $ .inr _, .inr $ .inl _, .inr $ .inr _ => simp [tailModel₀];

@[coe] abbrev embed_nat (n : ℕ) : tailModel₀ M o := .inr $ .inl n

@[simp]
lemma rel_root_embed_nat [M.IsTransitive] {n : ℕ} : tailModel₀.root (M := M) (o := o) ≺ (tailModel₀.embed_nat n) := by
  apply Frame.root_genaretes'!;
  simp [tailModel₀];

@[coe] abbrev embed_original (x : M) : tailModel₀ M o := .inr $ .inr x

@[simp]
lemma rel_root_embed_original [M.IsTransitive] {x : M} : tailModel₀.root (M := M) (o := o) ≺ (tailModel₀.embed_original x) := by
  apply Frame.root_genaretes'!;
  simp [tailModel₀];

instance cwf [M.IsFiniteTree r] : (tailModel₀ M o).IsConverseWellFounded := ⟨by
  apply ConverseWellFounded.iff_has_max.mpr;
  intro s hs;
  let s₁ := { x | (Sum.inr $ Sum.inr x) ∈ s };
  let s₂ := { x | (Sum.inr $ Sum.inl x) ∈ s };
  by_cases hs₁ : s₁.Nonempty;
  . obtain ⟨m, hm₁, hm₂⟩ := ConverseWellFounded.iff_has_max.mp M.cwf s₁ (by simpa);
    use embed_original m;
    constructor;
    . exact hm₁;
    . intro x hx;
      match x with
      | .inl _ => simp [tailModel₀];
      | .inr $ .inl _ => simp [tailModel₀];
      | .inr $ .inr y => simpa using hm₂ y (by tauto);
  . by_cases hs₂ : s₂.Nonempty;
    . let m := Set.IsWF.min (s := s₂) (Set.IsWF.of_wellFoundedLT _) (by assumption);
      use embed_nat m;
      constructor;
      . simpa using Set.IsWF.min_mem (s := s₂) _ _;
      . intro x hx;
        match x with
        | .inl _ => simp [tailModel₀];
        | .inr $ .inr x =>
          exfalso;
          apply hs₁;
          use x;
          simpa [s₁];
        | .inr $ .inl n =>
          suffices m ≤ n by simpa [tailModel₀];
          apply Set.IsWF.min_le;
          simpa [s₂];
    . use tailModel₀.root;
      simp [Set.Nonempty] at hs₁ hs₂;
      constructor;
      . contrapose! hs;
        ext x;
        match x with | .inl _ | .inr $ .inl n | .inr $ .inr x => tauto;
      . simp_all [tailModel₀, s₁, s₂];
⟩

lemma iff_root_rel_not_root {x : tailModel₀ M o} : tailModel₀.root ≺ x ↔ x ≠ tailModel₀.root := by
  constructor;
  . rintro h rfl;
    simp [Frame.Rel', tailModel₀] at h;
  . intro h;
    simp_all [Frame.Rel', tailModel₀];

protected def pMorphism_original : M →ₚ (tailModel₀ M o) where
  toFun := embed_original
  forth := by simp [tailModel₀];
  back := by simp [tailModel₀];
  atomic := by simp [tailModel₀]

lemma modal_equivalent_original {x : M} : ModalEquivalent (M₁ := M) (M₂ := tailModel₀ M o) x (embed_original x) := by
  apply tailModel₀.pMorphism_original.modal_equivalence;

lemma satisfies_box_of_satisfies_box_at_root [M.IsTransitive] (h : (tailModel₀.root (M := M) (o := o)) ⊧ □φ) {x : tailModel₀ M o} : x ⊧ □φ := by
  intro y Rxy;
  apply h;
  by_cases e : x = tailModel₀.root;
  . subst e;
    assumption;
  . apply Frame.trans ?_ Rxy;
    apply Frame.root_genaretes'!;
    assumption;

protected def pMorphism_extendRoot : M.extendRoot n →ₚ (tailModel₀ M o) where
  toFun := λ x =>
    match x with
    | .inl i => embed_nat (n - i - 1) -- TODO: fix
    | .inr x => embed_original x
  forth := by
    rintro (x | x) (y | y) Rxy <;>
    simp_all only [Model.extendRoot, Frame.extendRoot, tailModel₀];
    case inl.inl => omega;
  back := by
    rintro (x | x) (y | y | y) Rxy;
    case inl.inr.inl =>
      simp_all [Frame.Rel', tailModel₀, Model.extendRoot, Frame.extendRoot];
      use ⟨n - y - 1, by omega⟩;
      constructor;
      . simp;
        omega;
      . apply Fin.lt_def.mpr;
        simp;
        omega;
    all_goals simp_all [Frame.Rel', tailModel₀, Model.extendRoot, Frame.extendRoot];
  atomic := by
    rintro a (w | w) <;> simp [Model.extendRoot, tailModel₀];

lemma modal_equivalent_extendRoot_original {x : M} : ModalEquivalent (M₁ := M.extendRoot n) (M₂ := tailModel₀ M o) x (embed_original x) := by
  apply tailModel₀.pMorphism_extendRoot.modal_equivalence;

lemma modal_equivalent_extendRoot_nat {n : ℕ+} {i : Fin n} : ModalEquivalent (M₁ := M.extendRoot n) (M₂ := tailModel₀ M o) (Sum.inl i) (embed_nat (n - i - 1)) := by
  apply tailModel₀.pMorphism_extendRoot.modal_equivalence;

open Formula.Kripke in
lemma of_provable_rflSubformula_original_root [M.IsTransitive]
  {φ : Formula _}
  (hS : r ⊧ (φ.subformulas.prebox.image (λ ψ => □ψ ➝ ψ)).conj) :
  ∀ ψ ∈ φ.subformulas, ∀ i : ℕ, r ⊧ ψ ↔ (tailModel₀.embed_nat i : tailModel₀ M o) ⊧ ψ := by
  intro ψ hψ i;
  induction ψ generalizing i with
  | hatom p => simp [Semantics.Realize, tailModel₀, Satisfies];
  | hfalsum => simp;
  | himp ψ ξ ihψ ihξ => simp [ihψ (by grind) i, ihξ (by grind) i];
  | hbox ψ ihψ =>
    replace ihψ := ihψ (by grind);
    calc
      _ ↔ (∀ x, r ≺ x → x ⊧ ψ) ∧ r ⊧ ψ := by
        suffices (∀ y, r ≺ y → y ⊧ ψ) → r ⊧ ψ by simpa [Satisfies];
        apply Satisfies.fconj_def.mp hS (□ψ ➝ ψ) (by simpa);
      _ ↔ (∀ x : M, x ⊧ ψ) ∧ r ⊧ ψ := by
        suffices (∀ x, r ≺ x → x ⊧ ψ) ∧ r ⊧ ψ → (∀ x : M, x ⊧ ψ) by tauto;
        rintro ⟨h₁, h₂⟩ y;
        by_cases e : y = r;
        . subst e; assumption;
        . apply h₁;
          apply Frame.root_genaretes'!;
          assumption;
      _ ↔ (∀ x : M, x ⊧ ψ) ∧ ∀ j < i, (tailModel₀.embed_nat j : tailModel₀ M o) ⊧ ψ := by
        constructor;
        . rintro ⟨h₁, h₂⟩;
          constructor;
          . apply h₁;
          . intro j _;
            apply ihψ _ |>.mp h₂;
        . rintro h;
          constructor;
          . intro x; apply h.1;
          . exact h.1 r;
      _ ↔ (∀ x, (embed_original x : tailModel₀ M o) ⊧ ψ) ∧ ∀ j < i, (tailModel₀.embed_nat j : tailModel₀ M o) ⊧ ψ := by
        simp [modal_equivalent_original (M := M) (o := o) (φ := ψ)];
      _ ↔ _ := by
        constructor;
        . rintro ⟨h₁, h₂⟩ (_ | j | y) R;
          . contradiction;
          . apply h₂;
            exact R;
          . apply h₁;
        . rintro h;
          constructor;
          . intro x;
            apply h;
            tauto;
          . intro j hj;
            apply h;
            simpa [Frame.Rel', tailModel₀];

end tailModel₀


def tailModel (M : Kripke.Model) {r} [M.IsRootedBy r] : Kripke.Model := tailModel₀ M (M.Val r)

namespace tailModel

protected abbrev root {M : Kripke.Model} {r} [M.IsRootedBy r] : tailModel M := tailModel₀.root

instance : (tailModel M).IsRootedBy (tailModel.root) := by
  dsimp [tailModel];
  infer_instance;

end tailModel


end Kripke


section

open Classical
open Kripke
open Formula.Kripke

theorem GL_D_TFAE :
  [
    Modal.D ⊢! φ,
    ∀ M : Kripke.Model, ∀ r, [M.IsFiniteTree r] → ∀ o, (tailModel₀.root (M := M) (o := o)) ⊧ φ,
    ∀ M : Kripke.Model, ∀ r, [M.IsFiniteTree r] → r ⊧ φ.dzSubformula.conj ➝ φ,
    Modal.GL ⊢! φ.dzSubformula.conj ➝ φ,
  ].TFAE := by
    tfae_have 1 → 2 := by
      intro h M r _ o;
      induction h using D.rec' with
      | mem_GL h =>
        apply Sound.sound (𝓜 := Kripke.FrameClass.infinite_GL) h;
        apply Set.mem_setOf_eq.mpr;
        exact {
          trans := by intro x y z; exact Frame.trans (F := tailModel₀ M o |>.toFrame),
          cwf := by exact Frame.cwf (F := tailModel₀ M o |>.toFrame);
        }
      | axiomP =>
        apply Satisfies.not_def.mpr;
        apply Satisfies.not_box_def.mpr;
        use tailModel₀.embed_original r;
        constructor;
        . exact tailModel₀.rel_root_embed_original;
        . tauto;
      | @axiomDz φ ψ =>
        contrapose!;
        intro h;
        replace h := Satisfies.or_def.not.mp h;
        push_neg at h;
        obtain ⟨x, Rrx, hx⟩ := Satisfies.not_box_def.mp h.1;
        obtain ⟨y, Rry, hy⟩ := Satisfies.not_box_def.mp h.2;

        apply Satisfies.not_box_def.mpr;
        let z : tailModel₀ M o := tailModel₀.embed_nat $
          match x, y with
          | .inr $ .inl x, .inr $ .inl y => (max x y) + 1
          | .inr $ .inr _, .inr $ .inl y => y + 1
          | .inr $ .inl x, .inr $ .inr _ => x + 1
          | .inr $ .inr x, .inr $ .inr y => 0
        have Rzx : z ≺ x := by
          unfold z;
          match x, y with
          | .inr $ .inl _, .inr $ .inl _ => dsimp [tailModel₀]; omega;
          | .inr $ .inr _, .inr $ .inl _ => simp [tailModel₀, Frame.Rel'];
          | .inr $ .inl _, .inr $ .inr _ => simp [tailModel₀, Frame.Rel'];
          | .inr $ .inr _, .inr $ .inr _ => simp [tailModel₀, Frame.Rel'];
        have Rzy : z ≺ y := by
          unfold z;
          match x, y with
          | .inr $ .inl _, .inr $ .inl _ => dsimp [tailModel₀]; omega;
          | .inr $ .inr _, .inr $ .inl _ => simp [tailModel₀, Frame.Rel'];
          | .inr $ .inl _, .inr $ .inr _ => simp [tailModel₀, Frame.Rel'];
          | .inr $ .inr _, .inr $ .inr _ => simp [tailModel₀, Frame.Rel'];
        use z;
        constructor;
        . exact tailModel₀.rel_root_embed_nat;
        . apply Satisfies.or_def.not.mpr;
          push_neg;
          constructor;
          . apply Satisfies.not_box_def.mpr;
            use x;
          . apply Satisfies.not_box_def.mpr;
            use y;
      | mdp ihφψ ihφ => exact ihφψ ihφ
    tfae_have 2 → 3 := by
      contrapose!;
      rintro ⟨M, r, _, h⟩;
      have h₁ : ∀ X ⊆ φ.subformulas.prebox, Satisfies M r (□X.box.disj ➝ X.box.disj) := by simpa using Satisfies.not_imp_def.mp h |>.1;
      have h₂ := Satisfies.not_imp_def.mp h |>.2;

      let X := φ.subformulas.prebox.filter (λ ψ => ¬(r ⊧ □ψ));
      obtain ⟨x, Rrx, hx⟩ : ∃ x, r ≺ x ∧ ∀ ψ ∈ X, ¬x ⊧ □ψ := by
        have : r ⊧ ∼(X.box.disj) := by
          apply Satisfies.not_def.mpr;
          apply Satisfies.fdisj_def.not.mpr;
          simp [X];
        have : r ⊧ ∼□(X.box.disj) := by
          have := h₁ X $ by simp [X];
          tauto;
        obtain ⟨x, Rrx, hx⟩ := Satisfies.not_box_def.mp this;
        use x;
        constructor;
        . assumption;
        . simpa using Satisfies.fdisj_def.not.mp hx;

      let Mt := tailModel₀ (M↾x) (λ p => M.Val r p);

      have : ∀ ψ ∈ φ.subformulas, (tailModel₀.root : Mt) ⊧ ψ ↔ r ⊧ ψ := by
        intro ψ hψ;
        induction ψ with
        | hatom p => simp [tailModel₀, tailModel₀.root, Satisfies, Semantics.Realize]; -- TODO: extract
        | hfalsum => simp;
        | himp φ ψ ihφ ihψ => simp [ihφ (by grind), ihψ (by grind)];
        | hbox ψ ihψ =>
          replace ihψ := ihψ (by grind);
          constructor;
          . intro h;
            have : (tailModel₀.embed_original ⟨x, by tauto⟩ : Mt) ⊧ □ψ := tailModel₀.satisfies_box_of_satisfies_box_at_root h;
            have : x ⊧ □ψ :=
              Model.pointGenerate.modal_equivalent' _ _ |>.mp $
              tailModel₀.modal_equivalent_original |>.mpr $ this;
            contrapose! this;
            apply hx;
            simp_all [X];
          . intro h w Rrw;
            have H₁ : ∀ w : M↾x, w ⊧ ψ := by
              intro w;
              apply Model.pointGenerate.modal_equivalent' x w |>.mpr;
              apply h;
              rcases w.2 with (_ | Rrw);
              . convert Rrx;
              . apply M.trans Rrx $ HRel.TransGen.unwrap Rrw;
            match w with
            | .inl _ => contradiction;
            | .inr $ .inr w => exact tailModel₀.modal_equivalent_original.mp $ H₁ w;
            | .inr $ .inl n =>
              apply tailModel₀.of_provable_rflSubformula_original_root (M := M↾x) (φ := φ) ?_ ψ (by grind) n |>.mp;
              . apply H₁;
              . apply Model.pointGenerate.modal_equivalent_at_root x |>.mpr;
                apply Satisfies.conj_def.mpr;
                suffices ∀ (ψ : Formula ℕ), □ψ ∈ φ.subformulas → x ⊧ (□ψ ➝ ψ) by simpa;
                intro ψ hψ hψ;
                have : ψ ∉ X := by
                  contrapose! hψ;
                  apply hx;
                  assumption;
                have : r ⊧ (□ψ) := by
                  simp [X] at this;
                  tauto;
                apply this;
                assumption;
      refine ⟨M↾x, ⟨x, by tauto⟩, ?_, _, this φ (by grind) |>.not.mpr h₂⟩;
      . exact {}
    tfae_have 4 ↔ 3 := GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree
    tfae_have 4 → 1 := by
      intro h;
      apply (show Modal.D ⊢! φ.dzSubformula.conj ➝ φ by exact sumQuasiNormal.mem₁! h) ⨀ ?_;
      apply FConj!_iff_forall_provable.mpr;
      intro ψ hψ;
      obtain ⟨s, _, rfl⟩ : ∃ s ⊆ φ.subformulas.prebox, □s.box.disj ➝ s.box.disj = ψ := by simpa using hψ;
      exact D.fdisj_axiomDz;
    tfae_finish;

lemma iff_provable_D_provable_GL : Modal.D ⊢! φ ↔ Modal.GL ⊢! φ.dzSubformula.conj ➝ φ := GL_D_TFAE (φ := φ) |>.out 0 3

lemma D.unprovable_T : Modal.D ⊬ (Axioms.T (.atom 0)) := by
  apply GL_D_TFAE |>.out 0 1 |>.not.mpr;
  push_neg;
  let M : Kripke.Model := {
    World := Fin 1,
    Rel := (· < ·),
    Val := λ p i => True,
  }
  refine ⟨M, 0, ?_, (λ _ => False), ?_⟩;
  . exact {
      world_finite := inferInstance,
      root_generates := by
        suffices ∀ w : Fin 1, w = 0 by simp [M];
        trivial;
    }
  . apply Satisfies.not_imp_def.mpr
    constructor;
    . intro x Rrx;
      match x with
      | .inr $ .inl x => simp [tailModel₀, Satisfies, M]
      | .inr $ .inr x => simp [tailModel₀, Satisfies, M]
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
