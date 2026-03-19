module

public import Foundation.Modal.Logic.SumNormal
public import Foundation.Modal.Maximal.Unprovability
public import Mathlib.Data.ENat.Basic
public import Foundation.Modal.Kripke.Logic.GL.Completeness
public import Foundation.Modal.Kripke.Logic.Ver
public import Foundation.Modal.Logic.Global


@[expose] public section

namespace LO.Modal

open Logic

variable {n : ℕ∞}

protected def GLPoint3OplusBoxBot (n : ℕ∞) :=
  match n with
  | .some n => Modal.GLPoint3.sumNormal {□^[n]⊥}
  | .none   => Modal.GLPoint3

instance : (Modal.GLPoint3OplusBoxBot n).IsNormal := by
  dsimp [Modal.GLPoint3OplusBoxBot];
  split <;> infer_instance;

instance : Modal.GLPoint3 ⪯ Modal.GLPoint3OplusBoxBot n := by
  dsimp [Modal.GLPoint3OplusBoxBot];
  split <;> infer_instance;

@[simp]
lemma GLPoint3OplusBoxBot.boxbot {n : ℕ} : Modal.GLPoint3OplusBoxBot n ⊢ (□^[n]⊥) := by
  apply Logic.sumNormal.mem₂!;
  tauto;

open LO.Entailment LO.Modal.Entailment in
@[simp]
lemma GLPoint3OplusBoxBot.axiomNVer {n : ℕ} : Modal.GLPoint3OplusBoxBot n ⊢ (□^[n]φ) :=
  Modal.Entailment.boxItr_axiomK'! (multinec! (by cl_prover)) ⨀ GLPoint3OplusBoxBot.boxbot

@[simp] lemma eq_GLPoint3OplusBoxBot_omega_GLPoint3 : (Modal.GLPoint3OplusBoxBot ⊤) = Modal.GLPoint3 := by simp [Modal.GLPoint3OplusBoxBot];


section

open Kripke
open LO.Entailment LO.Modal.Entailment
open Formula (atom)
open Formula.Kripke

lemma GLPoint3OplusBoxBot.weakerThan_succ {n : ℕ} : (Modal.GLPoint3OplusBoxBot (n + 1)) ⪯ (Modal.GLPoint3OplusBoxBot n) := by
  apply weakerThan_iff.mpr;
  intro φ h;
  induction h using sumNormal.rec! with
  | mem₁ h => apply Entailment.WeakerThan.pbl h;
  | @mem₂ φ h =>
    suffices Modal.GLPoint3OplusBoxBot n ⊢ (□^[n]⊥) 🡒 (□^[(n + 1)](⊥)) by
      rw [(show φ = □^[(n + 1)]⊥ by replace h := Logic.iff_provable.mp h; simp_all;)];
      exact this ⨀ (by simp);
    apply boxItr_axiomK'!;
    apply multinec!;
    cl_prover;
  | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
  | subst ih => apply Logic.subst _ ih;
  | nec ih => apply nec! ih;

lemma GLPoint3OplusBoxBot.weakerThan_add {n k : ℕ} : (Modal.GLPoint3OplusBoxBot (n + k)) ⪯ (Modal.GLPoint3OplusBoxBot n) := by
  induction k with
  | zero => simp [Modal.GLPoint3OplusBoxBot];
  | succ k ih =>
    trans (Modal.GLPoint3OplusBoxBot (n + k));
    . apply Modal.GLPoint3OplusBoxBot.weakerThan_succ;
    . assumption;

lemma GLPoint3OplusBoxBot.weakerThan_lt {n m : ℕ} (hmn : m > n) : (Modal.GLPoint3OplusBoxBot m) ⪯ (Modal.GLPoint3OplusBoxBot n) := by
  rw [(show m = n + (m - n) by omega)];
  apply GLPoint3OplusBoxBot.weakerThan_add;

instance : (Modal.GLPoint3OplusBoxBot 1) ⪯ (Modal.GLPoint3OplusBoxBot 0) := GLPoint3OplusBoxBot.weakerThan_lt (by simp)
instance : (Modal.GLPoint3OplusBoxBot 2) ⪯ (Modal.GLPoint3OplusBoxBot 1) := GLPoint3OplusBoxBot.weakerThan_lt (by simp)

/--
  `<` on `Fin (k + 1)`, `m ≥ n` can be reached by `n` times `<`-step.
-/
lemma _root_.Rel.Iterate.fin_lt_stepping_stones {k n : ℕ} {m : Fin (k + 1)}
  (_ : n = 0 → m = 0)
  (_ : n ≤ m)
  : Rel.Iterate (α := Fin (k + 1)) (· < ·) n 0 m := by
  induction n generalizing m with
  | zero =>
    simp_all;
  | succ n ih =>
    rw [Rel.Iterate.forward];
    use ⟨n, by omega⟩;
    constructor;
    . apply ih;
      . simp;
      . simp;
    . simpa;

lemma GLPoint3OplusBoxBot.strictlyWeakerThan_GLPoint3 {n : ℕ} : (Modal.GLPoint3) ⪱ (Modal.GLPoint3OplusBoxBot n) := by
  apply strictlyWeakerThan_iff.mpr;
  constructor;
  . intro _ h;
    apply sumNormal.mem₁!;
    assumption;
  . use □^[n]⊥;
    constructor;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_GLPoint3);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin (n + 1), λ x y => (x < y)⟩, (λ _ _ => True)⟩;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {}
      . apply Satisfies.boxItr_def.not.mpr;
        push_neg;
        use ⟨n, by omega⟩;
        constructor;
        . apply Rel.Iterate.fin_lt_stepping_stones <;> simp;
        . tauto;
    . simp;

instance : (Modal.GLPoint3) ⪱ (Modal.GLPoint3OplusBoxBot 2) := GLPoint3OplusBoxBot.strictlyWeakerThan_GLPoint3

lemma eq_GLPoint3OplusBoxBot_0_Univ : (Modal.GLPoint3OplusBoxBot 0) = Set.univ := by
  have : Modal.GLPoint3OplusBoxBot 0 ⊢ ⊥ := GLPoint3OplusBoxBot.boxbot;
  ext φ;
  suffices Modal.GLPoint3OplusBoxBot 0 ⊢ ⊥ by
    simp only [←iff_provable, Set.mem_univ, iff_true];
    cl_prover [this];
  apply sumNormal.mem₂!;
  apply Logic.iff_provable.mpr;
  simp;


lemma eq_GLPoint3OplusBoxBot_1_Ver : (Modal.GLPoint3OplusBoxBot 1) = Modal.Ver := by
  ext φ;
  constructor;
  . simp only [←iff_provable];
    intro h;
    induction h using sumNormal.rec! with
    | mem₁ h => apply Entailment.WeakerThan.pbl h;
    | mem₂ h => simp_all [Logic.iff_provable];
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ih => apply Logic.subst _ ih;
    | nec ih => apply nec! ih;
  . suffices Modal.Ver ⊢ φ → Modal.GLPoint3OplusBoxBot 1 ⊢ φ by simpa [Logic.iff_provable];
    intro h;
    induction h using Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl);
      . simp;
      . apply axiomK''! (φ := ⊥);
        . apply nec!; cl_prover;
        . apply sumNormal.mem₂!;
          apply Logic.iff_provable.mpr;
          simp;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ]
    | nec ih => apply nec! ih;
    | _ => cl_prover;

instance : (Modal.GLPoint3OplusBoxBot 1) ≊ Modal.Ver := by rw [eq_GLPoint3OplusBoxBot_1_Ver];

lemma GLPoint3OplusBoxBot.provable_weakPoint2_in_2 : Modal.GLPoint3OplusBoxBot 2 ⊢ Axioms.WeakPoint2 (.atom 0) (.atom 1) := by
  suffices Modal.GLPoint3OplusBoxBot 2 ⊢ Axioms.CD (.atom 0) by
    apply C!_trans (Logic.subst (λ _ => (□(.atom 0) ⋏ (.atom 1))) this);
    -- TODO: `K_prover`
    apply normal_provable_of_K_provable;
    apply Complete.complete (𝓜 := Kripke.FrameClass.K);
    simp only [Formula.subst.subst_box, Formula.subst.subst_atom];
    intro F _ V x h y Rxy;
    apply Satisfies.or_def.mpr;
    right;
    exact (Satisfies.and_def.mp $ h y Rxy) |>.2;
  haveI : Modal.GLPoint3OplusBoxBot 2 ⊢ ◇(.atom 0) 🡒 ◇(.atom 0) ⋏ (□^[2](.atom 0)) := by
    have : Modal.GLPoint3OplusBoxBot 2 ⊢ □^[2](.atom 0) := GLPoint3OplusBoxBot.axiomNVer;
    cl_prover [this];
  haveI : Modal.GLPoint3OplusBoxBot 2 ⊢ ◇(.atom 0) 🡒 ∼□(⊡(.atom 0) 🡒 ∼(.atom 0)) := C!_trans this $ by
    -- TODO: `K_prover`
    apply normal_provable_of_K_provable;
    apply Complete.complete (𝓜 := Kripke.FrameClass.K);
    intro F _ V x h;
    replace h := Satisfies.and_def.mp h;
    obtain ⟨y, Rxy, h₁⟩ := Satisfies.dia_def.mp h.1;
    apply Satisfies.not_box_def.mpr;
    use y;
    constructor;
    . assumption;
    . apply Satisfies.not_imp_def.mpr;
      constructor;
      . apply Satisfies.and_def.mpr;
        constructor;
        . assumption;
        . intro z Ryz;
          apply Satisfies.boxItr_def.mp h.2;
          use y;
          tauto;
      . apply Satisfies.not_def.mp;
        apply Satisfies.negneg_def.mpr;
        assumption;
  haveI : Modal.GLPoint3OplusBoxBot 2 ⊢ ◇(.atom 0) 🡒 □(⊡(∼(.atom 0)) 🡒 (.atom 0)) := C!_trans this $ by
    have : Modal.GLPoint3OplusBoxBot 2 ⊢ □(⊡(.atom 0) 🡒 (∼(.atom 0))) ⋎ □(⊡(∼(.atom 0)) 🡒 (.atom 0)) := sumNormal.mem₁! (by simp);
    cl_prover [this];
  haveI : Modal.GLPoint3OplusBoxBot 2 ⊢ ◇(.atom 0) 🡒 □^[2](∼.atom 0) 🡒 □(.atom 0) := C!_trans this $ by
    apply C!_trans ?_ axiomK!;
    apply axiomK'!;
    apply nec!
    cl_prover;
  haveI : Modal.GLPoint3OplusBoxBot 2 ⊢ ◇(.atom 0) 🡒 □(.atom 0) := C!_trans this $ by
    have : Modal.GLPoint3OplusBoxBot 2 ⊢ (□^[2](∼(.atom 0))) := GLPoint3OplusBoxBot.axiomNVer;
    cl_prover [this];
  exact this;


lemma GLPoint2.provable_boxboxbot : Modal.GLPoint2 ⊢ (□^[2]⊥) := by
  have h₁ : Modal.GLPoint2 ⊢ □(∼□⊥) 🡒 □^[2]⊥  := by
    apply Entailment.WeakerThan.pbl (𝓢 := Modal.GL);
    haveI : Modal.GL ⊢ □(∼□⊥) 🡒 □⊥ := by
      suffices Modal.GL ⊢ □(□⊥ 🡒 ⊥) 🡒 □⊥ by exact this;
      simp [axiomL!];
    haveI : Modal.GL ⊢ □(∼□⊥) 🡒 □□⊥ := C!_trans this (by simp);
    exact this;
  have h₂ : Modal.GLPoint2 ⊢ ◇□⊥ 🡒 □^[2]⊥ := by
    haveI : Modal.GLPoint2 ⊢ ◇□⊥ 🡒 ◇(□(∼□⊥) ⋏ □⊥) := by
      -- TODO: `K_prover`
      apply normal_provable_of_K_provable;
      apply Complete.complete (𝓜 := Kripke.FrameClass.K);
      intro F _ V x h;
      obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
      apply Satisfies.dia_def.mpr;
      use y;
      constructor;
      . assumption;
      . apply Satisfies.and_def.mpr;
        constructor;
        . intro z Ryz;
          have := hy z Ryz;
          simp [Satisfies] at this;
        . assumption;
    haveI : Modal.GLPoint2 ⊢ ◇□⊥ 🡒 □(◇(∼□⊥) ⋎ □⊥) := C!_trans this (by simp [axiomWeakPoint2!]);
    haveI : Modal.GLPoint2 ⊢ ◇□⊥ 🡒 □(∼□□⊥ ⋎ □⊥) := C!_trans this $ axiomK'! $ nec! $ by
      -- TODO: `K_prover`
      apply normal_provable_of_K_provable;
      apply Complete.complete (𝓜 := Kripke.FrameClass.K);
      intro F _ V x h;
      apply Satisfies.or_def.mpr;
      rcases Satisfies.or_def.mp h with (h | h);
      . left;
        apply Satisfies.not_box_def.mpr;
        obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h;
        use y;
        constructor;
        . assumption;
        . assumption;
      . tauto;
    haveI : Modal.GLPoint2 ⊢ ◇□⊥ 🡒 □(□□⊥ 🡒 □⊥) := C!_trans this $ axiomK'! $ nec! (by cl_prover);
    haveI : Modal.GLPoint2 ⊢ ◇□⊥ 🡒 □□⊥ := C!_trans this (by simp)
    exact this;
  have h₃ : Modal.GLPoint2 ⊢ ◇□⊥ 🡘 ∼□(∼□⊥) := dia_duality!;
  cl_prover [h₁, h₂, h₃];

lemma GLPoint2.provable_axiomWeakPoint3 : Modal.GLPoint2 ⊢ (Axioms.WeakPoint3 (.atom 0) (.atom 1)) := by
  suffices Modal.GLPoint2 ⊢ ◇((.atom 0) ⋏ □(.atom 0)) 🡒 □(.atom 0) by
    suffices Modal.GLPoint2 ⊢ ∼□(⊡atom 0 🡒 atom 1) 🡒 □(⊡atom 1 🡒 atom 0) by cl_prover [this];
    apply C!_trans ?_ (Logic.subst (λ _ => ((⊡atom 1 🡒 atom 0))) this);
      -- TODO: `K_prover`
    apply normal_provable_of_K_provable;
    apply Complete.complete (𝓜 := Kripke.FrameClass.K);
    simp only [Formula.subst.subst_dia, Formula.subst.subst_and, Formula.subst.subst_atom, Formula.subst.subst_box];
    intro F _ V x h;
    obtain ⟨y, Rxy, hy⟩ := Satisfies.not_box_def.mp h;
    apply Satisfies.dia_def.mpr;
    use y;
    constructor;
    . assumption;
    . apply Satisfies.and_def.mpr;
      constructor;
      . intro h;
        replace h := Satisfies.and_def.mp h;
        tauto;
      . intro z Ryz hz;
        apply (Satisfies.and_def.mp $ Satisfies.not_imp_def.mp hy |>.1) |>.2;
        assumption;
  haveI : Modal.GLPoint2 ⊢ ◇(((.atom 0) ⋏ □(.atom 0))) 🡒 ◇(((.atom 0) ⋏ □(.atom 0)) ⋏ □(∼((.atom 0) ⋏ □(.atom 0)))) := by
    suffices Modal.GLPoint2 ⊢ □((□(∼(atom 0 ⋏ □atom 0)) 🡒 ∼(atom 0 ⋏ □atom 0))) 🡒 □(∼(atom 0 ⋏ □atom 0)) by
      apply (?_ ⨀ this);
      -- TODO: `K_prover`
      suffices Modal.GLPoint2 ⊢ (□(□(∼(atom 0)) 🡒 ∼(atom 0)) 🡒 □(∼(atom 0))) 🡒 ◇(atom 0) 🡒 ◇((atom 0) ⋏ □(∼(atom 0))) by
        exact Logic.subst (λ _ => (atom 0 ⋏ □atom 0)) this;
      apply normal_provable_of_K_provable;
      apply Complete.complete (𝓜 := Kripke.FrameClass.K);
      intro F _ V x;
      simp only [Semantics.Models, Satisfies, LogicalConnective.Prop.arrow_eq, imp_false,
        not_forall, Classical.not_imp, not_not, not_exists, not_and, forall_exists_index, and_imp];
      contrapose!;
      rintro ⟨y, Rxy, hy, h₁⟩;
      constructor;
      . intro z Rxz h₂ hz;
        obtain ⟨w, Rzw, hz⟩ := h₁ z Rxz hz;
        grind;
      . use y;
    simp;
  haveI : Modal.GLPoint2 ⊢ ◇((.atom 0) ⋏ □(.atom 0)) 🡒 ◇((.atom 0) ⋏ □(.atom 0) ⋏ □^[2](.atom 0) ⋏ □(∼((.atom 0) ⋏ □(.atom 0)))) := C!_trans this $ by
    have : Modal.GLPoint2 ⊢ □(.atom 0) 🡒 □^[2](.atom 0) := by simp;
    apply diaK'!;
    cl_prover [this];
  haveI : Modal.GLPoint2 ⊢ ◇((.atom 0) ⋏ □(.atom 0)) 🡒 ◇(□⊥ ⋏ (.atom 0)) := C!_trans this $ by
      -- TODO: `K_prover`
    apply diaK'!;
    apply normal_provable_of_K_provable;
    apply Complete.complete (𝓜 := Kripke.FrameClass.K);
    intro F _ V x hx;
    replace ⟨hx₁, hx₂⟩ := Satisfies.and_def.mp hx;
    replace ⟨hx₂, hx₃⟩ := Satisfies.and_def.mp hx₂;
    replace ⟨hx₃, hx₄⟩ := Satisfies.and_def.mp hx₃;
    apply Satisfies.and_def.mpr;
    constructor;
    . intro y Rxy;
      replace hx₂ := hx₂ _ Rxy;
      replace hx₄ := hx₄ _ Rxy;
      apply hx₄;
      apply Satisfies.and_def.mpr;
      constructor;
      . assumption;
      . intro z Ryz;
        apply Satisfies.boxItr_def.mp hx₃;
        use y;
        tauto;
    . assumption;
  haveI : Modal.GLPoint2 ⊢ ◇((.atom 0) ⋏ □(.atom 0)) 🡒 □(◇⊥ ⋎ (.atom 0)) := C!_trans this $ by simp;
  haveI : Modal.GLPoint2 ⊢ ◇((.atom 0) ⋏ □(.atom 0)) 🡒 □(.atom 0) := C!_trans this $ by
    apply axiomK'!;
    apply nec!;
    haveI : Modal.GLPoint2 ⊢ ∼◇⊥ := by
      -- TODO: `K_prover`
      apply normal_provable_of_K_provable;
      apply Complete.complete (𝓜 := Kripke.FrameClass.K);
      intro F _ V x;
      apply Satisfies.not_dia_def.mpr;
      tauto;
    cl_prover [this];
  exact this;

instance : Entailment.GLPoint3 Modal.GLPoint2 where
  WeakPoint3 φ ψ := by
    constructor;
    apply Logic.iff_provable.mp;
    simpa using Logic.subst (s := λ a => match a with | 0 => φ | 1 => ψ | _ => a) GLPoint2.provable_axiomWeakPoint3;

instance : Modal.GLPoint3 ⪯ Modal.GLPoint2 := by
  suffices Modal.GLPoint3 ⪯ Modal.GLPoint2 by infer_instance;
  apply weakerThan_iff.mpr;
  intro φ hφ;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h => rcases h with (rfl | rfl | rfl) <;> simp;
  | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ]
  | nec ih => apply nec! ih;
  | _ => cl_prover;

lemma eq_GLPoint3OplusBoxBot_2_GLPoint2 : (Modal.GLPoint3OplusBoxBot 2) = Modal.GLPoint2 := by
  ext φ;
  constructor;
  . simp only [←iff_provable];
    intro h;
    induction h using sumNormal.rec! with
    | mem₁ h => apply Entailment.WeakerThan.pbl h;
    | @mem₂ φ h =>
      rw [(show φ = □^[2]⊥ by replace h := Logic.iff_provable.mp h; simp_all;)];
      exact GLPoint2.provable_boxboxbot;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ih => apply Logic.subst _ ih;
    | nec ih => apply nec! ih;
  . suffices Modal.GLPoint2 ⊢ φ → Modal.GLPoint3OplusBoxBot 2 ⊢ φ by simpa [iff_provable];
    intro h;
    induction h using Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl | rfl);
      . simp;
      . apply sumNormal.mem₁!; simp;
      . apply Logic.subst s GLPoint3OplusBoxBot.provable_weakPoint2_in_2;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ]
    | nec ih => apply nec! ih;
    | _ => cl_prover;

instance : (Modal.GLPoint3OplusBoxBot 2) ≊ Modal.GLPoint2 := by rw [eq_GLPoint3OplusBoxBot_2_GLPoint2];



end

end LO.Modal
end
