import Foundation.Modal.Logic.Extension
import Foundation.Modal.Maximal.Unprovability
import Mathlib.Data.ENat.Basic
import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Logic.Ver
import Foundation.Modal.Logic.Global


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
lemma GLPoint3OplusBoxBot.boxbot {n : ℕ} : Modal.GLPoint3OplusBoxBot n ⊢! (□^[n]⊥) := by
  apply Logic.sumNormal.mem₂!;
  tauto;

@[simp] lemma eq_GLPoint3OplusBoxBot_omega_GLPoint3 : (Modal.GLPoint3OplusBoxBot ⊤) = Modal.GLPoint3 := by simp [Modal.GLPoint3OplusBoxBot];


section

open LO.Entailment LO.Modal.Entailment

lemma eq_GLPoint3OplusBoxBot_0_Univ : (Modal.GLPoint3OplusBoxBot 0) = Set.univ := by
  have : Modal.GLPoint3OplusBoxBot 0 ⊢! ⊥ := GLPoint3OplusBoxBot.boxbot;
  ext φ;
  suffices Modal.GLPoint3OplusBoxBot 0 ⊢! ⊥ by
    simp only [←iff_provable, Set.mem_univ, iff_true];
    cl_prover [this];
  apply sumNormal.mem₂!;
  simp;

lemma eq_GLPoint3OplusBoxBot_1_Ver : (Modal.GLPoint3OplusBoxBot 1) = Modal.Ver := by
  ext φ;
  constructor;
  . simp only [←iff_provable];
    intro h;
    induction h using sumNormal.rec! with
    | mem₁ h => apply Entailment.WeakerThan.pbl h;
    | mem₂ h => simp_all;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ih => apply Logic.subst! _ ih;
    | nec ih => apply nec! ih;
  . suffices Hilbert.Ver ⊢! φ → Modal.GLPoint3OplusBoxBot 1 ⊢! φ by simpa [←iff_provable];
    intro h;
    induction h using Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl);
      . simp;
      . apply axiomK''! (φ := ⊥);
        . apply nec!; cl_prover;
        . apply sumNormal.mem₂!
          simp;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ]
    | nec ih => apply nec! ih;
    | _ => cl_prover;

lemma GLPoint3OplusBoxBot.provable_weakPoint2_in_2 : Modal.GLPoint3OplusBoxBot 2 ⊢! Axioms.WeakPoint2 (.atom 0) (.atom 1) := by
  sorry;

open Formula.Kripke in
lemma GLPoint2.provable_boxboxbot : Modal.GLPoint2 ⊢! (□^[2]⊥) := by
  have h₁ : Modal.GLPoint2 ⊢! □(∼□⊥) ➝ □^[2]⊥  := by
    apply Entailment.WeakerThan.pbl (𝓢 := Modal.GL);
    haveI : Modal.GL ⊢! □(∼□⊥) ➝ □⊥ := by
      suffices Modal.GL ⊢! □(□⊥ ➝ ⊥) ➝ □⊥ by exact this;
      simp [axiomL!];
    haveI : Modal.GL ⊢! □(∼□⊥) ➝ □□⊥ := C!_trans this (by simp [axiomFour!]);
    exact this;
  have h₂ : Modal.GLPoint2 ⊢! ◇□⊥ ➝ □^[2]⊥ := by
    haveI : Modal.GLPoint2 ⊢! ◇□⊥ ➝ ◇(□(∼□⊥) ⋏ □⊥) := by
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
    haveI : Modal.GLPoint2 ⊢! ◇□⊥ ➝ □(◇(∼□⊥) ⋎ □⊥) := C!_trans this (by simp [axiomWeakPoint2!]);
    haveI : Modal.GLPoint2 ⊢! ◇□⊥ ➝ □(∼□□⊥ ⋎ □⊥) := C!_trans this $ axiomK'! $ nec! $ by
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
    haveI : Modal.GLPoint2 ⊢! ◇□⊥ ➝ □(□□⊥ ➝ □⊥) := C!_trans this $ axiomK'! $ nec! (by cl_prover);
    haveI : Modal.GLPoint2 ⊢! ◇□⊥ ➝ □□⊥ := C!_trans this (by simp [axiomL!])
    exact this;
  have h₃ : Modal.GLPoint2 ⊢! ◇□⊥ ⭤ ∼□(∼□⊥) := dia_duality!;
  cl_prover [h₁, h₂, h₃];

instance : Modal.GLPoint3 ⪯ Modal.GLPoint2 := by
  suffices Hilbert.GLPoint3 ⪯ Hilbert.GLPoint2 by infer_instance;
  apply weakerThan_iff.mpr;
  intro φ hφ;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h =>
    rcases h with (rfl | rfl | rfl);
    . simp;
    . simp;
    . apply Hilbert.Normal.subst! s;
      sorry;
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
      rw [(show φ = □^[2]⊥ by simpa using h)];
      exact GLPoint2.provable_boxboxbot;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ih => apply Logic.subst! _ ih;
    | nec ih => apply nec! ih;
  . suffices Hilbert.GLPoint2  ⊢! φ → Modal.GLPoint3OplusBoxBot 2 ⊢! φ by simpa [←iff_provable];
    intro h;
    induction h using Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl | rfl);
      . simp;
      . apply sumNormal.mem₁!; simp;
      . apply subst! s GLPoint3OplusBoxBot.provable_weakPoint2_in_2;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ]
    | nec ih => apply nec! ih;
    | _ => cl_prover;

end

end LO.Modal
