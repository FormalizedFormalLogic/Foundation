module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv

/-!
# Prenex normal form theorem over $\mathsf{PA}$

Every `Hierarchy Γ s φ` formula is, over models of `𝗣𝗔`, equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level, and this
equivalence is provable in `𝗣𝗔`.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

variable {Γ : Polarity} {s : ℕ} {n : ℕ} {φ : ArithmeticSemiformula Empty n}

open StrictEquiv (refl neg)

-- `peanoClosure`, `exs` and `all` stay `private`, even though their *statements* mention only the
-- public `StrictEquiv`: these `def`s are `Type`-valued (not `Prop`-valued), so unlike a
-- `theorem`/`lemma` (proof-irrelevant, only the statement is exposed), making one public would
-- expose its body.
private noncomputable def peanoClosure : Closure 𝗣𝗔 s := closure inferInstance

-- Contracts the two nested existentials `∃x∃y` of a strict `Σ_{s+1}` witness into a single
-- bounded pair `∃z (∃x ≤ z)(∃y ≤ z)`.
private noncomputable def exs {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv 𝗣𝗔 𝚺 (s + 1) φ) :
    StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∃¹ φ) := by
  obtain ⟨φ', hφ', hprov'⟩ := h;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAprov⟩ := peanoClosure.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (refl hψ₀');
  obtain ⟨B, hB, hBprov⟩ := peanoClosure.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hA);
  have hAiff := models_iff_of_provable_iff' hAprov;
  have hBiff := models_iff_of_provable_iff' hBprov;
  have hAiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 2) → V),
      V ⊧/e ((ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemiformula Empty (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔ V ⊧/e A := hAiff;
  have hBiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 1) → V),
      V ⊧/e (A.bexsLTSucc (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ V ⊧/e B := hBiff;
  use ∃¹ B;
  . exact hB.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have hAeval : ∀ y z : V, V ⊧/(y :> z :> e) A ↔ ∃ x ≤ z, V ⊧/(x :> y :> e) ψ₀ := by
      intro y z;
      rw [← hAiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hBeval : ∀ z : V, V ⊧/(z :> e) B ↔ ∃ y ≤ z, V ⊧/(y :> z :> e) A := by
      intro z;
      rw [← hBiff' V (z :> e)];
      simp;
    have hφeval : ∀ y : V, V ⊧/(y :> e) φ ↔ ∃ x, V ⊧/(x :> y :> e) ψ₀ := fun y =>
      (hiff' V (y :> e)).trans Semiformula.eval_ex;
    simp only [Semiformula.eval_ex, hφeval, hBeval, hAeval];
    constructor;
    . rintro ⟨y, x, hx⟩;
      exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;
    . rintro ⟨z, y, -, x, -, hx⟩;
      exact ⟨y, x, hx⟩;

private noncomputable def all {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv 𝗣𝗔 𝚷 (s + 1) φ) :
    StrictEquiv 𝗣𝗔 𝚷 (s + 1) (∀¹ φ) := by
  have h' : StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∼φ) := neg h;
  have h'' := neg (exs h');
  simpa using h'';

theorem Peano.nonempty_strictEquiv (h : Hierarchy Γ s φ) : Nonempty (StrictEquiv 𝗣𝗔 Γ s φ) := by
  induction h with
  | verum Γ s n => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.verum 𝚺 0 n)⟩;
  | falsum Γ s n => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
  | rel Γ s r v => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
  | nrel Γ s r v => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
  | and _ _ ihp ihq => exact ⟨peanoClosure.and _ ihp.some ihq.some⟩;
  | or _ _ ihp ihq => exact ⟨peanoClosure.or _ ihp.some ihq.some⟩;
  | ball pos _ ih => exact ⟨peanoClosure.ball _ pos ih.some⟩;
  | bexs pos _ ih => exact ⟨peanoClosure.bexs _ pos ih.some⟩;
  | exs _ ih => exact ⟨exs ih.some⟩;
  | all _ ih => exact ⟨all ih.some⟩;
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . exact ⟨StrictEquiv.refl (StrictHierarchy.sigma (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
    . exact ⟨StrictEquiv.exs_of_pi ih.some⟩;
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . exact ⟨StrictEquiv.refl (StrictHierarchy.pi (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
    . exact ⟨StrictEquiv.all_of_sigma ih.some⟩;
  | dummy_sigma hp ih => exact ⟨StrictEquiv.alt_up (all ih.some)⟩;
  | dummy_pi hp ih => exact ⟨StrictEquiv.alt_up (exs ih.some)⟩;

lemma Peano.exists_strictHierarchy_provable {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
  ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 ψ) := by
  have ⟨⟨ψ, ψ_hie, ψ_iff⟩⟩ := nonempty_strictEquiv h;
  use ψ;

lemma Peano.exists_strictHierarchy_provable_of_sentence {Γ s} {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
  ∃ π : ArithmeticSentence, StrictHierarchy Γ s π ∧ 𝗣𝗔 ⊢ σ 🡘 π := by
  obtain ⟨π, hπ, h⟩ := Peano.exists_strictHierarchy_provable h;
  exact ⟨π, hπ, h⟩;

end LO.FirstOrder.Arithmetic
