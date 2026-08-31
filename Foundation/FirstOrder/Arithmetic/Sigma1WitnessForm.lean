module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv
public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# Δ₀-witnessed form for Σ₁ formulas
-/

@[expose] public section

open Classical
open LO
open LO.FirstOrder

noncomputable section

namespace LO.FirstOrder.Arithmetic

variable {n : ℕ}

-- A `StrictHierarchy 𝚺 1` witness is always of the form `∃¹ θ` for some Δ₀ `θ`; extract that
-- `θ` as data (mirroring `StrictHierarchy.sigma_succ_elim`, a `Prop`-valued existential).
private noncomputable def strictSigma1Elim {φ : ArithmeticSemiformula Empty n} (h : StrictHierarchy 𝚺 1 φ) :
    Σ' θ : ArithmeticSemiformula Empty (n + 1), φ = ∃¹ θ ∧ Hierarchy 𝚺 0 θ :=
  ⟨h.sigma_succ_elim.choose, h.sigma_succ_elim.choose_spec.1,
    StrictHierarchy.zero_iff.mp h.sigma_succ_elim.choose_spec.2⟩

private def witnessForm_atomic {φ : ArithmeticSemiformula Empty n} (hφ : Hierarchy 𝚺 0 φ) :
    StrictEquiv 𝗜𝚺₁ 𝚺 1 φ where
  witness := ∃¹ (Rew.bShift ▹ φ)
  hierarchy := StrictHierarchy.sigma (StrictHierarchy.zero (by simpa using hφ))
  provable := provable_iff_of_models_iff fun V _ _ e => by
    simp only [Semiformula.eval_ex];
    constructor;
    . intro h; exact ⟨0, by simpa using h⟩;
    . rintro ⟨w, h⟩; simpa using h;

private noncomputable def witnessForm_and {φ₁ φ₂ : ArithmeticSemiformula Empty n}
    (h₁ : StrictEquiv 𝗜𝚺₁ 𝚺 1 φ₁) (h₂ : StrictEquiv 𝗜𝚺₁ 𝚺 1 φ₂) :
    StrictEquiv 𝗜𝚺₁ 𝚺 1 (φ₁ ⋏ φ₂) := by
  obtain ⟨ψ₁, hψ₁, hprov₁⟩ := h₁;
  obtain ⟨ψ₂, hψ₂, hprov₂⟩ := h₂;
  have hmi₁ := models_iff_of_provable_iff' hprov₁;
  have hmi₂ := models_iff_of_provable_iff' hprov₂;
  obtain ⟨θ₁, rfl, hθ₁⟩ := strictSigma1Elim hψ₁;
  obtain ⟨θ₂, rfl, hθ₂⟩ := strictSigma1Elim hψ₂;
  have h₁' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e φ₁ ↔ ∃ w, V ⊧/(w :> e) θ₁ := fun V _ _ e => (hmi₁ V e).trans Semiformula.eval_ex;
  have h₂' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e φ₂ ↔ ∃ w, V ⊧/(w :> e) θ₂ := fun V _ _ e => (hmi₂ V e).trans Semiformula.eval_ex;
  use ∃¹ ((θ₁ ⇜ (#0 :> (#·.succ.succ))).bexsLTSucc (#0 : ArithmeticSemiterm Empty (n + 1)) ⋏
    (θ₂ ⇜ (#0 :> (#·.succ.succ))).bexsLTSucc (#0 : ArithmeticSemiterm Empty (n + 1)));
  . exact StrictHierarchy.sigma (StrictHierarchy.zero (by simp [hθ₁, hθ₂]));
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_ex, LO.LogicalConnective.HomClass.map_and];
    rw [h₁' V e, h₂' V e];
    simp only [Semiformula.eval_bexsLTSucc, Arithmetic.lt_succ_iff_le, Semiformula.eval_insert1];
    constructor;
    . rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩;
      exact ⟨w₁ + w₂, ⟨w₁, self_le_add_right w₁ w₂, hw₁⟩, ⟨w₂, self_le_add_left w₂ w₁, hw₂⟩⟩;
    . rintro ⟨w, ⟨w₁, _, hw₁⟩, ⟨w₂, _, hw₂⟩⟩;
      exact ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩;

private noncomputable def witnessForm_or {φ₁ φ₂ : ArithmeticSemiformula Empty n}
    (h₁ : StrictEquiv 𝗜𝚺₁ 𝚺 1 φ₁) (h₂ : StrictEquiv 𝗜𝚺₁ 𝚺 1 φ₂) :
    StrictEquiv 𝗜𝚺₁ 𝚺 1 (φ₁ ⋎ φ₂) := by
  obtain ⟨ψ₁, hψ₁, hprov₁⟩ := h₁;
  obtain ⟨ψ₂, hψ₂, hprov₂⟩ := h₂;
  have hmi₁ := models_iff_of_provable_iff' hprov₁;
  have hmi₂ := models_iff_of_provable_iff' hprov₂;
  obtain ⟨θ₁, rfl, hθ₁⟩ := strictSigma1Elim hψ₁;
  obtain ⟨θ₂, rfl, hθ₂⟩ := strictSigma1Elim hψ₂;
  have h₁' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e φ₁ ↔ ∃ w, V ⊧/(w :> e) θ₁ := fun V _ _ e => (hmi₁ V e).trans Semiformula.eval_ex;
  have h₂' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e φ₂ ↔ ∃ w, V ⊧/(w :> e) θ₂ := fun V _ _ e => (hmi₂ V e).trans Semiformula.eval_ex;
  use ∃¹ (θ₁ ⋎ θ₂);
  . exact StrictHierarchy.sigma (StrictHierarchy.zero (by simp [hθ₁, hθ₂]));
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_ex, LO.LogicalConnective.HomClass.map_or];
    rw [h₁' V e, h₂' V e];
    aesop;

section Collection

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- Specialize the general `Σ_{s+1}`-collection of `BoundedCollection.lean` to `s = 0`
-- (i.e. Δ₀-collection over `𝗜𝚺₁`).
private lemma exists_bound_witness {θ : ArithmeticSemiformula Empty (n + 2)} (hθ : Hierarchy 𝚺 0 θ)
    (e : Fin n → V) (a : V) (h : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ :=
  sigma_exists_bound_witness (s := 0) (hθ.mono (by omega)) e a h

end Collection

private noncomputable def witnessForm_exs {φ : ArithmeticSemiformula Empty (n + 1)}
    (h : StrictEquiv 𝗜𝚺₁ 𝚺 1 φ) :
    StrictEquiv 𝗜𝚺₁ 𝚺 1 (∃¹ φ) := by
  obtain ⟨ψ, hψ, hprov⟩ := h;
  have hmi := models_iff_of_provable_iff' hprov;
  obtain ⟨θ', rfl, hθ'⟩ := strictSigma1Elim hψ;
  have h' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin (n + 1) → V),
      V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ' := fun V _ _ e => (hmi V e).trans Semiformula.eval_ex;
  use ∃¹ (((θ' ⇜ (#0 :> #1 :> (#·.succ.succ.succ))).bexsLTSucc
    (#1 : ArithmeticSemiterm Empty (n + 2))).bexsLTSucc (#0 : ArithmeticSemiterm Empty (n + 1)));
  . exact StrictHierarchy.sigma (StrictHierarchy.zero (by simp [hθ']));
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_ex, eval_bexsLTSucc', Semiformula.eval_insert2];
    constructor;
    . rintro ⟨x, hx⟩;
      obtain ⟨w', hw'⟩ := (h' V (x :> e)).mp hx;
      exact ⟨x + w', x, self_le_add_right x w', w', self_le_add_left w' x, hw'⟩;
    . rintro ⟨_, x, -, w', -, hw'⟩;
      exact ⟨x, (h' V (x :> e)).mpr ⟨w', hw'⟩⟩;

private noncomputable def witnessForm_ball {t : ArithmeticSemiterm Empty n} {φ : ArithmeticSemiformula Empty (n + 1)}
    (h : StrictEquiv 𝗜𝚺₁ 𝚺 1 φ) :
    StrictEquiv 𝗜𝚺₁ 𝚺 1 (φ.ballLT t) := by
  obtain ⟨ψ, hψ, hprov⟩ := h;
  have hmi := models_iff_of_provable_iff' hprov;
  obtain ⟨θ', rfl, hθ'⟩ := strictSigma1Elim hψ;
  have h' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin (n + 1) → V),
      V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ' := fun V _ _ e => (hmi V e).trans Semiformula.eval_ex;
  use ∃¹ (((θ' ⇜ (#0 :> #1 :> (#·.succ.succ.succ))).bexsLTSucc
    (#1 : ArithmeticSemiterm Empty (n + 2))).ballLT (Rew.bShift t : ArithmeticSemiterm Empty (n + 1)));
  . exact StrictHierarchy.sigma (StrictHierarchy.zero (by simp [hθ']));
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_ex, Semiformula.eval_ballLT, eval_bexsLTSucc', Semiformula.eval_insert2,
      Semiterm.val_bShift];
    constructor;
    . intro hφ;
      have hex : ∀ x < t.valb e, ∃ w', V ⊧/(w' :> x :> e) θ' :=
        fun x hx => (h' V (x :> e)).mp (hφ x hx);
      obtain ⟨w, hw⟩ := exists_bound_witness hθ' e (t.valb e) hex;
      exact ⟨w, fun x hx => hw x hx⟩;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨w', -, hθ'x⟩ := hw x hx;
      exact (h' V (x :> e)).mpr ⟨w', hθ'x⟩;

theorem ISigma1.exists_delta0_witness_provable {n : ℕ} {φ : ArithmeticSemiformula Empty n} (hφ : Hierarchy 𝚺 1 φ) :
    ∃ θ : ArithmeticSemiformula Empty (n + 1),
      Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ) := by
  have H : Nonempty (StrictEquiv 𝗜𝚺₁ 𝚺 1 φ) := by
    apply sigma₁_induction' hφ (P := fun n φ => Nonempty (StrictEquiv 𝗜𝚺₁ 𝚺 1 φ))
    . exact fun n => ⟨witnessForm_atomic (Hierarchy.verum _ _ _)⟩
    . exact fun n => ⟨witnessForm_atomic (Hierarchy.falsum _ _ _)⟩
    . exact fun n t₁ t₂ => ⟨witnessForm_atomic (Hierarchy.rel _ _ _ _)⟩
    . exact fun n t₁ t₂ => ⟨witnessForm_atomic (Hierarchy.nrel _ _ _ _)⟩
    . exact fun n t₁ t₂ => ⟨witnessForm_atomic (Hierarchy.rel _ _ _ _)⟩
    . exact fun n t₁ t₂ => ⟨witnessForm_atomic (Hierarchy.nrel _ _ _ _)⟩
    . rintro n φ ψ hφ hψ ⟨h₁⟩ ⟨h₂⟩; exact ⟨witnessForm_and h₁ h₂⟩
    . rintro n φ ψ hφ hψ ⟨h₁⟩ ⟨h₂⟩; exact ⟨witnessForm_or h₁ h₂⟩
    . rintro n t φ hφ ⟨h⟩; exact ⟨witnessForm_ball h⟩
    . rintro n φ hφ ⟨h⟩; exact ⟨witnessForm_exs h⟩
  obtain ⟨θ, heq, hθ⟩ := strictSigma1Elim H.some.hierarchy;
  exact ⟨θ, hθ, heq ▸ H.some.provable⟩;

theorem ISigma1.exists_delta0_witness_provable_of_sentence {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ σ 🡘 ∃¹ θ := by
  obtain ⟨θ, hθ, h⟩ := ISigma1.exists_delta0_witness_provable hσ;
  exact ⟨θ, hθ, h⟩;

/-- The `StrictEquiv`-vocabulary form of `ISigma1.exists_delta0_witness_provable`: every `Σ₁`
formula is `𝗜𝚺₁`-provably equivalent to a genuine `∃¹`-Δ₀ prenex form, without needing full `𝗣𝗔`. -/
noncomputable def ISigma1.strictEquiv_sigma1 {n : ℕ} {φ : ArithmeticSemiformula Empty n} (hφ : Hierarchy 𝚺 1 φ) :
    StrictEquiv 𝗜𝚺₁ 𝚺 1 φ :=
  let e := ISigma1.exists_delta0_witness_provable hφ
  ⟨∃¹ e.choose, StrictHierarchy.sigma (StrictHierarchy.zero e.choose_spec.1), e.choose_spec.2⟩

noncomputable def ISigma1.strictEquiv_sigma1_of_sentence {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    StrictEquiv 𝗜𝚺₁ 𝚺 1 σ :=
  ISigma1.strictEquiv_sigma1 hσ

end LO.FirstOrder.Arithmetic
