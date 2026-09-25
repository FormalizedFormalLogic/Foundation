module

public import Foundation.ProvabilityLogic.GL.Gentzen.Kripke
public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.ProvabilityLogic.Kripke.Soundness

/-!
# The logic `GL`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment GL Kripke Kripke.Model Kripke.Model.World

abbrev Logic.GL {α : Type*} : Logic α := normalOf ({□A 🡒 □□A | A} ∪ {□(□A 🡒 A) 🡒 □A | A})

notation "𝐆𝐋" => Logic.GL

namespace Logic.GL

open normalOf

variable {α : Type*} {A : Formula α}

@[simp] lemma axiom4 : 𝐆𝐋 ⊢ □A 🡒 □□A := axm (by simp)

@[simp] lemma axiomL : 𝐆𝐋 ⊢ □(□A 🡒 A) 🡒 □A := axm (by simp)

/-! ### Kripke soundness -/

section

variable {κ : Type*} [Nonempty κ] {M : Model κ α}

lemma forces_axiomL [M.IsGL] {x : M.World} : x ⊩[M] □(□A 🡒 A) 🡒 □A := by
  intro hx;
  by_contra hA;
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp hA;
  obtain ⟨t, ⟨Rxt, ht⟩, tmax⟩ := M.terminalOf {y | x ≺ y ∧ y ⊮[M] A} ⟨y, Rxy, hy⟩;
  apply ht;
  apply hx t Rxt;
  intro z Rtz;
  by_contra hz;
  exact tmax z ⟨IsTrans.trans _ _ _ Rxt Rtz, hz⟩ Rtz;

theorem sound (M : Model κ α) [M.IsGL] (h : 𝐆𝐋 ⊢ A) : M ⊧ A := by
  apply normalOf.sound _ h;
  rintro _ (⟨B, rfl⟩ | ⟨B, rfl⟩) x;
  · exact fun h y Rxy z Ryz ↦ h z (IsTrans.trans _ _ _ Rxy Ryz);
  · exact forces_axiomL;

end

/-! ### From the sequent calculus -/

lemma of_gentzen [DecidableEq α] {S : Sequent α} (h : ⊢ᴳ[𝐆𝐋] S) : 𝐆𝐋 ⊢ S.ant.conj 🡒 S.suc.disj := by
  induction h with
  | axm A => simp;
  | botL => simp only [Finset.conj_singleton]; exact efq;
  | wkL _ hΓ ih => exact C_trans (CFConjFConj_of_subset hΓ) ih;
  | wkR _ hΔ ih =>
    exact C_trans ih <| left_Fdisj_intro _ fun B hB ↦ right_Fdisj_intro _ (hΔ hB);
  | @impL Γ Δ A B _ _ ih₁ ih₂ =>
    have h₁ : 𝐆𝐋 ⊢ (insert (A 🡒 B) Γ).conj 🡒 (A 🡒 B) ⋏ Γ.conj := CinsertFConjKFConj;
    have h₂ : 𝐆𝐋 ⊢ (insert A Δ).disj 🡒 A ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : 𝐆𝐋 ⊢ B ⋏ Γ.conj 🡒 (insert B Γ).conj := CKFConjinsertFConj;
    cl_prover [ih₁, ih₂, h₁, h₂, h₃];
  | @impR Γ Δ A B _ ih =>
    have h₁ : 𝐆𝐋 ⊢ A ⋏ Γ.conj 🡒 (insert A Γ).conj := CKFConjinsertFConj;
    have h₂ : 𝐆𝐋 ⊢ (insert B Δ).disj 🡒 B ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : 𝐆𝐋 ⊢ (A 🡒 B) ⋎ Δ.disj 🡒 (insert (A 🡒 B) Δ).disj := CAFDisjinsertFDisj;
    cl_prover [ih, h₁, h₂, h₃];
  | @boxGL Γ A _ ih =>
    have h₁ : 𝐆𝐋 ⊢ □A ⋏ (Γ ∪ Γ.box).conj 🡒 (insert (□A) (Γ ∪ Γ.box)).conj := CKFConjinsertFConj;
    have ih : 𝐆𝐋 ⊢ (insert (□A) (Γ ∪ Γ.box)).conj 🡒 A := by simpa using ih;
    have h₂ : 𝐆𝐋 ⊢ □(Γ ∪ Γ.box).conj 🡒 □(□A 🡒 A) := box_mono (by cl_prover [ih, h₁]);
    have h₃ : 𝐆𝐋 ⊢ Γ.box.conj 🡒 Γ.box.box.conj :=
      right_Fconj_intro _ _ fun B hB ↦ by
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
        obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
        exact C_trans (left_Fconj_intro hC) axiom4;
    have h₄ : 𝐆𝐋 ⊢ □Γ.conj ⋏ □Γ.box.conj 🡒 □(Γ ∪ Γ.box).conj :=
      C_trans box_and (box_mono CKFconjFconjUnion);
    have h₅ : 𝐆𝐋 ⊢ Γ.box.conj 🡒 □Γ.conj := box_conj;
    have h₆ : 𝐆𝐋 ⊢ Γ.box.box.conj 🡒 □Γ.box.conj := box_conj;
    simp only [Finset.disj_singleton];
    cl_prover [h₂, h₃, h₄, h₅, h₆, axiomL (A := A)];

/-! ### Quasi-normal extensions -/

/-- A quasi-normal extension of `GL` proves `A` if it proves `Γ` and `𝐆𝐋 ⊢ Γ.conj 🡒 A`. -/
lemma sumQuasiNormal_of_conj [DecidableEq α] {L : Logic α} {Γ : FormulaFinset α}
    (hΓ : ∀ B ∈ Γ, 𝐆𝐋 +ᴸ L ⊢ B) (h : 𝐆𝐋 ⊢ Γ.conj 🡒 A) : 𝐆𝐋 +ᴸ L ⊢ A :=
  sumQuasiNormal.of_left h ⨀ FConj_iff_forall_provable.mpr hΓ

/-! ### Completeness -/

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

theorem provability_TFAE : [
    𝐆𝐋 ⊢ A,
    ⊢ᴳ[𝐆𝐋] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A
  ].TFAE := by
  tfae_have 1 → 3 := fun h _ _ M _ ↦ sound M h;
  tfae_have 3 → 2 := fun h ↦ Gentzen.complete fun M _ x _ ↦ ⟨A, by simp, h M x⟩;
  tfae_have 2 → 1 := fun h ↦ by simpa using of_gentzen h ⨀ (by simp [Finset.conj]);
  tfae_have 3 → 4 := fun h _ _ M _ ↦ h M.toModel M.root;
  tfae_have 4 → 3 := fun h _ _ M _ x ↦ Model.forces_cone.mp <| h (M.cone x);
  tfae_finish;

theorem iff_provable_gentzen : 𝐆𝐋 ⊢ A ↔ ⊢ᴳ[𝐆𝐋] ∅ ⟹ {A} := provability_TFAE.out 1 2

omit [DecidableEq α] in
theorem iff_valid_finite :
    𝐆𝐋 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A := by
  classical
  exact provability_TFAE.out 1 3

omit [DecidableEq α] in
theorem iff_root_forces : 𝐆𝐋 ⊢ A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A := by
  classical
  exact provability_TFAE.out 1 4

end Logic.GL

end FFL.ProvabilityLogic

end
