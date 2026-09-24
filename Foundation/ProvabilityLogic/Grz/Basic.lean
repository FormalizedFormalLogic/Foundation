module

public import Foundation.ProvabilityLogic.Grz.Gentzen.Kripke
public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.ProvabilityLogic.Kripke.Soundness

/-!
# The logic `Grz`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Grz Kripke Kripke.Model Kripke.Model.World

abbrev Logic.Grz {α : Type*} : Logic α :=
  normalOf ({□A 🡒 □□A | A} ∪ {□A 🡒 A | A} ∪ {□(□(A 🡒 □A) 🡒 A) 🡒 A | A})

notation "𝐆𝐫𝐳" => Logic.Grz

namespace Logic.Grz

open normalOf

variable {α : Type*} {A : Formula α}

@[simp] lemma axiom4 : 𝐆𝐫𝐳 ⊢ □A 🡒 □□A := axm (by simp)

@[simp] lemma axiomT : 𝐆𝐫𝐳 ⊢ □A 🡒 A := axm (by simp)

@[simp] lemma axiomGrz : 𝐆𝐫𝐳 ⊢ □(□(A 🡒 □A) 🡒 A) 🡒 A := axm (by simp)

/-! ### Kripke soundness -/

section

variable {κ : Type*} [Nonempty κ] {M : Model κ α}

open Classical in
lemma forces_axiomGrz [M.IsGrz] {x : M.World} : x ⊩[M] □(□(A 🡒 □A) 🡒 A) 🡒 A := by
  intro hx;
  have : ⊢ᴳ[Grz] {□(□(A 🡒 □A) 🡒 A)} ⟹ {□A} := by
    simpa using Gentzen.boxGrz (Γ := {□(A 🡒 □A) 🡒 A}) <|
      Gentzen.wkL (Γ := insert (□(□(A 🡒 □A) 🡒 A)) {□(A 🡒 □A)}) <|
      Gentzen.boxT <| Gentzen.impL (Gentzen.union (□(A 🡒 □A))) (Gentzen.union A);
  exact validateSequent_singleton_iff.mp (Gentzen.sound M this) x (by simpa) x (Std.Refl.refl x);

theorem sound (M : Model κ α) [M.IsGrz] (h : 𝐆𝐫𝐳 ⊢ A) : M ⊧ A := by
  apply normalOf.sound _ h;
  rintro _ ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩) x;
  · exact fun h y Rxy z Ryz ↦ h z (IsTrans.trans _ _ _ Rxy Ryz);
  · exact fun h ↦ h x (Std.Refl.refl x);
  · exact forces_axiomGrz;

end

/-! ### From the sequent calculus -/

lemma of_gentzen [DecidableEq α] {S : Sequent α} (h : ⊢ᴳ[Grz] S) : 𝐆𝐫𝐳 ⊢ S.ant.conj 🡒 S.suc.disj := by
  induction h with
  | axm A => simp;
  | botL => simp only [Finset.conj_singleton]; exact efq;
  | wkL _ hΓ ih => exact C_trans (CFConjFConj_of_subset hΓ) ih;
  | wkR _ hΔ ih =>
    exact C_trans ih <| left_Fdisj_intro _ fun B hB ↦ right_Fdisj_intro _ (hΔ hB);
  | @impL Γ Δ A B _ _ ih₁ ih₂ =>
    have h₁ : 𝐆𝐫𝐳 ⊢ (insert (A 🡒 B) Γ).conj 🡒 (A 🡒 B) ⋏ Γ.conj := CinsertFConjKFConj;
    have h₂ : 𝐆𝐫𝐳 ⊢ (insert A Δ).disj 🡒 A ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : 𝐆𝐫𝐳 ⊢ B ⋏ Γ.conj 🡒 (insert B Γ).conj := CKFConjinsertFConj;
    cl_prover [ih₁, ih₂, h₁, h₂, h₃];
  | @impR Γ Δ A B _ ih =>
    have h₁ : 𝐆𝐫𝐳 ⊢ A ⋏ Γ.conj 🡒 (insert A Γ).conj := CKFConjinsertFConj;
    have h₂ : 𝐆𝐫𝐳 ⊢ (insert B Δ).disj 🡒 B ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : 𝐆𝐫𝐳 ⊢ (A 🡒 B) ⋎ Δ.disj 🡒 (insert (A 🡒 B) Δ).disj := CAFDisjinsertFDisj;
    cl_prover [ih, h₁, h₂, h₃];
  | @boxT Γ Δ A _ ih =>
    have h₁ : 𝐆𝐫𝐳 ⊢ (insert (□A) Γ).conj 🡒 □A ⋏ Γ.conj := CinsertFConjKFConj;
    have h₂ : 𝐆𝐫𝐳 ⊢ A ⋏ Γ.conj 🡒 (insert A Γ).conj := CKFConjinsertFConj;
    cl_prover [ih, h₁, h₂, axiomT (A := A)];
  | @boxGrz Γ A _ ih =>
    have h₁ : 𝐆𝐫𝐳 ⊢ □(A 🡒 □A) ⋏ Γ.box.conj 🡒 (insert (□(A 🡒 □A)) Γ.box).conj :=
      CKFConjinsertFConj;
    have ih : 𝐆𝐫𝐳 ⊢ (insert (□(A 🡒 □A)) Γ.box).conj 🡒 A := by simpa using ih;
    have h₂ : 𝐆𝐫𝐳 ⊢ □Γ.box.conj 🡒 □(□(A 🡒 □A) 🡒 A) := box_mono (by cl_prover [ih, h₁]);
    have h₃ : 𝐆𝐫𝐳 ⊢ Γ.box.conj 🡒 Γ.box.box.conj :=
      right_Fconj_intro _ _ fun B hB ↦ by
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
        obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
        exact C_trans (left_Fconj_intro hC) axiom4;
    have h₄ : 𝐆𝐫𝐳 ⊢ Γ.box.box.conj 🡒 □Γ.box.conj := box_conj;
    have h₅ : 𝐆𝐫𝐳 ⊢ □□(□(A 🡒 □A) 🡒 A) 🡒 □A := box_mono axiomGrz;
    simp only [Finset.disj_singleton];
    cl_prover [h₂, h₃, h₄, h₅, axiom4 (A := □(A 🡒 □A) 🡒 A)];

/-! ### Completeness -/

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

theorem iff_provable_gentzen : 𝐆𝐫𝐳 ⊢ A ↔ ⊢ᴳ[Grz] ∅ ⟹ {A} := by
  constructor;
  · intro h;
    apply Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, sound M h x⟩;
  · intro h;
    have : 𝐆𝐫𝐳 ⊢ (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    simpa using of_gentzen h ⨀ this;

theorem iff_valid_finite :
    𝐆𝐫𝐳 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGrz] → M ⊧ A := by
  constructor;
  · intro h _ _ M _;
    exact sound M h;
  · intro h;
    apply iff_provable_gentzen.mpr;
    apply Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, h M x⟩;

theorem iff_root_forces : 𝐆𝐫𝐳 ⊢ A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGrz] → M.root ⊩[M.toModel] A := by
  constructor;
  · intro h _ _ M _;
    exact sound M.toModel h M.root;
  · intro h;
    apply iff_valid_finite.mpr;
    intro _ _ M _ x;
    exact Model.forces_cone.mp <| h (M.cone x);

theorem provability_TFAE : [
    𝐆𝐫𝐳 ⊢ A,
    ⊢ᴳ[Grz] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGrz] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGrz] → M.root ⊩[M.toModel] A
  ].TFAE := by
  tfae_have 1 ↔ 2 := iff_provable_gentzen;
  tfae_have 1 ↔ 3 := iff_valid_finite;
  tfae_have 1 ↔ 4 := iff_root_forces;
  tfae_finish;

end Logic.Grz

end FFL.ProvabilityLogic

end
