module

public import Foundation.ProvabilityLogic.Grz.Gentzen.Kripke
public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.Propositional.Entailment.Cl
public import Foundation.Meta.ClProver

/-!
# The Hilbert-style system `Grz`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Kripke Kripke.Model Kripke.Model.World

namespace Grz

variable {α : Type*}

inductive Derivation : Formula α → Type _
  | mdp {A B} : Derivation (A 🡒 B) → Derivation A → Derivation B
  | nec {A} : Derivation A → Derivation (□A)
  | verum : Derivation Axioms.Verum
  | implyK {A B} : Derivation (Axioms.ImplyK A B)
  | implyS {A B C} : Derivation (Axioms.ImplyS A B C)
  | andElimL {A B} : Derivation (Axioms.AndElim₁ A B)
  | andElimR {A B} : Derivation (Axioms.AndElim₂ A B)
  | andIntro {A B} : Derivation (Axioms.AndInst A B)
  | orIntroL {A B} : Derivation (Axioms.OrInst₁ A B)
  | orIntroR {A B} : Derivation (Axioms.OrInst₂ A B)
  | orElim {A B C} : Derivation (Axioms.OrElim A B C)
  | dne {A} : Derivation (Axioms.DNE A)
  | axiomK {A B} : Derivation (□(A 🡒 B) 🡒 □A 🡒 □B)
  | axiom4 {A} : Derivation (□A 🡒 □□A)
  | axiomT {A} : Derivation (□A 🡒 A)
  | axiomGrz {A} : Derivation (□(□(A 🡒 □A) 🡒 A) 🡒 A)

inductive Hilbert (α : Type*) : Type
  | grz

end Grz

notation:45 "⊢ᴴ[Grz] " A:46 => Entailment.Provable Grz.Hilbert.grz A

namespace Grz

variable {α : Type*}

instance : Entailment (Grz.Hilbert α) (Formula α) := ⟨fun _ ↦ Derivation⟩

instance : ModusPonens (Grz.Hilbert.grz : Grz.Hilbert α) := ⟨Derivation.mdp⟩
instance : HasAxiomImplyK (Grz.Hilbert.grz : Grz.Hilbert α) := ⟨Derivation.implyK⟩
instance : HasAxiomImplyS (Grz.Hilbert.grz : Grz.Hilbert α) := ⟨Derivation.implyS⟩
instance : HasAxiomAndInst (Grz.Hilbert.grz : Grz.Hilbert α) := ⟨Derivation.andIntro⟩

open Derivation in
instance : Entailment.Cl (Grz.Hilbert.grz : Grz.Hilbert α) where
  verum! := verum
  and₁! := andElimL
  and₂! := andElimR
  and₃! := andIntro
  or₁! := orIntroL
  or₂! := orIntroR
  or₃! := orElim
  dne! := dne

namespace Hilbert

variable {A B : Formula α}

lemma nec : ⊢ᴴ[Grz] A → ⊢ᴴ[Grz] □A := fun ⟨h⟩ ↦ ⟨Derivation.nec h⟩

@[simp] lemma axiomK : ⊢ᴴ[Grz] □(A 🡒 B) 🡒 □A 🡒 □B := ⟨Derivation.axiomK⟩

@[simp] lemma axiom4 : ⊢ᴴ[Grz] □A 🡒 □□A := ⟨Derivation.axiom4⟩

@[simp] lemma axiomT : ⊢ᴴ[Grz] □A 🡒 A := ⟨Derivation.axiomT⟩

@[simp] lemma axiomGrz : ⊢ᴴ[Grz] □(□(A 🡒 □A) 🡒 A) 🡒 A := ⟨Derivation.axiomGrz⟩

lemma box_mono (h : ⊢ᴴ[Grz] A 🡒 B) : ⊢ᴴ[Grz] □A 🡒 □B := axiomK ⨀ nec h

variable [DecidableEq α]

lemma box_and : ⊢ᴴ[Grz] □A ⋏ □B 🡒 □(A ⋏ B) := by
  have h₁ : ⊢ᴴ[Grz] □A 🡒 □(B 🡒 A ⋏ B) := box_mono and₃;
  have h₂ : ⊢ᴴ[Grz] □(B 🡒 A ⋏ B) 🡒 □B 🡒 □(A ⋏ B) := axiomK;
  cl_prover [h₁, h₂];

lemma box_conj {Γ : FormulaFinset α} : ⊢ᴴ[Grz] Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : ⊢ᴴ[Grz] □(∅ : FormulaFinset α).conj := nec (by simp [Finset.conj]);
    exact C_of_conseq this;
  | insert A Γ _ ih =>
    have h₁ : ⊢ᴴ[Grz] (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj :=
      CinsertFConjKFConj;
    have h₂ : ⊢ᴴ[Grz] □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : ⊢ᴴ[Grz] □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

end Hilbert

/-! ### Kripke soundness -/

namespace Hilbert

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

open Classical in
lemma forces_axiomGrz [M.IsGrz] {x : M.World} : x ⊩[M] □(□(A 🡒 □A) 🡒 A) 🡒 A := by
  intro hx;
  have : ⊢ᴳ[Grz] {□(□(A 🡒 □A) 🡒 A)} ⟹ {□A} := by
    simpa using Gentzen.boxGrz (Γ := {□(A 🡒 □A) 🡒 A}) <|
      Gentzen.wkL (Γ := insert (□(□(A 🡒 □A) 🡒 A)) {□(A 🡒 □A)}) <|
      Gentzen.boxT <| Gentzen.impL (Gentzen.union (□(A 🡒 □A))) (Gentzen.union A);
  exact validateSequent_singleton_iff.mp (Gentzen.sound M this) x (by simpa) x (Std.Refl.refl x);

theorem sound (M : Model κ α) [M.IsGrz] (h : ⊢ᴴ[Grz] A) : M ⊧ A := by
  obtain ⟨d⟩ := h;
  intro x;
  induction d generalizing x with
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih => exact fun y _ ↦ ih y;
  | axiomGrz => exact forces_axiomGrz;
  | axiomT => exact fun h ↦ h x (Std.Refl.refl x);
  | axiom4 => exact fun h y Rxy z Ryz ↦ h z (IsTrans.trans _ _ _ Rxy Ryz);
  | axiomK => exact fun h₁ h₂ y Rxy ↦ h₁ y Rxy (h₂ y Rxy);
  | _ => simp only [Axioms.Verum, Axioms.ImplyK, Axioms.ImplyS, Axioms.AndElim₁, Axioms.AndElim₂,
      Axioms.AndInst, Axioms.OrInst₁, Axioms.OrInst₂, Axioms.OrElim, Axioms.DNE]; grind;

end Hilbert

/-! ### From the sequent calculus -/

namespace Hilbert

variable {α : Type*} [DecidableEq α] {S : Sequent α}

lemma of_gentzen (h : ⊢ᴳ[Grz] S) : ⊢ᴴ[Grz] S.ant.conj 🡒 S.suc.disj := by
  induction h with
  | axm A => simp;
  | botL => simp only [Finset.conj_singleton]; exact efq;
  | wkL _ hΓ ih => exact C_trans (CFConjFConj_of_subset hΓ) ih;
  | wkR _ hΔ ih =>
    exact C_trans ih <| left_Fdisj_intro _ fun B hB ↦ right_Fdisj_intro _ (hΔ hB);
  | @impL Γ Δ A B _ _ ih₁ ih₂ =>
    have h₁ : ⊢ᴴ[Grz] (insert (A 🡒 B) Γ).conj 🡒 (A 🡒 B) ⋏ Γ.conj := CinsertFConjKFConj;
    have h₂ : ⊢ᴴ[Grz] (insert A Δ).disj 🡒 A ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : ⊢ᴴ[Grz] B ⋏ Γ.conj 🡒 (insert B Γ).conj := CKFConjinsertFConj;
    cl_prover [ih₁, ih₂, h₁, h₂, h₃];
  | @impR Γ Δ A B _ ih =>
    have h₁ : ⊢ᴴ[Grz] A ⋏ Γ.conj 🡒 (insert A Γ).conj := CKFConjinsertFConj;
    have h₂ : ⊢ᴴ[Grz] (insert B Δ).disj 🡒 B ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : ⊢ᴴ[Grz] (A 🡒 B) ⋎ Δ.disj 🡒 (insert (A 🡒 B) Δ).disj := CAFDisjinsertFDisj;
    cl_prover [ih, h₁, h₂, h₃];
  | @boxT Γ Δ A _ ih =>
    have h₁ : ⊢ᴴ[Grz] (insert (□A) Γ).conj 🡒 □A ⋏ Γ.conj := CinsertFConjKFConj;
    have h₂ : ⊢ᴴ[Grz] A ⋏ Γ.conj 🡒 (insert A Γ).conj := CKFConjinsertFConj;
    cl_prover [ih, h₁, h₂, axiomT (A := A)];
  | @boxGrz Γ A _ ih =>
    have h₁ : ⊢ᴴ[Grz] □(A 🡒 □A) ⋏ Γ.box.conj 🡒 (insert (□(A 🡒 □A)) Γ.box).conj :=
      CKFConjinsertFConj;
    have ih : ⊢ᴴ[Grz] (insert (□(A 🡒 □A)) Γ.box).conj 🡒 A := by simpa using ih;
    have h₂ : ⊢ᴴ[Grz] □Γ.box.conj 🡒 □(□(A 🡒 □A) 🡒 A) := box_mono (by cl_prover [ih, h₁]);
    have h₃ : ⊢ᴴ[Grz] Γ.box.conj 🡒 Γ.box.box.conj :=
      right_Fconj_intro _ _ fun B hB ↦ by
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
        obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
        exact C_trans (left_Fconj_intro hC) axiom4;
    have h₄ : ⊢ᴴ[Grz] Γ.box.box.conj 🡒 □Γ.box.conj := box_conj;
    have h₅ : ⊢ᴴ[Grz] □□(□(A 🡒 □A) 🡒 A) 🡒 □A := box_mono axiomGrz;
    simp only [Finset.disj_singleton];
    cl_prover [h₂, h₃, h₄, h₅, axiom4 (A := □(A 🡒 □A) 🡒 A)];

end Hilbert

/-! ### Completeness -/

namespace Hilbert

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

lemma iff_gentzen : ⊢ᴴ[Grz] A ↔ ⊢ᴳ[Grz] ∅ ⟹ {A} := by
  constructor;
  . intro h;
    apply Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, sound M h x⟩;
  . intro h;
    have : ⊢ᴴ[Grz] (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    simpa using of_gentzen h ⨀ this;

theorem iff_valid_finite :
    ⊢ᴴ[Grz] A ↔ ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGrz] → M ⊧ A := by
  constructor;
  . intro h _ _ M _;
    exact sound M h;
  . intro h;
    apply iff_gentzen.mpr;
    apply Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, h M x⟩;

theorem iff_root_forces : ⊢ᴴ[Grz] A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGrz] → M.root ⊩[M.toModel] A := by
  constructor;
  . intro h _ _ M _;
    exact sound M.toModel h M.root;
  . intro h;
    apply iff_valid_finite.mpr;
    intro _ _ M _ x;
    exact Model.forces_cone.mp <| h (M.cone x);

end Hilbert

end Grz

end FFL.ProvabilityLogic

end
