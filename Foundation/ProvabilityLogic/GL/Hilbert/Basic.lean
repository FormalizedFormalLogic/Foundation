module

public import Foundation.ProvabilityLogic.GL.Gentzen.Kripke
public import Foundation.ProvabilityLogic.Kripke.Cone
public import Foundation.Propositional.Entailment.Cl
public import Foundation.Meta.ClProver

/-!
# The Hilbert-style system `GL`
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Kripke Kripke.Model Kripke.Model.World

namespace GL

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
  | axiomL {A} : Derivation (□(□A 🡒 A) 🡒 □A)

inductive Hilbert (α : Type*) : Type
  | gl

end GL

notation:45 "⊢ᴴ[GL] " A:46 => Entailment.Provable GL.Hilbert.gl A

namespace GL

variable {α : Type*}

instance : Entailment (GL.Hilbert α) (Formula α) := ⟨fun _ ↦ Derivation⟩

instance : ModusPonens (GL.Hilbert.gl : GL.Hilbert α) := ⟨Derivation.mdp⟩
instance : HasAxiomImplyK (GL.Hilbert.gl : GL.Hilbert α) := ⟨Derivation.implyK⟩
instance : HasAxiomImplyS (GL.Hilbert.gl : GL.Hilbert α) := ⟨Derivation.implyS⟩
instance : HasAxiomAndInst (GL.Hilbert.gl : GL.Hilbert α) := ⟨Derivation.andIntro⟩

open Derivation in
instance : Entailment.Cl (GL.Hilbert.gl : GL.Hilbert α) where
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

lemma nec : ⊢ᴴ[GL] A → ⊢ᴴ[GL] □A := fun ⟨h⟩ ↦ ⟨Derivation.nec h⟩

@[simp] lemma axiomK : ⊢ᴴ[GL] □(A 🡒 B) 🡒 □A 🡒 □B := ⟨Derivation.axiomK⟩

@[simp] lemma axiom4 : ⊢ᴴ[GL] □A 🡒 □□A := ⟨Derivation.axiom4⟩

@[simp] lemma axiomL : ⊢ᴴ[GL] □(□A 🡒 A) 🡒 □A := ⟨Derivation.axiomL⟩

lemma box_mono (h : ⊢ᴴ[GL] A 🡒 B) : ⊢ᴴ[GL] □A 🡒 □B := axiomK ⨀ nec h

variable [DecidableEq α]

lemma box_and : ⊢ᴴ[GL] □A ⋏ □B 🡒 □(A ⋏ B) := by
  have h₁ : ⊢ᴴ[GL] □A 🡒 □(B 🡒 A ⋏ B) := box_mono and₃;
  have h₂ : ⊢ᴴ[GL] □(B 🡒 A ⋏ B) 🡒 □B 🡒 □(A ⋏ B) := axiomK;
  cl_prover [h₁, h₂];

lemma box_conj {Γ : FormulaFinset α} : ⊢ᴴ[GL] Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : ⊢ᴴ[GL] □(∅ : FormulaFinset α).conj := nec (by simp [Finset.conj]);
    exact C_of_conseq this;
  | insert A Γ _ ih =>
    have h₁ : ⊢ᴴ[GL] (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj :=
      CinsertFConjKFConj;
    have h₂ : ⊢ᴴ[GL] □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : ⊢ᴴ[GL] □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

end Hilbert

/-! ### Kripke soundness -/

namespace Hilbert

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

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

theorem sound (M : Model κ α) [M.IsGL] (h : ⊢ᴴ[GL] A) : M ⊧ A := by
  obtain ⟨d⟩ := h;
  intro x;
  induction d generalizing x with
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih => exact fun y _ ↦ ih y;
  | axiomL => exact forces_axiomL;
  | axiom4 => exact fun h y Rxy z Ryz ↦ h z (IsTrans.trans _ _ _ Rxy Ryz);
  | axiomK => exact fun h₁ h₂ y Rxy ↦ h₁ y Rxy (h₂ y Rxy);
  | _ => simp only [Axioms.Verum, Axioms.ImplyK, Axioms.ImplyS, Axioms.AndElim₁, Axioms.AndElim₂,
      Axioms.AndInst, Axioms.OrInst₁, Axioms.OrInst₂, Axioms.OrElim, Axioms.DNE]; grind;

end Hilbert

/-! ### From the sequent calculus -/

namespace Hilbert

variable {α : Type*} [DecidableEq α] {S : Sequent α}

omit [DecidableEq α] in
@[simp] lemma conj_singleton {A : Formula α} : ({A} : FormulaFinset α).conj = A := by
  simp [Finset.conj];

omit [DecidableEq α] in
@[simp] lemma disj_singleton {A : Formula α} : ({A} : FormulaFinset α).disj = A := by
  simp [Finset.disj];

lemma of_gentzen (h : ⊢ᴳ[GL] S) : ⊢ᴴ[GL] S.ant.conj 🡒 S.suc.disj := by
  induction h with
  | axm A => simp;
  | botL => simp only [conj_singleton]; exact efq;
  | wkL _ hΓ ih => exact C_trans (CFConjFConj_of_subset hΓ) ih;
  | wkR _ hΔ ih =>
    exact C_trans ih <| left_Fdisj_intro _ fun B hB ↦ right_Fdisj_intro _ (hΔ hB);
  | @impL Γ Δ A B _ _ ih₁ ih₂ =>
    have h₁ : ⊢ᴴ[GL] (insert (A 🡒 B) Γ).conj 🡒 (A 🡒 B) ⋏ Γ.conj := CinsertFConjKFConj;
    have h₂ : ⊢ᴴ[GL] (insert A Δ).disj 🡒 A ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : ⊢ᴴ[GL] B ⋏ Γ.conj 🡒 (insert B Γ).conj := CKFConjinsertFConj;
    cl_prover [ih₁, ih₂, h₁, h₂, h₃];
  | @impR Γ Δ A B _ ih =>
    have h₁ : ⊢ᴴ[GL] A ⋏ Γ.conj 🡒 (insert A Γ).conj := CKFConjinsertFConj;
    have h₂ : ⊢ᴴ[GL] (insert B Δ).disj 🡒 B ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : ⊢ᴴ[GL] (A 🡒 B) ⋎ Δ.disj 🡒 (insert (A 🡒 B) Δ).disj := CAFDisjinsertFDisj;
    cl_prover [ih, h₁, h₂, h₃];
  | @boxGL Γ A _ ih =>
    have h₁ : ⊢ᴴ[GL] □A ⋏ (Γ ∪ Γ.box).conj 🡒 (insert (□A) (Γ ∪ Γ.box)).conj := CKFConjinsertFConj;
    have ih : ⊢ᴴ[GL] (insert (□A) (Γ ∪ Γ.box)).conj 🡒 A := by simpa using ih;
    have h₂ : ⊢ᴴ[GL] □(Γ ∪ Γ.box).conj 🡒 □(□A 🡒 A) := box_mono (by cl_prover [ih, h₁]);
    have h₃ : ⊢ᴴ[GL] Γ.box.conj 🡒 Γ.box.box.conj :=
      right_Fconj_intro _ _ fun B hB ↦ by
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
        obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
        exact C_trans (left_Fconj_intro hC) axiom4;
    have h₄ : ⊢ᴴ[GL] □Γ.conj ⋏ □Γ.box.conj 🡒 □(Γ ∪ Γ.box).conj :=
      C_trans box_and (box_mono CKFconjFconjUnion);
    have h₅ : ⊢ᴴ[GL] Γ.box.conj 🡒 □Γ.conj := box_conj;
    have h₆ : ⊢ᴴ[GL] Γ.box.box.conj 🡒 □Γ.box.conj := box_conj;
    simp only [disj_singleton];
    cl_prover [h₂, h₃, h₄, h₅, h₆, axiomL (A := A)];

end Hilbert

/-! ### Completeness -/

namespace Hilbert

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

lemma iff_gentzen : ⊢ᴴ[GL] A ↔ ⊢ᴳ[GL] ∅ ⟹ {A} := by
  constructor;
  . intro h;
    apply Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, sound M h x⟩;
  . intro h;
    have : ⊢ᴴ[GL] (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    simpa using of_gentzen h ⨀ this;

theorem iff_valid_finite : ⊢ᴴ[GL] A ↔ ∀ {κ : Type u} [Nonempty κ] (M : Model κ α), [M.IsFiniteGL] → M ⊧ A := by
  constructor;
  . intro h _ _ M _;
    exact sound M h;
  . intro h;
    apply iff_gentzen.mpr;
    apply Gentzen.complete;
    intro _ _ M _ x _;
    exact ⟨A, by simp, h M x⟩;

theorem iff_root_forces : ⊢ᴴ[GL] A ↔
    ∀ {κ : Type u} [Nonempty κ] (M : RootedModel κ α), [M.IsFiniteGL] → M.root ⊩[M.toModel] A := by
  constructor;
  . intro h _ _ M _;
    exact sound M.toModel h M.root;
  . intro h;
    apply iff_valid_finite.mpr;
    intro _ _ M _ x;
    exact Model.forces_cone.mp <| h (M.cone x);

end Hilbert

end GL

end FFL.ProvabilityLogic

end
