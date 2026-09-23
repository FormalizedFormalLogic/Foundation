module

public import Foundation.ProvabilityLogic.Gentzen.GL.Kripke
public import Foundation.ProvabilityLogic.Logic.Basic
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

end GL

abbrev Logic.GL {α : Type*} : Logic α := { A | Nonempty (GL.Derivation A) }

notation "𝐆𝐋" => Logic.GL

namespace Logic.GL

variable {α : Type*}

lemma provable_iff {A : Formula α} : 𝐆𝐋 ⊢ A ↔ Nonempty (GL.Derivation A) := Logic.provable_iff

lemma mdp {A B : Formula α} : A 🡒 B ∈ 𝐆𝐋 → A ∈ 𝐆𝐋 → B ∈ 𝐆𝐋 := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨.mdp d₁ d₂⟩

instance : ModusPonens (𝐆𝐋 : Logic α) := ⟨fun h₁ h₂ ↦ ⟨mdp h₁.down h₂.down⟩⟩
instance : HasAxiomImplyK (𝐆𝐋 : Logic α) := ⟨⟨⟨.implyK⟩⟩⟩
instance : HasAxiomImplyS (𝐆𝐋 : Logic α) := ⟨⟨⟨.implyS⟩⟩⟩
instance : HasAxiomAndInst (𝐆𝐋 : Logic α) := ⟨⟨⟨.andIntro⟩⟩⟩

instance : Entailment.Cl (𝐆𝐋 : Logic α) where
  verum! := ⟨⟨.verum⟩⟩
  and₁! := ⟨⟨.andElimL⟩⟩
  and₂! := ⟨⟨.andElimR⟩⟩
  or₁! := ⟨⟨.orIntroL⟩⟩
  or₂! := ⟨⟨.orIntroR⟩⟩
  or₃! := ⟨⟨.orElim⟩⟩
  dne! := ⟨⟨.dne⟩⟩

section

variable {A B : Formula α}

lemma nec : 𝐆𝐋 ⊢ A → 𝐆𝐋 ⊢ □A := fun h ↦ provable_iff.mpr <| (provable_iff.mp h).map .nec

@[simp] lemma axiomK : 𝐆𝐋 ⊢ □(A 🡒 B) 🡒 □A 🡒 □B := provable_iff.mpr ⟨.axiomK⟩

@[simp] lemma axiom4 : 𝐆𝐋 ⊢ □A 🡒 □□A := provable_iff.mpr ⟨.axiom4⟩

@[simp] lemma axiomL : 𝐆𝐋 ⊢ □(□A 🡒 A) 🡒 □A := provable_iff.mpr ⟨.axiomL⟩

lemma box_mono (h : 𝐆𝐋 ⊢ A 🡒 B) : 𝐆𝐋 ⊢ □A 🡒 □B := axiomK ⨀ nec h

variable [DecidableEq α]

lemma box_and : 𝐆𝐋 ⊢ □A ⋏ □B 🡒 □(A ⋏ B) := by
  have h₁ : 𝐆𝐋 ⊢ □A 🡒 □(B 🡒 A ⋏ B) := box_mono and₃;
  have h₂ : 𝐆𝐋 ⊢ □(B 🡒 A ⋏ B) 🡒 □B 🡒 □(A ⋏ B) := axiomK;
  cl_prover [h₁, h₂];

lemma box_conj {Γ : FormulaFinset α} : 𝐆𝐋 ⊢ Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : 𝐆𝐋 ⊢ □(∅ : FormulaFinset α).conj := nec (by simp [Finset.conj]);
    exact C_of_conseq this;
  | insert A Γ _ ih =>
    have h₁ : 𝐆𝐋 ⊢ (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj :=
      CinsertFConjKFConj;
    have h₂ : 𝐆𝐋 ⊢ □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : 𝐆𝐋 ⊢ □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

end

/-! ### Kripke soundness -/

section

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

theorem sound (M : Model κ α) [M.IsGL] (h : 𝐆𝐋 ⊢ A) : M ⊧ A := by
  obtain ⟨d⟩ := provable_iff.mp h;
  clear h;
  intro x;
  induction d generalizing x with
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih => exact fun y _ ↦ ih y;
  | axiomL => exact forces_axiomL;
  | axiom4 => exact fun h y Rxy z Ryz ↦ h z (IsTrans.trans _ _ _ Rxy Ryz);
  | axiomK => exact fun h₁ h₂ y Rxy ↦ h₁ y Rxy (h₂ y Rxy);
  | _ => simp only [Axioms.Verum, Axioms.ImplyK, Axioms.ImplyS, Axioms.AndElim₁, Axioms.AndElim₂,
      Axioms.AndInst, Axioms.OrInst₁, Axioms.OrInst₂, Axioms.OrElim, Axioms.DNE]; grind;

end

/-! ### From the sequent calculus -/

section

variable {α : Type*} [DecidableEq α] {S : Sequent α}

omit [DecidableEq α] in
@[simp] lemma conj_singleton {A : Formula α} : ({A} : FormulaFinset α).conj = A := by
  simp [Finset.conj];

omit [DecidableEq α] in
@[simp] lemma disj_singleton {A : Formula α} : ({A} : FormulaFinset α).disj = A := by
  simp [Finset.disj];

lemma of_gentzen (h : ⊢ᴳ[GL] S) : 𝐆𝐋 ⊢ S.ant.conj 🡒 S.suc.disj := by
  induction h with
  | axm A => simp;
  | botL => simp only [conj_singleton]; exact efq;
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
    simp only [disj_singleton];
    cl_prover [h₂, h₃, h₄, h₅, h₆, axiomL (A := A)];

end

end Logic.GL

end FFL.ProvabilityLogic

end
