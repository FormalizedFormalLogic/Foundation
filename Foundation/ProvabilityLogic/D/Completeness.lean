import Foundation.FirstOrder.Internal.Consistency
import Foundation.ProvabilityLogic.S.Completeness
import Foundation.Modal.Logic.D.Basic


namespace LO

section

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0
open PeanoMinus ISigma0 ISigma1 Metamath Derivation

abbrev FirstOrder.ArithmeticTheory.LocalReflection (T : ArithmeticTheory) [T.Δ₁] (P : Sentence ℒₒᵣ → Prop) := Set.image (λ σ ↦ T.provabilityPred σ ➝ σ) P

end


namespace ProvabilityLogic

open Entailment
open Modal
open FirstOrder
open Provability
open ArithmeticTheory (ProvabilityLogic)

variable {T₀ T : ArithmeticTheory} [T₀ ⪯ T] [Diagonalization T₀] [T.Δ₁] [𝗜𝚺₁ ⪯ T]
         {𝔅 : Provability T₀ T} [𝔅.HBL] [ℕ ⊧ₘ* T] [𝔅.SoundOnModel ℕ]
         {A B : Formula ℕ}

def WWW : Set (Formula ℕ) := { ∼□⊥, □□(.atom 0) ➝ □(.atom 1) }
def XXX (T : ArithmeticTheory) [T.Δ₁] := ⋃₀ Set.univ.image (λ (f : T.StandardRealization) ↦ { f A | A ∈ WWW })
lemma wwww : T + T.LocalReflection (Arithmetic.Hierarchy 𝚺 1) ≊ T + (⋃₀ Set.univ.image (λ (f : T.StandardRealization) ↦ { f A | A ∈ WWW })) := by
  simp [WWW];
  sorry

local prefix:90 "■" => T.provabilityPred

theorem provabilityLogic_PA_PAPlusSigma1LocalReflection_eq_D :
  ProvabilityLogic T (T + T.LocalReflection (Arithmetic.Hierarchy 𝚺 1)) ≊ Modal.D := by
  generalize eU : T + T.LocalReflection (Arithmetic.Hierarchy 𝚺 1) = U;
  apply Logic.iff_equal_provable_equiv.mp;
  ext A;
  suffices (∀ (f : T.StandardRealization), U ⊢!. f A) ↔ (∀ (f : T.StandardRealization), T ⊢!. f (A.dzSubformula.conj) ➝ f A) by calc
    _ ↔ ProvabilityLogic T U ⊢! A                                      := by simp [Logic.iff_provable];
    _ ↔ ∀ f : T.StandardRealization, U ⊢!. f A                         := by simp [ProvabilityLogic.provable_iff];
    _ ↔ ∀ f : T.StandardRealization, T ⊢!. f A.dzSubformula.conj ➝ f A := this
    _ ↔ ∀ f : T.StandardRealization, T ⊢!. f (A.dzSubformula.conj ➝ A) := by simp;
    _ ↔ Modal.GL ⊢! A.dzSubformula.conj ➝ A                            := GL.arithmetical_completeness_sound_iff
    _ ↔ Modal.D ⊢! A                                                   := iff_provable_D_provable_GL.symm
    _ ↔ A ∈ Modal.D                                                    := by simp [Logic.iff_provable];
  constructor;
  . intro h f;
    -- subst eU;

    let V := T + ((⋃ f : T.StandardRealization, {x | x = f (∼□⊥) ∨ x = f (□□(.atom 0) ➝ □(.atom 0))}));
    have : ∀ σ ∈ T.LocalReflection (Arithmetic.Hierarchy 𝚺 1), V ⊢!. σ := by
      rintro _ ⟨σ, hσ, rfl⟩;
      obtain ⟨π, hπ₁, hπ₂⟩ : ∃ π : ArithmeticSentence, Arithmetic.Hierarchy 𝚺 1 π ∧ T ⊢!. ■π ⭤ σ ⋎ ■⊥ := by sorry;
      replace hπ₂ : T ⊢!. (∼■⊥) ⋏ (■■π ➝ ■π) ➝ (■σ ➝ σ) := by sorry; -- FGH theorem
      replace hπ₂ : V ⊢!. (∼■⊥) ⋏ (■■π ➝ ■π) ➝ (■σ ➝ σ) := by sorry;
      apply hπ₂ ⨀ ?_
      apply K!_intro;
      . let g : T.StandardRealization := ⟨λ _ => π⟩;
        have : V ⊢!. g (∼□⊥) := by sorry;
        sorry;
      . let g : T.StandardRealization := ⟨λ _ => π⟩;
        have : V ⊢!. g (□□(.atom 0) ➝ □(.atom 0)) := by sorry;
        sorry;
    have : ∀ σ, U ⊢!. σ → V ⊢!. σ := by sorry;
    have := this _ (h f);
    sorry;
    /-
    have : ∀ σ ∈ T.LocalReflection (Arithmetic.Hierarchy 𝚺 1), T ⊢!. (A.dzSubformula.image f |>.conj) ➝ σ := by
      rintro _ ⟨σ, hσ, rfl⟩;
      obtain ⟨π, hπ₁, hπ₂⟩ : ∃ π : ArithmeticSentence, Arithmetic.Hierarchy 𝚺 1 π ∧ T ⊢!. ■π ⭤ σ ⋎ ■⊥ := by sorry;
      replace hπ₂ : T ⊢!. (∼■⊥) ⋏ (■■π ➝ ■π) ➝ (■σ ➝ σ) := by
        sorry;
      apply C!_trans ?_ hπ₂;
      suffices ∃ δ, δ ∈ (Finset.image f A.dzSubformula) ∧ T ⊢!. δ ➝ ∼■⊥ ⋏ (■■π ➝ ■π) by sorry;
      sorry;
    have := h f;
    subst eU;

    dsimp [Modal.Formula.dzSubformula];
    obtain ⟨s, hs₁, hs₂⟩ : ∃ s : Finset (ArithmeticSentence), (∀ σ ∈ s, σ ∈ T.LocalReflection (Arithmetic.Hierarchy 𝚺 1)) ∧ T ⊢!. s.conj ➝ f A := by sorry; -- DT
    apply C!_trans ?_ hs₂;
    apply right_Fconj!_intro;
    intro σ hσ;
    obtain ⟨σ, hσ, rfl⟩ := by simpa using hs₁ _ hσ;
    sorry;
    -/
  . intro h f;
    have := h f;
    have : U ⊢!. (f A.dzSubformula.conj) ➝ (f A) := by sorry;
    apply this ⨀ ?_
    suffices ∀ D ∈ A.dzSubformula, U ⊢!. f D by sorry;
    intro D hD;
    simp at hD;
    obtain ⟨s, hs, rfl⟩ := hD;
    rw [Realization.interpret.def_imp];
    sorry;

instance : ProvabilityLogic 𝗣𝗔 (𝗣𝗔 + 𝗣𝗔.LocalReflection (Arithmetic.Hierarchy 𝚺 1)) ≊ Modal.D := provabilityLogic_PA_PAPlusSigma1LocalReflection_eq_D

end ProvabilityLogic


end LO
