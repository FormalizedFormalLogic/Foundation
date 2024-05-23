import Logic.Logic.HilbertStyle.Basic
import Logic.Logic.HilbertStyle.Supplemental
import Logic.Propositional.Superintuitionistic.Formula
import Logic.Propositional.Superintuitionistic.Axioms

namespace LO.Propositional.Superintuitionistic

variable {α : Type u} [DecidableEq α]

inductive Deduction (Λ : AxiomSet α) : Formula α → Type _
  | eaxm {p}       : p ∈ Λ → Deduction Λ p
  | mdp {p q} : Deduction Λ (p ⟶ q) → Deduction Λ p → Deduction Λ q
  | verum          : Deduction Λ $ ⊤
  | imply₁ p q     : Deduction Λ $ p ⟶ q ⟶ p
  | imply₂ p q r   : Deduction Λ $ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  | conj₁ p q      : Deduction Λ $ p ⋏ q ⟶ p
  | conj₂ p q      : Deduction Λ $ p ⋏ q ⟶ q
  | conj₃ p q      : Deduction Λ $ p ⟶ q ⟶ p ⋏ q
  | disj₁ p q      : Deduction Λ $ p ⟶ p ⋎ q
  | disj₂ p q      : Deduction Λ $ q ⟶ p ⋎ q
  | disj₃ p q r    : Deduction Λ $ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)

instance : System (Formula α) (AxiomSet α) := ⟨Deduction⟩

open Deduction

instance : System.Minimal (Λ : AxiomSet α) where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  conj₁ := conj₁
  conj₂ := conj₂
  conj₃ := conj₃
  disj₁ := disj₁
  disj₂ := disj₂
  disj₃ := disj₃

instance intuitionistic_of_subset_efq (hEFQ : 𝐄𝐅𝐐 ⊆ Λ := by assumption) : System.Intuitionistic (Λ : AxiomSet α) where
  efq _ := eaxm $ Set.mem_of_subset_of_mem hEFQ (by simp);

instance : System.Intuitionistic (𝐄𝐅𝐐 : AxiomSet α) := intuitionistic_of_subset_efq (by rfl)


instance classical_of_subset_dne (hDNE : 𝐃𝐍𝐄 ⊆ Λ := by assumption) : System.Classical (Λ : AxiomSet α) where
  dne _ := eaxm $ Set.mem_of_subset_of_mem hDNE (by simp);

instance : System.Classical (𝐃𝐍𝐄 : AxiomSet α) := classical_of_subset_dne (by rfl)


open System

lemma reducible_efq_dne : (𝐄𝐅𝐐 : AxiomSet α) ≤ₛ 𝐃𝐍𝐄 := by
  rintro p hp;
  simp [System.theory];
  induction hp.some with
  | eaxm h =>
    obtain ⟨q, hq⟩ := by simpa [axiomEFQ] using h;
    subst hq;
    apply efq!;
  | mdp h₁ h₂ ih₁ ih₂ => exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
  | _ => simp;

variable {p : Formula α}

theorem iff_provable_dn_efq_dne_provable: (𝐄𝐅𝐐 ⊢! ~~p) ↔ (𝐃𝐍𝐄 ⊢! p) := by
  constructor;
  . intro d; exact dne'! $ reducible_efq_dne d;
  . intro d;
    induction d.some with
    | eaxm h =>
      obtain ⟨q, hq⟩ := by simpa [axiomDNE] using h;
      subst hq;
      exact dn_collect_imply'! $ contra₀'! $ dni!;
    | @mdp p q h₁ h₂ ih₁ ih₂ =>
      exact (dn_distribute_imply'! $ ih₁ ⟨h₁⟩) ⨀ ih₂ ⟨h₂⟩;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : (𝐄𝐅𝐐 ⊢! ~p) ↔ (𝐃𝐍𝐄 ⊢! ~p) := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end LO.Propositional.Superintuitionistic
