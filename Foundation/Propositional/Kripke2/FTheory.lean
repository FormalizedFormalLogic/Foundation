import Foundation.Propositional.Hilbert.Corsi.Deduction
import Foundation.Propositional.Kripke2.Basic

namespace LO.Propositional

open LO.Entailment (disjunctive)
open LO.Propositional.Entailment.Corsi
open Formula

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

namespace Entailment.Corsi

variable [DecidableEq α]
variable [Entailment.VF 𝓢]

variable {φ ψ : Formula α}

lemma insert_LConj {Γ : List (Formula α)} : 𝓢 ⊢ φ ⋏ Γ.conj₂ ➝ (φ :: Γ).conj₂ := by
  match Γ with
  | [] => simp [List.conj₂];
  | γ :: Γ =>
    apply greedy;
    . apply Entailment.and₁!;
    . apply Entailment.and₂!;

@[simp, grind .] lemma conjconj {Γ : Finset (Formula α)} : 𝓢 ⊢ (Γ.conj) ➝ Γ.toList.conj₂ := by simp [Finset.conj];

lemma C_replace_both (h : 𝓢 ⊢ φ ➝ ψ) (h₁ : 𝓢 ⊢ φ' ➝ φ) (h₂ : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ' ➝ ψ' := by
  apply C_trans h₁;
  apply C_trans ?_ h₂;
  apply h;

@[grind <=]
lemma CKK_right_replace (h : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ ⋏ ψ ➝ φ ⋏ ψ' := by
  apply greedy;
  . simp;
  . apply C_trans ?_ h;
    simp;

lemma of_mem {Γ : List (Formula α)} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ he ih =>
    simp [List.conj₂_cons_nonempty he];
    simp at h;
    rcases h with rfl | h;
    . simp;
    . apply C_trans ?_ $ ih h;
      simp;
  | _ => simp_all;

lemma FConj_of_mem {Γ : Finset (Formula α)} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ φ := by
  apply of_mem;
  simpa using h;

lemma LConj₂Conj₂_of_provable {Γ Δ : List (Formula α)} (h : ∀ δ ∈ Δ, 𝓢 ⊢ Γ.conj₂ ➝ δ) : 𝓢 ⊢ Γ.conj₂ ➝ Δ.conj₂ := by
  induction Δ using List.induction_with_singleton with
  | hnil => apply af; simp;
  | hsingle φ =>
    apply h;
    simp;
  | hcons ψ Δ he ih =>
    simp [List.conj₂_cons_nonempty he];
    simp at h;
    apply greedy;
    . apply h.1;
    . apply ih h.2;

lemma LConj₂Conj₂_of_subset {Γ Δ : List (Formula α)} (h : ∀ φ, φ ∈ Δ → φ ∈ Γ) : 𝓢 ⊢ Γ.conj₂ ➝ Δ.conj₂ := by
  apply LConj₂Conj₂_of_provable;
  intro δ hδ;
  apply of_mem $ h δ hδ;

lemma CFConjFConj_of_subset {Γ Δ : Finset (Formula α)} (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := by
  apply LConj₂Conj₂_of_subset;
  simpa;

lemma FConj₂_of_LConj {Γ : List (Formula α)} : 𝓢 ⊢ Γ.conj₂ ➝ Γ.toFinset.conj := by
  apply LConj₂Conj₂_of_provable;
  intro γ hγ;
  apply of_mem;
  simpa using hγ;

lemma insert_FConj {Γ : Finset (Formula α)} : 𝓢 ⊢ φ ⋏ Γ.conj ➝ (insert φ Γ).conj := by
  apply C_replace_both $ insert_LConj;
  . show 𝓢 ⊢ φ ⋏ Γ.conj ➝ φ ⋏ ⋀Γ.toList;
    apply CKK_right_replace;
    simp;
  . show 𝓢 ⊢ ⋀(φ :: Γ.toList) ➝ (insert φ Γ).conj;
    apply C_trans FConj₂_of_LConj;
    rw [show (φ :: Γ.toList).toFinset = insert φ Γ by simp];
    exact impId;

lemma CFConjFConj_of_provable {Γ Δ : Finset (Formula α)} (h : ∀ δ ∈ Δ, 𝓢 ⊢ Γ.conj ➝ δ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := by
  apply LConj₂Conj₂_of_provable;
  intro δ hδ;
  apply C_trans ?_ $ h δ ?_;
  . exact impId;
  . simpa using hδ;

lemma Lgreedy {Γ : List (Formula α)} (h : ∀ γ ∈ Γ, 𝓢 ⊢ φ ➝ γ) : 𝓢 ⊢ φ ➝ Γ.conj₂ := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply af; simp;
  | hsingle ψ => apply h; simp;
  | hcons ψ Δ he ih =>
    simp [List.conj₂_cons_nonempty he];
    simp at h;
    apply greedy;
    . apply h.1;
    . apply ih h.2;

lemma Fgreedy {Γ : Finset (Formula α)} (h : ∀ γ ∈ Γ, 𝓢 ⊢ φ ➝ γ) : 𝓢 ⊢ φ ➝ Γ.conj := by
  apply Lgreedy;
  intro γ hγ;
  apply h γ;
  simpa using hγ;

end Entailment.Corsi


structure FTheory (L : Logic ℕ) where
  protected theory : FormulaSet ℕ
  protected no_bot : ⊥ ∉ theory
  protected andIR : ∀ {φ ψ}, φ ∈ theory → ψ ∈ theory → φ ⋏ ψ ∈ theory
  protected imp_closed : ∀ {φ ψ}, L ⊢ φ ➝ ψ → φ ∈ theory → ψ ∈ theory
  protected L_subset : L ⊆ theory


namespace FTheory

attribute [simp] FTheory.no_bot
attribute [grind <=] FTheory.andIR FTheory.imp_closed

variable {T : FTheory L} {φ ψ χ : Formula ℕ}

@[simp, grind <=]
lemma mem_of_provable [Entailment.HasAxiomVerum L] [Entailment.AFortiori L] (hφ : L ⊢ φ) : φ ∈ T.theory := by
  apply T.imp_closed (φ := ⊤) $ af hφ;
  apply T.L_subset;
  apply Logic.iff_provable.mp;
  simp;

lemma mem_trans [Entailment.HasAxiomI L] (h₁ : φ ➝ ψ ∈ T.theory) (h₂ : ψ ➝ χ ∈ T.theory) : φ ➝ χ ∈ T.theory := by
  apply T.imp_closed (axiomI (ψ := ψ));
  apply T.andIR h₁ h₂;

@[grind <=]
lemma mem_orIntroL [Entailment.HasAxiomOrInst L] (hφ : φ ∈ T.theory) : φ ⋎ ψ ∈ T.theory := by
  apply T.imp_closed (φ := φ);
  . exact orIntroL;
  . assumption;

@[grind <=]
lemma mem_orIntroR [Entailment.HasAxiomOrInst L] (hψ : ψ ∈ T.theory) : φ ⋎ ψ ∈ T.theory := by
  apply T.imp_closed (φ := ψ);
  . exact orIntroR;
  . assumption;

open Hilbert.Corsi in
lemma iff_mem_CorsiDeducible {T : FTheory (Hilbert.Corsi Ax)} : φ ∈ T.theory ↔ Deduction Ax T.theory φ := by
  constructor;
  . intro hφ;
    apply Deduction.ctx hφ;
  . intro h; induction h <;> grind

lemma mem_greedy [Entailment.HasAxiomC L] (h₁ : χ ➝ φ ∈ T.theory) (h₂ : χ ➝ ψ ∈ T.theory) : χ ➝ φ ⋏ ψ ∈ T.theory := by
  apply T.imp_closed axiomC;
  apply T.andIR h₁ h₂;

lemma mem_LGreedy {Γ : List _} [Entailment.F L] (h : ∀ γ ∈ Γ, φ ➝ γ ∈ T.theory) : φ ➝ Γ.conj₂ ∈ T.theory := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply T.mem_of_provable; apply af; simp;
  | hsingle ψ => apply h; simp;
  | hcons ψ Δ he ih =>
    simp [List.conj₂_cons_nonempty he];
    simp at h;
    apply mem_greedy
    . apply h.1;
    . apply ih h.2;

lemma mem_FGreedy {Γ : Finset _} [Entailment.F L] (h : ∀ γ ∈ Γ, φ ➝ γ ∈ T.theory) : φ ➝ Finset.conj Γ ∈ T.theory := by
  apply mem_LGreedy;
  intro γ hγ;
  apply h;
  simpa using hγ;

end FTheory


variable {L : Logic ℕ}

structure PrimeFTheory (L : Logic ℕ) extends FTheory L where
  protected prime : ∀ {φ ψ}, φ ⋎ ψ ∈ theory → φ ∈ theory ∨ ψ ∈ theory

namespace FTheory.lindenbaum

open Classical

variable {φ ψ χ ξ γ δ : Formula ℕ} {i j : ℕ} {T : PrimeFTheory L} {hT : χ ➝ ξ ∉ T.theory}

def construction (T : PrimeFTheory L) (hT : χ ➝ ξ ∉ T.theory) : ℕ → Set (Formula ℕ)
  | 0 => { δ | χ ➝ δ ∈ T.theory }
  | i + 1 =>
    match (ofNat i) with
    | some δ =>
      letI T' := construction T hT i
      if ∀ Γ : Finset (Formula _), ↑Γ ⊆ T' → Finset.conj (insert δ Γ) ➝ ξ ∉ T.theory then insert δ T'
      else T'
    | none => construction T hT i

def construction_omega (T : PrimeFTheory L) (hT : χ ➝ ξ ∉ T.theory) : Set (Formula ℕ) := ⋃ i, construction T hT i


lemma subset_construction_succ : construction T hT i ⊆ construction T hT (i + 1) := by
  dsimp [construction];
  split;
  . split <;> tauto;
  . tauto;

lemma subset_construction_add : construction T hT i ⊆ construction T hT (i + j) := by
  induction j with
  | zero => simp;
  | succ j ih =>
    trans construction T hT (i + j);
    . apply ih;
    . apply subset_construction_succ;

lemma subset_construction_mono (hij : i ≤ j) : construction T hT i ⊆ construction T hT j := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hij;
  apply subset_construction_add;


lemma mem_construction_of_mem_construction_omega (hφ : φ ∈ construction_omega T hT) : φ ∈ (construction T hT (toNat φ + 1)) := by
  simp only [construction_omega, Set.mem_iUnion] at hφ;
  obtain ⟨i, hi⟩ := hφ;
  induction i with
  | zero => apply subset_construction_mono (by omega) hi;
  | succ i ih =>
    apply ih;
    dsimp [construction] at hi;
    repeat split at hi;
    . simp at hi;
      rcases hi with rfl | h;
      .
        sorry;
      . assumption;
    . assumption;
    . assumption;


variable [Entailment.F L]


lemma iff_mem_omega_construction : φ ∈ construction_omega T hT ↔
  (χ ➝ φ ∈ T.theory) ∨
  (∀ Γ : Finset (Formula _), ↑Γ ⊆ (construction T hT (toNat φ)) → Finset.conj (insert φ Γ) ➝ ξ ∉ T.theory) := by
  simp only [construction_omega, Set.mem_iUnion];
  constructor;
  . rintro ⟨i, hi⟩;
    sorry;
  . contrapose!;
    intro h;
    constructor;
    . simpa [construction] using h 0;
    . have := h ((toNat φ) + 1);
      simp [construction, Formula.ofNat_toNat] at this;
      split_ifs at this <;> grind;

lemma iff_not_mem_omega_construction : φ ∉ construction_omega T hT ↔
  (χ ➝ φ ∉ T.theory) ∧
  (∃ Γ : Finset (Formula _), ↑Γ ⊆ (construction T hT (toNat φ)) ∧ Finset.conj (insert φ Γ) ➝ ξ ∈ T.theory) := by
  apply Iff.trans iff_mem_omega_construction.not;
  grind;

lemma not_mem_zero_of_not_mem_construction_omega (h : φ ∉ construction_omega T hT) : χ ➝ φ ∉ T.theory := by
  contrapose! h;
  apply iff_mem_omega_construction.mpr;
  tauto;

lemma construction_consistency (i : ℕ) : ∀ Γ, ↑Γ ⊆ construction T hT i → Finset.conj Γ ➝ ξ ∉ T.theory := by
  intro Γ hΓ;
  induction i with
  | zero =>
    by_contra hC;
    apply hT;
    apply T.mem_trans ?_ hC;
    apply T.mem_FGreedy
    apply hΓ;
  | succ i ih =>
    dsimp [construction] at hΓ;
    split at hΓ;
    . split_ifs at hΓ with h;
      . rename_i γ hγ;
        by_contra hC;
        apply h (Γ.erase γ);
        . simpa;
        . apply T.mem_trans ?_ hC;
          apply T.mem_of_provable;
          apply CFConjFConj_of_subset;
          apply Finset.insert_erase_subset;
      . apply ih;
        assumption;
    . apply ih;
      assumption;

lemma not_mem_construction_omega (h : γ ➝ ξ ∈ T.theory) : γ ∉ construction_omega T hT := by
  suffices ∀ i, γ ∉ construction T hT i by simpa [construction_omega];
  by_contra! hC;
  obtain ⟨i, hi⟩ := hC;
  induction i with
  | zero => apply hT $ T.mem_trans hi h;
  | succ i ih =>
    dsimp [construction] at hi;
    split at hi;
    . split_ifs at hi with h;
      . apply h ∅ (by tauto);
        suffices γ ➝ ξ ∈ T.theory by
          simp only [insert_empty_eq, Finset.conj_singleton];
          grind;
        assumption;
      . contradiction;
    . contradiction;

lemma construction_omega_noBot : ⊥ ∉ (construction_omega T hT) := by
  apply iff_not_mem_omega_construction.mpr;
  constructor;
  . by_contra hC;
    apply hT $ T.mem_trans hC ?_;
    apply T.mem_of_provable;
    simp;
  . use ∅;
    simp;

lemma mem_construction_omega_of_exists (h : ∃ i, φ ∈ construction T hT i) : φ ∈ construction_omega T hT := by
  simpa [construction_omega];

lemma construction_omega_andClosed :
  letI U := construction_omega T hT
  φ ∈ U → ψ ∈ U → φ ⋏ ψ ∈ U := by
  rintro hφ hψ;
  apply mem_construction_omega_of_exists;
  use (toNat (φ ⋏ ψ)) + 1;
  simp only [construction, Formula.ofNat_toNat];
  split_ifs with h;
  . tauto;
  . exfalso;
    push_neg at h;
    obtain ⟨Γ, hΓ, h⟩ := h;
    replace h : (Γ ∪ {φ, ψ}).conj ➝ ξ ∈ T.theory := by
      apply T.mem_trans ?_ h;
      apply T.mem_of_provable;
      apply CFConjFConj_of_provable;
      intro γ hγ;
      simp at hγ;
      rcases hγ with rfl | hγ;
      . apply greedy <;> . apply FConj_of_mem; grind;
      . apply FConj_of_mem;
        grind;
    apply construction_consistency (hT := hT) (toNat (φ ⋏ ψ)) (Γ := Γ ∪ {φ, ψ}) ?_ h;
    intro γ;
    suffices γ = φ ∨ γ = ψ ∨ γ ∈ Γ → γ ∈ construction T hT (toNat (φ ⋏ ψ)) by simpa;
    rintro (rfl | rfl | hγ);
    case inr.inr => apply hΓ; assumption;
    all_goals
    . apply subset_construction_mono (i := (toNat γ) + 1);
      . apply Nat.succ_le_of_lt; simp;
      . apply mem_construction_of_mem_construction_omega;
        assumption;

lemma construction_omega_impClosed :
  letI U := construction_omega T hT
  L ⊢ φ ➝ ψ → φ ∈ U → ψ ∈ U := by
  rintro hφψ hφ;
  by_contra hψ;
  obtain ⟨hψ, Γ, hΓ₁, hΓ₂⟩ := iff_not_mem_omega_construction.mp hψ;
  have H : (insert φ Γ).conj ➝ ξ ∈ T.theory := T.mem_trans ?_ hΓ₂;
  . rcases iff_mem_omega_construction.mp hφ with (hφ | hφ);
    . apply hψ;
      apply T.mem_trans hφ;
      apply T.mem_of_provable;
      exact hφψ;
    . apply hφ Γ ?_ H;
      sorry;
  . apply T.mem_of_provable;
    sorry;

lemma construction_omega_L_subset : L ⊆ construction_omega T hT := by
  intro φ hφ;
  apply mem_construction_omega_of_exists;
  use (toNat φ) + 1;
  simp only [construction, Formula.ofNat_toNat];
  split_ifs with h;
  . tauto;
  . exfalso;
    push_neg at h;
    obtain ⟨Γ, hΓ, h⟩ := h;
    apply construction_consistency (toNat φ) _ hΓ $ T.mem_trans ?_ h;
    apply T.mem_of_provable;
    apply C_trans ?_ (show L ⊢ φ ⋏ Γ.conj ➝ (insert φ Γ).conj by exact insert_FConj);
    apply greedy;
    . apply af;
      tauto;
    . exact impId;

lemma construction_omega_prime :
  letI U := construction_omega T hT
  φ ⋎ ψ ∈ U → φ ∈ U ∨ ψ ∈ U := by
  rintro hφψ;
  wlog lt_φψ : toNat φ ≤ toNat ψ;
  . symm;
    apply this;
    . sorry;
    . omega;
  by_contra! hC;
  obtain ⟨hφ, hψ⟩ := hC;
  replace ⟨_, Γ, hΓ₁, hΓ₂⟩ := iff_not_mem_omega_construction.mp hφ;
  replace ⟨_, Δ, hΔ₁, hΔ₂⟩ := iff_not_mem_omega_construction.mp hψ;
  apply construction_consistency (hT := hT) (toNat (φ ⋎ ψ) + 1) (Γ := insert (φ ⋎ ψ) (Γ ∪ Δ)) (ξ := ξ) _ ?_;
  . intro χ;
    simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union, SetLike.mem_coe];
    rintro (rfl | hχ | hχ);
    . apply mem_construction_of_mem_construction_omega hφψ;
    . apply subset_construction_mono (i := (φ ⋎ ψ).toNat);
      . omega;
      . apply Set.Subset.trans hΓ₁;
        . apply subset_construction_mono;
          apply Nat.le_of_lt;
          simp;
        . assumption;
    . apply subset_construction_mono (i := ψ.toNat);
      . suffices ψ.toNat < (φ ⋎ ψ).toNat by omega;
        simp;
      . exact hΔ₁ hχ;
  . have := T.andIR hΓ₂ hΔ₂;
    sorry;

lemma construction_rel :
  letI U := construction_omega T hT;
  (φ ➝ ψ ∈ T.theory → φ ∈ U → ψ ∈ U) := by
  sorry;

lemma construction_omega_mem_ant : χ ∈ construction_omega T hT := by
  apply iff_mem_omega_construction.mpr;
  left;
  apply T.mem_of_provable;
  apply impId;

lemma construction_omega_not_mem_csq : ξ ∉ construction_omega T hT := by
  apply iff_mem_omega_construction.not.mpr;
  push_neg;
  constructor;
  . assumption;
  . use ∅;
    simp;

end FTheory.lindenbaum

open FTheory.lindenbaum in
lemma FTheory.lindenbaum {χ ξ : Formula _} [Entailment.F L] (T : PrimeFTheory L) (hT : χ ➝ ξ ∉ T.theory) : ∃ U : PrimeFTheory L,
  (∀ φ ψ, φ ➝ ψ ∈ T.theory → φ ∈ U.theory → ψ ∈ U.theory) ∧
  χ ∈ U.theory ∧ ξ ∉ U.theory := by
  use {
     theory := construction_omega T hT,
     no_bot := construction_omega_noBot,
     andIR := construction_omega_andClosed,
     imp_closed := construction_omega_impClosed,
     L_subset := construction_omega_L_subset,
     prime := construction_omega_prime
  };
  constructor;
  . intro φ ψ;
    apply construction_rel;
  . exact ⟨construction_omega_mem_ant, construction_omega_not_mem_csq⟩;

abbrev emptyPrimeFTheory (L : Logic _) [Entailment.F L] [Entailment.Disjunctive L] : PrimeFTheory L where
  theory := L
  no_bot := by
    sorry;
  andIR hφ hψ := by
    simp only [←Logic.iff_provable] at hφ hψ ⊢;
    apply andIR <;> assumption;
  imp_closed := by
    intros φ ψ hφψ hφ;
    simp only [←Logic.iff_provable] at hφψ hφ ⊢;
    exact hφψ ⨀ hφ;
  L_subset := by tauto;
  prime {φ ψ} hφψ := by
    simp only [←Logic.iff_provable] at hφψ ⊢;
    exact disjunctive hφψ;

instance [Entailment.F L] [Entailment.Disjunctive L] : Nonempty (PrimeFTheory L) := ⟨emptyPrimeFTheory L⟩


namespace Kripke2

variable {Ax : Axiom ℕ} {φ ψ χ : Formula ℕ}
variable [Entailment.F L] [Entailment.Disjunctive L]

open Formula.Kripke2

abbrev canonicalModel (L : Logic ℕ) [Entailment.F L] [Entailment.Disjunctive L] : Kripke2.Model where
  World := PrimeFTheory L
  Rel T U := ∀ {φ ψ}, φ ➝ ψ ∈ T.theory → φ ∈ U.theory → ψ ∈ U.theory
  Val T a := (atom a) ∈ T.theory
  root := emptyPrimeFTheory L
  rooted := by
    intro T φ ψ hφψ hφ;
    rw [←Logic.iff_provable] at hφψ;
    exact T.imp_closed hφψ hφ;

lemma truthlemma {T : canonicalModel L} : Satisfies _ T φ ↔ φ ∈ T.theory := by
  induction φ generalizing T with
  | hatom a => simp [Kripke2.Satisfies];
  | hfalsum => simp [Kripke2.Satisfies];
  | hor φ ψ ihφ ihψ =>
    suffices φ ∈ T.theory ∨ ψ ∈ T.theory ↔ φ ⋎ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . rintro (hφ | hψ);
      . apply T.imp_closed orIntroL hφ;
      . apply T.imp_closed orIntroR hψ;
    . apply T.prime;
  | hand φ ψ ihφ ihψ =>
    suffices (φ ∈ T.theory ∧ ψ ∈ T.theory) ↔ φ ⋏ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . rintro ⟨hφ, hψ⟩;
      apply T.andIR hφ hψ;
    . intro h;
      constructor;
      . apply T.imp_closed andElimL h;
      . apply T.imp_closed andElimR h;
  | himp φ ψ ihφ ihψ =>
    suffices (∀ {U : canonicalModel L}, T ≺ U → φ ∈ U.theory → ψ ∈ U.theory) ↔ φ ➝ ψ ∈ T.theory by
      simpa [Kripke2.Satisfies, ihφ, ihψ];
    constructor;
    . contrapose!;
      exact FTheory.lindenbaum T;
    . rintro hφψ U RTU hφ;
      apply RTU hφψ hφ;

theorem provable_of_validOncanonicalModel : (canonicalModel L) ⊧ φ → L ⊢ φ := by
  contrapose!;
  intro h;
  apply ValidOnModel.not_of_exists_world;
  use (emptyPrimeFTheory L);
  apply truthlemma.not.mpr;
  apply Logic.iff_unprovable.mp;
  simpa;

end Kripke2

end LO.Propositional
