import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Meta.ClProver


section

variable {α β} {l : List α}

lemma List.exists_of_range (h : a ∈ List.map f (List.range n)) : ∃ i < n, a = f i := by
  obtain ⟨i, ⟨hi, rfl⟩⟩ := List.exists_of_mem_map h;
  use i;
  constructor;
  . simpa using hi;
  . simp;

end


namespace LO

namespace Box

variable [DecidableEq F] [Top F] [Box F] [Wedge F]


noncomputable abbrev boxlt (n : ℕ) (φ : F) := Finset.range (n + 1) |>.image (λ i => □^[i] φ) |>.conj
notation:90 "□^≤[" n "]" φ => Box.boxlt n φ

@[simp high] lemma boxlt_zero {φ : F} : (□^≤[0]φ) = φ := by simp [Box.boxlt];

/-
lemma boxlt_succ : 𝓢 ⊢! (□^≤[(n + 1)] φ) ⭤ ((□^≤[n] φ) ⋏ (□^[n] φ))  := by
  sorry;
-/

end Box

namespace Modal.Entailment

open LO.Entailment

variable {S F : Type*} [DecidableEq F] [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} [Entailment.K 𝓢] {n m : ℕ} {φ ψ ξ χ: F}

lemma boxlt_lt_succ! : 𝓢 ⊢! (□^≤[n + 1] φ) ➝ (□^≤[n] φ) := by
  apply CFconjFconj!_of_provable;
  intro ψ hψ;
  simp only [Finset.mem_image, Finset.mem_range] at hψ;
  obtain ⟨i, hi, rfl⟩ := hψ;
  apply Context.by_axm!
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio];
  use i;
  constructor;
  . omega;
  . simp;

lemma boxlt_lt_add! : 𝓢 ⊢! (□^≤[n + m] φ) ➝ (□^≤[n] φ) := by
  induction m with
  | zero => simp;
  | succ m ih =>
    rw [(show n + (m + 1) = n + m + 1 by rfl)];
    apply C!_trans boxlt_lt_succ! ih;

lemma boxlt_lt! (h : n ≥ m) : 𝓢 ⊢! (□^≤[n] φ) ➝ (□^≤[m] φ) := by
  convert boxlt_lt_add! (𝓢 := 𝓢) (n := m) (m := n - m) (φ := φ);
  omega;

lemma E_boxlt_succ! : 𝓢 ⊢! (□^≤[n + 1] φ) ⭤ (□^≤[n] φ) ⋏ (□^[(n + 1)] φ) := by
  apply E!_intro;
  . apply FConj_DT.mpr;
    apply K!_intro;
    . apply FConj_DT.mp;
      apply boxlt_lt!;
      omega;
    . apply Context.by_axm!;
      simp only [Finset.coe_image, Finset.coe_range, Box.multibox_succ, Set.mem_image, Set.mem_Iio];
      use n + 1;
      constructor;
      . omega;
      . simp;
  . suffices 𝓢 ⊢! (□^≤[n]φ) ⋏ (Finset.conj {(□^[(n + 1)]φ)}) ➝ (□^≤[n + 1]φ) by simpa using this;
    convert CKFconjFconjUnion! (𝓢 := 𝓢) (Γ := Finset.range (n + 1) |>.image (λ i => □^[i] φ)) (Δ := {(□^[(n + 1)]φ)});
    ext ψ;
    simp only [Finset.mem_image, Finset.mem_range, Box.multibox_succ, Finset.mem_union, Finset.mem_singleton];
    constructor;
    . rintro ⟨k, hk, rfl⟩;
      by_cases ha : k = n + 1;
      . right;
        subst ha;
        simp;
      . left;
        use k;
        constructor;
        . omega;
        . simp;
    . rintro (⟨k, hk, rfl⟩ | rfl);
      . use k;
        constructor;
        . omega;
        . simp;
      . use (n + 1);
        constructor;
        . omega;
        . simp;

lemma boxlt_regularity! (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! (□^≤[n] φ) ➝ (□^≤[n] ψ) := by
  induction n with
  | zero => simpa;
  | succ n ih =>
    suffices 𝓢 ⊢! ((□^≤[n]φ) ⋏ (□^[(n + 1)]φ)) ➝ ((□^≤[n]ψ) ⋏ (□^[(n + 1)]ψ)) by
      apply C!_replace ?_ ?_ this;
      . apply C_of_E_mp! E_boxlt_succ!;
      . apply C_of_E_mpr! E_boxlt_succ!;
    apply CKK!_of_C!_of_C! ih $ imply_multibox_distribute'! h;

end Modal.Entailment


end LO




namespace LO.Modal

variable {α}


open Modal.Entailment in
lemma normal_provable_of_K_provable {L : Logic ℕ} [L.IsNormal] (h : Modal.K ⊢! φ) : L ⊢! φ := by
  simp only [Hilbert.Normal.iff_logic_provable_provable] at h;
  induction h using Hilbert.Normal.rec! with
  | axm s h => rcases h with rfl; simp;
  | mdp hφψ hψ => exact hφψ ⨀ hψ;
  | nec ihφ => apply nec!; exact ihφ;
  | _ => simp;


namespace Formula

end Formula



inductive GlobalConsequence (L : Logic α) : Set (Formula α) → Formula α → Prop where
  | thm! {X φ}      : L ⊢! φ → GlobalConsequence L X φ
  | ctx! {X φ}      : φ ∈ X → GlobalConsequence L X φ
  | mdp! {X Y φ ψ}  : GlobalConsequence L X (φ ➝ ψ) → GlobalConsequence L Y φ → GlobalConsequence L (X ∪ Y) ψ
  | nec! {X φ}      : GlobalConsequence L X φ → GlobalConsequence L X (□φ)
  | imply₁! X φ ψ   : GlobalConsequence L X $ Axioms.Imply₁ φ ψ
  | imply₂! X φ ψ χ : GlobalConsequence L X $ Axioms.Imply₂ φ ψ χ
  | ec! X φ ψ       : GlobalConsequence L X $ Axioms.ElimContra φ ψ

notation X:45 " ⊢ᵍ[" L "]! " φ => GlobalConsequence L X φ

namespace GlobalConsequence

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {L : Logic ℕ} [L.IsNormal] {X Y : Set (Formula ℕ)} {φ ψ : Formula ℕ}

omit [L.IsNormal] in
lemma mdp'! (h₁ : X ⊢ᵍ[L]! φ ➝ ψ) (h₂ : X ⊢ᵍ[L]! φ) : X ⊢ᵍ[L]! ψ := by simpa using mdp! h₁ h₂

lemma fact2_7 : (X ⊢ᵍ[L]! φ) ↔ (∃ Γ : Finset (Formula _), ∃ n, ↑Γ ⊆ X ∧ L ⊢! (□^≤[n] Γ.conj) ➝ φ) := by
  constructor;
  . intro h;
    induction h with
    | thm! h =>
      use ∅, 0;
      constructor;
      . simp;
      . apply C!_of_conseq!;
        exact h;
    | @ctx! X ψ h =>
      use {ψ}, 0;
      constructor;
      . simpa;
      . simp;
    | @mdp! _ _ φ ψ _ _ ihφψ ihφ =>
      obtain ⟨Δ₁, n, ⟨hΔ₁, hφψ⟩⟩ := ihφψ;
      obtain ⟨Δ₂, m, ⟨hΔ₂, hφ⟩⟩ := ihφ;
      use Δ₁ ∪ Δ₂, n + m;
      constructor;
      . simp only [Finset.coe_union, Set.union_subset_iff];
        tauto_set;
      . replace hφψ : L ⊢! (□^≤[n + m](Δ₁ ∪ Δ₂).conj) ➝ φ ➝ ψ := C!_trans (C!_trans (boxlt_lt! (by omega)) (boxlt_regularity! (CFConj_FConj!_of_subset (by simp)))) hφψ;
        replace hφ  : L ⊢! (□^≤[n + m](Δ₁ ∪ Δ₂).conj) ➝ φ := C!_trans (C!_trans (boxlt_lt! (by omega)) (boxlt_regularity! (CFConj_FConj!_of_subset (by simp)))) hφ;
        cl_prover [hφψ, hφ];
    | @nec! _ φ h ih =>
      obtain ⟨Δ, n, ⟨h₁, h₂⟩⟩ := ih;
      use Δ, n + 1;
      constructor;
      . assumption;
      . apply C!_trans ?_ $ box_regularity! h₂;
        apply C!_trans ?_ collect_box_fconj!;
        apply CFconjFconj!_of_provable;
        intro ψ hψ;
        simp only [Finset.mem_image, Finset.mem_range, Function.iterate_one, exists_exists_and_eq_and] at hψ;
        obtain ⟨i, hi, rfl⟩ := hψ;
        apply Context.by_axm!;
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio];
        use i + 1;
        constructor;
        . omega;
        . simp;
    | imply₁! | imply₂! | ec! =>
      use ∅, 0;
      constructor;
      . simp;
      . apply normal_provable_of_K_provable;
        apply C!_of_conseq!;
        simp;
  . rintro ⟨Γ, n, hΓ, hφ⟩;
    induction n with
    | zero =>
      simp only [Box.boxlt_zero] at hφ;
      sorry;
    | succ n ih =>

      sorry;

end GlobalConsequence



end LO.Modal
