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


inductive GlobalConsequence (L : Logic α) : Set (Formula α) → Formula α → Type*
  | protected thm {X φ}      : L ⊢! φ → GlobalConsequence L X φ
  | protected ctx {X φ}      : φ ∈ X → GlobalConsequence L X φ
  | protected mdp {X Y φ ψ}  : GlobalConsequence L X (φ ➝ ψ) → GlobalConsequence L Y φ → GlobalConsequence L (X ∪ Y) ψ
  | protected nec {X φ}      : GlobalConsequence L X φ → GlobalConsequence L X (□φ)
  | protected imply₁ X φ ψ   : GlobalConsequence L X $ Axioms.Imply₁ φ ψ
  | protected imply₂ X φ ψ χ : GlobalConsequence L X $ Axioms.Imply₂ φ ψ χ
  | protected ec X φ ψ       : GlobalConsequence L X $ Axioms.ElimContra φ ψ

instance : Entailment (Formula α) (Logic α × Set (Formula α)) := ⟨λ (L, Γ) => GlobalConsequence L Γ⟩

namespace GlobalConsequence

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {L : Logic α} {X Y : Set (Formula α)} {φ ψ : Formula α}

instance : Entailment.Lukasiewicz (F := Formula α) (S := Logic α × Set (Formula α)) (L, X) where
  mdp ihφψ ihφ := by simpa using GlobalConsequence.mdp ihφψ ihφ;
  imply₁ := GlobalConsequence.imply₁ X
  imply₂ := GlobalConsequence.imply₂ X
  elimContra := GlobalConsequence.ec X

instance : Entailment.Necessitation (F := Formula α) (S := Logic α × Set (Formula α)) (L, X) where
  nec ihφ := by simpa using GlobalConsequence.nec ihφ

instance [L.IsNormal] : Entailment.K (F := Formula α) (S := Logic α × Set (Formula α)) (L, X) where
  K _ _ := by
    apply GlobalConsequence.thm;
    simp;

protected lemma thm! (h : L ⊢! φ) : (L, X) ⊢! φ := ⟨GlobalConsequence.thm h⟩

protected lemma ctx! (h : φ ∈ X) : (L, X) ⊢! φ := ⟨GlobalConsequence.ctx h⟩

protected lemma rec!
  {motive : (X : Set (Formula α)) → (φ : Formula α) → ((L, X) ⊢! φ) → Sort}
  (ctx! : ∀ {X φ} (h : φ ∈ X), motive X φ ⟨GlobalConsequence.ctx h⟩)
  (thm! : ∀ {X φ} (h : L ⊢! φ), motive X φ ⟨GlobalConsequence.thm h⟩)
  (mdp! : ∀ {X Y φ ψ}
    {hφψ : (L, X) ⊢! φ ➝ ψ} {hφ : (L, Y) ⊢! φ},
    motive X (φ ➝ ψ) hφψ → motive Y φ hφ →
    motive (X ∪ Y) ψ ⟨GlobalConsequence.mdp hφψ.some hφ.some⟩
  )
  (nec! : ∀ {X φ}
    {hφ : (L, X) ⊢! φ},
    motive X φ hφ → motive X (□φ) ⟨GlobalConsequence.nec hφ.some⟩
  )
  (imply₁! : ∀ {X φ ψ}, motive X (Axioms.Imply₁ φ ψ) ⟨GlobalConsequence.imply₁ X φ ψ⟩)
  (imply₂! : ∀ {X φ ψ ξ}, motive X (Axioms.Imply₂ φ ψ ξ) ⟨GlobalConsequence.imply₂ X φ ψ ξ⟩)
  (ec! : ∀ {X φ ψ}, motive X (Axioms.ElimContra φ ψ) ⟨GlobalConsequence.ec X φ ψ⟩)
  : ∀ {X : Set (Formula α)} {φ}, (d : (L, X) ⊢! φ) → motive X φ d := by
  rintro X φ ⟨d⟩;
  induction d with
  | ctx h => apply ctx! h;
  | thm h => apply thm! h;
  | mdp _ _ ihφψ ihφ => apply mdp! ihφψ ihφ;
  | nec _ ihφ => apply nec! ihφ;
  | imply₁ => apply imply₁!;
  | imply₂ => apply imply₂!;
  | ec => apply ec!;

section

variable {L : Logic ℕ} [L.IsNormal] {X Y : Set (Formula ℕ)} {φ ψ : Formula ℕ}

/--
  Jeřábek, Fact 2.7
-/
lemma iff_finite_boxlt_provable : ((L, X) ⊢! φ) ↔ (∃ Γ : Finset (Formula _), ∃ n, ↑Γ ⊆ X ∧ L ⊢! (□^≤[n] Γ.conj) ➝ φ) := by
  constructor;
  . intro h;
    induction h using GlobalConsequence.rec! with
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
    apply (GlobalConsequence.thm! hφ) ⨀ _;
    apply FConj!_iff_forall_provable.mpr;
    intro ψ hψ;
    simp only [Finset.mem_image, Finset.mem_range] at hψ;
    obtain ⟨i, hi, rfl⟩ := hψ;
    apply multinec!;
    apply FConj!_iff_forall_provable.mpr;
    intro ψ hψ;
    apply GlobalConsequence.ctx!;
    apply hΓ;
    simpa;

end

end GlobalConsequence

end LO.Modal
