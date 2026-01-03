import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Meta.ClProver


namespace LO.Modal

variable {α}


open Modal.Entailment in
lemma normal_provable_of_K_provable {L : Logic ℕ} [L.IsNormal] (h : Modal.K ⊢ φ) : L ⊢ φ := by
  induction h using Hilbert.Normal.rec! with
  | axm s h => rcases h with rfl; simp;
  | mdp hφψ hψ => exact hφψ ⨀ hψ;
  | nec ihφ => apply nec!; exact ihφ;
  | _ => simp;


namespace Formula

end Formula


inductive GlobalConsequence (L : Logic α) : Set (Formula α) → Formula α → Type*
  | protected thm {X φ}        : L ⊢ φ → GlobalConsequence L X φ
  | protected ctx {X φ}        : φ ∈ X → GlobalConsequence L X φ
  | protected mdp {X Y φ ψ}    : GlobalConsequence L X (φ ➝ ψ) → GlobalConsequence L Y φ → GlobalConsequence L (X ∪ Y) ψ
  | protected nec {X φ}        : GlobalConsequence L X φ → GlobalConsequence L X (□φ)
  | protected implyK X {φ ψ}   : GlobalConsequence L X $ Axioms.ImplyK φ ψ
  | protected implyS X {φ ψ χ} : GlobalConsequence L X $ Axioms.ImplyS φ ψ χ
  | protected ec X {φ ψ}       : GlobalConsequence L X $ Axioms.ElimContra φ ψ

instance : Entailment (Logic α × Set (Formula α)) (Formula α) := ⟨λ (L, Γ) => GlobalConsequence L Γ⟩

namespace GlobalConsequence

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {L : Logic α} {X Y : Set (Formula α)} {φ ψ : Formula α}

instance : Entailment.Lukasiewicz (F := Formula α) (S := Logic α × Set (Formula α)) (L, X) where
  mdp ihφψ ihφ := by simpa using GlobalConsequence.mdp ihφψ ihφ;
  implyK := GlobalConsequence.implyK X
  implyS := GlobalConsequence.implyS X
  elimContra := GlobalConsequence.ec X

instance : Entailment.Necessitation (F := Formula α) (S := Logic α × Set (Formula α)) (L, X) where
  nec ihφ := by simpa using GlobalConsequence.nec ihφ

instance [L.IsNormal] : Entailment.K (F := Formula α) (S := Logic α × Set (Formula α)) (L, X) where
  K _ _ := by
    apply GlobalConsequence.thm;
    simp;

protected lemma thm! (h : L ⊢ φ) : (L, X) ⊢ φ := ⟨GlobalConsequence.thm h⟩

protected lemma ctx! (h : φ ∈ X) : (L, X) ⊢ φ := ⟨GlobalConsequence.ctx h⟩

protected lemma rec!
  {motive : (X : Set (Formula α)) → (φ : Formula α) → ((L, X) ⊢ φ) → Sort}
  (ctx! : ∀ {X φ} (h : φ ∈ X), motive X φ ⟨GlobalConsequence.ctx h⟩)
  (thm! : ∀ {X φ} (h : L ⊢ φ), motive X φ ⟨GlobalConsequence.thm h⟩)
  (mdp! : ∀ {X Y φ ψ}
    {hφψ : (L, X) ⊢ φ ➝ ψ} {hφ : (L, Y) ⊢ φ},
    motive X (φ ➝ ψ) hφψ → motive Y φ hφ →
    motive (X ∪ Y) ψ ⟨GlobalConsequence.mdp hφψ.some hφ.some⟩
  )
  (nec! : ∀ {X φ}
    {hφ : (L, X) ⊢ φ},
    motive X φ hφ → motive X (□φ) ⟨GlobalConsequence.nec hφ.some⟩
  )
  (implyK! : ∀ {X φ ψ}, motive X (Axioms.ImplyK φ ψ) ⟨GlobalConsequence.implyK X⟩)
  (implyS! : ∀ {X φ ψ ξ}, motive X (Axioms.ImplyS φ ψ ξ) ⟨GlobalConsequence.implyS X⟩)
  (ec! : ∀ {X φ ψ}, motive X (Axioms.ElimContra φ ψ) ⟨GlobalConsequence.ec X⟩)
  : ∀ {X : Set (Formula α)} {φ}, (d : (L, X) ⊢ φ) → motive X φ d := by
  rintro X φ ⟨d⟩;
  induction d with
  | ctx h => apply ctx! h;
  | thm h => apply thm! h;
  | mdp _ _ ihφψ ihφ => apply mdp! ihφψ ihφ;
  | nec _ ihφ => apply nec! ihφ;
  | implyK => apply implyK!;
  | implyS => apply implyS!;
  | ec => apply ec!;

section

variable {L : Logic ℕ} [L.IsNormal] {X Y : Set (Formula ℕ)} {φ ψ : Formula ℕ}

/--
  Jeřábek, Fact 2.7
-/
lemma iff_finite_boxLe_provable : ((L, X) ⊢ φ) ↔ (∃ Γ : Finset (Formula _), ∃ n, ↑Γ ⊆ X ∧ L ⊢ (□^≤[n] Γ.conj) ➝ φ) := by
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
      . replace hφψ : L ⊢ (□^≤[n + m](Δ₁ ∪ Δ₂).conj) ➝ φ ➝ ψ := C!_trans (C!_trans (boxLe_lt! (by omega)) (boxLe_regularity! (CFConj_FConj!_of_subset (by simp)))) hφψ;
        replace hφ  : L ⊢ (□^≤[n + m](Δ₁ ∪ Δ₂).conj) ➝ φ := C!_trans (C!_trans (boxLe_lt! (by omega)) (boxLe_regularity! (CFConj_FConj!_of_subset (by simp)))) hφ;
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
    | implyK! | implyS! | ec! =>
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
