module

public import Foundation.FirstOrder.Arithmetic.Basic.Prenex

@[expose] public section
namespace LO.FirstOrder.Arithmetic

/-!
# Prenex normal form over ℕ (skeleton)

This file sets up the skeleton of the "prenex normal form theorem" over the standard model `ℕ`:
every `Hierarchy Γ s φ` formula (`s ≥ 1`) is equivalent, on `ℕ`, to a formula in `StrictHierarchy Γ s`
(i.e. genuine prenex form). Most of the interesting lemmas are only stated here (with `sorry`); the
proofs are left for follow-up work.

## Notes for implementers

- Bounded quantifier evaluation should always be rewritten to `ballLT`/`bexsLT` form first (via the
  bridge lemmas in this file), then use the simp lemmas `Semiformula.eval_ballLT`/`eval_bexsLT`.
- Variable insertion uses `Rew.bShift.q` (insert at position 1) / `Rew.bShift.q.q` (insert at position 2);
  variable swapping uses `Rew.subst (#1 :> #0 :> fun i => #(i+2))`. Strictness is preserved by
  `StrictHierarchy.rew`; positivity of terms is preserved by `Rew.bShift_positive` / `Rew.q_positive_iff`.
- Evaluation rewriting under substitutions should mostly close via
  `simp [Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons']` plus `Fin.cases` for
  componentwise computation.
-/

/-- `φ` is equivalent, on `ℕ`, to some strict `Γ`-formula of level `s`. -/
def EquivStrict (Γ : Polarity) (s : ℕ) {n : ℕ} (φ : ArithmeticSemiformula Empty n) : Prop :=
  ∃ φ' : ArithmeticSemiformula Empty n,
    StrictHierarchy Γ s φ' ∧ ∀ e : Fin n → ℕ, ℕ ⊧/e φ' ↔ ℕ ⊧/e φ

-- see plan §3.1 L0-5. Pure Nat statement, no dependency on formulas.
lemma nat_collection (m : ℕ) (P : ℕ → ℕ → Prop) :
    (∀ x < m, ∃ y, P x y) ↔ (∃ w, ∀ x < m, ∃ y < w, P x y) := sorry

lemma nat_exists_and_exists (P Q : ℕ → Prop) :
    ((∃ x, P x) ∧ (∃ y, Q y)) ↔ ∃ z, (∃ x < z + 1, P x) ∧ (∃ y < z + 1, Q y) := sorry

lemma nat_exists_exists (P : ℕ → ℕ → Prop) :
    (∃ x y, P x y) ↔ ∃ z, ∃ x < z + 1, ∃ y < z + 1, P x y := sorry

-- see plan §3.1 L0-6. Bridge between `ball`/`bexs` notation and `ballLT`/`bexsLT`.
lemma ball_eq_ballLT {n} (φ : ArithmeticSemiformula Empty (n + 1)) (u : ArithmeticSemiterm Empty n) :
    (∀⁰[“x. x < !!(Rew.bShift u)”] φ) = φ.ballLT u := rfl

lemma bexs_eq_bexsLT {n} (φ : ArithmeticSemiformula Empty (n + 1)) (u : ArithmeticSemiterm Empty n) :
    (∃⁰[“x. x < !!(Rew.bShift u)”] φ) = φ.bexsLT u := rfl

namespace EquivStrict

variable {Γ Γ' : Polarity} {s s' : ℕ} {n : ℕ} {φ ψ : ArithmeticSemiformula Empty n}

lemma refl (h : StrictHierarchy Γ s φ) : EquivStrict Γ s φ := ⟨φ, h, fun _ => Iff.rfl⟩

lemma of_iff (h : EquivStrict Γ s φ) (hiff : ∀ e : Fin n → ℕ, ℕ ⊧/e φ ↔ ℕ ⊧/e ψ) :
    EquivStrict Γ s ψ := by
  rcases h with ⟨φ', hφ', hiff'⟩
  exact ⟨φ', hφ', fun e => (hiff' e).trans (hiff e)⟩

lemma neg (h : EquivStrict Γ s φ) : EquivStrict Γ.alt s (∼φ) := by
  rcases h with ⟨φ', hφ', hiff'⟩
  refine ⟨∼φ', hφ'.neg, fun e => ?_⟩
  simp [hiff' e]

@[simp] lemma neg_iff : EquivStrict Γ.alt s (∼φ) ↔ EquivStrict Γ s φ := by
  constructor
  · intro h
    have := h.neg
    simpa using this
  · intro h
    exact h.neg

lemma alt_up (h : EquivStrict Γ (s + 1) φ) : EquivStrict Γ.alt (s + 2) φ := by
  rcases Γ with _ | _
  · rcases h with ⟨φ', hφ', hiff'⟩
    refine ⟨∀⁰ (Rew.bShift ▹ φ'), (hφ'.rew Rew.bShift).all, fun e => ?_⟩
    simp only [Semiformula.eval_all, Semiformula.eval_bShift]
    constructor
    · intro h
      exact (hiff' e).mp (h 0)
    · intro h _
      exact (hiff' e).mpr h
  · rcases h with ⟨φ', hφ', hiff'⟩
    refine ⟨∃⁰ (Rew.bShift ▹ φ'), (hφ'.rew Rew.bShift).exs, fun e => ?_⟩
    simp only [Semiformula.eval_ex, Semiformula.eval_bShift]
    constructor
    · intro ⟨_, h⟩
      exact (hiff' e).mp h
    · intro h
      exact ⟨0, (hiff' e).mpr h⟩

lemma of_deltaZero (hp : Hierarchy 𝚺 0 φ) (hs : 1 ≤ s) : EquivStrict Γ s φ := by
  have aux : ∀ s, 1 ≤ s → ∀ Γ : Polarity, EquivStrict Γ s φ := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs Γ
      rcases s with _ | _ | s
      · omega
      · exact refl (StrictHierarchy.base (Hierarchy.of_zero hp))
      · have h2 : EquivStrict Γ.alt (s + 1) φ := ih (s + 1) (by omega) (by omega) Γ.alt
        simpa using h2.alt_up
  exact aux s hs Γ

/-- The core closure properties needed at a fixed level `s`. -/
structure CoreClosure (s : ℕ) : Prop where
  and  : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n}, EquivStrict Γ s φ → EquivStrict Γ s ψ → EquivStrict Γ s (φ ⋏ ψ)
  or   : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n}, EquivStrict Γ s φ → EquivStrict Γ s ψ → EquivStrict Γ s (φ ⋎ ψ)
  ball : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → EquivStrict Γ s φ → EquivStrict Γ s (∀⁰[“x. x < !!t”] φ)
  bexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → EquivStrict Γ s φ → EquivStrict Γ s (∃⁰[“x. x < !!t”] φ)

-- see plan §3.4 L3-0
lemma coreClosure_one : CoreClosure 1 := sorry

-- see plan §3.4 L3-1
lemma or_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) ψ → EquivStrict 𝚺 (s + 2) (φ ⋎ ψ) := sorry

-- see plan §3.4 L3-2 (max confluence of existentials)
lemma and_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) ψ → EquivStrict 𝚺 (s + 2) (φ ⋏ ψ) := sorry

-- see plan §3.4 L3-3 (quantifier swap)
lemma bexs_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) (∃⁰[“x. x < !!t”] φ) := sorry

-- see plan §3.4 L3-4 (collection, hardest)
lemma ball_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) (∀⁰[“x. x < !!t”] φ) := sorry

lemma coreClosure_succ (ih : CoreClosure (s + 1)) : CoreClosure (s + 2) where
  and := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _
    · exact and_sigma_step ih hφ hψ
    · have hφ' : EquivStrict 𝚺 (s + 2) (∼φ) := by simpa using hφ.neg
      have hψ' : EquivStrict 𝚺 (s + 2) (∼ψ) := by simpa using hψ.neg
      have := (or_sigma_step ih hφ' hψ').neg
      simpa [Semiformula.imp_eq] using this
  or := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _
    · exact or_sigma_step ih hφ hψ
    · have hφ' : EquivStrict 𝚺 (s + 2) (∼φ) := by simpa using hφ.neg
      have hψ' : EquivStrict 𝚺 (s + 2) (∼ψ) := by simpa using hψ.neg
      have := (and_sigma_step ih hφ' hψ').neg
      simpa [Semiformula.imp_eq] using this
  ball := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _
    · exact ball_sigma_step ih ht hφ
    · have hφ' : EquivStrict 𝚺 (s + 2) (∼φ) := by simpa using hφ.neg
      have := (bexs_sigma_step ih ht hφ').neg
      simpa using this
  bexs := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _
    · exact bexs_sigma_step ih ht hφ
    · have hφ' : EquivStrict 𝚺 (s + 2) (∼φ) := by simpa using hφ.neg
      have := (ball_sigma_step ih ht hφ').neg
      simpa using this

lemma coreClosure (hs : 1 ≤ s) : CoreClosure s := by
  induction s with
  | zero => omega
  | succ s ih =>
    rcases s with _ | s
    · exact coreClosure_one
    · exact coreClosure_succ (ih (by omega))

lemma and (hs : 1 ≤ s) (hφ : EquivStrict Γ s φ) (hψ : EquivStrict Γ s ψ) : EquivStrict Γ s (φ ⋏ ψ) :=
  (coreClosure hs).and Γ hφ hψ

lemma or (hs : 1 ≤ s) (hφ : EquivStrict Γ s φ) (hψ : EquivStrict Γ s ψ) : EquivStrict Γ s (φ ⋎ ψ) :=
  (coreClosure hs).or Γ hφ hψ

lemma ball {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)}
    (hs : 1 ≤ s) (ht : t.Positive) (hφ : EquivStrict Γ s φ) : EquivStrict Γ s (∀⁰[“x. x < !!t”] φ) :=
  (coreClosure hs).ball Γ ht hφ

lemma bexs {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)}
    (hs : 1 ≤ s) (ht : t.Positive) (hφ : EquivStrict Γ s φ) : EquivStrict Γ s (∃⁰[“x. x < !!t”] φ) :=
  (coreClosure hs).bexs Γ ht hφ

lemma exs_of_pi {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚷 (s + 1) φ) :
    EquivStrict 𝚺 (s + 2) (∃⁰ φ) := by
  rcases h with ⟨φ', hφ', hiff'⟩
  refine ⟨∃⁰ φ', hφ'.exs, fun e => ?_⟩
  simp only [Semiformula.eval_ex]
  exact exists_congr (fun x => hiff' (x :> e))

lemma all_of_sigma {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚺 (s + 1) φ) :
    EquivStrict 𝚷 (s + 2) (∀⁰ φ) := by
  rcases h with ⟨φ', hφ', hiff'⟩
  refine ⟨∀⁰ φ', hφ'.all, fun e => ?_⟩
  simp only [Semiformula.eval_all]
  exact forall_congr' (fun x => hiff' (x :> e))

-- see plan §3.5 L4
lemma exs {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚺 (s + 1) φ) :
    EquivStrict 𝚺 (s + 1) (∃⁰ φ) := by
  rcases s with _ | s₀
  · -- s + 1 = 1: Σ₁ is already closed under ∃
    rcases h with ⟨φ', hφ', hiff'⟩
    cases hφ' with
    | base hb =>
      refine ⟨∃⁰ φ', StrictHierarchy.base hb.exs, fun e => ?_⟩
      simp only [Semiformula.eval_ex]
      exact exists_congr (fun x => hiff' (x :> e))
  · -- s + 1 = s₀ + 2: contract the two existentials ∃x∃y into a single bounded pair
    obtain ⟨φ', hφ', hiff'⟩ := h
    obtain ⟨ψ₀, rfl, hψ₀⟩ := StrictHierarchy.sigma_succ_elim hφ'
    have hs01 : 1 ≤ s₀ + 1 := by omega
    -- insert a fresh variable `z` at position 2 (after `x`, `y`)
    set ψ₀' : ArithmeticSemiformula Empty (n + 3) := Rew.bShift.q.q ▹ ψ₀ with hψ₀'def
    have hψ₀' : StrictHierarchy 𝚷 (s₀ + 1) ψ₀' := hψ₀.rew Rew.bShift.q.q
    set tx : ArithmeticSemiterm Empty (n + 2) := (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)) with htx
    set ty : ArithmeticSemiterm Empty (n + 1) := (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)) with hty
    have hB : EquivStrict 𝚷 (s₀ + 1) (ψ₀'.bexsLT tx) := by
      have := (coreClosure hs01).bexs 𝚷 (Rew.bShift_positive tx) (EquivStrict.refl hψ₀')
      rwa [bexs_eq_bexsLT] at this
    have hC : EquivStrict 𝚷 (s₀ + 1) ((ψ₀'.bexsLT tx).bexsLT ty) := by
      have := (coreClosure hs01).bexs 𝚷 (Rew.bShift_positive ty) hB
      rwa [bexs_eq_bexsLT] at this
    have hExs : EquivStrict 𝚺 (s₀ + 2) (∃⁰ ((ψ₀'.bexsLT tx).bexsLT ty)) := EquivStrict.exs_of_pi hC
    refine hExs.of_iff (fun e => ?_)
    have hrew : ∀ x y z : ℕ, ℕ ⊧/(x :> y :> z :> e) ψ₀' ↔ ℕ ⊧/(x :> y :> e) ψ₀ := by
      intro x y z
      have hb :
          (Semiterm.val (x :> y :> z :> e) (Empty.elim : Empty → ℕ) ∘
              (Rew.bShift.q.q : Rew ℒₒᵣ Empty (n + 2) Empty (n + 3)) ∘ Semiterm.bvar)
            = (x :> y :> e : Fin (n + 2) → ℕ) := by
        funext i
        cases i using Fin.cases with
        | zero =>
          simp only [Function.comp_apply, Rew.q_bvar_zero, Semiterm.val_bvar,
            Matrix.cons_val_zero]
        | succ i =>
          cases i using Fin.cases with
          | zero =>
            simp only [Function.comp_apply, Rew.q_bvar_succ, Rew.q_bvar_zero,
              Semiterm.val_bShift, Semiterm.val_bvar]
            simp
          | succ i =>
            simp only [Function.comp_apply, Rew.q_bvar_succ, Semiterm.val_bShift,
              Semiterm.val_bvar]
            simp
      have hf :
          (Semiterm.val (x :> y :> z :> e) (Empty.elim : Empty → ℕ) ∘
              (Rew.bShift.q.q : Rew ℒₒᵣ Empty (n + 2) Empty (n + 3)) ∘ Semiterm.fvar)
            = (Empty.elim : Empty → ℕ) := funext fun i => i.elim
      rw [hψ₀'def, Semiformula.eval_rew, hb, hf]
    have htyval : ∀ a : ℕ, ty.val (a :> e) Empty.elim = a + 1 := by simp [hty]
    have htxval : ∀ a b : ℕ, tx.val (a :> b :> e) Empty.elim = b + 1 := by simp [htx]
    have hleft : ℕ ⊧/e (∃⁰ ((ψ₀'.bexsLT tx).bexsLT ty)) ↔
        ∃ z, ∃ y < z + 1, ∃ x < z + 1, ℕ ⊧/(x :> y :> e) ψ₀ := by
      simp only [Semiformula.eval_ex, Semiformula.eval_bexsLT, htyval, htxval]
      refine exists_congr (fun z => exists_congr (fun y => and_congr_right (fun _ =>
        exists_congr (fun x => and_congr_right (fun _ => hrew x y z)))))
    have hright : ℕ ⊧/e (∃⁰ φ) ↔ ∃ y, ∃ x, ℕ ⊧/(x :> y :> e) ψ₀ := by
      simp only [Semiformula.eval_ex]
      exact exists_congr (fun y => (hiff' (y :> e)).symm.trans (by simp))
    rw [hleft, hright]
    exact (nat_exists_exists (fun y x => ℕ ⊧/(x :> y :> e) ψ₀)).symm

lemma all {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚷 (s + 1) φ) :
    EquivStrict 𝚷 (s + 1) (∀⁰ φ) := by
  have h' : EquivStrict 𝚺 (s + 1) (∼φ) := by simpa using h.neg
  have := (exs h').neg
  simpa using this

-- see plan §3.7 L7 (main theorem)
lemma hierarchy_equivStrict {Γ s} {φ : ArithmeticSemiformula Empty n} :
    Hierarchy Γ s φ → 1 ≤ s → EquivStrict Γ s φ := sorry

lemma mono (h : EquivStrict Γ s φ) (hs : 1 ≤ s) (hle : s ≤ s') : EquivStrict Γ s' φ := by
  rcases h with ⟨φ', hφ', hiff'⟩
  have hs' : 1 ≤ s' := le_trans hs hle
  have : EquivStrict Γ s' φ' := hierarchy_equivStrict (hφ'.hierarchy.mono hle) hs'
  exact this.of_iff hiff'

lemma mono' (h : EquivStrict Γ s φ) (hs : 1 ≤ s) (hlt : s < s') : EquivStrict Γ' s' φ := by
  rcases h with ⟨φ', hφ', hiff'⟩
  have hs' : 1 ≤ s' := le_trans hs (le_of_lt hlt)
  have : EquivStrict Γ' s' φ' := hierarchy_equivStrict (hφ'.hierarchy.strict_mono Γ' hlt) hs'
  exact this.of_iff hiff'

end EquivStrict

end LO.FirstOrder.Arithmetic
