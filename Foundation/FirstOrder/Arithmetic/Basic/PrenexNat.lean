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

-- Pure Nat statement, no dependency on formulas.
lemma nat_collection (m : ℕ) (P : ℕ → ℕ → Prop) :
    (∀ x < m, ∃ y, P x y) ↔ (∃ w, ∀ x < m, ∃ y < w, P x y) := by
  constructor
  · induction m with
    | zero => intro _; exact ⟨0, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
    | succ n ih =>
      intro h
      have h' : ∀ x < n, ∃ y, P x y := fun x hx => h x (Nat.lt_succ_of_lt hx)
      obtain ⟨w, hw⟩ := ih h'
      obtain ⟨y, hy⟩ := h n (Nat.lt_succ_self n)
      refine ⟨max w (y + 1), fun x hx => ?_⟩
      rcases (Nat.lt_succ_iff.mp hx).lt_or_eq with hx' | hx'
      · obtain ⟨y', hy'w, hy'⟩ := hw x hx'
        exact ⟨y', lt_of_lt_of_le hy'w (le_max_left w (y + 1)), hy'⟩
      · subst hx'
        exact ⟨y, lt_of_lt_of_le (Nat.lt_succ_self y) (le_max_right w (y + 1)), hy⟩
  · rintro ⟨w, hw⟩ x hx
    obtain ⟨y, _, hy⟩ := hw x hx
    exact ⟨y, hy⟩

lemma nat_exists_and_exists (P Q : ℕ → Prop) :
    ((∃ x, P x) ∧ (∃ y, Q y)) ↔ ∃ z, (∃ x < z + 1, P x) ∧ (∃ y < z + 1, Q y) := by
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨max x y, ⟨x, Nat.lt_succ_iff.mpr (le_max_left x y), hx⟩,
      ⟨y, Nat.lt_succ_iff.mpr (le_max_right x y), hy⟩⟩
  · rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

lemma nat_exists_exists (P : ℕ → ℕ → Prop) :
    (∃ x y, P x y) ↔ ∃ z, ∃ x < z + 1, ∃ y < z + 1, P x y := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨max x y, x, Nat.lt_succ_iff.mpr (le_max_left x y),
      y, Nat.lt_succ_iff.mpr (le_max_right x y), hxy⟩
  · rintro ⟨z, x, _, y, _, hxy⟩
    exact ⟨x, y, hxy⟩

-- Bridge between `ball`/`bexs` notation and `ballLT`/`bexsLT`.
@[simp, grind] lemma ball_eq_ballLT {n} (φ : ArithmeticSemiformula Empty (n + 1)) (u : ArithmeticSemiterm Empty n) :
    (∀⁰[“x. x < !!(Rew.bShift u)”] φ) = φ.ballLT u := rfl

@[simp, grind] lemma bexs_eq_bexsLT {n} (φ : ArithmeticSemiformula Empty (n + 1)) (u : ArithmeticSemiterm Empty n) :
    (∃⁰[“x. x < !!(Rew.bShift u)”] φ) = φ.bexsLT u := rfl

namespace EquivStrict

variable {Γ Γ' : Polarity} {s s' : ℕ} {n : ℕ} {φ ψ : ArithmeticSemiformula Empty n}

@[grind] lemma refl (h : StrictHierarchy Γ s φ) : EquivStrict Γ s φ := ⟨φ, h, fun _ => Iff.rfl⟩

lemma of_iff (h : EquivStrict Γ s φ) (hiff : ∀ e : Fin n → ℕ, ℕ ⊧/e φ ↔ ℕ ⊧/e ψ) :
    EquivStrict Γ s ψ := by
  rcases h with ⟨φ', hφ', hiff'⟩
  exact ⟨φ', hφ', fun e => (hiff' e).trans (hiff e)⟩

@[grind] lemma neg (h : EquivStrict Γ s φ) : EquivStrict Γ.alt s (∼φ) := by
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

@[grind] lemma alt_up (h : EquivStrict Γ (s + 1) φ) : EquivStrict Γ.alt (s + 2) φ := by
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

@[grind] lemma of_deltaZero (hp : Hierarchy 𝚺 0 φ) (hs : 1 ≤ s) : EquivStrict Γ s φ := by
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

lemma coreClosure_one : CoreClosure 1 where
  and {Γ n φ ψ} := by
    rintro ⟨φ', hφ', hiffφ⟩ ⟨ψ', hψ', hiffψ⟩
    exact ⟨φ' ⋏ ψ', StrictHierarchy.base (Hierarchy.and hφ'.hierarchy hψ'.hierarchy),
      fun e => and_congr (hiffφ e) (hiffψ e)⟩
  or {Γ n φ ψ} := by
    rintro ⟨φ', hφ', hiffφ⟩ ⟨ψ', hψ', hiffψ⟩
    exact ⟨φ' ⋎ ψ', StrictHierarchy.base (Hierarchy.or hφ'.hierarchy hψ'.hierarchy),
      fun e => or_congr (hiffφ e) (hiffψ e)⟩
  ball := fun Γ {n φ t} ht hφ => by
    rcases hφ with ⟨φ', hφ', hiff'⟩
    refine ⟨∀⁰[“x. x < !!t”] φ', StrictHierarchy.base (Hierarchy.ball ht hφ'.hierarchy), fun e => ?_⟩
    simp only [Semiformula.eval_ball]
    exact forall_congr' (fun x => imp_congr Iff.rfl (hiff' (x :> e)))
  bexs := fun Γ {n φ t} ht hφ => by
    rcases hφ with ⟨φ', hφ', hiff'⟩
    refine ⟨∃⁰[“x. x < !!t”] φ', StrictHierarchy.base (Hierarchy.bexs ht hφ'.hierarchy), fun e => ?_⟩
    simp only [Semiformula.eval_bexs]
    exact exists_congr (fun x => and_congr Iff.rfl (hiff' (x :> e)))

lemma or_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) ψ → EquivStrict 𝚺 (s + 2) (φ ⋎ ψ) := by
  intro n φ ψ hφ hψ
  rcases hφ with ⟨φ', hφ', hφiff'⟩
  rcases hψ with ⟨ψ', hψ', hψiff'⟩
  obtain ⟨φ₀, rfl, hφ₀⟩ := hφ'.sigma_succ_elim
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hψ'.sigma_succ_elim
  obtain ⟨χ, hχ, hχiff⟩ := ih.or 𝚷 (EquivStrict.refl hφ₀) (EquivStrict.refl hψ₀)
  refine ⟨∃⁰ χ, hχ.exs, fun e => ?_⟩
  simp only [Semiformula.eval_ex]
  constructor
  · rintro ⟨x, hx⟩
    rcases (hχiff (x :> e)).mp hx with h | h
    · exact Or.inl ((hφiff' e).mp ⟨x, h⟩)
    · exact Or.inr ((hψiff' e).mp ⟨x, h⟩)
  · rintro (h | h)
    · obtain ⟨x, hx⟩ := (hφiff' e).mpr h
      exact ⟨x, (hχiff (x :> e)).mpr (Or.inl hx)⟩
    · obtain ⟨x, hx⟩ := (hψiff' e).mpr h
      exact ⟨x, (hχiff (x :> e)).mpr (Or.inr hx)⟩

-- Confluence of existentials.
lemma and_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) ψ → EquivStrict 𝚺 (s + 2) (φ ⋏ ψ) := by
  intro n φ ψ hφ hψ
  rcases hφ with ⟨φ', hφ', hiffφ⟩
  rcases hψ with ⟨ψ', hψ', hiffψ⟩
  obtain ⟨φ₀, rfl, hφ₀⟩ := StrictHierarchy.sigma_succ_elim hφ'
  obtain ⟨ψ₀, rfl, hψ₀⟩ := StrictHierarchy.sigma_succ_elim hψ'
  -- Insert a fresh variable `z` at position 1 (so the context becomes `x :> z :> e`).
  have hφ₀' : StrictHierarchy 𝚷 (s + 1) (Rew.bShift.q ▹ φ₀) := hφ₀.rew Rew.bShift.q
  have hψ₀' : StrictHierarchy 𝚷 (s + 1) (Rew.bShift.q ▹ ψ₀) := hψ₀.rew Rew.bShift.q
  -- The guard term `z + 1`, in the ambient context `z :> e`.
  set u : ArithmeticSemiterm Empty (n + 1) := ‘#0 + 1’ with hu_def
  have hu_pos : (Rew.bShift u).Positive := Rew.bShift_positive u
  have hA : EquivStrict 𝚷 (s + 1) ((Rew.bShift.q ▹ φ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLT u) :=
    ih.bexs 𝚷 hu_pos (EquivStrict.refl hφ₀')
  have hB : EquivStrict 𝚷 (s + 1) ((Rew.bShift.q ▹ ψ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLT u) :=
    ih.bexs 𝚷 hu_pos (EquivStrict.refl hψ₀')
  have hAB : EquivStrict 𝚷 (s + 1)
      ((Rew.bShift.q ▹ φ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLT u ⋏
        (Rew.bShift.q ▹ ψ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLT u) :=
    ih.and 𝚷 hA hB
  obtain ⟨χ, hχ, hiffχ⟩ := hAB
  refine ⟨∃⁰ χ, hχ.exs, fun e => ?_⟩
  -- Evaluation of the shifted witnesses: inserting `z` does not affect `φ₀`/`ψ₀`.
  have hφ₀_eval : ∀ x z : ℕ, ℕ ⊧/(x :> z :> e) (Rew.bShift.q ▹ φ₀) ↔ ℕ ⊧/(x :> e) φ₀ := by
    intro x z
    have hb : (fun i : Fin (n + 1) =>
        Semiterm.val (M := ℕ) (x :> z :> e) Empty.elim
          ((Rew.bShift.q : Rew ℒₒᵣ Empty (n + 1) Empty (n + 2)) #i)) = x :> e := by
      funext i; cases i using Fin.cases <;> simp
    simp [Semiformula.eval_rew, Function.comp_def, hb]
  have hψ₀_eval : ∀ y z : ℕ, ℕ ⊧/(y :> z :> e) (Rew.bShift.q ▹ ψ₀) ↔ ℕ ⊧/(y :> e) ψ₀ := by
    intro y z
    have hb : (fun i : Fin (n + 1) =>
        Semiterm.val (M := ℕ) (y :> z :> e) Empty.elim
          ((Rew.bShift.q : Rew ℒₒᵣ Empty (n + 1) Empty (n + 2)) #i)) = y :> e := by
      funext i; cases i using Fin.cases <;> simp
    simp [Semiformula.eval_rew, Function.comp_def, hb]
  have hu_val : ∀ z : ℕ, u.val (z :> e) Empty.elim = z + 1 := by
    intro z; simp [hu_def]
  have hA_eval : ∀ z : ℕ,
      ℕ ⊧/(z :> e) ((Rew.bShift.q ▹ φ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLT u) ↔
        ∃ x < z + 1, ℕ ⊧/(x :> e) φ₀ := by
    intro z
    simp [Semiformula.eval_bexsLT, hu_val z, hφ₀_eval]
  have hB_eval : ∀ z : ℕ,
      ℕ ⊧/(z :> e) ((Rew.bShift.q ▹ ψ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLT u) ↔
        ∃ y < z + 1, ℕ ⊧/(y :> e) ψ₀ := by
    intro z
    simp [Semiformula.eval_bexsLT, hu_val z, hψ₀_eval]
  have step1 : ℕ ⊧/e (∃⁰ χ) ↔
      ∃ z, (∃ x < z + 1, ℕ ⊧/(x :> e) φ₀) ∧ (∃ y < z + 1, ℕ ⊧/(y :> e) ψ₀) := by
    simp only [Semiformula.eval_ex]
    refine exists_congr fun z => ?_
    rw [hiffχ (z :> e)]
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    exact and_congr (hA_eval z) (hB_eval z)
  -- `nat_exists_and_exists`-style confluence of existentials via `z = max x y`; proved inline
  -- (rather than by invoking the eponymous lemma later in the file) since it is used here
  -- before that lemma's declaration point.
  have step2 : ((∃ x, ℕ ⊧/(x :> e) φ₀) ∧ (∃ y, ℕ ⊧/(y :> e) ψ₀)) ↔
      ∃ z, (∃ x < z + 1, ℕ ⊧/(x :> e) φ₀) ∧ (∃ y < z + 1, ℕ ⊧/(y :> e) ψ₀) := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨max x y, ⟨x, Nat.lt_succ_iff.mpr (le_max_left x y), hx⟩,
        ⟨y, Nat.lt_succ_iff.mpr (le_max_right x y), hy⟩⟩
    · rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  rw [step1, ← step2]
  have hφ_iff : (∃ x, ℕ ⊧/(x :> e) φ₀) ↔ ℕ ⊧/e φ := Semiformula.eval_ex.symm.trans (hiffφ e)
  have hψ_iff : (∃ y, ℕ ⊧/(y :> e) ψ₀) ↔ ℕ ⊧/e ψ := Semiformula.eval_ex.symm.trans (hiffψ e)
  rw [hφ_iff, hψ_iff]
  simp [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]

-- Quantifier swap.
lemma bexs_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) (∃⁰[“x. x < !!t”] φ) := by
  intro n φ t ht hφ
  -- `t` is positive, hence of the shape `Rew.bShift u`.
  rcases Rew.positive_iff.mp ht with ⟨u, rfl⟩
  rcases hφ with ⟨φ', hφ', hiff'⟩
  -- `φ'` is (strict) Σ_{s+2}, so `φ' = ∃⁰ ψ₀` with `ψ₀` strict Π_{s+1}, bound order `y :> x :> e`.
  rcases StrictHierarchy.sigma_succ_elim hφ' with ⟨ψ₀, rfl, hψ₀⟩
  -- swap the two leading bound variables of `ψ₀`, turning the order into `x :> y :> e`.
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv
  set ψ₀' : ArithmeticSemiformula Empty (n + 2) := Rew.subst v ▹ ψ₀ with hψ₀'def
  have hψ₀' : StrictHierarchy 𝚷 (s + 1) ψ₀' := hψ₀.rew (Rew.subst v)
  -- evaluation of `ψ₀'` under `b :> a :> e` is the evaluation of `ψ₀` under `a :> b :> e` (the swap).
  have hswap : ∀ (a b : ℕ) (e : Fin n → ℕ),
      ℕ ⊧/(b :> a :> e) ψ₀' ↔ ℕ ⊧/(a :> b :> e) ψ₀ := by
    intro a b e
    show ℕ ⊧/(b :> a :> e) (Rew.subst v ▹ ψ₀) ↔ ℕ ⊧/(a :> b :> e) ψ₀
    rw [Semiformula.eval_rew]
    have hA : (Semiterm.val (b :> a :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.bvar
        = (a :> b :> e : Fin (n + 2) → ℕ) := by
      funext i
      cases i using Fin.cases with
      | zero => simp [hv]
      | succ i =>
        cases i using Fin.cases with
        | zero => simp [hv]
        | succ i => simp [hv]
    have hB : (Semiterm.val (b :> a :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.fvar
        = (Empty.elim : Empty → ℕ) := by
      funext i; exact i.elim
    rw [hA, hB]
  -- the guard, lifted to the `y :> x :> e` context of `ψ₀'`, is `Rew.bShift (Rew.bShift u)`.
  have key : EquivStrict 𝚷 (s + 1) (ψ₀'.bexsLT (Rew.bShift u)) :=
    ih.bexs 𝚷 (t := Rew.bShift (Rew.bShift u)) (by simp) (EquivStrict.refl hψ₀')
  rcases key with ⟨χ, hχ, hiffχ⟩
  refine ⟨∃⁰ χ, hχ.exs, fun e => ?_⟩
  -- the goal `∃⁰[x < !!(Rew.bShift u)] φ` is definitionally `φ.bexsLT u`, so `eval_bexsLT` applies.
  show ℕ ⊧/e (∃⁰ χ) ↔ ℕ ⊧/e (φ.bexsLT u)
  -- `ℕ ⊧/(b :> e) φ ↔ ∃ a, ℕ ⊧/(a :> b :> e) ψ₀`, obtained from the witness `φ' = ∃⁰ ψ₀` of `φ`.
  have hφ_iff : ∀ b : ℕ, ℕ ⊧/(b :> e) φ ↔ ∃ a, ℕ ⊧/(a :> b :> e) ψ₀ := by
    intro b
    rw [← hiff' (b :> e)]
    simp [Semiformula.eval_ex]
  simp only [Semiformula.eval_ex, hiffχ, Semiformula.eval_bexsLT, Semiterm.val_bShift, hswap, hφ_iff]
  grind

-- Collection (hardest case).
lemma ball_sigma_step (ih : CoreClosure (s + 1)) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → EquivStrict 𝚺 (s + 2) φ → EquivStrict 𝚺 (s + 2) (∀⁰[“x. x < !!t”] φ) := by
  intro n φ t ht hφ
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht
  obtain ⟨φ', hφ'strict, hφ'iff⟩ := hφ
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hφ'strict.sigma_succ_elim
  -- Lift `ψ₀` (context `y :> x :> e`) to context `y :> x :> w :> e`, the new
  -- variable `w` being ignored (this is exactly what `Rew.bShift.q.q` does:
  -- it fixes `#0` and `#1` and shifts everything from `#2` on by one).
  have hψ₀' : StrictHierarchy 𝚷 (s + 1) (Rew.bShift.q.q ▹ ψ₀) := hψ₀.rew _
  have hψ₀'eval : ∀ (y x w : ℕ) (e : Fin n → ℕ),
      ℕ ⊧/(y :> x :> w :> e) (Rew.bShift.q.q ▹ ψ₀) ↔ ℕ ⊧/(y :> x :> e) ψ₀ := by
    intro y x w e
    have hb : (Semiterm.val (y :> x :> w :> e) Empty.elim ∘
        (Rew.bShift.q.q : Rew ℒₒᵣ Empty (n + 2) Empty (n + 3)) ∘ Semiterm.bvar) = (y :> x :> e) := by
      funext i
      cases i using Fin.cases with
      | zero =>
        rw [Function.comp_apply, Function.comp_apply, Rew.q_bvar_zero]
        rfl
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          rw [Function.comp_apply, Function.comp_apply, Rew.q_bvar_succ, Rew.q_bvar_zero,
            Rew.bShift_bvar]
          rfl
        | succ i =>
          rw [Function.comp_apply, Function.comp_apply, Rew.q_bvar_succ, Rew.q_bvar_succ,
            Rew.bShift_bvar, Rew.bShift_bvar]
          rfl
    have hf : (Semiterm.val (y :> x :> w :> e) Empty.elim ∘
        (Rew.bShift.q.q : Rew ℒₒᵣ Empty (n + 2) Empty (n + 3)) ∘ Semiterm.fvar) = Empty.elim := by
      funext i; exact i.elim
    simp only [Semiformula.eval_rew, hb, hf]
  -- Inner step: bind `y` under `y < w` (context `x :> w :> e`).
  have hC : EquivStrict 𝚷 (s + 1)
      ((Rew.bShift.q.q ▹ ψ₀).bexsLT (#1 : ArithmeticSemiterm Empty (n + 2))) :=
    ih.bexs 𝚷 (t := Rew.bShift (#1 : ArithmeticSemiterm Empty (n + 2)))
      (Rew.bShift_positive _) (EquivStrict.refl hψ₀')
  -- Middle step: bind `x` under `x < u` (context `w :> e`).
  have hD : EquivStrict 𝚷 (s + 1)
      (((Rew.bShift.q.q ▹ ψ₀).bexsLT (#1 : ArithmeticSemiterm Empty (n + 2))).ballLT
        (Rew.bShift u)) :=
    ih.ball 𝚷 (t := Rew.bShift (Rew.bShift u)) (Rew.bShift_positive _) hC
  obtain ⟨χ, hχstrict, hχiff⟩ := hD
  -- Outer step: existentially quantify the collection bound `w`.
  refine ⟨∃⁰ χ, hχstrict.exs, fun e => ?_⟩
  have hcollect := nat_collection (u.valb e) (fun x y => ℕ ⊧/(y :> x :> e) ψ₀)
  have hDeval : ∀ w, ℕ ⊧/(w :> e) (((Rew.bShift.q.q ▹ ψ₀).bexsLT
      (#1 : ArithmeticSemiterm Empty (n + 2))).ballLT (Rew.bShift u)) ↔
      ∀ x < u.valb e, ∃ y < w, ℕ ⊧/(y :> x :> e) ψ₀ := by
    intro w
    simp only [Semiformula.eval_ballLT, Semiterm.val_bShift, Semiformula.eval_bexsLT]
    exact forall_congr' fun x => forall_congr' fun _ =>
      exists_congr fun y => and_congr_right fun _ => hψ₀'eval y x w e
  have hφx : ∀ x, ℕ ⊧/(x :> e) φ ↔ ∃ y, ℕ ⊧/(y :> x :> e) ψ₀ := fun x => (hφ'iff (x :> e)).symm
  calc
    ℕ ⊧/e (∃⁰ χ) ↔ ∃ w, ℕ ⊧/(w :> e) χ := Semiformula.eval_ex
    _ ↔ ∃ w, ∀ x < u.valb e, ∃ y < w, ℕ ⊧/(y :> x :> e) ψ₀ :=
        exists_congr fun w => (hχiff (w :> e)).trans (hDeval w)
    _ ↔ ∀ x < u.valb e, ∃ y, ℕ ⊧/(y :> x :> e) ψ₀ := hcollect.symm
    _ ↔ ∀ x < u.valb e, ℕ ⊧/(x :> e) φ := forall_congr' fun x => forall_congr' fun _ => (hφx x).symm
    _ ↔ ℕ ⊧/e (∀⁰[“x. x < !!(Rew.bShift u)”] φ) := by simp

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

@[grind] lemma coreClosure (hs : 1 ≤ s) : CoreClosure s := by
  induction s with
  | zero => omega
  | succ s ih =>
    rcases s with _ | s
    · exact coreClosure_one
    · exact coreClosure_succ (ih (by omega))

@[grind] lemma and (hs : 1 ≤ s) (hφ : EquivStrict Γ s φ) (hψ : EquivStrict Γ s ψ) : EquivStrict Γ s (φ ⋏ ψ) :=
  (coreClosure hs).and Γ hφ hψ

@[grind] lemma or (hs : 1 ≤ s) (hφ : EquivStrict Γ s φ) (hψ : EquivStrict Γ s ψ) : EquivStrict Γ s (φ ⋎ ψ) :=
  (coreClosure hs).or Γ hφ hψ

@[grind] lemma ball {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)}
    (hs : 1 ≤ s) (ht : t.Positive) (hφ : EquivStrict Γ s φ) : EquivStrict Γ s (∀⁰[“x. x < !!t”] φ) :=
  (coreClosure hs).ball Γ ht hφ

@[grind] lemma bexs {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)}
    (hs : 1 ≤ s) (ht : t.Positive) (hφ : EquivStrict Γ s φ) : EquivStrict Γ s (∃⁰[“x. x < !!t”] φ) :=
  (coreClosure hs).bexs Γ ht hφ

@[grind] lemma exs_of_pi {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚷 (s + 1) φ) :
    EquivStrict 𝚺 (s + 2) (∃⁰ φ) := by
  rcases h with ⟨φ', hφ', hiff'⟩
  refine ⟨∃⁰ φ', hφ'.exs, fun e => ?_⟩
  simp only [Semiformula.eval_ex]
  exact exists_congr (fun x => hiff' (x :> e))

@[grind] lemma all_of_sigma {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚺 (s + 1) φ) :
    EquivStrict 𝚷 (s + 2) (∀⁰ φ) := by
  rcases h with ⟨φ', hφ', hiff'⟩
  refine ⟨∀⁰ φ', hφ'.all, fun e => ?_⟩
  simp only [Semiformula.eval_all]
  exact forall_congr' (fun x => hiff' (x :> e))

@[grind] lemma exs {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚺 (s + 1) φ) :
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
            simp only [Function.comp_apply, Rew.q_bvar_succ, Rew.q_bvar_zero, Semiterm.val_bShift, Semiterm.val_bvar]
            simp
          | succ i =>
            simp only [Function.comp_apply, Rew.q_bvar_succ, Semiterm.val_bShift, Semiterm.val_bvar]
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

@[grind] lemma all {φ : ArithmeticSemiformula Empty (n + 1)} (h : EquivStrict 𝚷 (s + 1) φ) :
    EquivStrict 𝚷 (s + 1) (∀⁰ φ) := by
  have h' : EquivStrict 𝚺 (s + 1) (∼φ) := by simpa using h.neg
  have := (exs h').neg
  simpa using this

-- Note: the outer binders are named `Γ₀ s₀ n₀` (rather than the ambient section names
-- `Γ s n`) to avoid an elaboration issue where recursive self-calls to
-- `hierarchy_equivStrict` inside this very definition would get their implicit level/arity
-- arguments incorrectly unified with the *outer* case's own indices whenever the section
-- variables `Γ s n` (used by `EquivStrict.exs`/`all`/`alt_up` etc.) shared the same names as
-- this lemma's own bound variables.
@[grind] lemma hierarchy_equivStrict {Γ₀ s₀} {φ₀ : ArithmeticSemiformula Empty n₀} :
  Hierarchy Γ₀ s₀ φ₀ → 1 ≤ s₀ → EquivStrict Γ₀ s₀ φ₀
  | .verum _ _ _, hs => EquivStrict.of_deltaZero (Hierarchy.verum 𝚺 0 _) hs
  | .falsum _ _ _, hs => EquivStrict.of_deltaZero (Hierarchy.falsum 𝚺 0 _) hs
  | .rel _ _ r v, hs => EquivStrict.of_deltaZero (Hierarchy.rel 𝚺 0 r v) hs
  | .nrel _ _ r v, hs => EquivStrict.of_deltaZero (Hierarchy.nrel 𝚺 0 r v) hs
  | .and hp hq, hs => EquivStrict.and hs (hierarchy_equivStrict hp hs) (hierarchy_equivStrict hq hs)
  | .or hp hq, hs => EquivStrict.or hs (hierarchy_equivStrict hp hs) (hierarchy_equivStrict hq hs)
  | .ball pos hp, hs => EquivStrict.ball hs pos (hierarchy_equivStrict hp hs)
  | .bexs pos hp, hs => EquivStrict.bexs hs pos (hierarchy_equivStrict hp hs)
  | .exs hp, hs => EquivStrict.exs (hierarchy_equivStrict hp hs)
  | .all hp, hs => EquivStrict.all (hierarchy_equivStrict hp hs)
  | .sigma (s := 0) hp, _ => EquivStrict.refl (StrictHierarchy.base (Hierarchy.sigma hp))
  | .sigma (s := k + 1) hp, _ => EquivStrict.exs_of_pi (hierarchy_equivStrict hp (by omega))
  | .pi (s := 0) hp, _ => EquivStrict.refl (StrictHierarchy.base (Hierarchy.pi hp))
  | .pi (s := k + 1) hp, _ => EquivStrict.all_of_sigma (hierarchy_equivStrict hp (by omega))
  | .dummy_pi (s := k) hp, _ => (EquivStrict.exs (hierarchy_equivStrict hp (by omega))).alt_up
  | .dummy_sigma (s := k) hp, _ => (EquivStrict.all (hierarchy_equivStrict hp (by omega))).alt_up

@[grind] lemma mono (h : EquivStrict Γ s φ) (hs : 1 ≤ s) (hle : s ≤ s') : EquivStrict Γ s' φ := by
  rcases h with ⟨φ', hφ', hiff'⟩
  have hs' : 1 ≤ s' := le_trans hs hle
  have : EquivStrict Γ s' φ' := hierarchy_equivStrict (hφ'.hierarchy.mono hle) hs'
  exact this.of_iff hiff'

@[grind] lemma mono' (h : EquivStrict Γ s φ) (hs : 1 ≤ s) (hlt : s < s') : EquivStrict Γ' s' φ := by
  rcases h with ⟨φ', hφ', hiff'⟩
  have hs' : 1 ≤ s' := le_trans hs (le_of_lt hlt)
  have : EquivStrict Γ' s' φ' := hierarchy_equivStrict (hφ'.hierarchy.strict_mono Γ' hlt) hs'
  exact this.of_iff hiff'

end EquivStrict

end LO.FirstOrder.Arithmetic
