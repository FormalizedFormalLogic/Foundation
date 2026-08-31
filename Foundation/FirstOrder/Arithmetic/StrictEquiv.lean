module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# `T`-provable strict hierarchy equivalence

`StrictEquiv T Γ s φ` witnesses that `φ` is `T`-provably equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level.
`Closure T s` bundles the closure properties of `StrictEquiv T Γ s` under bounded quantification,
conjunction and disjunction, available over any theory `T` extending `𝗜𝚺 s`.
`nonempty_strictEquiv` produces such a witness for every `Hierarchy Γ s` formula.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

/-- Converse of `models_iff_of_provable_iff`. -/
lemma provable_iff_of_models_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  apply Arithmetic.complete T _;
  intro V _ _;
  simpa [models_iff] using h V;

/-- Converse of `provable_iff_of_models_iff`. -/
lemma models_iff_of_provable_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  have := consequence_iff.mp (Theory.Proof.sound h) V inferInstance;
  simp only [models_iff, Semiformula.eval_allClosure] at this;
  simpa using this e;

-- `Type 0` specialization of `models_iff_of_provable_iff`: storing the universe-polymorphic
-- version unapplied (e.g. `have h := models_iff_of_provable_iff hp`, fed to `V`/`e` later)
-- leaves `V`'s universe a metavariable that `simp` fails to unify against; pinning `V` here
-- avoids that.
lemma models_iff_of_provable_iff' {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) :
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ :=
  models_iff_of_provable_iff h

/-- A witness that `φ` is `T`-provably equivalent to some formula in `StrictHierarchy Γ s`. -/
structure StrictEquiv (T : ArithmeticTheory) (Γ : Polarity) (s : ℕ) {n : ℕ}
    (φ : ArithmeticSemiformula Empty n) where
  witness : ArithmeticSemiformula Empty n
  hierarchy : StrictHierarchy Γ s witness
  provable : T ⊢ ∀¹* (φ 🡘 witness)

namespace StrictEquiv

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}
  {φ : ArithmeticSemiformula Empty n}

lemma iff_models (d : StrictEquiv T Γ s φ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T]
    (e : Fin n → V) : V ⊧/e φ ↔ V ⊧/e d.witness :=
  models_iff_of_provable_iff d.provable V e

def refl (h : StrictHierarchy Γ s φ) : StrictEquiv T Γ s φ :=
  ⟨φ, h, provable_iff_of_models_iff fun _ _ _ _ => Iff.rfl⟩

def of_iff {ψ : ArithmeticSemiformula Empty n} (h : StrictEquiv T Γ s φ)
    (hiff : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    StrictEquiv T Γ s ψ :=
  ⟨h.witness, h.hierarchy, provable_iff_of_models_iff fun V _ _ e => (hiff V e).symm.trans (h.iff_models V e)⟩

def neg (h : StrictEquiv T Γ s φ) : StrictEquiv T Γ.alt s (∼φ) :=
  ⟨∼h.witness, h.hierarchy.neg, provable_iff_of_models_iff fun V _ _ e => by simp [h.iff_models V e]⟩

def alt_up (h : StrictEquiv T Γ s φ) : StrictEquiv T Γ.alt (s + 1) φ := by
  rcases Γ with _ | _;
  . use ∀¹ (Rew.bShift ▹ h.witness);
    . exact (h.hierarchy.rew Rew.bShift).pi;
    . apply provable_iff_of_models_iff;
      intro V _ _ e;
      have : Nonempty V := ⟨0⟩;
      simp [h.iff_models V e];
  . use ∃¹ (Rew.bShift ▹ h.witness);
    . exact (h.hierarchy.rew Rew.bShift).sigma;
    . apply provable_iff_of_models_iff;
      intro V _ _ e;
      simp [h.iff_models V e];

def of_deltaZero (hp : Hierarchy 𝚺 0 φ) : StrictEquiv T Γ s φ := by
  induction s generalizing Γ with
  | zero => exact refl (StrictHierarchy.zero hp);
  | succ s ih => simpa using alt_up (ih (Γ := Γ.alt));

def exs_of_pi {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚷 s φ) :
    StrictEquiv T 𝚺 (s + 1) (∃¹ φ) := by
  use ∃¹ h.witness;
  . exact h.hierarchy.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_ex];
    exact exists_congr (fun x => h.iff_models V (x :> e));

def all_of_sigma {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚺 s φ) :
    StrictEquiv T 𝚷 (s + 1) (∀¹ φ) := by
  use ∀¹ h.witness;
  . exact h.hierarchy.pi;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Semiformula.eval_all];
    exact forall_congr' (fun x => h.iff_models V (x :> e));

end StrictEquiv

open StrictEquiv (refl neg)

-- `StrictHierarchy.sigma_succ_elim` only asserts the *existence* of a witness formula (a `Prop`),
-- so extracting it as `Type`-valued data needs one (noncomputable) application of choice.
noncomputable def strictSigmaSuccElim {s n : ℕ} {φ : ArithmeticSemiformula Empty n}
    (h : StrictHierarchy 𝚺 (s + 1) φ) :
    Σ' ψ : ArithmeticSemiformula Empty (n + 1), φ = ∃¹ ψ ∧ StrictHierarchy 𝚷 s ψ :=
  ⟨h.sigma_succ_elim.choose, h.sigma_succ_elim.choose_spec⟩

noncomputable def bShiftWitness {n : ℕ} {t : ArithmeticSemiterm Empty (n + 1)} (ht : t.Positive) :
    Σ' u : ArithmeticSemiterm Empty n, t = Rew.bShift u :=
  ⟨(Rew.positive_iff.mp ht).choose, (Rew.positive_iff.mp ht).choose_spec⟩

-- The four closure properties are mutually dependent at each level: the polarity-flip trick builds
-- each one's `𝚷` case out of another's `𝚺` step, and the `𝚺` steps of `ball` and `and` consume
-- `bexs` at the previous level. They are therefore built by a single joint induction.
structure Closure (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) where
  ball : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv T Γ s φ → StrictEquiv T Γ s (∀¹[“x. x < !!t”] φ)
  bexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv T Γ s φ → StrictEquiv T Γ s (∃¹[“x. x < !!t”] φ)
  and : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T Γ s φ → StrictEquiv T Γ s ψ → StrictEquiv T Γ s (φ ⋏ ψ)
  or : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T Γ s φ → StrictEquiv T Γ s ψ → StrictEquiv T Γ s (φ ⋎ ψ)

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {s : ℕ}

def closure_zero : Closure T 0 where
  ball := fun Γ {n φ t} ht hφ =>
    ⟨∀¹[“x. x < !!t”] hφ.witness,
      StrictHierarchy.zero (Hierarchy.ball ht (StrictHierarchy.zero_iff.mp hφ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by
        simp only [Semiformula.eval_ball];
        exact forall_congr' (fun x => imp_congr Iff.rfl (hφ.iff_models V (x :> e)))⟩
  bexs := fun Γ {n φ t} ht hφ =>
    ⟨∃¹[“x. x < !!t”] hφ.witness,
      StrictHierarchy.zero (Hierarchy.bexs ht (StrictHierarchy.zero_iff.mp hφ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by
        simp only [Semiformula.eval_bexs];
        exact exists_congr (fun x => and_congr Iff.rfl (hφ.iff_models V (x :> e)))⟩
  and := fun Γ {n φ ψ} hφ hψ =>
    ⟨hφ.witness ⋏ hψ.witness,
      StrictHierarchy.zero
        (Hierarchy.and (StrictHierarchy.zero_iff.mp hφ.hierarchy) (StrictHierarchy.zero_iff.mp hψ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by simp [hφ.iff_models V e, hψ.iff_models V e]⟩
  or := fun Γ {n φ ψ} hφ hψ =>
    ⟨hφ.witness ⋎ hψ.witness,
      StrictHierarchy.zero
        (Hierarchy.or (StrictHierarchy.zero_iff.mp hφ.hierarchy) (StrictHierarchy.zero_iff.mp hψ.hierarchy)),
      provable_iff_of_models_iff fun V _ _ e => by simp [hφ.iff_models V e, hψ.iff_models V e]⟩

noncomputable def bexs_sigma_step (ih : Closure T s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv T 𝚺 (s + 1) φ → StrictEquiv T 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ) := by
  intro n φ t ht hφ;
  obtain ⟨u, rfl⟩ := bShiftWitness ht;
  obtain ⟨φ', hφ', hprov'⟩ := hφ;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  -- swap the two leading bound variables of `ψ₀`, turning the order into `x :> y :> e`.
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set ψ₀' : ArithmeticSemiformula Empty (n + 2) := Rew.subst v ▹ ψ₀ with hψ₀'def;
  have hψ₀'strict : StrictHierarchy 𝚷 s ψ₀' := hψ₀.rew (Rew.subst v);
  obtain ⟨χ, hχ, hχprov⟩ := ih.bexs 𝚷 (t := Rew.bShift (Rew.bShift u))
    (by simp) (refl hψ₀'strict);
  have hχiff := models_iff_of_provable_iff' hχprov;
  -- `∃¹[cond]ψ₀'` is definitionally `ψ₀'.bexsLT (Rew.bShift u)`; restate `hχiff` in that
  -- form so that `Semiformula.eval_bexsLT` can fire on it as a simp lemma.
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (ψ₀'.bexsLT (Rew.bShift u)) ↔ V ⊧/e χ := hχiff;
  use ∃¹ χ;
  . exact hχ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have hswap : ∀ (a b : V) (e : Fin n → V),
        V ⊧/(b :> a :> e) ψ₀' ↔ V ⊧/(a :> b :> e) ψ₀ := by
      intro a b e;
      show V ⊧/(b :> a :> e) (Rew.subst v ▹ ψ₀) ↔ V ⊧/(a :> b :> e) ψ₀;
      rw [Semiformula.eval_rew];
      have hA : (Semiterm.val (M := V) (b :> a :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.bvar
          = (a :> b :> e : Fin (n + 2) → V) := by
        funext i;
        cases i using Fin.cases with
        | zero => simp [hv];
        | succ i =>
          cases i using Fin.cases with
          | zero => simp [hv];
          | succ i => simp [hv];
      have hB : (Semiterm.val (M := V) (b :> a :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.fvar
          = (Empty.elim : Empty → V) := by
        funext i; exact i.elim;
      rw [hA, hB];
    have hφiff : ∀ b : V, V ⊧/(b :> e) φ ↔ ∃ a, V ⊧/(a :> b :> e) ψ₀ := fun b =>
      (hiff' V (b :> e)).trans Semiformula.eval_ex;
    show V ⊧/e (φ.bexsLT u) ↔ V ⊧/e (∃¹ χ);
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

noncomputable def ball_sigma_step (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv T 𝚺 (s + 1) φ → StrictEquiv T 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ) := by
  haveI := hT;
  intro n φ t ht hφ;
  obtain ⟨u, rfl⟩ := bShiftWitness ht;
  obtain ⟨φ', hφ', hprov'⟩ := hφ;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  have hψ₀qq : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAprov⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (refl hψ₀qq);
  have hAiff := models_iff_of_provable_iff' hAprov;
  obtain ⟨D, hD, hDprov⟩ := ih.ball 𝚷
    (t := Rew.bShift (Rew.bShift u)) (by simp) (refl hA);
  have hDiff := models_iff_of_provable_iff' hDprov;
  use ∃¹ D;
  . exact hD.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hAeval : ∀ x w : V, V ⊧/(x :> w :> e) A ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) ψ₀ := by
      intro x w;
      rw [← hAiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hDeval : ∀ w : V, V ⊧/(w :> e) D ↔ ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) ψ₀ := by
      intro w;
      rw [← hDiff V (w :> e)];
      simp [hAeval];
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) ψ₀ := fun x =>
      (hiff' V (x :> e)).trans Semiformula.eval_ex;
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ D);
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hDeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) ψ₀ := hψ₀.hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

noncomputable def or_sigma_step (ih : Closure T s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T 𝚺 (s + 1) φ → StrictEquiv T 𝚺 (s + 1) ψ → StrictEquiv T 𝚺 (s + 1) (φ ⋎ ψ) := by
  rintro n φ ψ ⟨φ', hφ', hφprov⟩ ⟨ψ', hψ', hψprov⟩;
  have hφiff := models_iff_of_provable_iff' hφprov;
  have hψiff := models_iff_of_provable_iff' hψprov;
  obtain ⟨φ₀, rfl, hφ₀⟩ := strictSigmaSuccElim hφ';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hψ';
  obtain ⟨χ, hχ, hχprov⟩ := ih.or 𝚷 (refl hφ₀) (refl hψ₀);
  have hχiff := models_iff_of_provable_iff' hχprov;
  use ∃¹ χ;
  . exact hχ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₀ := (hφiff V e).trans Semiformula.eval_ex;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₀ := (hψiff V e).trans Semiformula.eval_ex;
    simp only [LogicalConnective.HomClass.map_or, Semiformula.eval_ex, hφiff', hψiff'];
    constructor;
    . rintro (⟨x, hx⟩ | ⟨x, hx⟩);
      . exact ⟨x, (hχiff V (x :> e)).mp (by left; exact hx)⟩;
      . exact ⟨x, (hχiff V (x :> e)).mp (by right; exact hx)⟩;
    . rintro ⟨x, hx⟩;
      rcases (hχiff V (x :> e)).mpr hx with h | h;
      . left; exact ⟨x, h⟩;
      . right; exact ⟨x, h⟩;

noncomputable def and_sigma_step (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T 𝚺 (s + 1) φ → StrictEquiv T 𝚺 (s + 1) ψ → StrictEquiv T 𝚺 (s + 1) (φ ⋏ ψ) := by
  haveI : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le (s + 1))) hT;
  intro n φ ψ hφ hψ;
  obtain ⟨φ', hφ', hφprov⟩ := hφ;
  obtain ⟨ψ', hψ', hψprov⟩ := hψ;
  have hφiff := models_iff_of_provable_iff' hφprov;
  have hψiff := models_iff_of_provable_iff' hψprov;
  obtain ⟨φ₀, rfl, hφ₀⟩ := strictSigmaSuccElim hφ';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hψ';
  have hφ₀' : StrictHierarchy 𝚷 s (φ₀ ⇜ (#0 :> (#·.succ.succ))) := hφ₀.rew (Rew.subst _);
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> (#·.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAprov⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hφ₀');
  obtain ⟨B, hB, hBprov⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hψ₀');
  have hAiff := models_iff_of_provable_iff' hAprov;
  have hBiff := models_iff_of_provable_iff' hBprov;
  obtain ⟨χ, hχ, hχprov⟩ := ih.and 𝚷 (refl hA) (refl hB);
  have hχiff := models_iff_of_provable_iff' hχprov;
  use ∃¹ χ;
  . exact hχ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    -- `max`-merging the two witnesses below only needs `V`'s order structure.
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hA_eval : ∀ z : V, V ⊧/(z :> e) A ↔ ∃ x ≤ z, V ⊧/(x :> e) φ₀ := fun z => by
      rw [← hAiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₀ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemiformula Empty (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hB_eval : ∀ z : V, V ⊧/(z :> e) B ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ₀ := fun z => by
      rw [← hBiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₀ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemiformula Empty (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₀ := (hφiff V e).trans Semiformula.eval_ex;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₀ := (hψiff V e).trans Semiformula.eval_ex;
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      ← hχiff, hA_eval, hB_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

noncomputable def closure_succ (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) : Closure T (s + 1) where
  ball := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact ball_sigma_step hT ih ht hφ;
    . have hφ' : StrictEquiv T 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have h' := neg (bexs_sigma_step ih ht hφ');
      simpa using h';
  bexs := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . have hφ' : StrictEquiv T 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have h' := neg (ball_sigma_step hT ih ht hφ');
      simpa using h';
  and := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact and_sigma_step hT ih hφ hψ;
    . have hφ' : StrictEquiv T 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : StrictEquiv T 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have h' := neg (or_sigma_step ih hφ' hψ');
      simpa [Semiformula.imp_eq] using h';
  or := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . have hφ' : StrictEquiv T 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : StrictEquiv T 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have h' := neg (and_sigma_step hT ih hφ' hψ');
      simpa [Semiformula.imp_eq] using h';

noncomputable def closure (hT : 𝗜𝚺 s ⪯ T) : Closure T s := by
  induction s with
  | zero => exact closure_zero;
  | succ s ih =>
    have h : 𝗜𝚺 s ⪯ T :=
      Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.le_succ s)) hT;
    exact closure_succ hT (ih h);

-- Contracts the two nested existentials `∃x∃y` of a strict `Σ_{s+1}` witness into a single
-- bounded pair `∃z (∃x ≤ z)(∃y ≤ z)`.
noncomputable def exs (hT : 𝗜𝚺 s ⪯ T) (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚺 (s + 1) φ) :
    StrictEquiv T 𝚺 (s + 1) (∃¹ φ) := by
  haveI : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) hT;
  obtain ⟨φ', hφ', hprov'⟩ := h;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAprov⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (refl hψ₀');
  obtain ⟨B, hB, hBprov⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hA);
  have hAiff := models_iff_of_provable_iff' hAprov;
  have hBiff := models_iff_of_provable_iff' hBprov;
  have hAiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 2) → V),
      V ⊧/e ((ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemiformula Empty (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔ V ⊧/e A := hAiff;
  have hBiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (A.bexsLTSucc (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ V ⊧/e B := hBiff;
  use ∃¹ B;
  . exact hB.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    -- `max`-merging the two witnesses below only needs `V`'s order structure.
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hAeval : ∀ y z : V, V ⊧/(y :> z :> e) A ↔ ∃ x ≤ z, V ⊧/(x :> y :> e) ψ₀ := by
      intro y z;
      rw [← hAiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hBeval : ∀ z : V, V ⊧/(z :> e) B ↔ ∃ y ≤ z, V ⊧/(y :> z :> e) A := by
      intro z;
      rw [← hBiff' V (z :> e)];
      simp;
    have hφeval : ∀ y : V, V ⊧/(y :> e) φ ↔ ∃ x, V ⊧/(x :> y :> e) ψ₀ := fun y =>
      (hiff' V (y :> e)).trans Semiformula.eval_ex;
    simp only [Semiformula.eval_ex, hφeval, hBeval, hAeval];
    constructor;
    . rintro ⟨y, x, hx⟩;
      exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;
    . rintro ⟨z, y, -, x, -, hx⟩;
      exact ⟨y, x, hx⟩;

noncomputable def all (hT : 𝗜𝚺 s ⪯ T) (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv T 𝚷 (s + 1) φ) :
    StrictEquiv T 𝚷 (s + 1) (∀¹ φ) := by
  have h' : StrictEquiv T 𝚺 (s + 1) (∼φ) := neg h;
  have h'' := neg (exs hT c h');
  simpa using h'';

theorem nonempty_strictEquiv {Γ : Polarity} {n : ℕ} {φ : ArithmeticSemiformula Empty n}
    (h : Hierarchy Γ s φ) (hT : 𝗜𝚺 s ⪯ T) : Nonempty (StrictEquiv T Γ s φ) := by
  induction h with
  | verum Γ s n =>
    exact ⟨StrictEquiv.of_deltaZero (Hierarchy.verum 𝚺 0 n)⟩;
  | falsum Γ s n =>
    exact ⟨StrictEquiv.of_deltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
  | rel Γ s r v =>
    exact ⟨StrictEquiv.of_deltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
  | nrel Γ s r v =>
    exact ⟨StrictEquiv.of_deltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
  | and _ _ ihp ihq =>
    exact ⟨(closure hT).and _ (ihp hT).some (ihq hT).some⟩;
  | or _ _ ihp ihq =>
    exact ⟨(closure hT).or _ (ihp hT).some (ihq hT).some⟩;
  | ball pos _ ih =>
    exact ⟨(closure hT).ball _ pos (ih hT).some⟩;
  | bexs pos _ ih =>
    exact ⟨(closure hT).bexs _ pos (ih hT).some⟩;
  | @exs s n φ _ ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact ⟨exs hT' (closure hT') (ih hT).some⟩;
  | @all s n φ _ ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact ⟨all hT' (closure hT') (ih hT).some⟩;
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . exact ⟨StrictEquiv.refl (StrictHierarchy.sigma (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
    . exact ⟨StrictEquiv.exs_of_pi (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).some⟩;
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . exact ⟨StrictEquiv.refl (StrictHierarchy.pi (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
    . exact ⟨StrictEquiv.all_of_sigma (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).some⟩;
  | @dummy_sigma s n φ hp ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact ⟨StrictEquiv.alt_up (all hT' (closure hT') (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).some)⟩;
  | @dummy_pi s n φ hp ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact ⟨StrictEquiv.alt_up (exs hT' (closure hT') (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).some)⟩;

end LO.FirstOrder.Arithmetic
