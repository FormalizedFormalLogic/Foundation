module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# `T`-provable strict hierarchy equivalence

`StrictEquiv T Γ s φ` witnesses that `φ` is `T`-provably equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

/-- A `Type 0` model-theoretic equivalence between two formulas, valid in every model of `T`,
yields a `T`-provable biconditional via completeness. Converse of `models_iff_of_provable_iff`. -/
lemma provable_iff_of_models_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  apply Arithmetic.complete T _;
  intro V _ _;
  simpa [models_iff] using h V;

/-- A `T`-provable biconditional yields a model-theoretic equivalence in every model of `T`,
via soundness. Converse of `provable_iff_of_models_iff`. -/
lemma models_iff_of_provable_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  have := consequence_iff.mp (Theory.Proof.sound h) V inferInstance;
  simp only [models_iff, Semiformula.eval_allClosure] at this;
  simpa using this e;

-- `Type 0` specialization of `models_iff_of_provable_iff`, with `V` pinned in the statement
-- itself rather than left universe-polymorphic. Storing the general version unapplied (e.g. via
-- `have h := models_iff_of_provable_iff hp`, to be fed to `V`/`e` later) leaves `V`'s universe a
-- metavariable that `simp` fails to unify against; pinning it here avoids that.
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

-- `StrictEquiv` carries data (the witness formula), so an `Iff` between two instances of it
-- is not itself a `Prop`; state the analogue of `neg`'s converse between the truncated
-- (`Nonempty`) versions instead.
@[simp] lemma neg_iff :
    Nonempty (StrictEquiv T Γ.alt s (∼φ)) ↔ Nonempty (StrictEquiv T Γ s φ) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨by simpa using neg h⟩;
  . rintro ⟨h⟩; exact ⟨neg h⟩;

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

-- `StrictHierarchy.sigma_succ_elim` only asserts the *existence* of a witness formula (as a
-- `Prop`), so extracting it as `Type`-valued data requires one (noncomputable) application of
-- choice. Theory-independent, unlike `StrictEquiv` itself.
noncomputable def strictSigmaSuccElim {s n : ℕ} {φ : ArithmeticSemiformula Empty n}
    (h : StrictHierarchy 𝚺 (s + 1) φ) :
    Σ' ψ : ArithmeticSemiformula Empty (n + 1), φ = ∃¹ ψ ∧ StrictHierarchy 𝚷 s ψ :=
  ⟨h.sigma_succ_elim.choose, h.sigma_succ_elim.choose_spec⟩

-- `and`/`or` for `StrictHierarchy` merge two witnesses via `max`, which needs only ordered
-- semiring reasoning (available under `[𝗣𝗔⁻ ⪯ T]`), applied to a `bexs`-closure fact at the same
-- level `s`. Building that `bexs`-closure needs collection, so it is not reproduced here; callers
-- supply whatever `T`-specific bundle they already have (e.g. `closureBallBexs.bexs` for `𝗣𝗔`).
structure ClosureAndOr (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) where
  and : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T Γ s φ → StrictEquiv T Γ s ψ → StrictEquiv T Γ s (φ ⋏ ψ)
  or  : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T Γ s φ → StrictEquiv T Γ s ψ → StrictEquiv T Γ s (φ ⋎ ψ)

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {s : ℕ}

def closureAndOr_zero : ClosureAndOr T 0 where
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

noncomputable def or_sigma_step (ih : ClosureAndOr T s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T 𝚺 (s + 1) φ → StrictEquiv T 𝚺 (s + 1) ψ → StrictEquiv T 𝚺 (s + 1) (φ ⋎ ψ) := by
  intro n φ ψ hφ hψ;
  obtain ⟨φ', hφ', hφprov⟩ := hφ;
  obtain ⟨ψ', hψ', hψprov⟩ := hψ;
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

section

variable [𝗣𝗔⁻ ⪯ T]

noncomputable def and_sigma_step
    (hbexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
        t.Positive → StrictEquiv T Γ s φ → StrictEquiv T Γ s (∃¹[“x. x < !!t”] φ))
    (ih : ClosureAndOr T s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquiv T 𝚺 (s + 1) φ → StrictEquiv T 𝚺 (s + 1) ψ → StrictEquiv T 𝚺 (s + 1) (φ ⋏ ψ) := by
  intro n φ ψ hφ hψ;
  obtain ⟨φ', hφ', hφprov⟩ := hφ;
  obtain ⟨ψ', hψ', hψprov⟩ := hψ;
  have hφiff := models_iff_of_provable_iff' hφprov;
  have hψiff := models_iff_of_provable_iff' hψprov;
  obtain ⟨φ₀, rfl, hφ₀⟩ := strictSigmaSuccElim hφ';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hψ';
  have hφ₀' : StrictHierarchy 𝚷 s (φ₀ ⇜ (#0 :> (#·.succ.succ))) := hφ₀.rew (Rew.subst _);
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> (#·.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAprov⟩ := hbexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hφ₀');
  obtain ⟨B, hB, hBprov⟩ := hbexs 𝚷
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
    -- `max`-merging the two witnesses below only needs `V`'s order structure, available under
    -- `[𝗣𝗔⁻ ⪯ T]`.
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

noncomputable def closureAndOr_succ
    (hbexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
        t.Positive → StrictEquiv T Γ s φ → StrictEquiv T Γ s (∃¹[“x. x < !!t”] φ))
    (ih : ClosureAndOr T s) : ClosureAndOr T (s + 1) where
  and := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact and_sigma_step hbexs ih hφ hψ;
    . have hφ' : StrictEquiv T 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : StrictEquiv T 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have h' := neg (or_sigma_step ih hφ' hψ');
      simpa [Semiformula.imp_eq] using h';
  or := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . have hφ' : StrictEquiv T 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : StrictEquiv T 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have h' := neg (and_sigma_step hbexs ih hφ' hψ');
      simpa [Semiformula.imp_eq] using h';

noncomputable def closureAndOr
    (hbexs : ∀ s, ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
        t.Positive → StrictEquiv T Γ s φ → StrictEquiv T Γ s (∃¹[“x. x < !!t”] φ))
    {s : ℕ} : ClosureAndOr T s := by
  induction s with
  | zero => exact closureAndOr_zero;
  | succ s ih => exact closureAndOr_succ (hbexs s) ih;

end

end LO.FirstOrder.Arithmetic
