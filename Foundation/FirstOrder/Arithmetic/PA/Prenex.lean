module

public import Foundation.FirstOrder.Arithmetic.StrictEquiv
public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# Prenex normal form theorem over $\mathsf{PA}$

Every `Hierarchy Γ s φ` formula is, over models of `𝗣𝗔`, equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level, and this
equivalence is provable in `𝗣𝗔`.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

variable {Γ : Polarity} {s : ℕ} {n : ℕ} {φ ψ : ArithmeticSemiformula Empty n}

-- `ModelEquiv` is the `Type 0`, `𝗣𝗔`-fixed model-theoretic counterpart of `StrictEquiv`: it lets
-- `CoreClosure` (the induction-closure bundle driving `of_hierarchy`) be built up purely by model
-- theory, converting the result to a `𝗣𝗔`-provable `StrictEquiv` only once, via
-- `Arithmetic.complete`, at the boundary with the public `StrictEquiv` API. It has no meaning
-- outside this file's proof and stays `private`, as does everything built on top of it. Since it
-- is `Type`-valued (not `Prop`-valued), any `def` whose *value* mentions it — not just its type —
-- must itself stay `private` too: this module's visibility check exposes a public `def`'s body
-- (unlike a `theorem`/`lemma`, where proof irrelevance means only the statement is exposed), so
-- `exs`/`all`/`of_hierarchy`/`coreClosure` and friends all stay `private` even though some of
-- their *statements* mention only the now-public `StrictEquiv`.
private structure ModelEquiv (Γ : Polarity) (s : ℕ) {n : ℕ} (φ : ArithmeticSemiformula Empty n) where
  witness : ArithmeticSemiformula Empty n
  hierarchy : StrictHierarchy Γ s witness
  iff_models : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e witness

-- Combinators are named `ModelEquiv.xxx` via dotted `def`s (rather than a `namespace ModelEquiv`
-- block) because `ModelEquiv` is `private`: opening an actual namespace of the same name shadows
-- the private-declaration alias and makes the bare identifier `ModelEquiv` unresolvable below.
private def ModelEquiv.refl (h : StrictHierarchy Γ s φ) : ModelEquiv Γ s φ :=
  ⟨φ, h, fun _ _ _ _ => Iff.rfl⟩

private def ModelEquiv.neg (h : ModelEquiv Γ s φ) : ModelEquiv Γ.alt s (∼φ) :=
  ⟨∼h.witness, h.hierarchy.neg, fun V _ _ e => by simp [h.iff_models V e]⟩

/-- Convert to the public, `𝗣𝗔`-provable `StrictEquiv`, via completeness. -/
private def ModelEquiv.toStrictEquiv (h : ModelEquiv Γ s φ) : StrictEquiv 𝗣𝗔 Γ s φ :=
  ⟨h.witness, h.hierarchy, provable_iff_of_models_iff h.iff_models⟩

/-- Convert from the public, `𝗣𝗔`-provable `StrictEquiv`, via soundness. -/
private def ModelEquiv.ofStrictEquiv (d : StrictEquiv 𝗣𝗔 Γ s φ) : ModelEquiv Γ s φ :=
  ⟨d.witness, d.hierarchy, fun V _ _ e => d.iff_models V e⟩

open ModelEquiv (refl neg)

-- `StrictHierarchy.sigma_succ_elim` and `Rew.positive_iff` only assert the *existence* of a
-- witness formula/term (as a `Prop`). Since `StrictHierarchy` and `Semiterm.Positive` are
-- `Prop`-valued, Lean forbids eliminating them into a `Type`-valued goal directly, so extracting
-- the witness as data requires one (noncomputable) application of choice.
-- `n` here is a *fresh* arity (not the ambient section `n`): callers use this both at the
-- ambient arity (`or_sigma_step`, `and_sigma_step`) and at the ambient arity `+ 1`
-- (`bexs_sigma_step`, `ball_sigma_step`, `exs`).
private noncomputable def strictSigmaSuccElim {n : ℕ} {φ : ArithmeticSemiformula Empty n}
    (h : StrictHierarchy 𝚺 (s + 1) φ) :
    Σ' ψ : ArithmeticSemiformula Empty (n + 1), φ = ∃¹ ψ ∧ StrictHierarchy 𝚷 s ψ :=
  ⟨h.sigma_succ_elim.choose, h.sigma_succ_elim.choose_spec⟩

private noncomputable def bShiftWitness {t : ArithmeticSemiterm Empty (n + 1)} (ht : t.Positive) :
    Σ' u : ArithmeticSemiterm Empty n, t = Rew.bShift u :=
  ⟨(Rew.positive_iff.mp ht).choose, (Rew.positive_iff.mp ht).choose_spec⟩

/-- The core closure properties needed at a fixed level `s`. -/
private structure CoreClosure (s : ℕ) where
  and  : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      ModelEquiv Γ s φ → ModelEquiv Γ s ψ → ModelEquiv Γ s (φ ⋏ ψ)
  or   : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      ModelEquiv Γ s φ → ModelEquiv Γ s ψ → ModelEquiv Γ s (φ ⋎ ψ)
  ball : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → ModelEquiv Γ s φ → ModelEquiv Γ s (∀¹[“x. x < !!t”] φ)
  bexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → ModelEquiv Γ s φ → ModelEquiv Γ s (∃¹[“x. x < !!t”] φ)

private def coreClosure_zero : CoreClosure 0 where
  and := fun Γ {n φ ψ} hφ hψ =>
    ⟨hφ.witness ⋏ hψ.witness,
      StrictHierarchy.zero
        (Hierarchy.and (StrictHierarchy.zero_iff.mp hφ.hierarchy) (StrictHierarchy.zero_iff.mp hψ.hierarchy)),
      fun V _ _ e => by simp [hφ.iff_models V e, hψ.iff_models V e]⟩
  or := fun Γ {n φ ψ} hφ hψ =>
    ⟨hφ.witness ⋎ hψ.witness,
      StrictHierarchy.zero
        (Hierarchy.or (StrictHierarchy.zero_iff.mp hφ.hierarchy) (StrictHierarchy.zero_iff.mp hψ.hierarchy)),
      fun V _ _ e => by simp [hφ.iff_models V e, hψ.iff_models V e]⟩
  ball := fun Γ {n φ t} ht hφ =>
    ⟨∀¹[“x. x < !!t”] hφ.witness,
      StrictHierarchy.zero (Hierarchy.ball ht (StrictHierarchy.zero_iff.mp hφ.hierarchy)),
      fun V _ _ e => by
        simp only [Semiformula.eval_ball];
        exact forall_congr' (fun x => imp_congr Iff.rfl (hφ.iff_models V (x :> e)))⟩
  bexs := fun Γ {n φ t} ht hφ =>
    ⟨∃¹[“x. x < !!t”] hφ.witness,
      StrictHierarchy.zero (Hierarchy.bexs ht (StrictHierarchy.zero_iff.mp hφ.hierarchy)),
      fun V _ _ e => by
        simp only [Semiformula.eval_bexs];
        exact exists_congr (fun x => and_congr Iff.rfl (hφ.iff_models V (x :> e)))⟩

private noncomputable def or_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      ModelEquiv 𝚺 (s + 1) φ → ModelEquiv 𝚺 (s + 1) ψ → ModelEquiv 𝚺 (s + 1) (φ ⋎ ψ) := by
  intro n φ ψ hφ hψ;
  obtain ⟨φ', hφ', hφiff⟩ := hφ;
  obtain ⟨ψ', hψ', hψiff⟩ := hψ;
  obtain ⟨φ₀, rfl, hφ₀⟩ := strictSigmaSuccElim hφ';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hψ';
  obtain ⟨χ, hχ, hχiff⟩ := ih.or 𝚷 (refl hφ₀) (refl hψ₀);
  use ∃¹ χ;
  . exact hχ.sigma;
  . intro V _ _ e;
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

private noncomputable def and_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      ModelEquiv 𝚺 (s + 1) φ → ModelEquiv 𝚺 (s + 1) ψ → ModelEquiv 𝚺 (s + 1) (φ ⋏ ψ) := by
  intro n φ ψ hφ hψ;
  obtain ⟨φ', hφ', hφiff⟩ := hφ;
  obtain ⟨ψ', hψ', hψiff⟩ := hψ;
  obtain ⟨φ₀, rfl, hφ₀⟩ := strictSigmaSuccElim hφ';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hψ';
  have hφ₀' : StrictHierarchy 𝚷 s (φ₀ ⇜ (#0 :> (#·.succ.succ))) := hφ₀.rew (Rew.subst _);
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> (#·.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAiff⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hφ₀');
  obtain ⟨B, hB, hBiff⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hψ₀');
  obtain ⟨χ, hχ, hχiff⟩ := ih.and 𝚷 (refl hA) (refl hB);
  use ∃¹ χ;
  . exact hχ.sigma;
  . intro V _ _ e;
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

private noncomputable def bexs_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → ModelEquiv 𝚺 (s + 1) φ → ModelEquiv 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ) := by
  intro n φ t ht hφ;
  obtain ⟨u, rfl⟩ := bShiftWitness ht;
  obtain ⟨φ', hφ', hiff'⟩ := hφ;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  -- swap the two leading bound variables of `ψ₀`, turning the order into `x :> y :> e`.
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set ψ₀' : ArithmeticSemiformula Empty (n + 2) := Rew.subst v ▹ ψ₀ with hψ₀'def;
  have hψ₀'strict : StrictHierarchy 𝚷 s ψ₀' := hψ₀.rew (Rew.subst v);
  obtain ⟨χ, hχ, hχiff⟩ := ih.bexs 𝚷 (t := Rew.bShift (Rew.bShift u))
    (by simp) (refl hψ₀'strict);
  -- `∃¹[cond]ψ₀'` is definitionally `ψ₀'.bexsLT (Rew.bShift u)`; restate `hχiff` in that
  -- form so that `Semiformula.eval_bexsLT` can fire on it as a simp lemma.
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 1) → V),
      V ⊧/e (ψ₀'.bexsLT (Rew.bShift u)) ↔ V ⊧/e χ := hχiff;
  use ∃¹ χ;
  . exact hχ.sigma;
  . intro V _ _ e;
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

private noncomputable def ball_sigma_step (ih : CoreClosure s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → ModelEquiv 𝚺 (s + 1) φ → ModelEquiv 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ) := by
  intro n φ t ht hφ;
  obtain ⟨u, rfl⟩ := bShiftWitness ht;
  obtain ⟨φ', hφ', hiff'⟩ := hφ;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  have hψ₀qq : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAiff⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (refl hψ₀qq);
  obtain ⟨D, hD, hDiff⟩ := ih.ball 𝚷
    (t := Rew.bShift (Rew.bShift u)) (by simp) (refl hA);
  use ∃¹ D;
  . exact hD.sigma;
  . intro V _ _ e;
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

private noncomputable def coreClosure_succ (ih : CoreClosure s) : CoreClosure (s + 1) where
  and := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact and_sigma_step ih hφ hψ;
    . have hφ' : ModelEquiv 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : ModelEquiv 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have h' := neg (or_sigma_step ih hφ' hψ');
      simpa [Semiformula.imp_eq] using h';
  or := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . have hφ' : ModelEquiv 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : ModelEquiv 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have h' := neg (and_sigma_step ih hφ' hψ');
      simpa [Semiformula.imp_eq] using h';
  ball := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact ball_sigma_step ih ht hφ;
    . have hφ' : ModelEquiv 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have h' := neg (bexs_sigma_step ih ht hφ');
      simpa using h';
  bexs := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . have hφ' : ModelEquiv 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have h' := neg (ball_sigma_step ih ht hφ');
      simpa using h';

private noncomputable def coreClosure : CoreClosure s := by
  induction s with
  | zero => exact coreClosure_zero;
  | succ s ih => exact coreClosure_succ ih;

-- Contracts the two nested existentials `∃x∃y` of a strict `Σ_{s+1}` witness into a single
-- bounded pair `∃z (∃x ≤ z)(∃y ≤ z)`, using two applications of `coreClosure.bexs`.
private noncomputable def exs {φ : ArithmeticSemiformula Empty (n + 1)} (h : ModelEquiv 𝚺 (s + 1) φ) :
    ModelEquiv 𝚺 (s + 1) (∃¹ φ) := by
  obtain ⟨φ', hφ', hiff'⟩ := h;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAiff⟩ := coreClosure.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (refl hψ₀');
  obtain ⟨B, hB, hBiff⟩ := coreClosure.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hA);
  have hAiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 2) → V),
      V ⊧/e ((ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemiformula Empty (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔ V ⊧/e A := hAiff;
  have hBiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 1) → V),
      V ⊧/e (A.bexsLTSucc (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ V ⊧/e B := hBiff;
  use ∃¹ B;
  . exact hB.sigma;
  . intro V _ _ e;
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

private noncomputable def all {φ : ArithmeticSemiformula Empty (n + 1)} (h : ModelEquiv 𝚷 (s + 1) φ) :
    ModelEquiv 𝚷 (s + 1) (∀¹ φ) := by
  have h' : ModelEquiv 𝚺 (s + 1) (∼φ) := neg h;
  have h'' := neg (exs h');
  simpa using h'';

-- `Hierarchy` is `Prop`-valued with many constructors, so `induction h` cannot directly build a
-- `StrictEquiv` (a `Type`). Prove `Nonempty (StrictEquiv 𝗣𝗔 Γ s φ)` by induction instead (a
-- legal `Prop`-target elimination) and unwrap the single needed witness via choice. The `and`/
-- `or`/`ball`/`bexs`/`exs`/`all` cases dip into the `ModelEquiv`-based `CoreClosure` machinery
-- (round-tripping through `ModelEquiv.ofStrictEquiv`/`.toStrictEquiv`), while the remaining
-- cases use the theory-generic `StrictEquiv` combinators directly.
private noncomputable def of_hierarchy (h : Hierarchy Γ s φ) : StrictEquiv 𝗣𝗔 Γ s φ := by
  -- `ψ` (from the ambient `variable`) shares `φ`'s arity `n`, so `induction h` would otherwise
  -- generalize it too, needlessly threading a spurious `∀ ψ` through every inductive case.
  clear ψ;
  have nonempty : Nonempty (StrictEquiv 𝗣𝗔 Γ s φ) := by
    induction h with
    | verum Γ s n => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.verum 𝚺 0 n)⟩;
    | falsum Γ s n => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
    | rel Γ s r v => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
    | nrel Γ s r v => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
    | and _ _ ihp ihq =>
      exact ⟨(coreClosure.and _ (ModelEquiv.ofStrictEquiv ihp.some)
        (ModelEquiv.ofStrictEquiv ihq.some)).toStrictEquiv⟩;
    | or _ _ ihp ihq =>
      exact ⟨(coreClosure.or _ (ModelEquiv.ofStrictEquiv ihp.some)
        (ModelEquiv.ofStrictEquiv ihq.some)).toStrictEquiv⟩;
    | ball pos _ ih =>
      exact ⟨(coreClosure.ball _ pos (ModelEquiv.ofStrictEquiv ih.some)).toStrictEquiv⟩;
    | bexs pos _ ih =>
      exact ⟨(coreClosure.bexs _ pos (ModelEquiv.ofStrictEquiv ih.some)).toStrictEquiv⟩;
    | exs _ ih => exact ⟨(exs (ModelEquiv.ofStrictEquiv ih.some)).toStrictEquiv⟩;
    | all _ ih => exact ⟨(all (ModelEquiv.ofStrictEquiv ih.some)).toStrictEquiv⟩;
    | @sigma s n φ hp ih =>
      rcases s with _ | s;
      . exact ⟨StrictEquiv.refl (StrictHierarchy.sigma (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
      . exact ⟨StrictEquiv.exs_of_pi ih.some⟩;
    | @pi s n φ hp ih =>
      rcases s with _ | s;
      . exact ⟨StrictEquiv.refl (StrictHierarchy.pi (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
      . exact ⟨StrictEquiv.all_of_sigma ih.some⟩;
    | dummy_sigma hp ih =>
      exact ⟨StrictEquiv.alt_up (all (ModelEquiv.ofStrictEquiv ih.some)).toStrictEquiv⟩;
    | dummy_pi hp ih =>
      exact ⟨StrictEquiv.alt_up (exs (ModelEquiv.ofStrictEquiv ih.some)).toStrictEquiv⟩;
  exact nonempty.some;

namespace Hierarchy

theorem exists_strictHierarchy_provable {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
  ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 ψ) := by
  have hEquiv := of_hierarchy h;
  exact ⟨hEquiv.witness, hEquiv.hierarchy, hEquiv.provable⟩;

lemma exists_strictHierarchy_form {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧
      ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ := by
  have hEquiv := of_hierarchy h;
  exact ⟨hEquiv.witness, hEquiv.hierarchy, hEquiv.iff_models⟩;

theorem exists_strictHierarchy_provable_of_sentence {Γ s} {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
  ∃ π : ArithmeticSentence, StrictHierarchy Γ s π ∧ 𝗣𝗔 ⊢ σ 🡘 π := by
  obtain ⟨π, hπ, h⟩ := exists_strictHierarchy_provable h;
  exact ⟨π, hπ, h⟩;

end Hierarchy

end LO.FirstOrder.Arithmetic
