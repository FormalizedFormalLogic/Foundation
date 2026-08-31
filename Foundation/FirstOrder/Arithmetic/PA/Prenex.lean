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

variable {Γ : Polarity} {s : ℕ} {n : ℕ} {φ : ArithmeticSemiformula Empty n}

-- `ClosureBallBexs` (the ball/bexs induction-closure bundle driving `of_hierarchy`, needing
-- collection so it stays `𝗣𝗔`-fixed) and everything built on top of it (`exs`/`all`/`of_hierarchy`
-- and friends) have no meaning outside this file's proof and stay `private`, even though their
-- *statements* mention only the now-public `StrictEquiv`: since these `def`s are `Type`-valued
-- (not `Prop`-valued), this module's visibility check exposes a public `def`'s body (unlike a
-- `theorem`/`lemma`, where proof irrelevance means only the statement is exposed). Each step here
-- drops from `StrictEquiv` (provable) to a bare model-theoretic `Iff` via
-- `models_iff_of_provable_iff`, does the actual combinatorics purely model-theoretically, then
-- climbs back to `StrictEquiv` via `provable_iff_of_models_iff` (i.e. `Arithmetic.complete`) at
-- the very end. (The `and`/`or` counterpart, `ClosureAndOr`, needs no collection and lives,
-- theory-generically, in `StrictEquiv.lean`.)
open StrictEquiv (refl neg)

private noncomputable def bShiftWitness {t : ArithmeticSemiterm Empty (n + 1)} (ht : t.Positive) :
    Σ' u : ArithmeticSemiterm Empty n, t = Rew.bShift u :=
  ⟨(Rew.positive_iff.mp ht).choose, (Rew.positive_iff.mp ht).choose_spec⟩

-- `ball` and `bexs` are mutually dependent at each level (the polarity-flip trick builds each
-- one's `𝚷` case out of the *other*'s `𝚺` step), so they are constructed by a single joint
-- induction below. `and`/`or` (`ClosureAndOr` further down) never need `ball`, only `bexs`, so
-- once this closure is available for every `s` they are proved by a separate, independent
-- induction that simply reads off `bexs` at each level.
private structure ClosureBallBexs (s : ℕ) where
  ball : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv 𝗣𝗔 Γ s φ → StrictEquiv 𝗣𝗔 Γ s (∀¹[“x. x < !!t”] φ)
  bexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv 𝗣𝗔 Γ s φ → StrictEquiv 𝗣𝗔 Γ s (∃¹[“x. x < !!t”] φ)

private def closureBallBexs_zero : ClosureBallBexs 0 where
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

private noncomputable def bexs_sigma_step (ih : ClosureBallBexs s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv 𝗣𝗔 𝚺 (s + 1) φ → StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ) := by
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
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 1) → V),
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

private noncomputable def ball_sigma_step (ih : ClosureBallBexs s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquiv 𝗣𝗔 𝚺 (s + 1) φ → StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ) := by
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

private noncomputable def closureBallBexs_succ (ih : ClosureBallBexs s) : ClosureBallBexs (s + 1) where
  ball := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact ball_sigma_step ih ht hφ;
    . have hφ' : StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have h' := neg (bexs_sigma_step ih ht hφ');
      simpa using h';
  bexs := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . have hφ' : StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have h' := neg (ball_sigma_step ih ht hφ');
      simpa using h';

private noncomputable def closureBallBexs : ClosureBallBexs s := by
  induction s with
  | zero => exact closureBallBexs_zero;
  | succ s ih => exact closureBallBexs_succ ih;

-- `ClosureAndOr` (theory-generic, in `StrictEquiv.lean`) only needs a `bexs`-closure fact at
-- each level, not the full `ball`/`bexs` induction; specialize it to `𝗣𝗔` here by feeding it
-- `closureBallBexs.bexs`.
private noncomputable def paClosureAndOr : ClosureAndOr 𝗣𝗔 s :=
  closureAndOr (fun _s => closureBallBexs.bexs)

-- Contracts the two nested existentials `∃x∃y` of a strict `Σ_{s+1}` witness into a single
-- bounded pair `∃z (∃x ≤ z)(∃y ≤ z)`, using two applications of `closureBallBexs.bexs`.
private noncomputable def exs {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv 𝗣𝗔 𝚺 (s + 1) φ) :
    StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∃¹ φ) := by
  obtain ⟨φ', hφ', hprov'⟩ := h;
  have hiff' := models_iff_of_provable_iff' hprov';
  obtain ⟨ψ₀, rfl, hψ₀⟩ := strictSigmaSuccElim hφ';
  have hψ₀' : StrictHierarchy 𝚷 s (ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ))) := hψ₀.rew (Rew.subst _);
  obtain ⟨A, hA, hAprov⟩ := closureBallBexs.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (refl hψ₀');
  obtain ⟨B, hB, hBprov⟩ := closureBallBexs.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hA);
  have hAiff := models_iff_of_provable_iff' hAprov;
  have hBiff := models_iff_of_provable_iff' hBprov;
  have hAiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 2) → V),
      V ⊧/e ((ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemiformula Empty (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔ V ⊧/e A := hAiff;
  have hBiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 1) → V),
      V ⊧/e (A.bexsLTSucc (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ V ⊧/e B := hBiff;
  use ∃¹ B;
  . exact hB.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
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

private noncomputable def all {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquiv 𝗣𝗔 𝚷 (s + 1) φ) :
    StrictEquiv 𝗣𝗔 𝚷 (s + 1) (∀¹ φ) := by
  have h' : StrictEquiv 𝗣𝗔 𝚺 (s + 1) (∼φ) := neg h;
  have h'' := neg (exs h');
  simpa using h'';

-- `Hierarchy` is `Prop`-valued with many constructors, so `induction h` cannot directly build a
-- `StrictEquiv` (a `Type`). Prove `Nonempty (StrictEquiv 𝗣𝗔 Γ s φ)` by induction instead (a
-- legal `Prop`-target elimination) and unwrap the single needed witness via choice.
private noncomputable def of_hierarchy (h : Hierarchy Γ s φ) : StrictEquiv 𝗣𝗔 Γ s φ := by
  have nonempty : Nonempty (StrictEquiv 𝗣𝗔 Γ s φ) := by
    induction h with
    | verum Γ s n => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.verum 𝚺 0 n)⟩;
    | falsum Γ s n => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
    | rel Γ s r v => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
    | nrel Γ s r v => exact ⟨StrictEquiv.of_deltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
    | and _ _ ihp ihq => exact ⟨paClosureAndOr.and _ ihp.some ihq.some⟩;
    | or _ _ ihp ihq => exact ⟨paClosureAndOr.or _ ihp.some ihq.some⟩;
    | ball pos _ ih => exact ⟨closureBallBexs.ball _ pos ih.some⟩;
    | bexs pos _ ih => exact ⟨closureBallBexs.bexs _ pos ih.some⟩;
    | exs _ ih => exact ⟨exs ih.some⟩;
    | all _ ih => exact ⟨all ih.some⟩;
    | @sigma s n φ hp ih =>
      rcases s with _ | s;
      . exact ⟨StrictEquiv.refl (StrictHierarchy.sigma (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
      . exact ⟨StrictEquiv.exs_of_pi ih.some⟩;
    | @pi s n φ hp ih =>
      rcases s with _ | s;
      . exact ⟨StrictEquiv.refl (StrictHierarchy.pi (StrictHierarchy.zero (Hierarchy.zero_iff.mp hp)))⟩;
      . exact ⟨StrictEquiv.all_of_sigma ih.some⟩;
    | dummy_sigma hp ih => exact ⟨StrictEquiv.alt_up (all ih.some)⟩;
    | dummy_pi hp ih => exact ⟨StrictEquiv.alt_up (exs ih.some)⟩;
  exact nonempty.some;

theorem Peano.exists_strictHierarchy_provable {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
  ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 ψ) := by
  have hEquiv := of_hierarchy h;
  exact ⟨hEquiv.witness, hEquiv.hierarchy, hEquiv.provable⟩;

theorem Peano.exists_strictHierarchy_provable_of_sentence {Γ s} {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
  ∃ π : ArithmeticSentence, StrictHierarchy Γ s π ∧ 𝗣𝗔 ⊢ σ 🡘 π := by
  obtain ⟨π, hπ, h⟩ := Peano.exists_strictHierarchy_provable h;
  exact ⟨π, hπ, h⟩;

end LO.FirstOrder.Arithmetic
