module

public import Foundation.FirstOrder.Arithmetic.Basic.Prenex
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# Prenex normal form theorem

Every `Hierarchy Γ s φ` formula is, over models of `𝗣𝗔`, equivalent to some formula in
`StrictHierarchy Γ s`, i.e. a genuine prenex normal form of the same level, and this
equivalence is provable in `𝗣𝗔`.
-/

@[expose] public section

open LO
open LO.FirstOrder

universe u

namespace LO.FirstOrder.Arithmetic

-- Every declaration below whose *type* mentions the private `StrictEquivOnPA` must itself be
-- `private`: this module's public/private visibility check forbids a public declaration's
-- signature from referring to a private identifier (bodies may still call private lemmas
-- freely). Only the three theorems in `namespace Hierarchy` at the end of the file, whose
-- statements are fully inlined, are exposed publicly.
namespace StrictEquivOnPA

private def StrictEquivOnPA (Γ : Polarity) (s : ℕ) {n : ℕ} (φ : ArithmeticSemiformula Empty n) : Prop :=
  ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ

variable {Γ Γ' : Polarity} {s s' : ℕ} {n : ℕ} {φ ψ : ArithmeticSemiformula Empty n}

private lemma refl (h : StrictHierarchy Γ s φ) : StrictEquivOnPA.{u} Γ s φ :=
  ⟨φ, h, fun _ _ _ _ => Iff.rfl⟩

private lemma of_iff (h : StrictEquivOnPA.{u} Γ s φ)
    (hiff : ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    StrictEquivOnPA.{u} Γ s ψ := by
  obtain ⟨φ', hφ', hiff'⟩ := h;
  exact ⟨φ', hφ', fun V _ _ e => (hiff V e).symm.trans (hiff' V e)⟩;

private lemma neg (h : StrictEquivOnPA.{u} Γ s φ) : StrictEquivOnPA.{u} Γ.alt s (∼φ) := by
  obtain ⟨φ', hφ', hiff'⟩ := h;
  exact ⟨∼φ', hφ'.neg, fun V _ _ e => by simp [hiff' V e]⟩;

@[simp] private lemma neg_iff : StrictEquivOnPA.{u} Γ.alt s (∼φ) ↔ StrictEquivOnPA.{u} Γ s φ := by
  constructor;
  . intro h; simpa using neg h;
  . intro h; exact neg h;

private lemma alt_up (h : StrictEquivOnPA.{u} Γ s φ) : StrictEquivOnPA.{u} Γ.alt (s + 1) φ := by
  obtain ⟨φ', hφ', hiff'⟩ := h;
  rcases Γ with _ | _;
  . use ∀¹ (Rew.bShift ▹ φ');
    and_intros;
    . exact (hφ'.rew Rew.bShift).pi;
    . intro V _ _ e;
      have : Nonempty V := ⟨0⟩;
      simp [hiff' V e];
  . use ∃¹ (Rew.bShift ▹ φ');
    and_intros;
    . exact (hφ'.rew Rew.bShift).sigma;
    . intro V _ _ e;
      simp [hiff' V e];

private lemma of_deltaZero (hp : Hierarchy 𝚺 0 φ) : StrictEquivOnPA.{u} Γ s φ := by
  induction s generalizing Γ with
  | zero => exact refl (StrictHierarchy.zero hp);
  | succ s ih => simpa using alt_up (ih (Γ := Γ.alt));

/-- The core closure properties needed at a fixed level `s`. -/
private structure CoreClosure (s : ℕ) : Prop where
  and  : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s ψ → StrictEquivOnPA.{u} Γ s (φ ⋏ ψ)
  or   : ∀ Γ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s ψ → StrictEquivOnPA.{u} Γ s (φ ⋎ ψ)
  ball : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s (∀¹[“x. x < !!t”] φ)
  bexs : ∀ Γ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} Γ s φ → StrictEquivOnPA.{u} Γ s (∃¹[“x. x < !!t”] φ)

private lemma coreClosure_zero : CoreClosure 0 where
  and := fun Γ {n φ ψ} hφ hψ => by
    obtain ⟨φ', hφ', hiffφ⟩ := hφ;
    obtain ⟨ψ', hψ', hiffψ⟩ := hψ;
    use φ' ⋏ ψ';
    and_intros;
    . exact StrictHierarchy.zero
        (Hierarchy.and (StrictHierarchy.zero_iff.mp hφ') (StrictHierarchy.zero_iff.mp hψ'));
    . intro V _ _ e;
      simp [hiffφ V e, hiffψ V e];
  or := fun Γ {n φ ψ} hφ hψ => by
    obtain ⟨φ', hφ', hiffφ⟩ := hφ;
    obtain ⟨ψ', hψ', hiffψ⟩ := hψ;
    use φ' ⋎ ψ';
    and_intros;
    . exact StrictHierarchy.zero
        (Hierarchy.or (StrictHierarchy.zero_iff.mp hφ') (StrictHierarchy.zero_iff.mp hψ'));
    . intro V _ _ e;
      simp [hiffφ V e, hiffψ V e];
  ball := fun Γ {n φ t} ht hφ => by
    obtain ⟨φ', hφ', hiff'⟩ := hφ;
    use ∀¹[“x. x < !!t”] φ';
    and_intros;
    . exact StrictHierarchy.zero (Hierarchy.ball ht (StrictHierarchy.zero_iff.mp hφ'));
    . intro V _ _ e;
      simp only [Semiformula.eval_ball];
      exact forall_congr' (fun x => imp_congr Iff.rfl (hiff' V (x :> e)));
  bexs := fun Γ {n φ t} ht hφ => by
    obtain ⟨φ', hφ', hiff'⟩ := hφ;
    use ∃¹[“x. x < !!t”] φ';
    and_intros;
    . exact StrictHierarchy.zero (Hierarchy.bexs ht (StrictHierarchy.zero_iff.mp hφ'));
    . intro V _ _ e;
      simp only [Semiformula.eval_bexs];
      exact exists_congr (fun x => and_congr Iff.rfl (hiff' V (x :> e)));

private lemma or_sigma_step (ih : CoreClosure.{u} s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) ψ → StrictEquivOnPA.{u} 𝚺 (s + 1) (φ ⋎ ψ) := by
  intro n φ ψ hφ hψ;
  obtain ⟨φ', hφ', hφiff⟩ := hφ;
  obtain ⟨ψ', hψ', hψiff⟩ := hψ;
  obtain ⟨φ₀, rfl, hφ₀⟩ := hφ'.sigma_succ_elim;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hψ'.sigma_succ_elim;
  obtain ⟨χ, hχ, hχiff⟩ := ih.or 𝚷 (refl hφ₀) (refl hψ₀);
  use ∃¹ χ;
  and_intros;
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

-- Insertion of an unused fresh variable at position 1 does not affect evaluation.
private lemma eval_insert1 {n} (θ : ArithmeticSemiformula Empty (n + 1)) (V : Type u) [ORingStructure V]
    (u w : V) (e : Fin n → V) :
    V ⊧/(u :> w :> e) (Rew.bShift.q ▹ θ) ↔ V ⊧/(u :> e) θ := by
  simp [Semiformula.eval_rew_q, Function.comp_def];

private lemma funext_two {α : Type*} {n : ℕ} {f g : Fin (n + 2) → α}
    (h0 : f 0 = g 0) (h1 : f (Fin.succ 0) = g (Fin.succ 0))
    (hs : ∀ i : Fin n, f i.succ.succ = g i.succ.succ) : f = g := by
  funext i;
  induction i using Fin.cases with
  | zero => exact h0;
  | succ i =>
    induction i using Fin.cases with
    | zero => exact h1;
    | succ i => exact hs i;

-- Insertion of an unused fresh variable at position 2 does not affect evaluation.
private lemma eval_insert2 {n} (θ : ArithmeticSemiformula Empty (n + 2)) (V : Type u) [ORingStructure V]
    (y x w : V) (e : Fin n → V) :
    V ⊧/(y :> x :> w :> e) (Rew.bShift.q.q ▹ θ) ↔ V ⊧/(y :> x :> e) θ := by
  simp only [Semiformula.eval_rew_q, Function.comp_def];
  exact Iff.of_eq (congrArg (fun b => Semiformula.Evalb (M := V) b θ)
    (funext_two (by simp) (by simp) fun i => by simp));

private lemma and_sigma_step (ih : CoreClosure.{u} s) :
    ∀ {n} {φ ψ : ArithmeticSemiformula Empty n},
      StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) ψ → StrictEquivOnPA.{u} 𝚺 (s + 1) (φ ⋏ ψ) := by
  intro n φ ψ hφ hψ;
  obtain ⟨φ', hφ', hφiff⟩ := hφ;
  obtain ⟨ψ', hψ', hψiff⟩ := hψ;
  obtain ⟨φ₀, rfl, hφ₀⟩ := hφ'.sigma_succ_elim;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hψ'.sigma_succ_elim;
  have hφ₀' : StrictHierarchy 𝚷 s (Rew.bShift.q ▹ φ₀) := hφ₀.rew Rew.bShift.q;
  have hψ₀' : StrictHierarchy 𝚷 s (Rew.bShift.q ▹ ψ₀) := hψ₀.rew Rew.bShift.q;
  obtain ⟨A, hA, hAiff⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hφ₀');
  obtain ⟨B, hB, hBiff⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl hψ₀');
  obtain ⟨χ, hχ, hχiff⟩ := ih.and 𝚷 (refl hA) (refl hB);
  use ∃¹ χ;
  and_intros;
  . exact hχ.sigma;
  . intro V _ _ e;
    have hA_eval : ∀ z : V, V ⊧/(z :> e) A ↔ ∃ x ≤ z, V ⊧/(x :> e) φ₀ := fun z => by
      rw [← hAiff V (z :> e)];
      show V ⊧/(z :> e)
        ((Rew.bShift.q ▹ φ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [eval_insert1];
    have hB_eval : ∀ z : V, V ⊧/(z :> e) B ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ₀ := fun z => by
      rw [← hBiff V (z :> e)];
      show V ⊧/(z :> e)
        ((Rew.bShift.q ▹ ψ₀ : ArithmeticSemiformula Empty (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [eval_insert1];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₀ := (hφiff V e).trans Semiformula.eval_ex;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₀ := (hψiff V e).trans Semiformula.eval_ex;
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      ← hχiff, hA_eval, hB_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

private lemma bexs_sigma_step (ih : CoreClosure.{u} s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ) := by
  intro n φ t ht hφ;
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  obtain ⟨φ', hφ', hiff'⟩ := hφ;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hφ'.sigma_succ_elim;
  -- swap the two leading bound variables of `ψ₀`, turning the order into `x :> y :> e`.
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set ψ₀' : ArithmeticSemiformula Empty (n + 2) := Rew.subst v ▹ ψ₀ with hψ₀'def;
  have hψ₀'strict : StrictHierarchy 𝚷 s ψ₀' := hψ₀.rew (Rew.subst v);
  obtain ⟨χ, hχ, hχiff⟩ := ih.bexs 𝚷 (t := Rew.bShift (Rew.bShift u))
    (by simp) (refl hψ₀'strict);
  -- `∃¹[cond]ψ₀'` is definitionally `ψ₀'.bexsLT (Rew.bShift u)`; restate `hχiff` in that
  -- form so that `Semiformula.eval_bexsLT` can fire on it as a simp lemma.
  have hχiff' : ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin (n + 1) → V),
      V ⊧/e (ψ₀'.bexsLT (Rew.bShift u)) ↔ V ⊧/e χ := hχiff;
  use ∃¹ χ;
  and_intros;
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

private lemma ball_sigma_step (ih : CoreClosure.{u} s) :
    ∀ {n} {φ : ArithmeticSemiformula Empty (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictEquivOnPA.{u} 𝚺 (s + 1) φ → StrictEquivOnPA.{u} 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ) := by
  intro n φ t ht hφ;
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  obtain ⟨φ', hφ', hiff'⟩ := hφ;
  obtain ⟨ψ₀, rfl, hψ₀⟩ := hφ'.sigma_succ_elim;
  have hψ₀qq : StrictHierarchy 𝚷 s (Rew.bShift.q.q ▹ ψ₀) := hψ₀.rew Rew.bShift.q.q;
  obtain ⟨A, hA, hAiff⟩ := ih.bexs 𝚷
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) (refl hψ₀qq);
  obtain ⟨D, hD, hDiff⟩ := ih.ball 𝚷
    (t := Rew.bShift (Rew.bShift u)) (by simp) (refl hA);
  use ∃¹ D;
  and_intros;
  . exact hD.sigma;
  . intro V _ _ e;
    have hAeval : ∀ x w : V, V ⊧/(x :> w :> e) A ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) ψ₀ := by
      intro x w;
      rw [← hAiff V (x :> w :> e)];
      simp [eval_insert2, Arithmetic.lt_succ_iff_le];
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

private lemma coreClosure_succ (ih : CoreClosure.{u} s) : CoreClosure.{u} (s + 1) where
  and := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact and_sigma_step ih hφ hψ;
    . have hφ' : StrictEquivOnPA.{u} 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : StrictEquivOnPA.{u} 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have := neg (or_sigma_step ih hφ' hψ');
      simpa [Semiformula.imp_eq] using this;
  or := fun Γ {n φ ψ} hφ hψ => by
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . have hφ' : StrictEquivOnPA.{u} 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have hψ' : StrictEquivOnPA.{u} 𝚺 (s + 1) (∼ψ) := by simpa using neg hψ;
      have := neg (and_sigma_step ih hφ' hψ');
      simpa [Semiformula.imp_eq] using this;
  ball := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact ball_sigma_step ih ht hφ;
    . have hφ' : StrictEquivOnPA.{u} 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have := neg (bexs_sigma_step ih ht hφ');
      simpa using this;
  bexs := fun Γ {n φ t} ht hφ => by
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . have hφ' : StrictEquivOnPA.{u} 𝚺 (s + 1) (∼φ) := by simpa using neg hφ;
      have := neg (ball_sigma_step ih ht hφ');
      simpa using this;

private lemma coreClosure : CoreClosure.{u} s := by
  induction s with
  | zero => exact coreClosure_zero;
  | succ s ih => exact coreClosure_succ ih;

private lemma exs {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚺 (s + 1) φ) :
    StrictEquivOnPA.{u} 𝚺 (s + 1) (∃¹ φ) := sorry

private lemma all {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚷 (s + 1) φ) :
    StrictEquivOnPA.{u} 𝚷 (s + 1) (∀¹ φ) := sorry

private lemma exs_of_pi {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚷 s φ) :
    StrictEquivOnPA.{u} 𝚺 (s + 1) (∃¹ φ) := by
  obtain ⟨φ', hφ', hiff'⟩ := h;
  use ∃¹ φ';
  and_intros;
  . exact hφ'.sigma;
  . intro V _ _ e;
    simp only [Semiformula.eval_ex];
    exact exists_congr (fun x => hiff' V (x :> e));

private lemma all_of_sigma {φ : ArithmeticSemiformula Empty (n + 1)} (h : StrictEquivOnPA.{u} 𝚺 s φ) :
    StrictEquivOnPA.{u} 𝚷 (s + 1) (∀¹ φ) := by
  obtain ⟨φ', hφ', hiff'⟩ := h;
  use ∀¹ φ';
  and_intros;
  . exact hφ'.pi;
  . intro V _ _ e;
    simp only [Semiformula.eval_all];
    exact forall_congr' (fun x => hiff' V (x :> e));

private lemma strictEquivOnPA_of_hierarchy (h : Hierarchy Γ s φ) : StrictEquivOnPA.{u} Γ s φ := sorry

end StrictEquivOnPA

namespace Hierarchy

lemma exists_strictHierarchy_form {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ :=
  StrictEquivOnPA.strictEquivOnPA_of_hierarchy h

theorem exists_strictHierarchy_provable {Γ s n} {φ : ArithmeticSemiformula Empty n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemiformula Empty n, StrictHierarchy Γ s ψ ∧ 𝗣𝗔 ⊢ ∀¹* (φ 🡘 ψ) := by
  obtain ⟨ψ, hψ, H⟩ := exists_strictHierarchy_form.{0} h;
  use ψ;
  and_intros;
  . exact hψ;
  . apply FirstOrder.Arithmetic.complete.{0} 𝗣𝗔 _ ?_;
    intro M _ _;
    simpa [models_iff] using fun e => H M e;

theorem exists_strictHierarchy_provable_of_sentence {Γ s} {σ : ArithmeticSentence} (h : Hierarchy Γ s σ) :
    ∃ π : ArithmeticSentence, StrictHierarchy Γ s π ∧ 𝗣𝗔 ⊢ σ 🡘 π := by
  obtain ⟨π, hπ, h⟩ := exists_strictHierarchy_provable h;
  exact ⟨π, hπ, h⟩;

end Hierarchy

end LO.FirstOrder.Arithmetic
