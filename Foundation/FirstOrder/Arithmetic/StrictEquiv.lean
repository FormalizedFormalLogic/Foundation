module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.BoundedCollection
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# `T`-provable strict hierarchy equivalence

Every `Hierarchy Γ s` formula is `T`-provably equivalent to an alternating quantifier prefix over a
bounded matrix. The file also provides the equivalent bounded-matrix formulation.
-/

@[expose] public section

open LO
open LO.FirstOrder

namespace LO.FirstOrder.Arithmetic

lemma provable_iff_of_models_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemisentence n}
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  apply Arithmetic.complete T _;
  intro V _ _;
  simpa [models_iff] using h V;

lemma models_iff_of_provable_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemisentence n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  have := consequence_iff.mp (Theory.Proof.sound h) V inferInstance;
  simp only [models_iff, Semiformula.eval_allClosure] at this;
  simpa using this e;

-- Pinning `V` to `Type` keeps `simp` from stalling on an unsolved universe metavariable when the
-- result is stored unapplied.
lemma models_iff_of_provable_iff' {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemisentence n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) :
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e ψ :=
  models_iff_of_provable_iff h

structure PrenexEquivOf (T : ArithmeticTheory) (Γ : Polarity) (s : ℕ) (n : ℕ) (φ : ArithmeticSemisentence n)
  extends Prenex ℒₒᵣ Empty Γ s n where
  provable : T ⊢ ∀¹* (φ 🡘 ↑toPrenex)

namespace PrenexEquivOf

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s n : ℕ}

lemma iff_models (φ' : PrenexEquivOf T Γ s _ φ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
  V ⊧/e φ ↔ V ⊧/e (↑φ'.toPrenex : ArithmeticSemisentence n) :=
  models_iff_of_provable_iff φ'.provable V e

def refl (θ' : Prenex ℒₒᵣ Empty Γ s n) : PrenexEquivOf T Γ s _ (θ'.val) :=
  ⟨θ', provable_iff_of_models_iff fun _ _ _ _ ↦ Iff.rfl⟩

def ofEq (h : φ = ψ) (φ' : PrenexEquivOf T Γ s _ φ) : PrenexEquivOf T Γ s _ ψ := h ▸ φ'

def ofModelIff (φ' : PrenexEquivOf T Γ s _ φ)
    (hiff : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e ψ ↔ V ⊧/e φ) :
    PrenexEquivOf T Γ s _ ψ :=
  ⟨φ'.toPrenex,
    provable_iff_of_models_iff fun V _ _ e ↦ (hiff V e).trans (φ'.iff_models V e)⟩

def neg (φ' : PrenexEquivOf T Γ s _ φ) : PrenexEquivOf T Γ.alt s _ (∼φ) :=
  ⟨φ'.toPrenex.neg,
    provable_iff_of_models_iff fun V _ _ e ↦ by simp [φ'.iff_models V e]⟩

def altUp (φ' : PrenexEquivOf T Γ s _ φ) : PrenexEquivOf T Γ.alt (s + 1) _ φ := by
  rcases Γ with _ | _;
  . exact ⟨(φ'.rew Rew.bShift).pi,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        have : Nonempty V := ⟨0⟩;
        simp [φ'.iff_models V e]⟩;
  . exact ⟨(φ'.rew Rew.bShift).sigma,
      provable_iff_of_models_iff fun V _ _ e ↦ by simp [φ'.iff_models V e]⟩;

def ofDeltaZero (hp : Hierarchy 𝚺 0 φ) : PrenexEquivOf T Γ s _ φ := by
  induction s generalizing Γ with
  | zero => exact refl (Prenex.zero Γ φ hp);
  | succ s ih => simpa using altUp (ih (Γ := Γ.alt));

def exsOfPi (φ' : PrenexEquivOf T 𝚷 s _ φ) : PrenexEquivOf T 𝚺 (s + 1) n (∃¹ φ) :=
  ⟨φ'.sigma, provable_iff_of_models_iff fun V _ _ e ↦ by
    rw [Prenex.coe_sigma];
    exact exists_congr (fun x ↦ φ'.iff_models V (x :> e))⟩

def allOfSigma (φ' : PrenexEquivOf T 𝚺 s _ φ) : PrenexEquivOf T 𝚷 (s + 1) n (∀¹ φ) := ⟨
  φ'.pi,
  by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Prenex.coe_pi, Semiformula.eval_all];
    exact forall_congr' (fun x ↦ φ'.iff_models V (x :> e))
⟩

omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
lemma provable_sigmaInv (φ' : PrenexEquivOf T 𝚺 (s + 1) _ φ) : T ⊢ ∀¹* (φ 🡘 ∃¹ (↑φ'.sigmaInv.val)) := by
  have h := φ'.provable; rwa [φ'.coe_sigmaInv] at h

omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
lemma provable_piInv (φ' : PrenexEquivOf T 𝚷 (s + 1) _ φ) : T ⊢ ∀¹* (φ 🡘 ∀¹ (↑φ'.piInv.val)) := by
  have h := φ'.provable; rwa [φ'.coe_piInv] at h

lemma iff_models_sigmaInv (φ' : PrenexEquivOf T 𝚺 (s + 1) _ φ) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) (↑φ'.sigmaInv : ArithmeticSemisentence (n + 1)) :=
  (models_iff_of_provable_iff φ'.provable_sigmaInv V e).trans Semiformula.eval_ex

lemma iff_models_piInv (φ' : PrenexEquivOf T 𝚷 (s + 1) _ φ) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ ∀ x, V ⊧/(x :> e) (↑φ'.piInv : ArithmeticSemisentence (n + 1)) := by
  simpa [Semiformula.eval_all] using models_iff_of_provable_iff φ'.provable_piInv V e

structure Closure (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) where
  ball : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → PrenexEquivOf T Γ s _ φ →
        Nonempty (PrenexEquivOf T Γ s _ (∀¹[“x. x < !!t”] φ))
  bexs : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → PrenexEquivOf T Γ s _ φ →
        Nonempty (PrenexEquivOf T Γ s _ (∃¹[“x. x < !!t”] φ))
  and : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      PrenexEquivOf T Γ s _ φ →
      PrenexEquivOf T Γ s _ ψ →
        Nonempty (PrenexEquivOf T Γ s _ (φ ⋏ ψ))
  or : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      PrenexEquivOf T Γ s _ φ →
      PrenexEquivOf T Γ s _ ψ →
        Nonempty (PrenexEquivOf T Γ s _ (φ ⋎ ψ))

lemma closure_zero : Closure T 0 where
  ball := by
    intro Γ n φ t ht φ';
    use Prenex.zero Γ _ (Hierarchy.ball ht φ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Prenex.coe_zero, Semiformula.eval_ball];
    exact forall_congr' (fun x => imp_congr Iff.rfl (φ'.iff_models V (x :> e)));
  bexs := by
    intro Γ n φ t ht φ';
    use Prenex.zero Γ _ (Hierarchy.bexs ht φ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [Prenex.coe_zero, Semiformula.eval_bexs];
    exact exists_congr (fun x => and_congr Iff.rfl (φ'.iff_models V (x :> e)));
  and := by
    intro Γ n φ ψ φ' ψ';
    use Prenex.zero Γ _ (Hierarchy.and φ'.deltaZero ψ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [Prenex.coe_zero, φ'.iff_models V e, ψ'.iff_models V e];
  or := by
    intro Γ n φ ψ φ' ψ';
    use Prenex.zero Γ _ (Hierarchy.or φ'.deltaZero ψ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [Prenex.coe_zero, φ'.iff_models V e, ψ'.iff_models V e];

lemma bexs_sigma_step (ih : Closure T s) (ht : t.Positive)
  (φ' : PrenexEquivOf T 𝚺 (s + 1) _ φ) :
  Nonempty (PrenexEquivOf T 𝚺 (s + 1) n (∃¹[“x. x < !!t”] φ)) := by
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set φ₂ : ArithmeticSemisentence (n + 2) := Rew.subst v ▹ φ₁;
  let φ₂' : Prenex ℒₒᵣ Empty 𝚷 s (n + 2) := φ₁'.rew (Rew.subst v);
  obtain ⟨χ'⟩ := ih.bexs 𝚷 (φ := φ₂) (t := Rew.bShift (Rew.bShift u)) (by simp)
    ((refl φ₂').ofEq (by simp [φ₂', φ₂, φ₁, Prenex.coe_rew]));
  have hχiff := models_iff_of_provable_iff' χ'.provable;
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (φ₂.bexsLT (Rew.bShift u)) ↔
        V ⊧/e (↑χ'.toPrenex : ArithmeticSemisentence (n + 1)) :=
    hχiff;
  use χ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [Prenex.coe_sigma];
    have hswap : ∀ (a b : V) (e : Fin n → V),
        V ⊧/(b :> a :> e) φ₂ ↔ V ⊧/(a :> b :> e) φ₁ := by
      intro a b e;
      show V ⊧/(b :> a :> e) (Rew.subst v ▹ φ₁) ↔ V ⊧/(a :> b :> e) φ₁;
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
    have hφiff : ∀ b : V, V ⊧/(b :> e) φ ↔ ∃ a, V ⊧/(a :> b :> e) φ₁ := fun b =>
      φ'.iff_models_sigmaInv V (b :> e);
    show V ⊧/e (φ.bexsLT u) ↔
      V ⊧/e (∃¹ (↑χ'.toPrenex : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

lemma ball_sigma_step [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s) (ht : t.Positive)
  (φ' : PrenexEquivOf T 𝚺 (s + 1) _ φ) :
  Nonempty (PrenexEquivOf T 𝚺 (s + 1) n (∀¹[“x. x < !!t”] φ)) := by
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' : Prenex ℒₒᵣ Empty 𝚷 s (n + 3) :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨α'⟩ := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁, Prenex.coe_rew]));
  have hαiff := models_iff_of_provable_iff' α'.provable;
  obtain ⟨δ'⟩ := ih.ball 𝚷 (t := Rew.bShift (Rew.bShift u)) (by simp) (refl α'.toPrenex);
  have hδiff := models_iff_of_provable_iff' δ'.provable;
  use δ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [Prenex.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hαeval : ∀ x w : V, V ⊧/(x :> w :> e) (↑α'.toPrenex : ArithmeticSemisentence (n + 2)) ↔
        ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro x w;
      rw [← hαiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hδeval : ∀ w : V, V ⊧/(w :> e) (↑δ'.toPrenex : ArithmeticSemisentence (n + 1)) ↔
        ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro w;
      rw [← hδiff V (w :> e)];
      simp [hαeval];
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) φ₁ := fun x =>
      φ'.iff_models_sigmaInv V (x :> e);
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ (↑δ'.toPrenex : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hδeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) φ₁ := φ₁'.hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

lemma or_sigma_step {n} {φ ψ : ArithmeticSemisentence n} (ih : Closure T s)
    (φ' : PrenexEquivOf T 𝚺 (s + 1) _ φ)
    (ψ' : PrenexEquivOf T 𝚺 (s + 1) _ ψ) :
    Nonempty (PrenexEquivOf T 𝚺 (s + 1) _ (φ ⋎ ψ)) := by
  set φ₁' := φ'.sigmaInv;
  set ψ₁' := ψ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  obtain ⟨χ'⟩ := ih.or 𝚷 (refl φ₁') (refl ψ₁');
  have hχiff := models_iff_of_provable_iff' χ'.provable;
  use χ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [Prenex.coe_sigma];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := φ'.iff_models_sigmaInv V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := ψ'.iff_models_sigmaInv V e;
    simp only [LogicalConnective.HomClass.map_or, Semiformula.eval_ex, hφiff', hψiff'];
    constructor;
    . rintro (⟨x, hx⟩ | ⟨x, hx⟩);
      . exact ⟨x, (hχiff V (x :> e)).mp (by left; exact hx)⟩;
      . exact ⟨x, (hχiff V (x :> e)).mp (by right; exact hx)⟩;
    . rintro ⟨x, hx⟩;
      rcases (hχiff V (x :> e)).mpr hx with h | h;
      . left; exact ⟨x, h⟩;
      . right; exact ⟨x, h⟩;

lemma and_sigma_step {n} {φ ψ : ArithmeticSemisentence n} [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s)
  (φ' : PrenexEquivOf T 𝚺 (s + 1) _ φ)
  (ψ' : PrenexEquivOf T 𝚺 (s + 1) _ ψ) :
  Nonempty (PrenexEquivOf T 𝚺 (s + 1) _ (φ ⋏ ψ)) := by
  have : 𝗜𝚺₀ ⪯ T :=
    Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le (s + 1))) inferInstance;
  set φ₁' := φ'.sigmaInv;
  set ψ₁' := ψ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  let φ₂' : Prenex ℒₒᵣ Empty 𝚷 s (n + 2) :=
    φ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨α'⟩ := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁, Prenex.coe_rew]));
  let ψ₂' : Prenex ℒₒᵣ Empty 𝚷 s (n + 2) :=
    ψ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨β'⟩ := ih.bexs 𝚷 (φ := ψ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ((refl ψ₂').ofEq (by simp [ψ₂', ψ₁, Prenex.coe_rew]));
  have hαiff := models_iff_of_provable_iff' α'.provable;
  have hβiff := models_iff_of_provable_iff' β'.provable;
  obtain ⟨χ'⟩ := ih.and 𝚷 (refl α'.toPrenex) (refl β'.toPrenex);
  have hχiff := models_iff_of_provable_iff' χ'.provable;
  use χ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [Prenex.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hα_eval : ∀ z : V, V ⊧/(z :> e) (↑α'.toPrenex : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) φ₁ := fun z => by
      rw [← hαiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hβ_eval : ∀ z : V, V ⊧/(z :> e) (↑β'.toPrenex : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) ψ₁ := fun z => by
      rw [← hβiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := φ'.iff_models_sigmaInv V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := ψ'.iff_models_sigmaInv V e;
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      ← hχiff, hα_eval, hβ_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

lemma closure_succ [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s) : Closure T (s + 1) where
  ball := by
    intro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact ball_sigma_step ih ht hφ;
    . obtain ⟨χ'⟩ := bexs_sigma_step ih ht hφ.neg;
      exact ⟨by simpa using χ'.neg⟩;
  bexs := by
    intro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . obtain ⟨χ'⟩ := ball_sigma_step ih ht hφ.neg;
      exact ⟨by simpa using χ'.neg⟩;
  and := by
    intro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact and_sigma_step ih hφ hψ;
    . obtain ⟨χ'⟩ := or_sigma_step ih hφ.neg hψ.neg;
      exact ⟨by simpa [Semiformula.imp_eq] using χ'.neg⟩;
  or := by
    intro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . obtain ⟨χ'⟩ := and_sigma_step ih hφ.neg hψ.neg;
      exact ⟨by simpa [Semiformula.imp_eq] using χ'.neg⟩;

lemma closure [𝗜𝚺 s ⪯ T] : Closure T s := by
  rename_i h;
  induction s generalizing h with
  | zero => exact closure_zero;
  | succ s ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) h;
    exact closure_succ ih;

lemma exs [𝗜𝚺 s ⪯ T] (c : Closure T s) (φ' : PrenexEquivOf T 𝚺 (s + 1) _ φ) :
  Nonempty (PrenexEquivOf T 𝚺 (s + 1) n (∃¹ φ)) := by
  have : 𝗜𝚺₀ ⪯ T :=
    Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) inferInstance;
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' : Prenex ℒₒᵣ Empty 𝚷 s (n + 3) :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨α'⟩ := c.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁, Prenex.coe_rew]));
  obtain ⟨β'⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl α'.toPrenex);
  have hαiff := models_iff_of_provable_iff' α'.provable;
  have hβiff := models_iff_of_provable_iff' β'.provable;
  have hαiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 2) → V),
      V ⊧/e ((φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemisentence (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔
      V ⊧/e (↑α'.toPrenex : ArithmeticSemisentence (n + 2)) :=
    hαiff;
  have hβiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e ((↑α'.toPrenex : ArithmeticSemisentence (n + 2)).bexsLTSucc
        (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔
      V ⊧/e (↑β'.toPrenex : ArithmeticSemisentence (n + 1)) :=
    hβiff;
  use β'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [Prenex.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hαeval : ∀ y z : V, V ⊧/(y :> z :> e) (↑α'.toPrenex : ArithmeticSemisentence (n + 2)) ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ₁ := by
      intro y z;
      rw [← hαiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hβeval : ∀ z : V, V ⊧/(z :> e) (↑β'.toPrenex : ArithmeticSemisentence (n + 1)) ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e) (↑α'.toPrenex : ArithmeticSemisentence (n + 2)) := by
      intro z;
      rw [← hβiff' V (z :> e)];
      simp;
    have hφeval : ∀ y : V, V ⊧/(y :> e) φ ↔ ∃ x, V ⊧/(x :> y :> e) φ₁ := fun y =>
      φ'.iff_models_sigmaInv V (y :> e);
    simp only [Semiformula.eval_ex, hφeval, hβeval, hαeval];
    constructor;
    . rintro ⟨y, x, hx⟩;
      exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;
    . rintro ⟨z, y, -, x, -, hx⟩;
      exact ⟨y, x, hx⟩;

lemma all [𝗜𝚺 s ⪯ T] (c : Closure T s) (φ' : PrenexEquivOf T 𝚷 (s + 1) _ φ) :
  Nonempty (PrenexEquivOf T 𝚷 (s + 1) n (∀¹ φ)) := by
  obtain ⟨χ'⟩ := exs c φ'.neg;
  exact ⟨by simpa using χ'.neg⟩;

end PrenexEquivOf

open PrenexEquivOf (refl ofDeltaZero exsOfPi allOfSigma altUp closure exs all)

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}

theorem nonempty_prenexEquivOf (h : Hierarchy Γ s φ) [𝗜𝚺 s ⪯ T] : Nonempty (PrenexEquivOf T Γ s n φ) := by
  rename_i hT;
  induction h generalizing hT  with
  | verum Γ s n => exact ⟨ofDeltaZero (Hierarchy.verum 𝚺 0 n)⟩;
  | falsum Γ s n => exact ⟨ofDeltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
  | rel Γ s r v => exact ⟨ofDeltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
  | nrel Γ s r v => exact ⟨ofDeltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
  | and _ _ ihp ihq =>
    obtain ⟨φ'⟩ := ihp; obtain ⟨ψ'⟩ := ihq;
    exact closure.and _ φ' ψ';
  | or _ _ ihp ihq =>
    obtain ⟨φ'⟩ := ihp; obtain ⟨ψ'⟩ := ihq;
    exact closure.or _ φ' ψ';
  | ball pos _ ih => obtain ⟨φ'⟩ := ih; exact closure.ball _ pos φ';
  | bexs pos _ ih => obtain ⟨φ'⟩ := ih; exact closure.bexs _ pos φ';
  | @exs s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨φ'⟩ := ih;
    exact exs closure φ';
  | @all s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨φ'⟩ := ih;
    exact all closure φ';
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . use (Prenex.zero 𝚷 φ (Hierarchy.zero_iff.mp hp)).sigma;
      simp [provable_iff_of_models_iff];
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
      exact ih.map exsOfPi;
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . use (Prenex.zero 𝚺 φ (Hierarchy.zero_iff.mp hp)).pi;
      simp [provable_iff_of_models_iff];
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
      exact ih.map allOfSigma;
  | @dummy_sigma s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨φ'⟩ := ih;
    obtain ⟨ψ'⟩ := all closure φ';
    exact ⟨altUp ψ'⟩;
  | @dummy_pi s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    obtain ⟨φ'⟩ := ih;
    obtain ⟨ψ'⟩ := exs closure φ';
    exact ⟨altUp ψ'⟩;

variable (T : ArithmeticTheory) {Γ : Polarity} {s n : ℕ} [𝗜𝚺 s ⪯ T]

theorem exists_matrix_provable (h : Hierarchy Γ s φ) :
  ∃ φ₀ : ArithmeticSemisentence (n + s), Hierarchy 𝚺 0 φ₀ ∧ T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans inferInstance (ISigma_weakerThan_of_le_trans (Nat.zero_le s) ‹𝗜𝚺 s ⪯ T›);
  obtain ⟨φ'⟩ := nonempty_prenexEquivOf (T := T) h;
  exact ⟨φ'.matrix, φ'.toPrenex.matrix_Δ₀, φ'.provable⟩;

theorem exists_matrix_provable' (h : Hierarchy Γ s φ) :
    ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀.val) := by
  obtain ⟨φ₀, hφ₀, hprov⟩ := exists_matrix_provable T h;
  exact ⟨.mkSigma φ₀ hφ₀, by simpa using hprov⟩;

end LO.FirstOrder.Arithmetic
