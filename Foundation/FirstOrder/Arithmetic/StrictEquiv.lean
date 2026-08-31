module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.BoundedCollection
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# `T`-provable strict hierarchy equivalence

Every `Hierarchy Γ s` formula is `T`-provably equivalent to an alternating quantifier prefix over a
bounded kernel. The file also provides the equivalent bounded-kernel formulation.
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

structure StrictHierarchyFormulaEquivOf (T : ArithmeticTheory) (Γ : Polarity) (s : ℕ) {n : ℕ}
    (φ : ArithmeticSemisentence n) extends StrictHierarchyFormula ℒₒᵣ Empty Γ s n where
  provable : T ⊢ ∀¹* (φ 🡘 ↑toStrictHierarchyFormula)

namespace StrictHierarchyFormulaEquivOf

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}
  {φ ψ : ArithmeticSemisentence n}

@[coe] def val (φ' : StrictHierarchyFormulaEquivOf T Γ s φ) : ArithmeticSemisentence n :=
  ↑φ'.toStrictHierarchyFormula

instance : CoeTC (StrictHierarchyFormulaEquivOf T Γ s φ) (ArithmeticSemisentence n) := ⟨val⟩

-- Simp normalizes towards `↑φ'.toStrictHierarchyFormula`, matching the structure field
-- `provable`; the short `↑φ'` spelling above is purely for writing terms concisely.
omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
@[simp] lemma val_eq_coe_toStrictHierarchyFormula (φ' : StrictHierarchyFormulaEquivOf T Γ s φ) :
    (↑φ' : ArithmeticSemisentence n) = ↑φ'.toStrictHierarchyFormula := rfl

lemma iff_models (φ' : StrictHierarchyFormulaEquivOf T Γ s φ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e (↑φ' : ArithmeticSemisentence n) :=
  models_iff_of_provable_iff φ'.provable V e

lemma iff_models' (φ' : StrictHierarchyFormulaEquivOf T Γ s φ) :
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V),
      V ⊧/e φ ↔ V ⊧/e (↑φ' : ArithmeticSemisentence n) :=
  models_iff_of_provable_iff' φ'.provable

def refl (θ : StrictHierarchyFormula ℒₒᵣ Empty Γ s n) :
    StrictHierarchyFormulaEquivOf T Γ s (↑θ : ArithmeticSemisentence n) :=
  ⟨θ, provable_iff_of_models_iff fun _ _ _ _ ↦ Iff.rfl⟩

def ofEq (h : φ = ψ) (φ' : StrictHierarchyFormulaEquivOf T Γ s φ) :
    StrictHierarchyFormulaEquivOf T Γ s ψ := h ▸ φ'

def ofModelIff (φ' : StrictHierarchyFormulaEquivOf T Γ s φ)
    (hiff : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e ψ ↔ V ⊧/e φ) :
    StrictHierarchyFormulaEquivOf T Γ s ψ :=
  ⟨φ'.toStrictHierarchyFormula,
    provable_iff_of_models_iff fun V _ _ e ↦ (hiff V e).trans (φ'.iff_models V e)⟩

def neg (φ' : StrictHierarchyFormulaEquivOf T Γ s φ) :
    StrictHierarchyFormulaEquivOf T Γ.alt s (∼φ) :=
  ⟨φ'.toStrictHierarchyFormula.neg,
    provable_iff_of_models_iff fun V _ _ e ↦ by simp [φ'.iff_models V e]⟩

def altUp (φ' : StrictHierarchyFormulaEquivOf T Γ s φ) :
    StrictHierarchyFormulaEquivOf T Γ.alt (s + 1) φ := by
  rcases Γ with _ | _;
  . exact ⟨(φ'.rew Rew.bShift).pi,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        have : Nonempty V := ⟨0⟩;
        simp [φ'.iff_models V e]⟩;
  . exact ⟨(φ'.rew Rew.bShift).sigma,
      provable_iff_of_models_iff fun V _ _ e ↦ by simp [φ'.iff_models V e]⟩;

def ofDeltaZero (hp : Hierarchy 𝚺 0 φ) : StrictHierarchyFormulaEquivOf T Γ s φ := by
  induction s generalizing Γ with
  | zero => exact refl (StrictHierarchyFormula.zero Γ φ hp);
  | succ s ih => simpa using altUp (ih (Γ := Γ.alt));

def exsOfPi {φ : ArithmeticSemisentence (n + 1)} (φ' : StrictHierarchyFormulaEquivOf T 𝚷 s φ) :
    StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (∃¹ φ) :=
  ⟨φ'.sigma, provable_iff_of_models_iff fun V _ _ e ↦ by
    rw [StrictHierarchyFormula.coe_sigma];
    exact exists_congr (fun x ↦ φ'.iff_models V (x :> e))⟩

def allOfSigma {φ : ArithmeticSemisentence (n + 1)} (φ' : StrictHierarchyFormulaEquivOf T 𝚺 s φ) :
    StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) (∀¹ φ) :=
  ⟨φ'.pi, provable_iff_of_models_iff fun V _ _ e ↦ by
    simp only [StrictHierarchyFormula.coe_pi, Semiformula.eval_all];
    exact forall_congr' (fun x ↦ φ'.iff_models V (x :> e))⟩

omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
lemma provable_sigmaInv (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) :
    T ⊢ ∀¹* (φ 🡘 ∃¹ (↑φ'.sigmaInv : ArithmeticSemisentence (n + 1))) := by
  have h := φ'.provable; rwa [φ'.coe_sigmaInv] at h

omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
lemma provable_piInv (φ' : StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) φ) :
    T ⊢ ∀¹* (φ 🡘 ∀¹ (↑φ'.piInv : ArithmeticSemisentence (n + 1))) := by
  have h := φ'.provable; rwa [φ'.coe_piInv] at h

lemma iff_models_sigmaInv (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) (↑φ'.sigmaInv : ArithmeticSemisentence (n + 1)) :=
  (models_iff_of_provable_iff φ'.provable_sigmaInv V e).trans Semiformula.eval_ex

lemma iff_models_sigmaInv' (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) :
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V),
      V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) (↑φ'.sigmaInv : ArithmeticSemisentence (n + 1)) :=
  fun V _ _ e ↦ φ'.iff_models_sigmaInv V e

lemma iff_models_piInv (φ' : StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) φ) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ ∀ x, V ⊧/(x :> e) (↑φ'.piInv : ArithmeticSemisentence (n + 1)) := by
  simpa [Semiformula.eval_all] using models_iff_of_provable_iff φ'.provable_piInv V e

lemma iff_models_piInv' (φ' : StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) φ) :
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V),
      V ⊧/e φ ↔ ∀ x, V ⊧/(x :> e) (↑φ'.piInv : ArithmeticSemisentence (n + 1)) :=
  fun V _ _ e ↦ φ'.iff_models_piInv V e

structure Closure (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) : Prop where
  ball : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → Nonempty (StrictHierarchyFormulaEquivOf T Γ s φ) →
        Nonempty (StrictHierarchyFormulaEquivOf T Γ s (∀¹[“x. x < !!t”] φ))
  bexs : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → Nonempty (StrictHierarchyFormulaEquivOf T Γ s φ) →
        Nonempty (StrictHierarchyFormulaEquivOf T Γ s (∃¹[“x. x < !!t”] φ))
  and : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      Nonempty (StrictHierarchyFormulaEquivOf T Γ s φ) →
      Nonempty (StrictHierarchyFormulaEquivOf T Γ s ψ) →
        Nonempty (StrictHierarchyFormulaEquivOf T Γ s (φ ⋏ ψ))
  or : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      Nonempty (StrictHierarchyFormulaEquivOf T Γ s φ) →
      Nonempty (StrictHierarchyFormulaEquivOf T Γ s ψ) →
        Nonempty (StrictHierarchyFormulaEquivOf T Γ s (φ ⋎ ψ))

lemma closure_zero : Closure T 0 where
  ball := by
    rintro Γ n φ t ht ⟨φ'⟩;
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.ball ht φ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [StrictHierarchyFormula.coe_zero, Semiformula.eval_ball];
    exact forall_congr' (fun x => imp_congr Iff.rfl (φ'.iff_models V (x :> e)));
  bexs := by
    rintro Γ n φ t ht ⟨φ'⟩;
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.bexs ht φ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [StrictHierarchyFormula.coe_zero, Semiformula.eval_bexs];
    exact exists_congr (fun x => and_congr Iff.rfl (φ'.iff_models V (x :> e)));
  and := by
    rintro Γ n φ ψ ⟨φ'⟩ ⟨ψ'⟩;
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.and φ'.deltaZero ψ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [StrictHierarchyFormula.coe_zero, φ'.iff_models V e, ψ'.iff_models V e];
  or := by
    rintro Γ n φ ψ ⟨φ'⟩ ⟨ψ'⟩;
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.or φ'.deltaZero ψ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [StrictHierarchyFormula.coe_zero, φ'.iff_models V e, ψ'.iff_models V e];

lemma bexs_sigma_step {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)}
    (ih : Closure T s) (ht : t.Positive) :
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) →
      Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ)) := by
  rintro ⟨φ'⟩;
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  set φ'' := φ'.sigmaInv;
  set ψ₀ : ArithmeticSemisentence (n + 2) := ↑φ'';
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set ψ₀' : ArithmeticSemisentence (n + 2) := Rew.subst v ▹ ψ₀;
  let φ''' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 2) := φ''.rew (Rew.subst v);
  obtain ⟨χ⟩ := ih.bexs 𝚷 (φ := ψ₀') (t := Rew.bShift (Rew.bShift u)) (by simp)
    ⟨(refl φ''').ofEq (by simp [φ''', ψ₀', ψ₀, StrictHierarchyFormula.coe_rew])⟩;
  have hχiff := χ.iff_models';
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (ψ₀'.bexsLT (Rew.bShift u)) ↔ V ⊧/e (↑χ : ArithmeticSemisentence (n + 1)) :=
    hχiff;
  use χ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
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
      φ'.iff_models_sigmaInv V (b :> e);
    show V ⊧/e (φ.bexsLT u) ↔ V ⊧/e (∃¹ (↑χ : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

lemma ball_sigma_step {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)}
    (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) (ht : t.Positive) :
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) →
      Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ)) := by
  have := hT;
  rintro ⟨φ'⟩;
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  set φ'' := φ'.sigmaInv;
  set ψ₀ : ArithmeticSemisentence (n + 2) := ↑φ'';
  let φ''' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 3) :=
    φ''.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨A⟩ := ih.bexs 𝚷 (φ := ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ⟨(refl φ''').ofEq (by simp [φ''', ψ₀, StrictHierarchyFormula.coe_rew])⟩;
  have hAiff := models_iff_of_provable_iff' A.provable;
  obtain ⟨D⟩ := ih.ball 𝚷 (t := Rew.bShift (Rew.bShift u)) (by simp) ⟨refl A.toStrictHierarchyFormula⟩;
  have hDiff := models_iff_of_provable_iff' D.provable;
  use D.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hAeval : ∀ x w : V, V ⊧/(x :> w :> e) (↑A.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) ↔
        ∃ y ≤ w, V ⊧/(y :> x :> e) ψ₀ := by
      intro x w;
      rw [← hAiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hDeval : ∀ w : V, V ⊧/(w :> e) (↑D.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
        ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) ψ₀ := by
      intro w;
      rw [← hDiff V (w :> e)];
      simp [hAeval];
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) ψ₀ := fun x =>
      φ'.iff_models_sigmaInv V (x :> e);
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ (↑D.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hDeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) ψ₀ := φ''.hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

lemma or_sigma_step {n} {φ ψ : ArithmeticSemisentence n} (ih : Closure T s) :
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) →
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) ψ) →
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (φ ⋎ ψ)) := by
  rintro ⟨φ'⟩ ⟨ψ'⟩;
  set φ'' := φ'.sigmaInv;
  set ψ'' := ψ'.sigmaInv;
  set φ₀ : ArithmeticSemisentence (n + 1) := ↑φ'';
  set ψ₀ : ArithmeticSemisentence (n + 1) := ↑ψ'';
  obtain ⟨χ⟩ := ih.or 𝚷 ⟨refl φ''⟩ ⟨refl ψ''⟩;
  have hχiff := χ.iff_models';
  use χ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₀ := φ'.iff_models_sigmaInv V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₀ := ψ'.iff_models_sigmaInv V e;
    simp only [LogicalConnective.HomClass.map_or, Semiformula.eval_ex, hφiff', hψiff'];
    constructor;
    . rintro (⟨x, hx⟩ | ⟨x, hx⟩);
      . exact ⟨x, (hχiff V (x :> e)).mp (by left; exact hx)⟩;
      . exact ⟨x, (hχiff V (x :> e)).mp (by right; exact hx)⟩;
    . rintro ⟨x, hx⟩;
      rcases (hχiff V (x :> e)).mpr hx with h | h;
      . left; exact ⟨x, h⟩;
      . right; exact ⟨x, h⟩;

lemma and_sigma_step {n} {φ ψ : ArithmeticSemisentence n} (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) :
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) →
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) ψ) →
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (φ ⋏ ψ)) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le (s + 1))) hT;
  rintro ⟨φ'⟩ ⟨ψ'⟩;
  set φ'' := φ'.sigmaInv;
  set ψ'' := ψ'.sigmaInv;
  set φ₀ : ArithmeticSemisentence (n + 1) := ↑φ'';
  set ψ₀ : ArithmeticSemisentence (n + 1) := ↑ψ'';
  let φ''' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 2) :=
    φ''.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨A⟩ := ih.bexs 𝚷 (φ := φ₀ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ⟨(refl φ''').ofEq (by simp [φ''', φ₀, StrictHierarchyFormula.coe_rew])⟩;
  let ψ''' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 2) :=
    ψ''.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨B⟩ := ih.bexs 𝚷 (φ := ψ₀ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ⟨(refl ψ''').ofEq (by simp [ψ''', ψ₀, StrictHierarchyFormula.coe_rew])⟩;
  have hAiff := models_iff_of_provable_iff' A.provable;
  have hBiff := models_iff_of_provable_iff' B.provable;
  obtain ⟨χ⟩ := ih.and 𝚷 ⟨refl A.toStrictHierarchyFormula⟩ ⟨refl B.toStrictHierarchyFormula⟩;
  have hχiff := models_iff_of_provable_iff' χ.provable;
  use χ.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hA_eval : ∀ z : V, V ⊧/(z :> e) (↑A.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) φ₀ := fun z => by
      rw [← hAiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₀ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hB_eval : ∀ z : V, V ⊧/(z :> e) (↑B.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) ψ₀ := fun z => by
      rw [← hBiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₀ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₀ := φ'.iff_models_sigmaInv V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₀ := ψ'.iff_models_sigmaInv V e;
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      ← hχiff, hA_eval, hB_eval];
    constructor;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
    . rintro ⟨z, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;

lemma closure_succ (hT : 𝗜𝚺 (s + 1) ⪯ T) (ih : Closure T s) : Closure T (s + 1) where
  ball := by
    rintro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact ball_sigma_step hT ih ht hφ;
    . simpa using (bexs_sigma_step ih ht (hφ.map neg)).map neg;
  bexs := by
    rintro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact bexs_sigma_step ih ht hφ;
    . simpa using (ball_sigma_step hT ih ht (hφ.map neg)).map neg;
  and := by
    rintro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact and_sigma_step hT ih hφ hψ;
    . simpa [Semiformula.imp_eq] using (or_sigma_step ih (hφ.map neg) (hψ.map neg)).map neg;
  or := by
    rintro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact or_sigma_step ih hφ hψ;
    . simpa [Semiformula.imp_eq] using (and_sigma_step hT ih (hφ.map neg) (hψ.map neg)).map neg;

lemma closure (hT : 𝗜𝚺 s ⪯ T) : Closure T s := by
  induction s with
  | zero => exact closure_zero;
  | succ s ih =>
    exact closure_succ hT (ih (ISigma_weakerThan_of_le_trans (by omega) hT));

lemma exs (hT : 𝗜𝚺 s ⪯ T) (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemisentence (n + 1)}
    (h : Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ)) :
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (∃¹ φ)) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) hT;
  obtain ⟨φ'⟩ := h;
  set φ'' := φ'.sigmaInv;
  set ψ₀ : ArithmeticSemisentence (n + 2) := ↑φ'';
  let φ''' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 3) :=
    φ''.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨A⟩ := c.bexs 𝚷 (φ := ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ⟨(refl φ''').ofEq (by simp [φ''', ψ₀, StrictHierarchyFormula.coe_rew])⟩;
  obtain ⟨B⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ⟨refl A.toStrictHierarchyFormula⟩;
  have hAiff := models_iff_of_provable_iff' A.provable;
  have hBiff := models_iff_of_provable_iff' B.provable;
  have hAiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 2) → V),
      V ⊧/e ((ψ₀ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemisentence (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔
      V ⊧/e (↑A.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) :=
    hAiff;
  have hBiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e ((↑A.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)).bexsLTSucc
        (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔
      V ⊧/e (↑B.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) :=
    hBiff;
  use B.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hAeval : ∀ y z : V, V ⊧/(y :> z :> e) (↑A.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) ψ₀ := by
      intro y z;
      rw [← hAiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hBeval : ∀ z : V, V ⊧/(z :> e) (↑B.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e) (↑A.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) := by
      intro z;
      rw [← hBiff' V (z :> e)];
      simp;
    have hφeval : ∀ y : V, V ⊧/(y :> e) φ ↔ ∃ x, V ⊧/(x :> y :> e) ψ₀ := fun y =>
      φ'.iff_models_sigmaInv V (y :> e);
    simp only [Semiformula.eval_ex, hφeval, hBeval, hAeval];
    constructor;
    . rintro ⟨y, x, hx⟩;
      exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;
    . rintro ⟨z, y, -, x, -, hx⟩;
      exact ⟨y, x, hx⟩;

lemma all (hT : 𝗜𝚺 s ⪯ T) (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemisentence (n + 1)}
    (h : Nonempty (StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) φ)) :
    Nonempty (StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) (∀¹ φ)) := by
  simpa using (exs hT c (h.map neg)).map neg;

end StrictHierarchyFormulaEquivOf

open StrictHierarchyFormulaEquivOf (refl ofDeltaZero exsOfPi allOfSigma altUp closure exs all)

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}

theorem nonempty_strictHierarchyFormulaEquivOf {φ : ArithmeticSemisentence n}
    (h : Hierarchy Γ s φ) (hT : 𝗜𝚺 s ⪯ T) : Nonempty (StrictHierarchyFormulaEquivOf T Γ s φ) := by
  induction h with
  | verum Γ s n => exact ⟨ofDeltaZero (Hierarchy.verum 𝚺 0 n)⟩;
  | falsum Γ s n => exact ⟨ofDeltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
  | rel Γ s r v => exact ⟨ofDeltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
  | nrel Γ s r v => exact ⟨ofDeltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
  | and _ _ ihp ihq => exact (closure hT).and _ (ihp hT) (ihq hT);
  | or _ _ ihp ihq => exact (closure hT).or _ (ihp hT) (ihq hT);
  | ball pos _ ih => exact (closure hT).ball _ pos (ih hT);
  | bexs pos _ ih => exact (closure hT).bexs _ pos (ih hT);
  | @exs s n φ _ ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact exs hT' (closure hT') (ih hT);
  | @all s n φ _ ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact all hT' (closure hT') (ih hT);
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . use (StrictHierarchyFormula.zero 𝚷 φ (Hierarchy.zero_iff.mp hp)).sigma;
      simp [provable_iff_of_models_iff];
    . exact (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).map exsOfPi;
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . use (StrictHierarchyFormula.zero 𝚺 φ (Hierarchy.zero_iff.mp hp)).pi;
      simp [provable_iff_of_models_iff];
    . exact (ih (ISigma_weakerThan_of_le_trans (by omega) hT)).map allOfSigma;
  | @dummy_sigma s n φ hp ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact (all hT' (closure hT') (ih (ISigma_weakerThan_of_le_trans (by omega) hT))).map altUp;
  | @dummy_pi s n φ hp ih =>
    have hT' : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact (exs hT' (closure hT') (ih (ISigma_weakerThan_of_le_trans (by omega) hT))).map altUp;

variable {T : ArithmeticTheory} {Γ : Polarity} {s n : ℕ}

theorem exists_kernel_provable {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) (hT : 𝗜𝚺 s ⪯ T) :
    ∃ φ₀ : ArithmeticSemisentence (n + s),
      Hierarchy 𝚺 0 φ₀ ∧ T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans inferInstance (ISigma_weakerThan_of_le_trans (Nat.zero_le s) hT);
  obtain ⟨φ'⟩ := nonempty_strictHierarchyFormulaEquivOf h hT;
  exact ⟨φ'.kernel, φ'.kernel_deltaZero, φ'.provable⟩;

theorem exists_kernel_provable' {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) (hT : 𝗜𝚺 s ⪯ T) :
    ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀.val) := by
  obtain ⟨φ₀, hφ₀, hprov⟩ := exists_kernel_provable h hT;
  exact ⟨.mkSigma φ₀ hφ₀, by simpa using hprov⟩;

namespace ISigma1

lemma exists_delta0_kernel_provable {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚺 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ) := by
  obtain ⟨θ, hθ, hprov⟩ := exists_kernel_provable h (inferInstance : 𝗜𝚺 1 ⪯ 𝗜𝚺₁);
  exact ⟨θ, hθ, hprov⟩;

lemma exists_delta0_kernel_provable_pi {φ : ArithmeticSemisentence n} (h : Hierarchy 𝚷 1 φ) :
    ∃ θ : ArithmeticSemisentence (n + 1), Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∀¹ θ) := by
  obtain ⟨θ, hθ, hprov⟩ := exists_kernel_provable h (inferInstance : 𝗜𝚺 1 ⪯ 𝗜𝚺₁);
  exact ⟨θ, hθ, hprov⟩;

end ISigma1

end LO.FirstOrder.Arithmetic
