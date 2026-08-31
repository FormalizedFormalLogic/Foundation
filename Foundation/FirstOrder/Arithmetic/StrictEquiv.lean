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

def refl (θ' : StrictHierarchyFormula ℒₒᵣ Empty Γ s n) :
    StrictHierarchyFormulaEquivOf T Γ s (↑θ' : ArithmeticSemisentence n) :=
  ⟨θ', provable_iff_of_models_iff fun _ _ _ _ ↦ Iff.rfl⟩

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

structure Closure (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) where
  ball : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictHierarchyFormulaEquivOf T Γ s φ →
        StrictHierarchyFormulaEquivOf T Γ s (∀¹[“x. x < !!t”] φ)
  bexs : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → StrictHierarchyFormulaEquivOf T Γ s φ →
        StrictHierarchyFormulaEquivOf T Γ s (∃¹[“x. x < !!t”] φ)
  and : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      StrictHierarchyFormulaEquivOf T Γ s φ →
      StrictHierarchyFormulaEquivOf T Γ s ψ →
        StrictHierarchyFormulaEquivOf T Γ s (φ ⋏ ψ)
  or : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      StrictHierarchyFormulaEquivOf T Γ s φ →
      StrictHierarchyFormulaEquivOf T Γ s ψ →
        StrictHierarchyFormulaEquivOf T Γ s (φ ⋎ ψ)

def closureZero : Closure T 0 where
  ball := by
    intro Γ n φ t ht φ';
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.ball ht φ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [StrictHierarchyFormula.coe_zero, Semiformula.eval_ball];
    exact forall_congr' (fun x => imp_congr Iff.rfl (φ'.iff_models V (x :> e)));
  bexs := by
    intro Γ n φ t ht φ';
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.bexs ht φ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp only [StrictHierarchyFormula.coe_zero, Semiformula.eval_bexs];
    exact exists_congr (fun x => and_congr Iff.rfl (φ'.iff_models V (x :> e)));
  and := by
    intro Γ n φ ψ φ' ψ';
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.and φ'.deltaZero ψ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [StrictHierarchyFormula.coe_zero, φ'.iff_models V e, ψ'.iff_models V e];
  or := by
    intro Γ n φ ψ φ' ψ';
    use StrictHierarchyFormula.zero Γ _ (Hierarchy.or φ'.deltaZero ψ'.deltaZero);
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simp [StrictHierarchyFormula.coe_zero, φ'.iff_models V e, ψ'.iff_models V e];

-- Extracting `u` from `Rew.positive_iff.mp ht : ∃ u, t = Rew.bShift u` into a data-valued
-- (`Type`-returning) goal requires `Classical.choice`.
noncomputable def bexsSigmaStep {n} {φ : ArithmeticSemisentence (n + 1)}
    {t : ArithmeticSemiterm Empty (n + 1)} (ih : Closure T s) (ht : t.Positive)
    (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) :
    StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ) := by
  obtain ⟨u, rfl⟩ := Classical.indefiniteDescription _ (Rew.positive_iff.mp ht);
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set φ₂ : ArithmeticSemisentence (n + 2) := Rew.subst v ▹ φ₁;
  let φ₂' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 2) := φ₁'.rew (Rew.subst v);
  have χ' := ih.bexs 𝚷 (φ := φ₂) (t := Rew.bShift (Rew.bShift u)) (by simp)
    ((refl φ₂').ofEq (by simp [φ₂', φ₂, φ₁, StrictHierarchyFormula.coe_rew]));
  have hχiff := χ'.iff_models';
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (φ₂.bexsLT (Rew.bShift u)) ↔ V ⊧/e (↑χ' : ArithmeticSemisentence (n + 1)) :=
    hχiff;
  use χ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
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
    show V ⊧/e (φ.bexsLT u) ↔ V ⊧/e (∃¹ (↑χ' : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

-- Extracting `u` from `Rew.positive_iff.mp ht : ∃ u, t = Rew.bShift u` into a data-valued
-- (`Type`-returning) goal requires `Classical.choice`.
noncomputable def ballSigmaStep {n} {φ : ArithmeticSemisentence (n + 1)}
    {t : ArithmeticSemiterm Empty (n + 1)} [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s) (ht : t.Positive)
    (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) :
    StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ) := by
  obtain ⟨u, rfl⟩ := Classical.indefiniteDescription _ (Rew.positive_iff.mp ht);
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 3) :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  have α' := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁, StrictHierarchyFormula.coe_rew]));
  have hαiff := models_iff_of_provable_iff' α'.provable;
  have δ' := ih.ball 𝚷 (t := Rew.bShift (Rew.bShift u)) (by simp) (refl α'.toStrictHierarchyFormula);
  have hδiff := models_iff_of_provable_iff' δ'.provable;
  use δ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hαeval : ∀ x w : V, V ⊧/(x :> w :> e) (↑α'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) ↔
        ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro x w;
      rw [← hαiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hδeval : ∀ w : V, V ⊧/(w :> e) (↑δ'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
        ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro w;
      rw [← hδiff V (w :> e)];
      simp [hαeval];
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) φ₁ := fun x =>
      φ'.iff_models_sigmaInv V (x :> e);
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ (↑δ'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hδeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) φ₁ := φ₁'.hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

def orSigmaStep {n} {φ ψ : ArithmeticSemisentence n} (ih : Closure T s)
    (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ)
    (ψ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) ψ) :
    StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (φ ⋎ ψ) := by
  set φ₁' := φ'.sigmaInv;
  set ψ₁' := ψ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  have χ' := ih.or 𝚷 (refl φ₁') (refl ψ₁');
  have hχiff := χ'.iff_models';
  use χ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
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

def andSigmaStep {n} {φ ψ : ArithmeticSemisentence n} [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s)
    (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ)
    (ψ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) ψ) :
    StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (φ ⋏ ψ) := by
  have : 𝗜𝚺₀ ⪯ T :=
    Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le (s + 1))) inferInstance;
  set φ₁' := φ'.sigmaInv;
  set ψ₁' := ψ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  let φ₂' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 2) :=
    φ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  have α' := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁, StrictHierarchyFormula.coe_rew]));
  let ψ₂' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 2) :=
    ψ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  have β' := ih.bexs 𝚷 (φ := ψ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ((refl ψ₂').ofEq (by simp [ψ₂', ψ₁, StrictHierarchyFormula.coe_rew]));
  have hαiff := models_iff_of_provable_iff' α'.provable;
  have hβiff := models_iff_of_provable_iff' β'.provable;
  have χ' := ih.and 𝚷 (refl α'.toStrictHierarchyFormula) (refl β'.toStrictHierarchyFormula);
  have hχiff := models_iff_of_provable_iff' χ'.provable;
  use χ'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hα_eval : ∀ z : V, V ⊧/(z :> e) (↑α'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) φ₁ := fun z => by
      rw [← hαiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hβ_eval : ∀ z : V, V ⊧/(z :> e) (↑β'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
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

noncomputable def closureSucc [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s) : Closure T (s + 1) where
  ball := by
    intro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact ballSigmaStep ih ht hφ;
    . simpa using (bexsSigmaStep ih ht hφ.neg).neg;
  bexs := by
    intro Γ n φ t ht hφ;
    rcases Γ with _ | _;
    . exact bexsSigmaStep ih ht hφ;
    . simpa using (ballSigmaStep ih ht hφ.neg).neg;
  and := by
    intro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact andSigmaStep ih hφ hψ;
    . simpa [Semiformula.imp_eq] using (orSigmaStep ih hφ.neg hψ.neg).neg;
  or := by
    intro Γ n φ ψ hφ hψ;
    rcases Γ with _ | _;
    . exact orSigmaStep ih hφ hψ;
    . simpa [Semiformula.imp_eq] using (andSigmaStep ih hφ.neg hψ.neg).neg;

noncomputable def closure [𝗜𝚺 s ⪯ T] : Closure T s := by
  revert ‹𝗜𝚺 s ⪯ T›;
  induction s with
  | zero => intro _; exact closureZero;
  | succ s ih =>
    intro inst;
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) inst;
    exact closureSucc ih;

def exs [𝗜𝚺 s ⪯ T] (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemisentence (n + 1)}
    (φ' : StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) φ) :
    StrictHierarchyFormulaEquivOf T 𝚺 (s + 1) (∃¹ φ) := by
  have : 𝗜𝚺₀ ⪯ T :=
    Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) inferInstance;
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' : StrictHierarchyFormula ℒₒᵣ Empty 𝚷 s (n + 3) :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  have α' := c.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁, StrictHierarchyFormula.coe_rew]));
  have β' := c.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl α'.toStrictHierarchyFormula);
  have hαiff := models_iff_of_provable_iff' α'.provable;
  have hβiff := models_iff_of_provable_iff' β'.provable;
  have hαiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 2) → V),
      V ⊧/e ((φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemisentence (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔
      V ⊧/e (↑α'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) :=
    hαiff;
  have hβiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e ((↑α'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)).bexsLTSucc
        (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔
      V ⊧/e (↑β'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) :=
    hβiff;
  use β'.sigma;
  . apply provable_iff_of_models_iff;
    intro V _ _ e;
    rw [StrictHierarchyFormula.coe_sigma];
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hαeval : ∀ y z : V, V ⊧/(y :> z :> e) (↑α'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ₁ := by
      intro y z;
      rw [← hαiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hβeval : ∀ z : V, V ⊧/(z :> e) (↑β'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 1)) ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e) (↑α'.toStrictHierarchyFormula : ArithmeticSemisentence (n + 2)) := by
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

def all [𝗜𝚺 s ⪯ T] (c : Closure T s) {n : ℕ}
    {φ : ArithmeticSemisentence (n + 1)}
    (φ' : StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) φ) :
    StrictHierarchyFormulaEquivOf T 𝚷 (s + 1) (∀¹ φ) := by
  simpa using (exs c φ'.neg).neg;

end StrictHierarchyFormulaEquivOf

open StrictHierarchyFormulaEquivOf (refl ofDeltaZero exsOfPi allOfSigma altUp closure exs all)

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}

theorem nonempty_strictHierarchyFormulaEquivOf {φ : ArithmeticSemisentence n}
    (h : Hierarchy Γ s φ) [𝗜𝚺 s ⪯ T] : Nonempty (StrictHierarchyFormulaEquivOf T Γ s φ) := by
  rename_i hT;
  induction h generalizing hT  with
  | verum Γ s n => exact ⟨ofDeltaZero (Hierarchy.verum 𝚺 0 n)⟩;
  | falsum Γ s n => exact ⟨ofDeltaZero (Hierarchy.falsum 𝚺 0 n)⟩;
  | rel Γ s r v => exact ⟨ofDeltaZero (Hierarchy.rel 𝚺 0 r v)⟩;
  | nrel Γ s r v => exact ⟨ofDeltaZero (Hierarchy.nrel 𝚺 0 r v)⟩;
  | and _ _ ihp ihq =>
    obtain ⟨φ'⟩ := ihp; obtain ⟨ψ'⟩ := ihq;
    exact ⟨closure.and _ φ' ψ'⟩;
  | or _ _ ihp ihq =>
    obtain ⟨φ'⟩ := ihp; obtain ⟨ψ'⟩ := ihq;
    exact ⟨closure.or _ φ' ψ'⟩;
  | ball pos _ ih => obtain ⟨φ'⟩ := ih; exact ⟨closure.ball _ pos φ'⟩;
  | bexs pos _ ih => obtain ⟨φ'⟩ := ih; exact ⟨closure.bexs _ pos φ'⟩;
  | @exs s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact ih.map (exs closure);
  | @all s n φ _ ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact ih.map (all closure);
  | @sigma s n φ hp ih =>
    rcases s with _ | s;
    . use (StrictHierarchyFormula.zero 𝚷 φ (Hierarchy.zero_iff.mp hp)).sigma;
      simp [provable_iff_of_models_iff];
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
      exact ih.map exsOfPi;
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . use (StrictHierarchyFormula.zero 𝚺 φ (Hierarchy.zero_iff.mp hp)).pi;
      simp [provable_iff_of_models_iff];
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
      exact ih.map allOfSigma;
  | @dummy_sigma s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact (ih.map (all closure)).map altUp;
  | @dummy_pi s n φ hp ih =>
    have : 𝗜𝚺 s ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
    exact (ih.map (exs closure)).map altUp;

variable (T : ArithmeticTheory) {Γ : Polarity} {s n : ℕ} [𝗜𝚺 s ⪯ T]

theorem exists_kernel_provable {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
  ∃ φ₀ : ArithmeticSemisentence (n + s), Hierarchy 𝚺 0 φ₀ ∧ T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans inferInstance (ISigma_weakerThan_of_le_trans (Nat.zero_le s) ‹𝗜𝚺 s ⪯ T›);
  obtain ⟨φ'⟩ := nonempty_strictHierarchyFormulaEquivOf (T := T) h;
  exact ⟨φ'.kernel, φ'.kernel_deltaZero, φ'.provable⟩;

theorem exists_kernel_provable' {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀.val) := by
  obtain ⟨φ₀, hφ₀, hprov⟩ := exists_kernel_provable T h;
  exact ⟨.mkSigma φ₀ hφ₀, by simpa using hprov⟩;

end LO.FirstOrder.Arithmetic
