module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Arithmetic.BoundedCollection
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# `T`-provable strict hierarchy equivalence

Every `Hierarchy Γ s` formula is `T`-provably equivalent to an alternating quantifier prefix over a
bounded matrix. The file also provides the equivalent bounded-matrix formulation.
-/

@[expose] public section

open LO

namespace LO.FirstOrder

structure ArithmeticSemisentence.PrenexNormalForm (T : ArithmeticTheory) (Γ : Polarity) (s : ℕ) {n : ℕ} (φ : ArithmeticSemisentence n) where
  matrix : ArithmeticSemisentence (n + s)
  matrix_Δ₀ : Arithmetic.Hierarchy 𝚺 0 matrix
  provable : T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s matrix)

namespace ArithmeticSemisentence.PrenexNormalForm

open Arithmetic

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s n n₁ n₂ : ℕ}

@[coe]
def val {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ s) : ArithmeticSemisentence n := Polarity.quantItr Γ s φ'.matrix

instance {φ : ArithmeticSemisentence n} : CoeTC (φ.PrenexNormalForm T Γ s) (ArithmeticSemisentence n) := ⟨val⟩

lemma iff_models {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ s) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
  V ⊧/e φ ↔ V ⊧/e φ'.val :=
  Arithmetic.models_iff_of_provable_iff φ'.provable V e

def refl {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ s) : φ'.val.PrenexNormalForm T Γ s :=
  ⟨φ'.matrix, φ'.matrix_Δ₀, provable_iff_of_models_iff fun _ _ _ _ ↦ Iff.rfl⟩

def ofEq {φ ψ : ArithmeticSemisentence n} (h : φ = ψ) (φ' : φ.PrenexNormalForm T Γ s) : ψ.PrenexNormalForm T Γ s := h ▸ φ'

def ofModelIff {φ ψ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ s)
  (hiff : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V), V ⊧/e ψ ↔ V ⊧/e φ) :
  ψ.PrenexNormalForm T Γ s :=
  ⟨φ'.matrix, φ'.matrix_Δ₀, provable_iff_of_models_iff fun V _ _ e ↦ (hiff V e).trans (φ'.iff_models V e)⟩

def neg {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ s) : PrenexNormalForm T Γ.alt s (∼φ) := ⟨
  (∼φ'.matrix),
  φ'.matrix_Δ₀.neg.of_zero,
  by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simpa [val, ← Semiformula.neg_quantItr] using
      not_congr (φ'.iff_models V e)
⟩

def rew {φ : ArithmeticSemisentence n₁} (φ' : φ.PrenexNormalForm T Γ s) (ω : Rew ℒₒᵣ Empty n₁ Empty n₂)
  : PrenexNormalForm T Γ s (ω ▹ φ'.val) := ⟨
  ω.qpow s ▹ φ'.matrix,
  φ'.matrix_Δ₀.rew _,
  provable_iff_of_models_iff fun V _ _ e ↦ by simp [val]
⟩

@[simp]
lemma coe_rew
  {φ : ArithmeticSemisentence n₁} (φ' : φ.PrenexNormalForm T Γ s)
  (ω : Rew ℒₒᵣ Empty n₁ Empty n₂) : (φ'.rew ω).val = ω ▹ φ'.val := by
  simp [val, rew]


def sigma {φ : ArithmeticSemisentence (n + 1)} (φ' : φ.PrenexNormalForm T 𝚷 s) :
  PrenexNormalForm T 𝚺 (s + 1) (∃¹ φ) := ⟨
  Rew.castLE (Nat.succ_add n s).le ▹ φ'.matrix,
  φ'.matrix_Δ₀.rew _,
  by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simpa [val, Rewriting.quantItr_succ_smul_castLE] using
      exists_congr (fun x ↦ φ'.iff_models V (x :> e))
⟩

@[simp]
lemma coe_sigma {φ : ArithmeticSemisentence (n + 1)} (φ' : φ.PrenexNormalForm T 𝚷 s) :
    φ'.sigma.val = ∃¹ φ'.val := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]


def pi {φ : ArithmeticSemisentence (n + 1)} (φ' : φ.PrenexNormalForm T 𝚺 s) :
    PrenexNormalForm T 𝚷 (s + 1) (∀¹ φ) := ⟨
  Rew.castLE (Nat.succ_add n s).le ▹ φ'.matrix,
  φ'.matrix_Δ₀.rew _,
  by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    simpa [val, Rewriting.quantItr_succ_smul_castLE] using
      forall_congr' (fun x ↦ φ'.iff_models V (x :> e))
⟩

@[simp]
lemma coe_pi {φ : ArithmeticSemisentence (n + 1)} (φ' : φ.PrenexNormalForm T 𝚺 s) :
    φ'.pi.val = ∀¹ φ'.val := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]


def sigmaInv {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T 𝚺 (s + 1)) :
  PrenexNormalForm T 𝚷 s
    (Polarity.quantItr 𝚷 s (Rew.castLE (Nat.succ_add n s).ge ▹ φ'.matrix)) := ⟨
  Rew.castLE (Nat.succ_add n s).ge ▹ φ'.matrix,
  φ'.matrix_Δ₀.rew _,
  by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    exact Iff.rfl
⟩

lemma coe_sigmaInv {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T 𝚺 (s + 1)) :
    φ'.val = ∃¹ φ'.sigmaInv.val := by
  change Polarity.quantItr 𝚺 (s + 1) φ'.matrix =
    (𝚺 : Polarity).quant (Polarity.quantItr (𝚺 : Polarity).alt s (Rew.castLE _ ▹ φ'.matrix))
  rw [← Rewriting.quantItr_succ_smul_castLE, ← TransitiveRewriting.comp_app]
  simp


def piInv {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T 𝚷 (s + 1)) :
    PrenexNormalForm T 𝚺 s
      (Polarity.quantItr 𝚺 s (Rew.castLE (Nat.succ_add n s).ge ▹ φ'.matrix)) := ⟨
  Rew.castLE (Nat.succ_add n s).ge ▹ φ'.matrix,
  φ'.matrix_Δ₀.rew _,
  by
    apply provable_iff_of_models_iff;
    intro V _ _ e;
    exact Iff.rfl
⟩

lemma coe_piInv {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T 𝚷 (s + 1)) :
    φ'.val = ∀¹ φ'.piInv.val := by
  change Polarity.quantItr 𝚷 (s + 1) φ'.matrix =
    (𝚷 : Polarity).quant (Polarity.quantItr (𝚷 : Polarity).alt s (Rew.castLE _ ▹ φ'.matrix))
  rw [← Rewriting.quantItr_succ_smul_castLE, ← TransitiveRewriting.comp_app]
  simp


omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
lemma hierarchy {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ s) :
    Hierarchy Γ s φ'.val := by
  change Hierarchy Γ s (Polarity.quantItr Γ s φ'.matrix)
  simpa only [Nat.zero_add] using
    Hierarchy.quantItr (Γ := Γ) (j := 0) φ'.matrix_Δ₀.of_zero

omit [𝗘𝗤 ℒₒᵣ ⪯ T] in
@[simp] lemma deltaZero {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ 0) :
    Hierarchy 𝚺 0 φ'.val := φ'.matrix_Δ₀

def altUp {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T Γ s) :
    φ.PrenexNormalForm T Γ.alt (s + 1) := by
  rcases Γ with _ | _;
  . exact (φ'.rew Rew.bShift).pi.ofModelIff fun V _ _ e ↦ by
        have : Nonempty V := ⟨0⟩;
        simp [φ'.iff_models V e]
  . exact (φ'.rew Rew.bShift).sigma.ofModelIff fun V _ _ e ↦ by
      simp [φ'.iff_models V e]

def ofDeltaZero {φ : ArithmeticSemisentence n} (φ_Δ₀ : Hierarchy 𝚺 0 φ) :
    φ.PrenexNormalForm T Γ s := by
  induction s generalizing Γ with
  | zero => exact ⟨φ, φ_Δ₀, provable_iff_of_models_iff fun _ _ _ _ ↦ Iff.rfl⟩
  | succ s ih => simpa using altUp (ih (Γ := Γ.alt));

def exsOfPi {φ : ArithmeticSemisentence (n + 1)} (φ' : φ.PrenexNormalForm T 𝚷 s) :
    PrenexNormalForm T 𝚺 (s + 1) (∃¹ φ) :=
  φ'.sigma

def allOfSigma {φ : ArithmeticSemisentence (n + 1)} (φ' : φ.PrenexNormalForm T 𝚺 s) :
    PrenexNormalForm T 𝚷 (s + 1) (∀¹ φ) :=
  φ'.pi

lemma provable_sigmaInv {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T 𝚺 (s + 1)) :
    T ⊢ ∀¹* (φ 🡘 ∃¹ φ'.sigmaInv.val) := by
  rw [← coe_sigmaInv]
  exact φ'.provable

lemma provable_piInv {φ : ArithmeticSemisentence n} (φ' : φ.PrenexNormalForm T 𝚷 (s + 1)) :
    T ⊢ ∀¹* (φ 🡘 ∀¹ φ'.piInv.val) := by
  rw [← coe_piInv]
  exact φ'.provable

lemma iff_models_sigmaInv {φ : ArithmeticSemisentence n}
    (φ' : φ.PrenexNormalForm T 𝚺 (s + 1)) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ'.sigmaInv.val :=
  (models_iff_of_provable_iff φ'.provable_sigmaInv V e).trans Semiformula.eval_ex

lemma iff_models_piInv {φ : ArithmeticSemisentence n}
    (φ' : φ.PrenexNormalForm T 𝚷 (s + 1)) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ ∀ x, V ⊧/(x :> e) φ'.piInv.val := by
  simpa [Semiformula.eval_all] using models_iff_of_provable_iff φ'.provable_piInv V e

structure Closure (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (s : ℕ) where
  ball : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → φ.PrenexNormalForm T Γ s →
        Nonempty (PrenexNormalForm T Γ s (∀¹[“x. x < !!t”] φ))
  bexs : ∀ Γ {n} {φ : ArithmeticSemisentence (n + 1)} {t : ArithmeticSemiterm Empty (n + 1)},
      t.Positive → φ.PrenexNormalForm T Γ s →
        Nonempty (PrenexNormalForm T Γ s (∃¹[“x. x < !!t”] φ))
  and : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      φ.PrenexNormalForm T Γ s →
      ψ.PrenexNormalForm T Γ s →
        Nonempty (PrenexNormalForm T Γ s (φ ⋏ ψ))
  or : ∀ Γ {n} {φ ψ : ArithmeticSemisentence n},
      φ.PrenexNormalForm T Γ s →
      ψ.PrenexNormalForm T Γ s →
        Nonempty (PrenexNormalForm T Γ s (φ ⋎ ψ))

lemma closure_zero : Closure T 0 where
  ball := by
    intro Γ n φ t ht φ';
    exact ⟨_, Hierarchy.ball ht φ'.deltaZero,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        simpa [Semiformula.eval_ball] using
          forall_congr' (fun x ↦ imp_congr Iff.rfl (φ'.iff_models V (x :> e)))⟩;
  bexs := by
    intro Γ n φ t ht φ';
    exact ⟨_, Hierarchy.bexs ht φ'.deltaZero,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        simpa [Semiformula.eval_bexs] using
          exists_congr (fun x ↦ and_congr Iff.rfl (φ'.iff_models V (x :> e)))⟩;
  and := by
    intro Γ n φ ψ φ' ψ';
    exact ⟨_,
      Hierarchy.and φ'.deltaZero ψ'.deltaZero,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        simp [φ'.iff_models V e, ψ'.iff_models V e]
    ⟩;
  or := by
    intro Γ n φ ψ φ' ψ';
    exact ⟨_, Hierarchy.or φ'.deltaZero ψ'.deltaZero,
      provable_iff_of_models_iff fun V _ _ e ↦ by
        simp [φ'.iff_models V e, ψ'.iff_models V e]⟩;

lemma bexs_sigma_step {n} {φ : ArithmeticSemisentence (n + 1)}
    {t : ArithmeticSemiterm Empty (n + 1)} (ih : Closure T s) (ht : t.Positive)
    (φ' : φ.PrenexNormalForm T 𝚺 (s + 1)) :
  Nonempty (PrenexNormalForm T 𝚺 (s + 1) (∃¹[“x. x < !!t”] φ)) := by
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  set v : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2) :=
    #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  set φ₂ : ArithmeticSemisentence (n + 2) := Rew.subst v ▹ φ₁;
  let φ₂' := φ₁'.rew (Rew.subst v);
  obtain ⟨χ'⟩ := ih.bexs 𝚷 (φ := φ₂) (t := Rew.bShift (Rew.bShift u)) (by simp)
    ((refl φ₂').ofEq (by simp [φ₂', φ₂, φ₁]));
  have hχiff := χ'.iff_models;
  have hχiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e (φ₂.bexsLT (Rew.bShift u)) ↔
        V ⊧/e (↑χ' : ArithmeticSemisentence (n + 1)) :=
    hχiff;
  refine ⟨χ'.sigma.matrix, χ'.sigma.matrix_Δ₀, ?_⟩;
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  · change V ⊧/e (φ.bexsLT u) ↔ V ⊧/e χ'.sigma.val;
    rw [coe_sigma]
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
      V ⊧/e (∃¹ (↑χ' : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_bexsLT, Semiformula.eval_ex, ← hχiff', Semiterm.val_bShift,
      hswap, hφiff];
    grind;

lemma ball_sigma_step {n} {φ : ArithmeticSemisentence (n + 1)}
    {t : ArithmeticSemiterm Empty (n + 1)} [𝗜𝚺 (s + 1) ⪯ T]
    (ih : Closure T s) (ht : t.Positive) (φ' : φ.PrenexNormalForm T 𝚺 (s + 1)) :
  Nonempty (PrenexNormalForm T 𝚺 (s + 1) (∀¹[“x. x < !!t”] φ)) := by
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨α'⟩ := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁]));
  have hαiff := α'.iff_models;
  obtain ⟨δ'⟩ := ih.ball 𝚷 (t := Rew.bShift (Rew.bShift u)) (by simp) (refl α');
  have hδiff := δ'.iff_models;
  refine ⟨δ'.sigma.matrix, δ'.sigma.matrix_Δ₀, ?_⟩;
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  · change V ⊧/e (φ.ballLT u) ↔ V ⊧/e δ'.sigma.val;
    rw [coe_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := models_of_subtheory (T := 𝗜𝚺 (s + 1)) (U := T) inferInstance;
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have hαeval : ∀ x w : V, V ⊧/(x :> w :> e) (↑α' : ArithmeticSemisentence (n + 2)) ↔
        ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro x w;
      rw [← hαiff V (x :> w :> e)];
      simp [Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    have hδeval : ∀ w : V, V ⊧/(w :> e) (↑δ' : ArithmeticSemisentence (n + 1)) ↔
        ∀ x < u.valb e, ∃ y ≤ w, V ⊧/(y :> x :> e) φ₁ := by
      intro w;
      rw [← hδiff V (w :> e)];
      simp [hαeval];
    have hφeval : ∀ x : V, V ⊧/(x :> e) φ ↔ ∃ y, V ⊧/(y :> x :> e) φ₁ := fun x =>
      φ'.iff_models_sigmaInv V (x :> e);
    show V ⊧/e (φ.ballLT u) ↔ V ⊧/e (∃¹ (↑δ' : ArithmeticSemisentence (n + 1)));
    simp only [Semiformula.eval_ballLT, Semiformula.eval_ex, hδeval, hφeval];
    constructor;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) φ₁ := φ₁'.hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;

lemma or_sigma_step {n} {φ ψ : ArithmeticSemisentence n} (ih : Closure T s)
    (φ' : φ.PrenexNormalForm T 𝚺 (s + 1))
    (ψ' : ψ.PrenexNormalForm T 𝚺 (s + 1)) :
    Nonempty (PrenexNormalForm T 𝚺 (s + 1) (φ ⋎ ψ)) := by
  set φ₁' := φ'.sigmaInv;
  set ψ₁' := ψ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  obtain ⟨χ'⟩ := ih.or 𝚷 (refl φ₁') (refl ψ₁');
  have hχiff := χ'.iff_models;
  refine ⟨χ'.sigma.matrix, χ'.sigma.matrix_Δ₀, ?_⟩;
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  · change V ⊧/e (φ ⋎ ψ) ↔ V ⊧/e χ'.sigma.val;
    rw [coe_sigma]
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := φ'.iff_models_sigmaInv V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := ψ'.iff_models_sigmaInv V e;
    simp only [LogicalConnective.HomClass.map_or, Semiformula.eval_ex, hφiff', hψiff'];
    constructor;
    . rintro (⟨x, hx⟩ | ⟨x, hx⟩);
      . exact ⟨x, (hχiff V (x :> e)).mp (Or.inl hx)⟩;
      . exact ⟨x, (hχiff V (x :> e)).mp (Or.inr hx)⟩;
    . rintro ⟨x, hx⟩;
      rcases (hχiff V (x :> e)).mpr hx with h | h;
      . left; exact ⟨x, h⟩;
      . right; exact ⟨x, h⟩;

lemma and_sigma_step {n} {φ ψ : ArithmeticSemisentence n} [𝗜𝚺 (s + 1) ⪯ T] (ih : Closure T s)
  (φ' : φ.PrenexNormalForm T 𝚺 (s + 1))
  (ψ' : ψ.PrenexNormalForm T 𝚺 (s + 1)) :
  Nonempty (PrenexNormalForm T 𝚺 (s + 1) (φ ⋏ ψ)) := by
  have : 𝗜𝚺₀ ⪯ T := Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (by omega)) ‹𝗜𝚺(s + 1) ⪯ T›;
  set φ₁' := φ'.sigmaInv;
  set ψ₁' := ψ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 1) := ↑φ₁';
  set ψ₁ : ArithmeticSemisentence (n + 1) := ↑ψ₁';
  let φ₂' :=
    φ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨α'⟩ := ih.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁]));
  let ψ₂' :=
    ψ₁'.rew (Rew.subst (#0 :> (#·.succ.succ)));
  obtain ⟨β'⟩ := ih.bexs 𝚷 (φ := ψ₁ ⇜ (#0 :> (#·.succ.succ)))
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) ((refl ψ₂').ofEq (by simp [ψ₂', ψ₁]));
  have hαiff := α'.iff_models;
  have hβiff := β'.iff_models;
  obtain ⟨χ'⟩ := ih.and 𝚷 (refl α') (refl β');
  have hχiff := χ'.iff_models;
  refine ⟨χ'.sigma.matrix, χ'.sigma.matrix_Δ₀, ?_⟩;
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  · change V ⊧/e (φ ⋏ ψ) ↔ V ⊧/e χ'.sigma.val;
    rw [coe_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hα_eval : ∀ z : V, V ⊧/(z :> e) (↑α' : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) φ₁ := fun z => by
      rw [← hαiff V (z :> e)];
      show V ⊧/(z :> e)
        ((φ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hβ_eval : ∀ z : V, V ⊧/(z :> e) (↑β' : ArithmeticSemisentence (n + 1)) ↔
        ∃ x ≤ z, V ⊧/(x :> e) ψ₁ := fun z => by
      rw [← hβiff V (z :> e)];
      show V ⊧/(z :> e)
        ((ψ₁ ⇜ (#0 :> (#·.succ.succ)) : ArithmeticSemisentence (n + 2)).bexsLTSucc
          (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔ _;
      simp [Semiformula.eval_insert1, -Semiformula.eval_substs];
    have hφiff' : V ⊧/e φ ↔ ∃ x, V ⊧/(x :> e) φ₁ := φ'.iff_models_sigmaInv V e;
    have hψiff' : V ⊧/e ψ ↔ ∃ x, V ⊧/(x :> e) ψ₁ := ψ'.iff_models_sigmaInv V e;
    have hχ_eval : ∀ z : V, V ⊧/(z :> e) (↑χ' : ArithmeticSemisentence (n + 1)) ↔
        V ⊧/(z :> e) (↑α' : ArithmeticSemisentence (n + 1)) ∧
          V ⊧/(z :> e) (↑β' : ArithmeticSemisentence (n + 1)) := fun z ↦
      (hχiff V (z :> e)).symm;
    simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_ex, hφiff', hψiff',
      hχ_eval, hα_eval, hβ_eval];
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

lemma exs {n} {φ : ArithmeticSemisentence (n + 1)} [𝗜𝚺 s ⪯ T]
    (c : Closure T s) (φ' : φ.PrenexNormalForm T 𝚺 (s + 1)) :
  Nonempty (PrenexNormalForm T 𝚺 (s + 1) (∃¹ φ)) := by
  have : 𝗜𝚺₀ ⪯ T :=
    Entailment.WeakerThan.trans (ISigma_weakerThan_of_le (Nat.zero_le s)) inferInstance;
  set φ₁' := φ'.sigmaInv;
  set φ₁ : ArithmeticSemisentence (n + 2) := ↑φ₁';
  let φ₂' :=
    φ₁'.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)));
  obtain ⟨α'⟩ := c.bexs 𝚷 (φ := φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)))
    (t := Rew.bShift (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)))
    (Rew.bShift_positive _) ((refl φ₂').ofEq (by simp [φ₂', φ₁]));
  obtain ⟨β'⟩ := c.bexs 𝚷
    (t := Rew.bShift (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)))
    (Rew.bShift_positive _) (refl α');
  have hαiff := α'.iff_models;
  have hβiff := β'.iff_models;
  have hαiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 2) → V),
      V ⊧/e ((φ₁ ⇜ (#0 :> #1 :> (#·.succ.succ.succ)) : ArithmeticSemisentence (n + 3)).bexsLTSucc
        (‘#1’ : ArithmeticSemiterm Empty (n + 2))) ↔
      V ⊧/e (↑α' : ArithmeticSemisentence (n + 2)) :=
    hαiff;
  have hβiff' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin (n + 1) → V),
      V ⊧/e ((↑α' : ArithmeticSemisentence (n + 2)).bexsLTSucc
        (‘#0’ : ArithmeticSemiterm Empty (n + 1))) ↔
      V ⊧/e (↑β' : ArithmeticSemisentence (n + 1)) :=
    hβiff;
  refine ⟨β'.sigma.matrix, β'.sigma.matrix_Δ₀, ?_⟩;
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  · change V ⊧/e (∃¹ φ) ↔ V ⊧/e β'.sigma.val;
    rw [coe_sigma]
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance;
    have hαeval : ∀ y z : V, V ⊧/(y :> z :> e) (↑α' : ArithmeticSemisentence (n + 2)) ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ₁ := by
      intro y z;
      rw [← hαiff' V (y :> z :> e)];
      simp [Semiformula.eval_insert2, -Semiformula.eval_substs];
    have hβeval : ∀ z : V, V ⊧/(z :> e) (↑β' : ArithmeticSemisentence (n + 1)) ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e) (↑α' : ArithmeticSemisentence (n + 2)) := by
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

lemma all {n} {φ : ArithmeticSemisentence (n + 1)} [𝗜𝚺 s ⪯ T]
    (c : Closure T s) (φ' : φ.PrenexNormalForm T 𝚷 (s + 1)) :
  Nonempty (PrenexNormalForm T 𝚷 (s + 1) (∀¹ φ)) := by
  obtain ⟨χ'⟩ := exs c φ'.neg;
  exact ⟨by simpa using χ'.neg⟩;

end ArithmeticSemisentence.PrenexNormalForm

namespace Arithmetic

open LO.FirstOrder.ArithmeticSemisentence.PrenexNormalForm
  (ofDeltaZero exsOfPi allOfSigma altUp closure exs all)

variable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s : ℕ} {n : ℕ}

theorem nonempty_prenexNormalForm {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ)
    [𝗜𝚺 s ⪯ T] : Nonempty (ArithmeticSemisentence.PrenexNormalForm T Γ s φ) := by
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
    . exact ⟨(ofDeltaZero (Γ := 𝚷) (s := 0) (Hierarchy.zero_iff.mp hp)).sigma⟩;
    . have : 𝗜𝚺 (s + 1) ⪯ T := ISigma_weakerThan_of_le_trans (by omega) hT;
      exact ih.map exsOfPi;
  | @pi s n φ hp ih =>
    rcases s with _ | s;
    . exact ⟨(ofDeltaZero (Γ := 𝚺) (s := 0) (Hierarchy.zero_iff.mp hp)).pi⟩;
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
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) (ISigma_weakerThan_of_le_trans (by omega) ‹𝗜𝚺 s ⪯ T›);
  obtain ⟨φ'⟩ := nonempty_prenexNormalForm (T := T) h;
  exact ⟨φ'.matrix, φ'.matrix_Δ₀, φ'.provable⟩;

theorem exists_matrix_provable' (h : Hierarchy Γ s φ) :
    ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 Polarity.quantItr Γ s φ₀.val) := by
  obtain ⟨φ₀, hφ₀, hprov⟩ := exists_matrix_provable T h;
  exact ⟨.mkSigma φ₀ hφ₀, by simpa using hprov⟩;

end Arithmetic

end LO.FirstOrder
