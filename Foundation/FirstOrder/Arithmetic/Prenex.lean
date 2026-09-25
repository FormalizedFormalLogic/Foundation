module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# Prenex normal form for the arithmetical hierarchy

For `𝗕𝚺 s ⪯ T`, every `Hierarchy Γ s` formula `φ` is `T`-provably equivalent to `φ₀.toPrenex Γ s`
for some `φ₀ : ArithmeticSemisentence (n + s)` in `Hierarchy 𝚺 0`.

## References

- [HP98]
-/

@[expose] public section

open FFL

namespace FFL.FirstOrder

namespace Arithmetic

private abbrev PrenexBase : ℕ → ArithmeticTheory
  | 0     => 𝗜𝚺₀
  | s + 1 => 𝗕𝚷 s

private lemma models_PrenexBase_of_models_CollectionOnHierarchy {V : Type*} [ORingStructure V]
    (Γ : Polarity) (s : ℕ) [h : V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] : V↓[ℒₒᵣ] ⊧* PrenexBase s :=
  match s, h with
  | 0, h => models_of_ss h Set.subset_union_left
  | s + 1, h => models_of_ss h (CollectionOnHierarchy_subset_of_lt (Nat.lt_succ_self s))

/-- A formula in `Γ`-prenex form of level `s`, stored as the `𝚺₀` matrix that remains after
stripping the `s` leading alternating quantifiers. -/
structure Prenex (Γ : Polarity) (s : ℕ) (ξ : Type*) (n : ℕ) where
  matrix : 𝚺₀.Semiformula ξ (n + s)

namespace Prenex

variable {Γ : Polarity} {s : ℕ} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}
variable {V : Type*} [ORingStructure V]

@[coe]
def val (φ : Prenex Γ s ξ n) : ArithmeticSemiformula ξ n := φ.matrix.val.toPrenex Γ s

instance : CoeTC (Prenex Γ s ξ n) (ArithmeticSemiformula ξ n) := ⟨val⟩

def neg (φ : Prenex Γ s ξ n) : Prenex Γ.alt s ξ n :=
  ⟨.mkSigma (∼φ.matrix.val) φ.matrix.sigma_prop.neg.of_zero⟩

instance : HTilde (Prenex Γ s ξ n) (Prenex Γ.alt s ξ n) := ⟨neg⟩

def rew (φ : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : Prenex Γ s ξ₂ n₂ :=
  ⟨φ.matrix.rew (ω.qpow s)⟩

def sigma (φ : Prenex 𝚷 s ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def pi (φ : Prenex 𝚺 s ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def sigmaInv (φ : Prenex 𝚺 (s + 1) ξ n) : Prenex 𝚷 s ξ (n + 1) :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def piInv (φ : Prenex 𝚷 (s + 1) ξ n) : Prenex 𝚺 s ξ (n + 1) :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def altUp (φ : Prenex Γ s ξ n) : Prenex Γ.alt (s + 1) ξ n := by
  rcases Γ with _ | _
  · exact (φ.rew Rew.bShift).pi
  · exact (φ.rew Rew.bShift).sigma

def ofΔ₀ (φ : 𝚺₀.Semiformula ξ n) : (Γ : Polarity) → (s : ℕ) → Prenex Γ s ξ n
  | Γ, 0     => ⟨φ⟩
  | Γ, s + 1 => by simpa using altUp (ofΔ₀ φ Γ.alt s)

def verum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) Γ s

def falsum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) Γ s

def rel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) Γ s

def nrel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) Γ s


@[simp, grind .]
lemma val_hierarchy {φ : Prenex Γ s ξ n} : Hierarchy Γ s φ.val := by
  change Hierarchy Γ s (φ.matrix.val.toPrenex Γ s)
  simpa only [Nat.zero_add] using Hierarchy.toPrenex (Γ := Γ) (j := 0) φ.matrix.sigma_prop.of_zero

@[simp, grind .]
lemma val_deltaZero {φ : Prenex Γ 0 ξ n} : Hierarchy 𝚺 0 φ.val := φ.matrix.sigma_prop

-- The binders are spelled out rather than taken from `variable`, to fix the order `Γ s n ξ`.
@[simp, grind .]
lemma val_strictHierarchy {Γ : Polarity} {s n : ℕ} {ξ : Type*} {φ : Prenex Γ s ξ n} :
    StrictHierarchy Γ s φ.val :=
  StrictHierarchy.toPrenex_of_deltaZero (Hierarchy.zero_iff_delta_zero.mp φ.matrix.sigma_prop)

@[simp, grind .]
lemma val_neg (φ : Prenex Γ s ξ n) : (∼φ).val = ∼φ.val := by
  change (neg φ).val = ∼φ.val
  simp [neg, val]

@[simp, grind .]
lemma val_rew (φ : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) :
  (φ.rew ω).val = ω ▹ φ.val := by
  simp [val, rew]

@[simp, grind .]
lemma val_sigma {φ : Prenex 𝚷 s ξ (n + 1)} : φ.sigma.val = ∃¹ φ.val := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]

@[simp, grind .]
lemma val_pi {φ : Prenex 𝚺 s ξ (n + 1)} : φ.pi.val = ∀¹ φ.val := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]

@[simp, grind .]
lemma val_sigmaInv {φ : Prenex 𝚺 (s + 1) ξ n} : φ.val = ∃¹ φ.sigmaInv.val := by
  unfold val sigmaInv
  simp only [Bounding.HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_sigma, ← Polarity.alt_sigma, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp



@[simp, grind .]
lemma val_piInv {φ : Prenex 𝚷 (s + 1) ξ n} : φ.val = ∀¹ φ.piInv.val := by
  unfold val piInv
  simp only [Bounding.HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_pi, ← Polarity.alt_pi, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp

variable {f : ξ → V}

lemma models_sigmaInv (φ : Prenex 𝚺 (s + 1) ξ n) (e : Fin n → V) :
    Semiformula.Eval e f φ.val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.sigmaInv.val := by
  rw [val_sigmaInv]; exact Semiformula.eval_ex;

lemma models_piInv (φ : Prenex 𝚷 (s + 1) ξ n) (e : Fin n → V) :
    Semiformula.Eval e f φ.val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.piInv.val := by
  rw [val_piInv]; exact Semiformula.eval_all;

lemma models_sigma (φ : Prenex 𝚷 s ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f φ.sigma.val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [val_sigma]; exact Semiformula.eval_ex;

lemma models_pi (φ : Prenex 𝚺 s ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f φ.pi.val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [val_pi]; exact Semiformula.eval_all;

lemma models_altUp (φ : Prenex Γ s ξ n) (e : Fin n → V) :
  Semiformula.Eval e f φ.altUp.val ↔ Semiformula.Eval e f φ.val := by
  rcases Γ <;> simp [
    Polarity.eq_sigma, Polarity.alt_sigma, altUp,
    -val_piInv, -val_sigmaInv,
    Semiformula.eval_all, Nat.succ_eq_add_one
  ]

lemma models_ofΔ₀ (φ : 𝚺₀.Semiformula ξ n) (e : Fin n → V) :
    Semiformula.Eval e f (ofΔ₀ φ Γ s).val ↔ Semiformula.Eval e f φ.val := by
  induction s generalizing Γ with
  | zero => rfl
  | succ s ih =>
    rcases Γ with _ | _
    · change Semiformula.Eval e f (ofΔ₀ φ 𝚷 s).altUp.val ↔ Semiformula.Eval e f φ.val
      exact (models_altUp (ofΔ₀ φ 𝚷 s) e).trans (ih (Γ := 𝚷))
    · change Semiformula.Eval e f (ofΔ₀ φ 𝚺 s).altUp.val ↔ Semiformula.Eval e f φ.val
      exact (models_altUp (ofΔ₀ φ 𝚺 s) e).trans (ih (Γ := 𝚺))

lemma models_verum (e : Fin n → V) :
    Semiformula.Eval e f (verum : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (⊤ : ArithmeticSemiformula ξ n) :=
  models_ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) e

lemma models_falsum (e : Fin n → V) :
    Semiformula.Eval e f (falsum : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (⊥ : ArithmeticSemiformula ξ n) :=
  models_ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) e

lemma models_rel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n)
    (e : Fin n → V) :
    Semiformula.Eval e f (rel r v : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (Semiformula.rel r v) :=
  models_ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) e

lemma models_nrel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n)
    (e : Fin n → V) :
    Semiformula.Eval e f (nrel r v : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (Semiformula.nrel r v) :=
  models_ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) e

lemma provable_iff_sigmaInv {T : ArithmeticTheory} {φ : ArithmeticSemiformula Empty n}
  {φ' : Prenex 𝚺 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
  T ⊢ ∀¹* (φ 🡘 ∃¹ φ'.sigmaInv.val) := φ'.val_sigmaInv ▸ hφ'

lemma provable_iff_piInv {T : ArithmeticTheory} {φ : ArithmeticSemiformula Empty n}
  {φ' : Prenex 𝚷 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
  T ⊢ ∀¹* (φ 🡘 ∀¹ φ'.piInv.val) := φ'.val_piInv ▸ hφ'

mutual

def ball : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm ξ n → Prenex Γ s ξ (n + 1) → Prenex Γ s ξ n
  | _, 0    , _, u, φ => ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) φ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, φ =>
      (ball (Rew.bShift u)
        (bexs ‘#1 + 1’ (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(bexs u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def bexs : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm ξ n → Prenex Γ s ξ (n + 1) → Prenex Γ s ξ n
  | _, 0    , _, u, φ => ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) φ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, φ =>
      (bexs (Rew.bShift u) (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(ball u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

local notation:64 "∀'[" u "] " φ => Prenex.ball u φ
local notation:64 "∃'[" u "] " φ => Prenex.bexs u φ

@[simp]
lemma ball_zero {u : ArithmeticSemiterm ξ n} {φ : Prenex Γ 0 ξ (n + 1)} :
  (∀'[u] φ) = ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) φ.val_deltaZero)⟩ := by
  simp [ball]

lemma ball_succ_sigma {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚺 (s + 1) ξ (n + 1)} :
  (∀'[u] φ) =
    (∀'[Rew.bShift u]
      (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma := by
  rw [ball]

lemma ball_succ_pi {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚷 (s + 1) ξ (n + 1)} :
  (∀'[u] φ) = ∼(∃'[u] ∼φ) := by
  rw [ball]


@[simp]
lemma bexs_zero {u : ArithmeticSemiterm ξ n} {φ : Prenex Γ 0 ξ (n + 1)} :
  (∃'[u] φ) = ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) φ.val_deltaZero)⟩ := by
  simp [bexs]

lemma bexs_succ_sigma {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚺 (s + 1) ξ (n + 1)} :
  (∃'[u] φ) =
    (∃'[Rew.bShift u] (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma := by
  rw [bexs]

lemma bexs_succ_pi {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚷 (s + 1) ξ (n + 1)} :
  (∃'[u] φ) = ∼(∀'[u] ∼φ) := by
  rw [bexs]


mutual

def and : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s ξ n → Prenex Γ s ξ n → Prenex Γ s ξ n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ =>
      (and (∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
           (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(or (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def or : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s ξ n → Prenex Γ s ξ n → Prenex Γ s ξ n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ => (or φ.sigmaInv ψ.sigmaInv).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(and (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

instance : HWedge (Prenex Γ s ξ n) (Prenex Γ s ξ n) (Prenex Γ s ξ n) := ⟨and⟩
instance : HVee (Prenex Γ s ξ n) (Prenex Γ s ξ n) (Prenex Γ s ξ n) := ⟨or⟩

@[simp]
lemma and_zero {φ ψ : Prenex Γ 0 ξ n} :
    (φ ⋏ ψ) = ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  change and φ ψ = _
  simp [and]

lemma and_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) ξ n} :
  (φ ⋏ ψ) = ((∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ))))) ⋏
    (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma := by
  change and φ ψ = _
  rw [and]; rfl

lemma and_succ_pi {φ ψ : Prenex 𝚷 (s + 1) ξ n} : (φ ⋏ ψ) = ∼(∼φ ⋎ ∼ψ) := by
  change and φ ψ = _
  rw [and]; rfl


@[simp]
lemma or_zero {φ ψ : Prenex Γ 0 ξ n} :
    (φ ⋎ ψ) = ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  change or φ ψ = _
  simp [or]

lemma or_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) ξ n} : (φ ⋎ ψ) = (φ.sigmaInv ⋎ ψ.sigmaInv).sigma := by
  change or φ ψ = _
  rw [or]; rfl

lemma or_succ_pi {φ ψ : Prenex 𝚷 (s + 1) ξ n} : (φ ⋎ ψ) = ∼(∼φ ⋏ ∼ψ) := by
  change or φ ψ = _
  rw [or]; rfl

private lemma models_bexs_witness [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (hb : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : Prenex 𝚷 s ξ (m + 1)) (e : Fin m → V),
      Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val)
    (φ : Prenex 𝚺 (s + 1) ξ (n + 1)) (x w : V) (e : Fin n → V) :
    Semiformula.Eval (x :> w :> e) f
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val
      ↔ ∃ y ≤ w, Semiformula.Eval (y :> x :> e) f φ.sigmaInv.val := by
  rw [hb];
  have hswap : ∀ z : V,
      Semiformula.Eval (z :> x :> w :> e) f
          (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))).val ↔
        Semiformula.Eval (z :> x :> e) f φ.sigmaInv.val := by
    intro z;
    rw [val_rew, Semiformula.eval_rew];
    have hA : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) f) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.bvar
        = (z :> x :> e : Fin (n + 2) → V) := by
      funext i;
      cases i using Fin.cases with
      | zero => simp;
      | succ i =>
        cases i using Fin.cases with
        | zero => simp;
        | succ i => simp;
    have hB : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) f) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.fvar
        = f := by
      funext i; simp;
    rw [hA, hB];
  have hval : (‘#1 + 1’ : ArithmeticSemiterm ξ (n + 2)).val (x :> w :> e) f = w + 1 := by simp;
  rw [hval];
  simp only [hswap, Arithmetic.lt_succ_iff_le];

mutual

private theorem models_ball :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (u : ArithmeticSemiterm ξ n) →
      (φ : Prenex Γ s ξ (n + 1)) → (e : Fin n → V) →
    Semiformula.Eval e f (∀'[u] φ).val ↔ ∀ x < u.val e f, Semiformula.Eval (x :> e) f φ.val
  | _, 0, _, _, u, φ, e => by
    simp [ball_zero, Prenex.val, Semiformula.eval_ball];
  | 𝚺, s + 1, _, _, u, φ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 s;
    have iha : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : Prenex 𝚷 s ξ (m + 1)) (e : Fin m → V),
        Semiformula.Eval e f (∀'[u] φ).val ↔ ∀ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_ball u φ e;
    have ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : Prenex 𝚷 s ξ (m + 1)) (e : Fin m → V),
        Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_bexs u φ e;
    rw [ball_succ_sigma (u := u) (φ := φ), models_sigma];
    simp only [iha (Rew.bShift u), Semiterm.val_bShift, models_bexs_witness ihb φ,
      models_sigmaInv φ];
    constructor;
    · rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;
    · intro h;
      exact (CollectionOnHierarchy.collection 𝚷 s
        (.of_strictHierarchy φ.sigmaInv.val_strictHierarchy e f) (u.val e f) h).imp
        fun b hb x hx ↦ (hb x hx).imp fun y hy ↦ ⟨le_of_lt hy.1, hy.2⟩;
  | 𝚷, s + 1, _, _, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : Prenex 𝚺 (s + 1) ξ (m + 1))
        (e : Fin m → V),
        Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_bexs u φ e;
    have hthis : Semiformula.Eval e f (∃'[u] ∼φ).val ↔
        ∃ x < u.val e f, Semiformula.Eval (x :> e) f (∼φ).val := ih u (∼φ) e;
    have hval : (∀'[u] φ).val = ∼(∃'[u] ∼φ).val := by
      rw [ball_succ_pi (u := u) (φ := φ)];
      exact val_neg (∃'[u] ∼φ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

private theorem models_bexs :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (u : ArithmeticSemiterm ξ n) →
      (φ : Prenex Γ s ξ (n + 1)) → (e : Fin n → V) →
    Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val
  | _, 0, _, _, u, φ, e => by
    simp [bexs_zero, Prenex.val, Semiformula.eval_bexs];
  | 𝚺, s + 1, n, _, u, φ, e => by
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 s;
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : Prenex 𝚷 s ξ (m + 1)) (e : Fin m → V),
        Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_bexs u φ e;
    set φ₁' := φ.sigmaInv;
    set φ₁ := φ₁'.val;
    set v := #1 :> #0 :> fun i => #(i.succ.succ) with hv;
    let φ₂' := φ₁'.rew (Rew.subst v);
    have hswap : ∀ (x b : V), Semiformula.Eval (x :> b :> e) f φ₂'.val ↔
        Semiformula.Eval (b :> x :> e) f φ₁ := by
      intro x b;
      rw [val_rew, Semiformula.eval_rew];
      have hA : (Semiterm.val (M := V) (x :> b :> e) f) ∘ (Rew.subst v) ∘ Semiterm.bvar
          = (b :> x :> e : Fin (n + 2) → V) := by
        funext i;
        cases i using Fin.cases with
        | zero => simp [hv];
        | succ i =>
          cases i using Fin.cases with
          | zero => simp [hv];
          | succ i => simp [hv];
      have hB : (Semiterm.val (M := V) (x :> b :> e) f) ∘ (Rew.subst v) ∘ Semiterm.fvar
          = f := by
        funext i; simp;
      rw [hA, hB];
    rw [bexs_succ_sigma (u := u) (φ := φ), val_sigma]
    change (∃ b, Semiformula.Eval (b :> e) f (∃'[Rew.bShift u] φ₂').val) ↔
      ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val;
    simp only [ih (Rew.bShift u) φ₂', Semiterm.val_bShift, hswap, models_sigmaInv φ];
    grind;
  | 𝚷, s + 1, _, _, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : Prenex 𝚺 (s + 1) ξ (m + 1))
        (e : Fin m → V),
        Semiformula.Eval e f (∀'[u] φ).val ↔ ∀ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_ball u φ e;
    have hthis : Semiformula.Eval e f (∀'[u] ∼φ).val ↔
        ∀ x < u.val e f, Semiformula.Eval (x :> e) f (∼φ).val := ih u (∼φ) e;
    have hval : (∃'[u] φ).val = ∼(∀'[u] ∼φ).val := by
      rw [bexs_succ_pi (u := u) (φ := φ)];
      exact val_neg (∀'[u] ∼φ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

mutual

private theorem models_and :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (φ ψ : Prenex Γ s ξ n) → (e : Fin n → V) →
    Semiformula.Eval e f (φ ⋏ ψ).val ↔ Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val
  | _, 0, _, _, φ, ψ, e => by
    simp [and_zero, Prenex.val];
  | 𝚺, s + 1, n, _, φ, ψ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 s;
    have iha : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋏ ψ).val ↔
          Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_and φ ψ e;
    rw [and_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
    set φ₂' := φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
    set ψ₂' := ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
    have hα_eval : ∀ z : V,
        Semiformula.Eval (z :> e) f (∃'[‘#0 + 1’] φ₂').val ↔
          ∃ x ≤ z, Semiformula.Eval (x :> e) f φ.sigmaInv.val := by
      intro z;
      rw [models_bexs ‘#0 + 1’ φ₂' (z :> e)];
      simp only [φ₂', val_rew, Semiformula.eval_insert1];
      simp [Arithmetic.lt_succ_iff_le];
    have hβ_eval : ∀ z : V,
        Semiformula.Eval (z :> e) f (∃'[‘#0 + 1’] ψ₂').val ↔
          ∃ x ≤ z, Semiformula.Eval (x :> e) f ψ.sigmaInv.val := by
      intro z;
      rw [models_bexs ‘#0 + 1’ ψ₂' (z :> e)];
      simp only [ψ₂', val_rew, Semiformula.eval_insert1];
      simp [Arithmetic.lt_succ_iff_le];
    simp only [iha (∃'[‘#0 + 1’] φ₂') (∃'[‘#0 + 1’] ψ₂'), models_sigmaInv φ, models_sigmaInv ψ,
      hα_eval, hβ_eval];
    constructor;
    · rintro ⟨z, ⟨x, -, hx⟩, ⟨y, -, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
  | 𝚷, s + 1, _, _, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋎ ψ).val ↔
          Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_or φ ψ e;
    have hthis : Semiformula.Eval e f (∼φ ⋎ ∼ψ).val ↔
        Semiformula.Eval e f (∼φ).val ∨ Semiformula.Eval e f (∼ψ).val := ih (∼φ) (∼ψ) e;
    have hval : (φ ⋏ ψ).val = ∼(∼φ ⋎ ∼ψ).val := by
      rw [and_succ_pi (φ := φ) (ψ := ψ)];
      exact val_neg (∼φ ⋎ ∼ψ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

private theorem models_or :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (φ ψ : Prenex Γ s ξ n) → (e : Fin n → V) →
    Semiformula.Eval e f (φ ⋎ ψ).val ↔ Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val
  | _, 0, _, _, φ, ψ, e => by
    simp [or_zero, Prenex.val];
  | 𝚺, s + 1, _, _, φ, ψ, e => by
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 s;
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋎ ψ).val ↔
          Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_or φ ψ e;
    rw [or_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
    simp only [ih φ.sigmaInv ψ.sigmaInv, models_sigmaInv φ, models_sigmaInv ψ];
    exact exists_or;
  | 𝚷, s + 1, _, _, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋏ ψ).val ↔
          Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_and φ ψ e;
    have hthis : Semiformula.Eval e f (∼φ ⋏ ∼ψ).val ↔
        Semiformula.Eval e f (∼φ).val ∧ Semiformula.Eval e f (∼ψ).val := ih (∼φ) (∼ψ) e;
    have hval : (φ ⋎ ψ).val = ∼(∼φ ⋏ ∼ψ).val := by
      rw [or_succ_pi (φ := φ) (ψ := ψ)];
      exact val_neg (∼φ ⋏ ∼ψ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

def exs (φ : Prenex 𝚺 (s + 1) ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n :=
  (∃'[‘#0 + 1’] (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma

def all (φ : Prenex 𝚷 (s + 1) ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n := ∼(exs (∼φ))

local prefix:64 "∃' " => Prenex.exs
local prefix:64 "∀' " => Prenex.all

private lemma models_exs [V↓[ℒₒᵣ] ⊧* 𝗕𝚷s] (φ : Prenex 𝚺 (s + 1) ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f (∃' φ).val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
  have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 s;
  change Semiformula.Eval e f
      (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
        (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma.val ↔
    ∃ x, Semiformula.Eval (x :> e) f φ.val;
  rw [models_sigma];
  have hβeval : ∀ z : V,
      Semiformula.Eval (z :> e) f
        (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
          (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).val ↔
        ∃ y ≤ z, Semiformula.Eval (y :> z :> e) f
          (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val := by
    intro z;
    rw [models_bexs];
    have hval : (‘#0 + 1’ : ArithmeticSemiterm ξ (n + 1)).val (z :> e) f = z + 1 := by simp;
    rw [hval];
    simp only [Arithmetic.lt_succ_iff_le];
  have hαeval : ∀ y z : V,
      Semiformula.Eval (y :> z :> e) f
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val ↔
        ∃ x ≤ z, Semiformula.Eval (x :> y :> e) f φ.sigmaInv.val :=
    fun y z => models_bexs_witness models_bexs φ y z e;
  simp only [hβeval, hαeval, models_sigmaInv φ];
  constructor;
  · rintro ⟨z, y, -, x, -, hx⟩;
    exact ⟨y, x, hx⟩;
  · rintro ⟨y, x, hx⟩;
    exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;

private lemma models_all [V↓[ℒₒᵣ] ⊧* 𝗕𝚷s] (φ : Prenex 𝚷 (s + 1) ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f (∀' φ).val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.val := by
  have hthis : Semiformula.Eval e f (∃' ∼φ).val ↔ ∃ x, Semiformula.Eval (x :> e) f (∼φ).val :=
    models_exs (∼φ) e;
  have hval : (∀' φ).val = ∼(∃' ∼φ).val := by
    unfold all;
    exact val_neg (∃' ∼φ);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

theorem models_exists_prenex {Γ Γ' : Polarity} {s n : ℕ} {φ : ArithmeticSemiformula ξ n}
    (h : Hierarchy Γ s φ) :
  ∃ φ' : Prenex Γ s ξ n,
    ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗕 Γ' s],
      ∀ (e : Fin n → V) (f : ξ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f φ'.val := by
  suffices h' : ∃ φ' : Prenex Γ s ξ n,
      ∀ (V : Type _) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PrenexBase s],
        ∀ (e : Fin n → V) (f : ξ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f φ'.val by
    obtain ⟨φ', hφ'⟩ := h';
    use φ';
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy Γ' s;
    exact hφ' V e f;
  induction h with
  | @bounded Γ s n φ h =>
    let φ₀ : 𝚺₀.Semiformula ξ n := .mkSigma φ (Hierarchy.bounded 𝚺 0 n h);
    use ofΔ₀ φ₀ Γ s;
    intro V _ _ e f;
    exact (models_ofΔ₀ φ₀ e).symm;
  | and _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋏ ψ';
    intro V _ _ e f;
    grind [models_and φ' ψ' e, LogicalConnective.Prop.and_eq];
  | or _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋎ ψ';
    intro V _ _ e f;
    grind [models_or φ' ψ' e, LogicalConnective.Prop.or_eq];
  | ball hR pos _ ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀'[u] φ';
    intro V _ _ e f;
    rw [models_ball u φ' e];
    simp only [Semiformula.eval_ball];
    exact forall_congr' fun x => (imp_congr Iff.rfl (hφ' V (x :> e) f)).trans (by simp);
  | bexs hR pos _ ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃'[u] φ';
    intro V _ _ e f;
    rw [models_bexs u φ' e];
    simp only [Semiformula.eval_bexs];
    exact exists_congr fun x => (and_congr Iff.rfl (hφ' V (x :> e) f)).trans (by simp);
  | @exs s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃' φ';
    intro V _ _ e f;
    rw [models_exs φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e) f;
  | @all s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀' φ';
    intro V _ _ e f;
    rw [models_all φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e) f;
  | @sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.sigma;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 s;
    rw [models_sigma φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e) f;
  | @pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.pi;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 s;
    rw [models_pi φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e) f;
  | @dummy_sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∀' φ').altUp;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase (s + 1) :=
      models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 (s + 1);
    exact Semiformula.eval_all.trans
      ((forall_congr' fun x => hφ' V (x :> e) f).trans
        ((models_all φ' e).symm.trans (models_altUp (∀' φ') e).symm));
  | @dummy_pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∃' φ').altUp;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase (s + 1) :=
      models_PrenexBase_of_models_CollectionOnHierarchy 𝚷 (s + 1);
    exact Semiformula.eval_ex.trans
      ((exists_congr fun x => hφ' V (x :> e) f).trans
      ((models_exs φ' e).symm.trans (models_altUp (∃' φ') e).symm));

end Prenex

section

variable {Γ : Polarity} {s : ℕ} (T : ArithmeticTheory) [𝗕𝚺s ⪯ T]
         {n : ℕ} {φ : ArithmeticSemisentence n}

theorem exists_prenex_of_hierarchy (h : Hierarchy Γ s φ) :
  ∃ φ' : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 φ'.val) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := s);
  obtain ⟨φ', hφ'⟩ := Prenex.models_exists_prenex (Γ' := 𝚺) h;
  use φ';
  apply provable_iff_of_models_iff.{0};
  intro V _ _ e;
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 s := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* T);
  exact hφ' V e Empty.elim;

theorem exists_matrix_provable (h : Hierarchy Γ s φ) :
  ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  obtain ⟨_, hφ'⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨_, by simpa [Prenex.val] using hφ'⟩;

theorem exists_strictHierarchy_of_hierarchy (h : Hierarchy Γ s φ) :
  ∃ ψ : ArithmeticSemisentence n, StrictHierarchy Γ s ψ ∧ T ⊢ ∀¹* (φ 🡘 ψ) := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨φ'.val, Prenex.val_strictHierarchy, hφ'⟩;

end

lemma StrictDefinable.of_definable {V : Type*} [ORingStructure V] {Γ Γ' : Polarity} {s k : ℕ}
    [V↓[ℒₒᵣ] ⊧* 𝗕 Γ' s] {P : (Fin k → V) → Prop} (hP : Γ-[s].Definable P) :
    StrictDefinable Γ s P := by
  obtain ⟨φ, hφ⟩ := hP;
  obtain ⟨θ, hθ⟩ := Prenex.models_exists_prenex (Γ' := Γ') φ.polarity_prop;
  exact ⟨θ.val, Prenex.val_strictHierarchy, fun v ↦ (hθ V v id).symm.trans hφ.iff⟩;

end Arithmetic

end FFL.FirstOrder
