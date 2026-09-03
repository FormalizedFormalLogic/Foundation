module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Arithmetic.BoundedCollection
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# Prenex normal form for the arithmetical hierarchy

For `𝗜𝚺 s ⪯ T`, every `Hierarchy Γ s` formula `φ` is `T`-provably equivalent to `φ₀.toPrenex Γ s`
for some `φ₀ : ArithmeticSemisentence (n + s)` in `Hierarchy 𝚺 0`.
-/

@[expose] public section

open LO

namespace LO.FirstOrder

namespace Arithmetic

structure Prenex (Γ : Polarity) (s : ℕ) (ξ : Type*) (n : ℕ) where
  matrix : 𝚺₀.Semiformula ξ (n + s)

namespace Prenex

variable {Γ : Polarity} {s : ℕ} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}
variable {V : Type*} [ORingStructure V]

@[coe]
def val (φ : Prenex Γ s ξ n) : ArithmeticSemiformula ξ n := φ.matrix.val.toPrenex Γ s

instance : CoeTC (Prenex Γ s ξ n) (ArithmeticSemiformula ξ n) := ⟨val⟩

def neg (φ : Prenex Γ s ξ n) : Prenex Γ.alt s ξ n := ⟨.mkSigma (∼φ.matrix.val) φ.matrix.sigma_prop.neg.of_zero⟩

local prefix:75 "∼" => Prenex.neg

def rew (φ : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : Prenex Γ s ξ₂ n₂ := ⟨φ.matrix.rew (ω.qpow s)⟩

def sigma (φ : Prenex 𝚷 s ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def pi (φ : Prenex 𝚺 s ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def sigmaInv (φ : Prenex 𝚺 (s + 1) ξ n) : Prenex 𝚷 s ξ (n + 1) := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def piInv (φ : Prenex 𝚷 (s + 1) ξ n) : Prenex 𝚺 s ξ (n + 1) := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def altUp (φ : Prenex Γ s ξ n) : Prenex Γ.alt (s + 1) ξ n := by
  rcases Γ with _ | _
  . exact (φ.rew Rew.bShift).pi
  . exact (φ.rew Rew.bShift).sigma

def ofΔ₀ (φ : 𝚺₀.Semiformula ξ n) : (Γ : Polarity) → (s : ℕ) → Prenex Γ s ξ n
  | Γ, 0     => ⟨φ⟩
  | Γ, s + 1 => by simpa using altUp (ofΔ₀ φ Γ.alt s)

def verum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) Γ s

def falsum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) Γ s

def rel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) Γ s

def nrel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) Γ s


@[simp, grind .]
lemma val_hierarchy {φ : Prenex Γ s ξ n} : Hierarchy Γ s φ.val := by
  change Hierarchy Γ s (φ.matrix.val.toPrenex Γ s)
  simpa only [Nat.zero_add] using Hierarchy.toPrenex (Γ := Γ) (j := 0) φ.matrix.sigma_prop.of_zero

@[simp, grind .]
lemma val_deltaZero {φ : Prenex Γ 0 ξ n} : Hierarchy 𝚺 0 φ.val := φ.matrix.sigma_prop

@[simp, grind .]
lemma val_neg (φ : Prenex Γ s ξ n) : (∼φ).val = ∼φ.val := by simp [neg, val]

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
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_sigma, ← Polarity.alt_sigma, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp



@[simp, grind .]
lemma val_piInv {φ : Prenex 𝚷 (s + 1) ξ n} : φ.val = ∀¹ φ.piInv.val := by
  unfold val piInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_pi, ← Polarity.alt_pi, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp

lemma models_sigmaInv (φ : Prenex 𝚺 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e φ.val ↔ ∃ x, V ⊧/(x :> e) φ.sigmaInv.val := by
  rw [val_sigmaInv]; exact Semiformula.eval_ex;

lemma models_piInv (φ : Prenex 𝚷 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e φ.val ↔ ∀ x, V ⊧/(x :> e) φ.piInv.val := by
  rw [val_piInv]; exact Semiformula.eval_all;

lemma models_sigma (φ : Prenex 𝚷 s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e φ.sigma.val ↔ ∃ x, V ⊧/(x :> e) φ.val := by
  rw [val_sigma]; exact Semiformula.eval_ex;

lemma models_pi (φ : Prenex 𝚺 s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e φ.pi.val ↔ ∀ x, V ⊧/(x :> e) φ.val := by
  rw [val_pi]; exact Semiformula.eval_all;

lemma models_altUp (φ : Prenex Γ s Empty n) (e : Fin n → V) :
  V ⊧/e φ.altUp.val ↔ V ⊧/e φ.val := by
  rcases Γ <;> simp [
    Polarity.eq_sigma, Polarity.alt_sigma, altUp,
    -val_piInv, -val_sigmaInv,
    Semiformula.eval_all, Nat.succ_eq_add_one
  ]

lemma models_ofΔ₀ (φ : 𝚺₀.Semisentence n) (e : Fin n → V) :
    V ⊧/e (ofΔ₀ φ Γ s).val ↔ V ⊧/e φ.val := by
  induction s generalizing Γ with
  | zero => rfl
  | succ s ih =>
    rcases Γ with _ | _
    . change V ⊧/e (ofΔ₀ φ 𝚷 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚷 s) e).trans (ih (Γ := 𝚷))
    . change V ⊧/e (ofΔ₀ φ 𝚺 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚺 s) e).trans (ih (Γ := 𝚺))

lemma models_verum (e : Fin n → V) :
    V ⊧/e (verum : Prenex Γ s Empty n).val ↔ V ⊧/e (⊤ : ArithmeticSemisentence n) :=
  models_ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) e

lemma models_falsum (e : Fin n → V) :
    V ⊧/e (falsum : Prenex Γ s Empty n).val ↔ V ⊧/e (⊥ : ArithmeticSemisentence n) :=
  models_ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) e

lemma models_rel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm Empty n)
    (e : Fin n → V) :
    V ⊧/e (rel r v : Prenex Γ s Empty n).val ↔ V ⊧/e (Semiformula.rel r v) :=
  models_ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) e

lemma models_nrel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm Empty n)
    (e : Fin n → V) :
    V ⊧/e (nrel r v : Prenex Γ s Empty n).val ↔ V ⊧/e (Semiformula.nrel r v) :=
  models_ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) e

variable {T : ArithmeticTheory}

lemma provable_iff_sigmaInv {φ' : Prenex 𝚺 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
  T ⊢ ∀¹* (φ 🡘 ∃¹ φ'.sigmaInv.val) := φ'.val_sigmaInv ▸ hφ'

lemma provable_iff_piInv {φ' : Prenex 𝚷 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
  T ⊢ ∀¹* (φ 🡘 ∀¹ φ'.piInv.val) := φ'.val_piInv ▸ hφ'

mutual

def ball : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm Empty n → Prenex Γ s Empty (n + 1) → Prenex Γ s Empty n
  | _, 0    , _, u, φ => ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) φ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, φ => (ball (Rew.bShift u) (bexs ‘#1 + 1’ (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(bexs u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def bexs : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm Empty n → Prenex Γ s Empty (n + 1) → Prenex Γ s Empty n
  | _, 0    , _, u, φ => ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) φ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, φ => (bexs (Rew.bShift u) (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(ball u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

local notation:64 "∀'[" u "] " φ => Prenex.ball u φ
local notation:64 "∃'[" u "] " φ => Prenex.bexs u φ

@[simp]
lemma ball_zero {u : ArithmeticSemiterm Empty n} {φ : Prenex Γ 0 Empty (n + 1)} :
  (∀'[u] φ) = ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) φ.val_deltaZero)⟩ := by
  simp [ball]

lemma ball_succ_sigma {u : ArithmeticSemiterm Empty n} {φ : Prenex 𝚺 (s + 1) Empty (n + 1)} :
  (∀'[u] φ) = (∀'[Rew.bShift u] (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma := by
  rw [ball]

lemma ball_succ_pi {u : ArithmeticSemiterm Empty n} {φ : Prenex 𝚷 (s + 1) Empty (n + 1)} :
  (∀'[u] φ) = ∼(∃'[u] ∼φ) := by
  rw [ball]


@[simp]
lemma bexs_zero {u : ArithmeticSemiterm Empty n} {φ : Prenex Γ 0 Empty (n + 1)} :
  (∃'[u] φ) = ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) φ.val_deltaZero)⟩ := by
  simp [bexs]

lemma bexs_succ_sigma {u : ArithmeticSemiterm Empty n} {φ : Prenex 𝚺 (s + 1) Empty (n + 1)} :
  (∃'[u] φ) = (∃'[Rew.bShift u] (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma := by
  rw [bexs]

lemma bexs_succ_pi {u : ArithmeticSemiterm Empty n} {φ : Prenex 𝚷 (s + 1) Empty (n + 1)} :
  (∃'[u] φ) = ∼(∀'[u] ∼φ) := by
  rw [bexs]


mutual

def and : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s Empty n → Prenex Γ s Empty n → Prenex Γ s Empty n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ =>
      (and (∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
           (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(or (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def or : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s Empty n → Prenex Γ s Empty n → Prenex Γ s Empty n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ => (or φ.sigmaInv ψ.sigmaInv).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(and (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

local infixr:69 " ⋏ " => Prenex.and
local infixr:68 " ⋎ " => Prenex.or

@[simp]
lemma and_zero {φ ψ : Prenex Γ 0 Empty n} : (φ ⋏ ψ) = ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  simp [and]

lemma and_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) Empty n} :
  (φ ⋏ ψ) = ((∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ))))) ⋏
    (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma := by
  rw [and]

lemma and_succ_pi {φ ψ : Prenex 𝚷 (s + 1) Empty n} : (φ ⋏ ψ) = ∼(∼φ ⋎ ∼ψ) := by rw [and]


@[simp]
lemma or_zero {φ ψ : Prenex Γ 0 Empty n} : (φ ⋎ ψ) = ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  simp [or]

lemma or_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) Empty n} : (φ ⋎ ψ) = (φ.sigmaInv ⋎ ψ.sigmaInv).sigma := by
  rw [or]

lemma or_succ_pi {φ ψ : Prenex 𝚷 (s + 1) Empty n} : (φ ⋎ ψ) = ∼(∼φ ⋏ ∼ψ) := by
  rw [or]

lemma models_ball_zero (u : ArithmeticSemiterm Empty n) (φ : Prenex Γ 0 Empty (n + 1))
    (e : Fin n → V) :
    V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val := by
  simp [ball_zero, Prenex.val, Semiformula.eval_ball];

lemma models_bexs_zero (u : ArithmeticSemiterm Empty n) (φ : Prenex Γ 0 Empty (n + 1))
    (e : Fin n → V) :
    V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val := by
  simp [bexs_zero, Prenex.val, Semiformula.eval_bexs];

lemma models_and_zero (φ ψ : Prenex Γ 0 Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val := by
  simp [and_zero, Prenex.val];

lemma models_or_zero (φ ψ : Prenex Γ 0 Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val := by
  simp [or_zero, Prenex.val];

lemma models_bexs_succ_sigma
    (ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val)
    (u : ArithmeticSemiterm Empty n) (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val := by
  set φ₁' := φ.sigmaInv;
  set φ₁ := φ₁'.val;
  set v := #1 :> #0 :> fun i => #(i.succ.succ) with hv;
  let φ₂' := φ₁'.rew (Rew.subst v);
  have hswap : ∀ (x b : V), V ⊧/(x :> b :> e) φ₂'.val ↔ V ⊧/(b :> x :> e) φ₁ := by
    intro x b;
    rw [val_rew, Semiformula.eval_rew];
    have hA : (Semiterm.val (M := V) (x :> b :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.bvar
        = (b :> x :> e : Fin (n + 2) → V) := by
      funext i;
      cases i using Fin.cases with
      | zero => simp [hv];
      | succ i =>
        cases i using Fin.cases with
        | zero => simp [hv];
        | succ i => simp [hv];
    have hB : (Semiterm.val (M := V) (x :> b :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.fvar
        = (Empty.elim : Empty → V) := by
      funext i; exact i.elim;
    rw [hA, hB];
  rw [bexs_succ_sigma (u := u) (φ := φ), val_sigma]
  show (∃ b, V ⊧/(b :> e) (∃'[Rew.bShift u] φ₂').val) ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val;
  simp only [ih (Rew.bShift u) φ₂', Semiterm.val_bShift, hswap, models_sigmaInv φ];
  grind;

lemma models_bexs_witness [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (hb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val)
    (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (x w : V) (e : Fin n → V) :
    V ⊧/(x :> w :> e)
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val
      ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) φ.sigmaInv.val := by
  rw [hb];
  have hswap : ∀ z : V,
      V ⊧/(z :> x :> w :> e) (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))).val ↔
        V ⊧/(z :> x :> e) φ.sigmaInv.val := by
    intro z;
    rw [val_rew, Semiformula.eval_rew];
    have hA : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) Empty.elim) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.bvar
        = (z :> x :> e : Fin (n + 2) → V) := by
      funext i;
      cases i using Fin.cases with
      | zero => simp;
      | succ i =>
        cases i using Fin.cases with
        | zero => simp;
        | succ i => simp;
    have hB : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) Empty.elim) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.fvar
        = (Empty.elim : Empty → V) := by
      funext i; exact i.elim;
    rw [hA, hB];
  have hval : (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)).valb (x :> w :> e) = w + 1 := by simp;
  rw [hval];
  simp only [hswap, Arithmetic.lt_succ_iff_le];

lemma models_ball_succ_sigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)]
    (iha : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val)
    (ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val)
    (u : ArithmeticSemiterm Empty n) (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
  rw [ball_succ_sigma (u := u) (φ := φ), models_sigma];
  simp only [iha (Rew.bShift u), Semiterm.val_bShift, models_bexs_witness ihb φ,
    models_sigmaInv φ];
  constructor;
  . rintro ⟨w, hw⟩ x hx;
    obtain ⟨y, -, hy⟩ := hw x hx;
    exact ⟨y, hy⟩;
  . intro h;
    have hθ : Hierarchy 𝚺 (s + 1) φ.sigmaInv.val := φ.sigmaInv.val_hierarchy.accum 𝚺;
    exact sigma_exists_bound_witness hθ e (u.valb e) h;

lemma models_ball_succ_pi
    (h : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val)
    (u : ArithmeticSemiterm Empty n) (φ : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val := by
  have hthis : V ⊧/e (∃'[u] ∼φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) (∼φ).val := h u (∼φ) e;
  have hval : (∀'[u] φ).val = ∼(∃'[u] ∼φ).val := by
    rw [ball_succ_pi (u := u) (φ := φ)];
    exact val_neg (∃'[u] ∼φ);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_bexs_succ_pi
    (h : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val)
    (u : ArithmeticSemiterm Empty n) (φ : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val := by
  have hthis : V ⊧/e (∀'[u] ∼φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) (∼φ).val := h u (∼φ) e;
  have hval : (∃'[u] φ).val = ∼(∀'[u] ∼φ).val := by
    rw [bexs_succ_pi (u := u) (φ := φ)];
    exact val_neg (∀'[u] ∼φ);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_ball_bexs [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (u : ArithmeticSemiterm Empty n) (φ : Prenex Γ s Empty (n + 1)) (e : Fin n → V) :
    (V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val) ∧
    (V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val) := by
  rename_i h;
  induction s generalizing Γ n u e h with
  | zero => exact ⟨models_ball_zero u φ e, models_bexs_zero u φ e⟩;
  | succ s ih =>
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have iha : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => (ih u φ e).1;
    have ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => (ih u φ e).2;
    have haSigma : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_ball_succ_sigma iha ihb u φ e;
    have hbSigma : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_bexs_succ_sigma ihb u φ e;
    rcases Γ with _ | _;
    . exact ⟨haSigma u φ e, hbSigma u φ e⟩;
    . exact ⟨models_ball_succ_pi hbSigma u φ e, models_bexs_succ_pi haSigma u φ e⟩;

lemma models_ball [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (u : ArithmeticSemiterm Empty n) (φ : Prenex Γ s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val :=
  (models_ball_bexs u φ e).1

lemma models_bexs [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (u : ArithmeticSemiterm Empty n) (φ : Prenex Γ s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
  (models_ball_bexs u φ e).2

lemma models_or_succ_sigma
    (ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
      V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val)
    (φ ψ : Prenex 𝚺 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val := by
  rw [or_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
  simp only [ih φ.sigmaInv ψ.sigmaInv, models_sigmaInv φ, models_sigmaInv ψ];
  exact exists_or;

lemma models_and_succ_sigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
      V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val)
    (φ ψ : Prenex 𝚺 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s);
  rw [and_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
  set φ₂' := φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
  set ψ₂' := ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
  have hα_eval : ∀ z : V, V ⊧/(z :> e) (∃'[‘#0 + 1’] φ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) φ.sigmaInv.val := by
    intro z;
    rw [models_bexs ‘#0 + 1’ φ₂' (z :> e)];
    simp only [φ₂', val_rew, Semiformula.eval_insert1];
    simp [Arithmetic.lt_succ_iff_le];
  have hβ_eval : ∀ z : V, V ⊧/(z :> e) (∃'[‘#0 + 1’] ψ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ.sigmaInv.val := by
    intro z;
    rw [models_bexs ‘#0 + 1’ ψ₂' (z :> e)];
    simp only [ψ₂', val_rew, Semiformula.eval_insert1];
    simp [Arithmetic.lt_succ_iff_le];
  simp only [ih (∃'[‘#0 + 1’] φ₂') (∃'[‘#0 + 1’] ψ₂'), models_sigmaInv φ, models_sigmaInv ψ,
    hα_eval, hβ_eval];
  constructor;
  . rintro ⟨z, ⟨x, -, hx⟩, ⟨y, -, hy⟩⟩;
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
  . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
    exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;

lemma models_and_succ_pi
    (h : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
      V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val)
    (φ ψ : Prenex 𝚷 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val := by
  have hthis : V ⊧/e (∼φ ⋎ ∼ψ).val ↔ V ⊧/e (∼φ).val ∨ V ⊧/e (∼ψ).val := h (∼φ) (∼ψ) e;
  have hval : (φ ⋏ ψ).val = ∼(∼φ ⋎ ∼ψ).val := by
    rw [and_succ_pi (φ := φ) (ψ := ψ)];
    exact val_neg (∼φ ⋎ ∼ψ);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_or_succ_pi
    (h : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
      V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val)
    (φ ψ : Prenex 𝚷 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val := by
  have hthis : V ⊧/e (∼φ ⋏ ∼ψ).val ↔ V ⊧/e (∼φ).val ∧ V ⊧/e (∼ψ).val := h (∼φ) (∼ψ) e;
  have hval : (φ ⋎ ψ).val = ∼(∼φ ⋏ ∼ψ).val := by
    rw [or_succ_pi (φ := φ) (ψ := ψ)];
    exact val_neg (∼φ ⋏ ∼ψ);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_and_or [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (φ ψ : Prenex Γ s Empty n) (e : Fin n → V) :
    (V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val) ∧
    (V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val) := by
  rename_i h;
  induction s generalizing Γ n e h with
  | zero => exact ⟨models_and_zero φ ψ e, models_or_zero φ ψ e⟩;
  | succ s ih =>
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have iha : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val :=
      fun φ ψ e => (ih φ ψ e).1;
    have iho : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val :=
      fun φ ψ e => (ih φ ψ e).2;
    have haSigma : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val :=
      fun φ ψ e => models_and_succ_sigma iha φ ψ e;
    have hoSigma : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val :=
      fun φ ψ e => models_or_succ_sigma iho φ ψ e;
    rcases Γ with _ | _;
    . exact ⟨haSigma φ ψ e, hoSigma φ ψ e⟩;
    . exact ⟨models_and_succ_pi hoSigma φ ψ e, models_or_succ_pi haSigma φ ψ e⟩;

lemma models_and [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (φ ψ : Prenex Γ s Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val :=
  (models_and_or φ ψ e).1

lemma models_or [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (φ ψ : Prenex Γ s Empty n) (e : Fin n → V) :
    V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val :=
  (models_and_or φ ψ e).2

def exs (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) : Prenex 𝚺 (s + 1) Empty n :=
  (∃'[‘#0 + 1’] (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma

def all (φ : Prenex 𝚷 (s + 1) Empty (n + 1)) : Prenex 𝚷 (s + 1) Empty n := ∼(exs (∼φ))

local prefix:64 "∃' " => Prenex.exs
local prefix:64 "∀' " => Prenex.all

lemma models_exs [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∃' φ).val ↔ ∃ x, V ⊧/(x :> e) φ.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s);
  show V ⊧/e
      (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
        (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma.val ↔
    ∃ x, V ⊧/(x :> e) φ.val;
  rw [models_sigma];
  have hβeval : ∀ z : V,
      V ⊧/(z :> e)
        (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
          (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).val ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e)
          (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val := by
    intro z;
    rw [models_bexs];
    have hval : (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)).valb (z :> e) = z + 1 := by simp;
    rw [hval];
    simp only [Arithmetic.lt_succ_iff_le];
  have hαeval : ∀ y z : V,
      V ⊧/(y :> z :> e)
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ.sigmaInv.val :=
    fun y z => models_bexs_witness models_bexs φ y z e;
  simp only [hβeval, hαeval, models_sigmaInv φ];
  constructor;
  . rintro ⟨z, y, -, x, -, hx⟩;
    exact ⟨y, x, hx⟩;
  . rintro ⟨y, x, hx⟩;
    exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;

lemma models_all [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (φ : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∀' φ).val ↔ ∀ x, V ⊧/(x :> e) φ.val := by
  have hthis : V ⊧/e (∃' ∼φ).val ↔ ∃ x, V ⊧/(x :> e) (∼φ).val := models_exs (∼φ) e;
  have hval : (∀' φ).val = ∼(∃' ∼φ).val := by
    unfold all;
    exact val_neg (∃' ∼φ);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

theorem models_exists_prenex {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
  ∃ φ' : Prenex Γ s Empty n,
    ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e φ'.val := by
  induction h with
  | verum Γ s n =>
    use verum;
    intro V _ _ e;
    exact (models_verum e).symm;
  | falsum Γ s n =>
    use falsum;
    intro V _ _ e;
    exact (models_falsum e).symm;
  | rel Γ s r v =>
    use rel r v;
    intro V _ _ e;
    exact (models_rel r v e).symm;
  | nrel Γ s r v =>
    use nrel r v;
    intro V _ _ e;
    exact (models_nrel r v e).symm;
  | and _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋏ ψ';
    intro V _ _ e;
    rw [models_and φ' ψ' e];
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq];
    exact and_congr (hφ' V e) (hψ' V e);
  | or _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋎ ψ';
    intro V _ _ e;
    rw [models_or φ' ψ' e];
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq];
    exact or_congr (hφ' V e) (hψ' V e);
  | ball pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀'[u] φ';
    intro V _ _ e;
    rw [models_ball u φ' e];
    simp only [Semiformula.eval_ball];
    exact forall_congr' fun x => (imp_congr Iff.rfl (hφ' V (x :> e))).trans (by simp);
  | bexs pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃'[u] φ';
    intro V _ _ e;
    rw [models_bexs u φ' e];
    simp only [Semiformula.eval_bexs];
    exact exists_congr fun x => (and_congr Iff.rfl (hφ' V (x :> e))).trans (by simp);
  | @exs s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃' φ';
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_exs φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e);
  | @all s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀' φ';
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_all φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e);
  | @sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.sigma;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_sigma φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e);
  | @pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.pi;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_pi φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e);
  | @dummy_sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∀' φ').altUp;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (show s ≤ s + 1 + 1 by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := mod_ISigma_of_le (show s + 1 ≤ s + 1 + 1 by omega);
    exact Semiformula.eval_all.trans
      ((forall_congr' fun x => hφ' V (x :> e)).trans
        ((models_all φ' e).symm.trans (models_altUp (∀' φ') e).symm));
  | @dummy_pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∃' φ').altUp;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (show s ≤ s + 1 + 1 by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := mod_ISigma_of_le (show s + 1 ≤ s + 1 + 1 by omega);
    exact Semiformula.eval_ex.trans
      ((exists_congr fun x => hφ' V (x :> e)).trans
        ((models_exs φ' e).symm.trans (models_altUp (∃' φ') e).symm));

end Prenex

theorem exists_prenex_of_hierarchy {Γ : Polarity} {s : ℕ} (T : ArithmeticTheory) [𝗜𝚺 s ⪯ T]
  {n : ℕ} {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
  ∃ φ' : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 φ'.val) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_ISigma (s := s);
  obtain ⟨φ', hφ'⟩ := Prenex.models_exists_prenex h;
  use φ';
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := models_of_subtheory (T := 𝗜𝚺 s) (U := T) (inferInstance);
  exact hφ' V e;

theorem exists_matrix_provable {Γ : Polarity} {s: ℕ} (T : ArithmeticTheory) [𝗜𝚺 s ⪯ T]
  {n : ℕ} {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
  ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  obtain ⟨_, hφ'⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨_, by simpa [Prenex.val] using hφ'⟩;

end Arithmetic

end LO.FirstOrder
