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

@[coe]
def val (π : Prenex Γ s ξ n) : ArithmeticSemiformula ξ n := π.matrix.val.toPrenex Γ s

instance : CoeTC (Prenex Γ s ξ n) (ArithmeticSemiformula ξ n) := ⟨val⟩

def neg (π : Prenex Γ s ξ n) : Prenex Γ.alt s ξ n := ⟨.mkSigma (∼π.matrix.val) π.matrix.sigma_prop.neg.of_zero⟩

def rew (π : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : Prenex Γ s ξ₂ n₂ := ⟨π.matrix.rew (ω.qpow s)⟩

def sigma (π : Prenex 𝚷 s ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def pi (π : Prenex 𝚺 s ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def sigmaInv (π : Prenex 𝚺 (s + 1) ξ n) : Prenex 𝚷 s ξ (n + 1) := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def piInv (π : Prenex 𝚷 (s + 1) ξ n) : Prenex 𝚺 s ξ (n + 1) := ⟨π.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def altUp (π : Prenex Γ s ξ n) : Prenex Γ.alt (s + 1) ξ n := by
  rcases Γ with _ | _
  . exact (π.rew Rew.bShift).pi
  . exact (π.rew Rew.bShift).sigma

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
lemma val_hierarchy {π : Prenex Γ s ξ n} : Hierarchy Γ s π.val := by
  change Hierarchy Γ s (π.matrix.val.toPrenex Γ s)
  simpa only [Nat.zero_add] using Hierarchy.toPrenex (Γ := Γ) (j := 0) π.matrix.sigma_prop.of_zero

@[simp, grind .]
lemma val_deltaZero {π : Prenex Γ 0 ξ n} : Hierarchy 𝚺 0 π.val := π.matrix.sigma_prop

@[simp, grind .]
lemma val_neg (π : Prenex Γ s ξ n) : π.neg.val = ∼π.val := by simp [neg, val]

@[simp, grind .]
lemma val_rew (π : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) :
  (π.rew ω).val = ω ▹ π.val := by
  simp [val, rew]

@[simp, grind .]
lemma val_sigma {π : Prenex 𝚷 s ξ (n + 1)} : π.sigma.val = ∃¹ π.val := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]

@[simp, grind .]
lemma val_pi {π : Prenex 𝚺 s ξ (n + 1)} : π.pi.val = ∀¹ π.val := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]

@[simp, grind .]
lemma val_sigmaInv {π : Prenex 𝚺 (s + 1) ξ n} : π.val = ∃¹ π.sigmaInv.val := by
  unfold val sigmaInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_sigma, ← Polarity.alt_sigma, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp



@[simp, grind .]
lemma val_piInv {π : Prenex 𝚷 (s + 1) ξ n} : π.val = ∀¹ π.piInv.val := by
  unfold val piInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_pi, ← Polarity.alt_pi, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp

lemma models_sigmaInv (π : Prenex 𝚺 (s + 1) Empty n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e π.val ↔ ∃ x, V ⊧/(x :> e) π.sigmaInv.val := by
  rw [val_sigmaInv]; exact Semiformula.eval_ex;

lemma models_piInv (π : Prenex 𝚷 (s + 1) Empty n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e π.val ↔ ∀ x, V ⊧/(x :> e) π.piInv.val := by
  rw [val_piInv]; exact Semiformula.eval_all;

lemma models_sigma (π : Prenex 𝚷 s Empty (n + 1)) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e π.sigma.val ↔ ∃ x, V ⊧/(x :> e) π.val := by
  rw [val_sigma]; exact Semiformula.eval_ex;

lemma models_pi (π : Prenex 𝚺 s Empty (n + 1)) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e π.pi.val ↔ ∀ x, V ⊧/(x :> e) π.val := by
  rw [val_pi]; exact Semiformula.eval_all;

lemma models_altUp (π : Prenex Γ s Empty n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
  V ⊧/e π.altUp.val ↔ V ⊧/e π.val := by
  rcases Γ <;> simp [
    Polarity.eq_sigma, Polarity.alt_sigma, altUp,
    -val_piInv, -val_sigmaInv,
    Semiformula.eval_all, Nat.succ_eq_add_one
  ]

lemma models_ofΔ₀ (φ : 𝚺₀.Semisentence n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e (ofΔ₀ φ Γ s).val ↔ V ⊧/e φ.val := by
  induction s generalizing Γ with
  | zero => rfl
  | succ s ih =>
    rcases Γ with _ | _
    . change V ⊧/e (ofΔ₀ φ 𝚷 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚷 s) V e).trans (ih (Γ := 𝚷))
    . change V ⊧/e (ofΔ₀ φ 𝚺 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚺 s) V e).trans (ih (Γ := 𝚺))

variable {T : ArithmeticTheory}

lemma provable_iff_sigmaInv {π : Prenex 𝚺 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ 🡘 ∃¹ π.sigmaInv.val) := π.val_sigmaInv ▸ hπ

lemma provable_iff_piInv {π : Prenex 𝚷 (s + 1) Empty n} (hπ : T ⊢ ∀¹* (φ 🡘 π.val)) :
  T ⊢ ∀¹* (φ 🡘 ∀¹ π.piInv.val) := π.val_piInv ▸ hπ

mutual

def ball : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm Empty n → Prenex Γ s Empty (n + 1) → Prenex Γ s Empty n
  | _, 0    , _, u, π => ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) π.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, π => (ball (Rew.bShift u) (bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, u, π => (bexs u π.neg).neg
termination_by Γ s n _u _π => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def bexs : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm Empty n → Prenex Γ s Empty (n + 1) → Prenex Γ s Empty n
  | _, 0    , _, u, π => ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) π.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, π => (bexs (Rew.bShift u) (π.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma
  | 𝚷, _ + 1, _, u, π => (ball u π.neg).neg
termination_by Γ s n _u _π => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

@[simp]
lemma ball_zero {u : ArithmeticSemiterm Empty n} {π : Prenex Γ 0 Empty (n + 1)} :
  ball u π = ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) π.val_deltaZero)⟩ := by
  simp [ball]

lemma ball_succ_sigma {u : ArithmeticSemiterm Empty n} {π : Prenex 𝚺 (s + 1) Empty (n + 1)} :
  ball u π = (ball (Rew.bShift u) (bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma := by
  rw [ball]

lemma ball_succ_pi {u : ArithmeticSemiterm Empty n} {π : Prenex 𝚷 (s + 1) Empty (n + 1)} :
  ball u π = (bexs u π.neg).neg := by
  rw [ball]


@[simp]
lemma bexs_zero {u : ArithmeticSemiterm Empty n} {π : Prenex Γ 0 Empty (n + 1)} :
  bexs u π = ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) π.val_deltaZero)⟩ := by
  simp [bexs]

lemma bexs_succ_sigma {u : ArithmeticSemiterm Empty n} {π : Prenex 𝚺 (s + 1) Empty (n + 1)} :
  bexs u π = (bexs (Rew.bShift u) (π.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma := by
  rw [bexs]

lemma bexs_succ_pi {u : ArithmeticSemiterm Empty n} {π : Prenex 𝚷 (s + 1) Empty (n + 1)} :
  bexs u π = (ball u π.neg).neg := by
  rw [bexs]


mutual

def and : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s Empty n → Prenex Γ s Empty n → Prenex Γ s Empty n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ =>
      (and (bexs ‘#0 + 1’ (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
           (bexs ‘#0 + 1’ (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, φ, ψ => (or φ.neg ψ.neg).neg
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def or : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s Empty n → Prenex Γ s Empty n → Prenex Γ s Empty n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ => (or φ.sigmaInv ψ.sigmaInv).sigma
  | 𝚷, _ + 1, _, φ, ψ => (and φ.neg ψ.neg).neg
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

@[simp]
lemma and_zero {φ ψ : Prenex Γ 0 Empty n} : and φ ψ = ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  simp [and]

lemma and_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) Empty n} :
  and φ ψ = (and
    (bexs ‘#0 + 1’ (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
    (bexs ‘#0 + 1’ (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
  ).sigma := by
  rw [and]

lemma and_succ_pi {φ ψ : Prenex 𝚷 (s + 1) Empty n} : and φ ψ = (or φ.neg ψ.neg).neg := by
  rw [and]


@[simp]
lemma or_zero {φ ψ : Prenex Γ 0 Empty n} : or φ ψ = ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  simp [or]

lemma or_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) Empty n} : or φ ψ = (or φ.sigmaInv ψ.sigmaInv).sigma := by
  rw [or]

lemma or_succ_pi {φ ψ : Prenex 𝚷 (s + 1) Empty n} : or φ ψ = (and φ.neg ψ.neg).neg := by
  rw [or]

lemma models_ball_zero (u : ArithmeticSemiterm Empty n) (π : Prenex Γ 0 Empty (n + 1))
    (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val := by
  simp [ball_zero, Prenex.val, Semiformula.eval_ball];

lemma models_bexs_zero (u : ArithmeticSemiterm Empty n) (π : Prenex Γ 0 Empty (n + 1))
    (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val := by
  simp [bexs_zero, Prenex.val, Semiformula.eval_bexs];

lemma models_and_zero (π ρ : Prenex Γ 0 Empty n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val := by
  simp [and_zero, Prenex.val];

lemma models_or_zero (π ρ : Prenex Γ 0 Empty n) (V : Type*) [ORingStructure V] (e : Fin n → V) :
    V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val := by
  simp [or_zero, Prenex.val];

lemma models_bexs_succ_sigma {V : Type*} [ORingStructure V]
    (ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val)
    (u : ArithmeticSemiterm Empty n) (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val := by
  set φ₁' := π.sigmaInv;
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
  rw [bexs_succ_sigma (u := u) (π := π), val_sigma]
  show (∃ b, V ⊧/(b :> e) (bexs (Rew.bShift u) φ₂').val) ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val;
  simp only [ih (Rew.bShift u) φ₂', Semiterm.val_bShift, hswap, models_sigmaInv π V];
  grind;

lemma models_bexs_witness {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (hb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val)
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (x w : V) (e : Fin n → V) :
    V ⊧/(x :> w :> e)
        (bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val
      ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) π.sigmaInv.val := by
  rw [hb];
  have hswap : ∀ z : V,
      V ⊧/(z :> x :> w :> e) (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))).val ↔
        V ⊧/(z :> x :> e) π.sigmaInv.val := by
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

lemma models_ball_succ_sigma {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)]
    (iha : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val)
    (ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val)
    (u : ArithmeticSemiterm Empty n) (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
  rw [ball_succ_sigma (u := u) (π := π), models_sigma];
  simp only [iha (Rew.bShift u), Semiterm.val_bShift, models_bexs_witness ihb π,
    models_sigmaInv π V];
  constructor;
  . rintro ⟨w, hw⟩ x hx;
    obtain ⟨y, -, hy⟩ := hw x hx;
    exact ⟨y, hy⟩;
  . intro h;
    have hθ : Hierarchy 𝚺 (s + 1) π.sigmaInv.val := π.sigmaInv.val_hierarchy.accum 𝚺;
    exact sigma_exists_bound_witness hθ e (u.valb e) h;

lemma models_ball_succ_pi {V : Type*} [ORingStructure V]
    (h : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚺 (s + 1) Empty (m + 1))
      (e : Fin m → V), V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val)
    (u : ArithmeticSemiterm Empty n) (π : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val := by
  have hthis : V ⊧/e (bexs u π.neg).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.neg.val := h u π.neg e;
  have hval : (ball u π).val = ∼(bexs u π.neg).val := by
    rw [ball_succ_pi (u := u) (π := π)];
    exact val_neg (bexs u π.neg);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_bexs_succ_pi {V : Type*} [ORingStructure V]
    (h : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚺 (s + 1) Empty (m + 1))
      (e : Fin m → V), V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val)
    (u : ArithmeticSemiterm Empty n) (π : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val := by
  have hthis : V ⊧/e (ball u π.neg).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.neg.val := h u π.neg e;
  have hval : (bexs u π).val = ∼(ball u π.neg).val := by
    rw [bexs_succ_pi (u := u) (π := π)];
    exact val_neg (ball u π.neg);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_ball_bexs {V : Type*} [ORingStructure V] :
    ∀ (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] {Γ : Polarity} {n : ℕ}
      (u : ArithmeticSemiterm Empty n) (π : Prenex Γ s Empty (n + 1)) (e : Fin n → V),
      (V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val) ∧
      (V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val) := by
  intro s;
  induction s with
  | zero => intro _ Γ n u π e; exact ⟨models_ball_zero u π V e, models_bexs_zero u π V e⟩;
  | succ s ih =>
    intro _ Γ n u π e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have iha : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val :=
      fun u π e => (ih u π e).1;
    have ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val :=
      fun u π e => (ih u π e).2;
    have haSigma : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val :=
      fun u π e => models_ball_succ_sigma iha ihb u π e;
    have hbSigma : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (π : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val :=
      fun u π e => models_bexs_succ_sigma ihb u π e;
    rcases Γ with _ | _;
    . exact ⟨haSigma u π e, hbSigma u π e⟩;
    . exact ⟨models_ball_succ_pi hbSigma u π e, models_bexs_succ_pi haSigma u π e⟩;

lemma models_ball {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (u : ArithmeticSemiterm Empty n) (π : Prenex Γ s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (ball u π).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) π.val :=
  (models_ball_bexs s u π e).1

lemma models_bexs {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (u : ArithmeticSemiterm Empty n) (π : Prenex Γ s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (bexs u π).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) π.val :=
  (models_ball_bexs s u π e).2

lemma models_or_succ_sigma {V : Type*} [ORingStructure V]
    (ih : ∀ {m : ℕ} (π ρ : Prenex 𝚷 s Empty m) (e : Fin m → V),
      V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val)
    (π ρ : Prenex 𝚺 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val := by
  rw [or_succ_sigma (φ := π) (ψ := ρ), models_sigma];
  simp only [ih π.sigmaInv ρ.sigmaInv, models_sigmaInv π V, models_sigmaInv ρ V];
  exact exists_or;

lemma models_and_succ_sigma {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (ih : ∀ {m : ℕ} (π ρ : Prenex 𝚷 s Empty m) (e : Fin m → V),
      V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val)
    (π ρ : Prenex 𝚺 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s);
  rw [and_succ_sigma (φ := π) (ψ := ρ), models_sigma];
  set φ₂' := π.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
  set ψ₂' := ρ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
  have hα_eval : ∀ z : V, V ⊧/(z :> e) (bexs ‘#0 + 1’ φ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) π.sigmaInv.val := by
    intro z;
    rw [models_bexs ‘#0 + 1’ φ₂' (z :> e)];
    simp only [φ₂', val_rew, Semiformula.eval_insert1];
    simp [Arithmetic.lt_succ_iff_le];
  have hβ_eval : ∀ z : V, V ⊧/(z :> e) (bexs ‘#0 + 1’ ψ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) ρ.sigmaInv.val := by
    intro z;
    rw [models_bexs ‘#0 + 1’ ψ₂' (z :> e)];
    simp only [ψ₂', val_rew, Semiformula.eval_insert1];
    simp [Arithmetic.lt_succ_iff_le];
  simp only [ih (bexs ‘#0 + 1’ φ₂') (bexs ‘#0 + 1’ ψ₂'), models_sigmaInv π V, models_sigmaInv ρ V,
    hα_eval, hβ_eval];
  constructor;
  . rintro ⟨z, ⟨x, -, hx⟩, ⟨y, -, hy⟩⟩;
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
  . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
    exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;

lemma models_and_succ_pi {V : Type*} [ORingStructure V]
    (h : ∀ {m : ℕ} (π ρ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
      V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val)
    (π ρ : Prenex 𝚷 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val := by
  have hthis : V ⊧/e (or π.neg ρ.neg).val ↔ V ⊧/e π.neg.val ∨ V ⊧/e ρ.neg.val := h π.neg ρ.neg e;
  have hval : (and π ρ).val = ∼(or π.neg ρ.neg).val := by
    rw [and_succ_pi (φ := π) (ψ := ρ)];
    exact val_neg (or π.neg ρ.neg);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_or_succ_pi {V : Type*} [ORingStructure V]
    (h : ∀ {m : ℕ} (π ρ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
      V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val)
    (π ρ : Prenex 𝚷 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val := by
  have hthis : V ⊧/e (and π.neg ρ.neg).val ↔ V ⊧/e π.neg.val ∧ V ⊧/e ρ.neg.val := h π.neg ρ.neg e;
  have hval : (or π ρ).val = ∼(and π.neg ρ.neg).val := by
    rw [or_succ_pi (φ := π) (ψ := ρ)];
    exact val_neg (and π.neg ρ.neg);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

lemma models_and_or {V : Type*} [ORingStructure V] :
    ∀ (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] {Γ : Polarity} {n : ℕ}
      (π ρ : Prenex Γ s Empty n) (e : Fin n → V),
      (V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val) ∧
      (V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val) := by
  intro s;
  induction s with
  | zero => intro _ Γ n π ρ e; exact ⟨models_and_zero π ρ V e, models_or_zero π ρ V e⟩;
  | succ s ih =>
    intro _ Γ n π ρ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have iha : ∀ {m : ℕ} (π ρ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val :=
      fun π ρ e => (ih π ρ e).1;
    have iho : ∀ {m : ℕ} (π ρ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val :=
      fun π ρ e => (ih π ρ e).2;
    have haSigma : ∀ {m : ℕ} (π ρ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val :=
      fun π ρ e => models_and_succ_sigma iha π ρ e;
    have hoSigma : ∀ {m : ℕ} (π ρ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val :=
      fun π ρ e => models_or_succ_sigma iho π ρ e;
    rcases Γ with _ | _;
    . exact ⟨haSigma π ρ e, hoSigma π ρ e⟩;
    . exact ⟨models_and_succ_pi hoSigma π ρ e, models_or_succ_pi haSigma π ρ e⟩;

lemma models_and {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (π ρ : Prenex Γ s Empty n) (e : Fin n → V) :
    V ⊧/e (and π ρ).val ↔ V ⊧/e π.val ∧ V ⊧/e ρ.val :=
  (models_and_or s π ρ e).1

lemma models_or {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (π ρ : Prenex Γ s Empty n) (e : Fin n → V) :
    V ⊧/e (or π ρ).val ↔ V ⊧/e π.val ∨ V ⊧/e ρ.val :=
  (models_and_or s π ρ e).2

def exs (π : Prenex 𝚺 (s + 1) Empty (n + 1)) : Prenex 𝚺 (s + 1) Empty n :=
  (bexs ‘#0 + 1’ (bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma

def all (π : Prenex 𝚷 (s + 1) Empty (n + 1)) : Prenex 𝚷 (s + 1) Empty n := (exs π.neg).neg

lemma models_exs {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (π : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (exs π).val ↔ ∃ x, V ⊧/(x :> e) π.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s);
  show V ⊧/e
      (bexs ‘#0 + 1’ (bexs ‘#1 + 1’
        (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma.val ↔
    ∃ x, V ⊧/(x :> e) π.val;
  rw [models_sigma];
  have hβeval : ∀ z : V,
      V ⊧/(z :> e)
        (bexs ‘#0 + 1’ (bexs ‘#1 + 1’
          (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).val ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e)
          (bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val := by
    intro z;
    rw [models_bexs];
    have hval : (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)).valb (z :> e) = z + 1 := by simp;
    rw [hval];
    simp only [Arithmetic.lt_succ_iff_le];
  have hαeval : ∀ y z : V,
      V ⊧/(y :> z :> e)
        (bexs ‘#1 + 1’ (π.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) π.sigmaInv.val :=
    fun y z => models_bexs_witness models_bexs π y z e;
  simp only [hβeval, hαeval, models_sigmaInv π V];
  constructor;
  . rintro ⟨z, y, -, x, -, hx⟩;
    exact ⟨y, x, hx⟩;
  . rintro ⟨y, x, hx⟩;
    exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;

lemma models_all {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (π : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (all π).val ↔ ∀ x, V ⊧/(x :> e) π.val := by
  have hthis : V ⊧/e (exs π.neg).val ↔ ∃ x, V ⊧/(x :> e) π.neg.val := models_exs π.neg e;
  have hval : (all π).val = ∼(exs π.neg).val := by
    unfold all;
    exact val_neg (exs π.neg);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;

theorem models_exists_prenex {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ π : Prenex Γ s Empty n,
      ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] (e : Fin n → V),
        V ⊧/e φ ↔ V ⊧/e π.val := by
  induction h with
  | verum Γ s n =>
    use verum;
    intro V _ _ e;
    unfold verum;
    exact (models_ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) V e).symm;
  | falsum Γ s n =>
    use falsum;
    intro V _ _ e;
    unfold falsum;
    exact (models_ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) V e).symm;
  | rel Γ s r v =>
    use rel r v;
    intro V _ _ e;
    unfold rel;
    exact (models_ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) V e).symm;
  | nrel Γ s r v =>
    use nrel r v;
    intro V _ _ e;
    unfold nrel;
    exact (models_ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) V e).symm;
  | and _ _ ihφ ihψ =>
    obtain ⟨π, hπ⟩ := ihφ;
    obtain ⟨ρ, hρ⟩ := ihψ;
    use and π ρ;
    intro V _ _ e;
    rw [models_and π ρ e];
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq];
    exact and_congr (hπ V e) (hρ V e);
  | or _ _ ihφ ihψ =>
    obtain ⟨π, hπ⟩ := ihφ;
    obtain ⟨ρ, hρ⟩ := ihψ;
    use or π ρ;
    intro V _ _ e;
    rw [models_or π ρ e];
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq];
    exact or_congr (hπ V e) (hρ V e);
  | ball pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨π, hπ⟩ := ih;
    use ball u π;
    intro V _ _ e;
    rw [models_ball u π e];
    simp only [Semiformula.eval_ball];
    exact forall_congr' fun x => (imp_congr Iff.rfl (hπ V (x :> e))).trans (by simp);
  | bexs pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨π, hπ⟩ := ih;
    use bexs u π;
    intro V _ _ e;
    rw [models_bexs u π e];
    simp only [Semiformula.eval_bexs];
    exact exists_congr fun x => (and_congr Iff.rfl (hπ V (x :> e))).trans (by simp);
  | @exs s n φ _ ih =>
    obtain ⟨π, hπ⟩ := ih;
    use exs π;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_exs π e, Semiformula.eval_ex];
    exact exists_congr fun x => hπ V (x :> e);
  | @all s n φ _ ih =>
    obtain ⟨π, hπ⟩ := ih;
    use all π;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_all π e, Semiformula.eval_all];
    exact forall_congr' fun x => hπ V (x :> e);
  | @sigma s n φ _ ih =>
    obtain ⟨π, hπ⟩ := ih;
    use π.sigma;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_sigma π V e, Semiformula.eval_ex];
    exact exists_congr fun x => hπ V (x :> e);
  | @pi s n φ _ ih =>
    obtain ⟨π, hπ⟩ := ih;
    use π.pi;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_pi π V e, Semiformula.eval_all];
    exact forall_congr' fun x => hπ V (x :> e);
  | @dummy_sigma s n φ _ ih =>
    obtain ⟨π, hπ⟩ := ih;
    use π.all.altUp;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1 + 1) (by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := mod_ISigma_of_le (n₂ := s + 1 + 1) (by omega);
    exact Semiformula.eval_all.trans
      ((forall_congr' fun x => hπ V (x :> e)).trans
        ((models_all π e).symm.trans (models_altUp π.all V e).symm));
  | @dummy_pi s n φ _ ih =>
    obtain ⟨π, hπ⟩ := ih;
    use π.exs.altUp;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1 + 1) (by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := mod_ISigma_of_le (n₂ := s + 1 + 1) (by omega);
    exact Semiformula.eval_ex.trans
      ((exists_congr fun x => hπ V (x :> e)).trans
        ((models_exs π e).symm.trans (models_altUp π.exs V e).symm));

end Prenex

variable (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n}

theorem exists_prenex_of_hierarchy (h : Hierarchy Γ s φ) [𝗜𝚺 s ⪯ T] :
    ∃ π : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 π.val) := by
  obtain ⟨π, hπ⟩ := Prenex.models_exists_prenex h;
  use π;
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := models_of_subtheory (T := 𝗜𝚺 s) (U := T) inferInstance;
  exact hπ V e;

variable (T : ArithmeticTheory) {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} [𝗜𝚺 s ⪯ T]

theorem exists_matrix_provable (h : Hierarchy Γ s φ) :
  ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) (ISigma_weakerThan_of_le_trans (by omega) ‹𝗜𝚺 s ⪯ T›);
  obtain ⟨_, hπ⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨_, by simpa [Prenex.val] using hπ⟩;

end Arithmetic

end LO.FirstOrder
