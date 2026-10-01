module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-!
# Prenex arithmetical hierarchy

`Prenex Γ s ξ n` is a `Δ₀` matrix beneath `s` alternating quantifiers, the outermost being `Γ`,
and `PrenexHierarchy Γ s φ` says that `φ` is syntactically of this form.

## References

- [HP98]
-/

@[expose] public section

open FFL

namespace FFL.FirstOrder

namespace Arithmetic

/-- A formula in `Γ`-prenex form of level `s`, stored as the bounded matrix that remains after
stripping the `s` leading alternating quantifiers. -/
structure Prenex (Γ : Polarity) (s : ℕ) (ξ : Type*) (n : ℕ) where
  matrix : ℬ[<, ℒₒᵣ].Semiformula ξ (n + s)

namespace Prenex

variable {Γ : Polarity} {s : ℕ} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}
variable {V : Type*} [ORingStructure V]

@[coe]
def val (φ : Prenex Γ s ξ n) : ArithmeticSemiformula ξ n := φ.matrix.val.toPrenex Γ s

instance : CoeTC (Prenex Γ s ξ n) (ArithmeticSemiformula ξ n) := ⟨val⟩

def neg (φ : Prenex Γ s ξ n) : Prenex Γ.alt s ξ n := ⟨⟨∼φ.matrix.val, φ.matrix.bounded.neg⟩⟩

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

def ofΔ₀ (φ : ℬ[<, ℒₒᵣ].Semiformula ξ n) : (Γ : Polarity) → (s : ℕ) → Prenex Γ s ξ n
  | Γ, 0     => ⟨φ⟩
  | Γ, s + 1 => by simpa using altUp (ofΔ₀ φ Γ.alt s)

def verum : Prenex Γ s ξ n := ofΔ₀ ⟨⊤, .verum n⟩ Γ s

def falsum : Prenex Γ s ξ n := ofΔ₀ ⟨⊥, .falsum n⟩ Γ s

def rel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ ⟨.rel r v, .rel r v⟩ Γ s

def nrel {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ ⟨.nrel r v, .nrel r v⟩ Γ s

def succ : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s ξ n → Prenex Γ (s + 1) ξ n
  | Γ, 0,     _, φ => ofΔ₀ φ.matrix Γ 1
  | 𝚺, _ + 1, _, φ => φ.sigmaInv.succ.sigma
  | 𝚷, _ + 1, _, φ => φ.piInv.succ.pi

@[simp, grind .]
lemma val_hierarchy {φ : Prenex Γ s ξ n} : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ.val := by
  simpa [val] using Bounding.Hierarchy.toPrenex (Γ := Γ) (j := 0) φ.matrix.hierarchy;

@[simp, grind .]
lemma val_deltaZero {φ : Prenex Γ 0 ξ n} : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ.val := φ.matrix.hierarchy

@[simp, grind .]
lemma val_neg (φ : Prenex Γ s ξ n) : (∼φ).val = ∼φ.val :=
  (Semiformula.neg_toPrenex ..).symm

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
  unfold val sigmaInv;
  rw [Bounding.Semiformula.val_rew, ← Polarity.quant_sigma, ← Polarity.alt_sigma,
    ← Rewriting.quantItr_succ_smul_castLE, ← TransitiveRewriting.comp_app];
  simp;

@[simp, grind .]
lemma val_piInv {φ : Prenex 𝚷 (s + 1) ξ n} : φ.val = ∀¹ φ.piInv.val := by
  unfold val piInv;
  rw [Bounding.Semiformula.val_rew, ← Polarity.quant_pi, ← Polarity.alt_pi,
    ← Rewriting.quantItr_succ_smul_castLE, ← TransitiveRewriting.comp_app];
  simp;

variable {f : ξ → V}

lemma models_sigmaInv (φ : Prenex 𝚺 (s + 1) ξ n) (e : Fin n → V) :
    Semiformula.Eval e f φ.val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.sigmaInv.val := by
  rw [val_sigmaInv, Semiformula.eval_ex];

lemma models_piInv (φ : Prenex 𝚷 (s + 1) ξ n) (e : Fin n → V) :
    Semiformula.Eval e f φ.val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.piInv.val := by
  rw [val_piInv, Semiformula.eval_all];

lemma models_sigma (φ : Prenex 𝚷 s ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f φ.sigma.val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [val_sigma, Semiformula.eval_ex];

lemma models_pi (φ : Prenex 𝚺 s ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f φ.pi.val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [val_pi, Semiformula.eval_all];

lemma models_altUp (φ : Prenex Γ s ξ n) (e : Fin n → V) :
    Semiformula.Eval e f φ.altUp.val ↔ Semiformula.Eval e f φ.val := by
  rcases Γ <;> simp [altUp, -val_piInv, -val_sigmaInv];

lemma models_ofΔ₀ (φ : ℬ[<, ℒₒᵣ].Semiformula ξ n) (e : Fin n → V) :
    Semiformula.Eval e f (ofΔ₀ φ Γ s).val ↔ Semiformula.Eval e f φ.val := by
  induction s generalizing Γ with
  | zero => rfl
  | succ s ih =>
    rcases Γ with _ | _;
    · exact (models_altUp (ofΔ₀ φ 𝚷 s) e).trans ih;
    · exact (models_altUp (ofΔ₀ φ 𝚺 s) e).trans ih;

lemma models_verum (e : Fin n → V) :
    Semiformula.Eval e f (verum : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (⊤ : ArithmeticSemiformula ξ n) :=
  models_ofΔ₀ ⟨⊤, .verum n⟩ e

lemma models_falsum (e : Fin n → V) :
    Semiformula.Eval e f (falsum : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (⊥ : ArithmeticSemiformula ξ n) :=
  models_ofΔ₀ ⟨⊥, .falsum n⟩ e

lemma models_rel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n)
    (e : Fin n → V) :
    Semiformula.Eval e f (rel r v : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (Semiformula.rel r v) :=
  models_ofΔ₀ ⟨.rel r v, .rel r v⟩ e

lemma models_nrel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n)
    (e : Fin n → V) :
    Semiformula.Eval e f (nrel r v : Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (Semiformula.nrel r v) :=
  models_ofΔ₀ ⟨.nrel r v, .nrel r v⟩ e

lemma models_succ (φ : Prenex Γ s ξ n) (e : Fin n → V) :
    Semiformula.Eval e f φ.succ.val ↔ Semiformula.Eval e f φ.val := by
  induction s generalizing Γ n with
  | zero => exact models_ofΔ₀ φ.matrix e;
  | succ s ih =>
    rcases Γ with _ | _;
    · simp only [succ, models_sigma, ih, models_sigmaInv φ];
    · simp only [succ, models_pi, ih, models_piInv φ];

lemma provable_iff_sigmaInv {T : ArithmeticTheory} {φ : ArithmeticSemiformula Empty n}
    {φ' : Prenex 𝚺 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
    T ⊢ ∀¹* (φ 🡘 ∃¹ φ'.sigmaInv.val) := φ'.val_sigmaInv ▸ hφ'

lemma provable_iff_piInv {T : ArithmeticTheory} {φ : ArithmeticSemiformula Empty n}
    {φ' : Prenex 𝚷 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
    T ⊢ ∀¹* (φ 🡘 ∀¹ φ'.piInv.val) := φ'.val_piInv ▸ hφ'

end Prenex

/-- `φ` is syntactically a `Δ₀` matrix beneath `s` alternating quantifiers, the outermost `Γ`. -/
def PrenexHierarchy (Γ : Polarity) (s : ℕ) {ξ : Type*} {n : ℕ}
    (φ : ArithmeticSemiformula ξ n) : Prop :=
  ∃ ψ : Prenex Γ s ξ n, φ = ψ.val

@[simp, grind .]
lemma Prenex.val_prenexHierarchy {Γ : Polarity} {s n : ℕ} {ξ : Type*} {φ : Prenex Γ s ξ n} :
    PrenexHierarchy Γ s φ.val := ⟨φ, rfl⟩

namespace PrenexHierarchy

variable {Γ : Polarity} {s n n₁ n₂ : ℕ} {ξ ξ₁ ξ₂ : Type*}

section

variable {φ : ArithmeticSemiformula ξ n}

lemma zero_iff_bounded : PrenexHierarchy Γ 0 φ ↔ ℬ[<, ℒₒᵣ].Closure φ := by
  constructor;
  · rintro ⟨ψ, rfl⟩;
    exact ψ.matrix.bounded;
  · exact fun h ↦ ⟨⟨⟨φ, h⟩⟩, rfl⟩;

lemma zero_iff : PrenexHierarchy Γ 0 φ ↔ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ :=
  zero_iff_bounded.trans Bounding.Hierarchy.zero_iff_bounded.symm

lemma sigma_succ_iff : PrenexHierarchy 𝚺 (s + 1) φ ↔ ∃ ψ, PrenexHierarchy 𝚷 s ψ ∧ φ = ∃¹ ψ := by
  constructor;
  · rintro ⟨χ, rfl⟩;
    exact ⟨_, χ.sigmaInv.val_prenexHierarchy, χ.val_sigmaInv⟩;
  · rintro ⟨_, ⟨χ, rfl⟩, rfl⟩;
    exact ⟨χ.sigma, χ.val_sigma.symm⟩;

lemma pi_succ_iff : PrenexHierarchy 𝚷 (s + 1) φ ↔ ∃ ψ, PrenexHierarchy 𝚺 s ψ ∧ φ = ∀¹ ψ := by
  constructor;
  · rintro ⟨χ, rfl⟩;
    exact ⟨_, χ.piInv.val_prenexHierarchy, χ.val_piInv⟩;
  · rintro ⟨_, ⟨χ, rfl⟩, rfl⟩;
    exact ⟨χ.pi, χ.val_pi.symm⟩;

lemma hierarchy (h : PrenexHierarchy Γ s φ) : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ := by
  obtain ⟨ψ, rfl⟩ := h;
  exact ψ.val_hierarchy;

lemma neg (h : PrenexHierarchy Γ s φ) : PrenexHierarchy Γ.alt s (∼φ) := by
  obtain ⟨ψ, rfl⟩ := h;
  exact ⟨∼ψ, (Prenex.val_neg ψ).symm⟩;

@[simp] lemma neg_iff : PrenexHierarchy Γ s (∼φ) ↔ PrenexHierarchy Γ.alt s φ :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ by simpa using h.neg⟩

end

lemma exs {φ : ArithmeticSemiformula ξ (n + 1)} (h : PrenexHierarchy 𝚷 s φ) :
    PrenexHierarchy 𝚺 (s + 1) (∃¹ φ) := sigma_succ_iff.mpr ⟨φ, h, rfl⟩

lemma all {φ : ArithmeticSemiformula ξ (n + 1)} (h : PrenexHierarchy 𝚺 s φ) :
    PrenexHierarchy 𝚷 (s + 1) (∀¹ φ) := pi_succ_iff.mpr ⟨φ, h, rfl⟩

section

variable {φ : ArithmeticSemiformula ξ₁ n₁}

lemma rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) (h : PrenexHierarchy Γ s φ) :
    PrenexHierarchy Γ s (ω ▹ φ) := by
  obtain ⟨ψ, rfl⟩ := h;
  exact ⟨ψ.rew ω, (ψ.val_rew ω).symm⟩;

lemma of_rew {ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂} (h : PrenexHierarchy Γ s (ω ▹ φ)) :
    PrenexHierarchy Γ s φ := by
  induction s generalizing Γ n₁ n₂ with
  | zero => exact zero_iff_bounded.mpr (Bounding.Closure.rew_iff.mp (zero_iff_bounded.mp h));
  | succ s ih =>
    rcases Γ with _ | _;
    · obtain ⟨ψ, hψ, e⟩ := sigma_succ_iff.mp h;
      obtain ⟨φ', rfl, rfl⟩ := (Semiformula.eq_exs_iff _).mp e;
      exact (ih hψ).exs;
    · obtain ⟨ψ, hψ, e⟩ := pi_succ_iff.mp h;
      obtain ⟨φ', rfl, rfl⟩ := (Semiformula.eq_all_iff _).mp e;
      exact (ih hψ).all;

@[simp] lemma rew_iff {ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂} :
    PrenexHierarchy Γ s (ω ▹ φ) ↔ PrenexHierarchy Γ s φ := ⟨of_rew, rew ω⟩

end

section

variable {φ : ArithmeticSemiformula ξ n}

lemma exists_eval_iff_of_le (h : PrenexHierarchy Γ s φ) {s' : ℕ} (hs : s ≤ s') :
    ∃ ψ, PrenexHierarchy Γ s' ψ ∧
      ∀ (V : Type*) [ORingStructure V] (e : Fin n → V) (f : ξ → V),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ := by
  induction s', hs using Nat.le_induction with
  | base => exact ⟨φ, h, fun _ _ _ _ ↦ Iff.rfl⟩;
  | succ s' _ ih =>
    obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := ih;
    exact ⟨χ.succ.val, χ.succ.val_prenexHierarchy,
      fun V _ e f ↦ (hχ V e f).trans (χ.models_succ e).symm⟩;

lemma exists_eval_iff_of_lt (h : PrenexHierarchy Γ s φ) (Γ' : Polarity) {s' : ℕ} (hs : s < s') :
    ∃ ψ, PrenexHierarchy Γ' s' ψ ∧
      ∀ (V : Type*) [ORingStructure V] (e : Fin n → V) (f : ξ → V),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ := by
  obtain rfl | rfl : Γ' = Γ ∨ Γ' = Γ.alt := by rcases Γ <;> rcases Γ' <;> simp;
  · exact h.exists_eval_iff_of_le hs.le;
  obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩;
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := h.exists_eval_iff_of_le (Nat.le_of_lt_succ hs);
  exact ⟨χ.altUp.val, χ.altUp.val_prenexHierarchy,
    fun V _ e f ↦ (hχ V e f).trans (χ.models_altUp e).symm⟩;

lemma exists_eval_iff_of_deltaZero (h : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (Γ : Polarity) (s : ℕ) :
    ∃ ψ, PrenexHierarchy Γ s ψ ∧
      ∀ (V : Type*) [ORingStructure V] (e : Fin n → V) (f : ξ → V),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ := by
  have hφ : ℬ[<, ℒₒᵣ].Closure φ := Bounding.Hierarchy.zero_iff_bounded.mp h;
  exact ⟨_, (Prenex.ofΔ₀ ⟨φ, hφ⟩ Γ s).val_prenexHierarchy,
    fun _ _ e _ ↦ (Prenex.models_ofΔ₀ ⟨φ, hφ⟩ e).symm⟩;

end

end PrenexHierarchy

end Arithmetic

end FFL.FirstOrder
