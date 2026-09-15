module

public import Foundation.FirstOrder.Arithmetic.R0.Basic

/-!
# Independence of `Ω₁`, `Ω₂`, `Ω₃`, `Ω₄` and `Ω₅` in $\mathsf{R_0}$
-/

@[expose] public section

noncomputable section

namespace FFL.FirstOrder.Arithmetic.R0

namespace Countermodel

private lemma numeral_eq_of_succ {M : Type*} [ORingStructure M] {f : ℕ → M}
    (h0 : f 0 = 0) (h1 : f 1 = 1) (hs : ∀ n, f (n + 1) = f n + 1) :
    ∀ n, (ORingStructure.numeral n : M) = f n
  |     0 => h0.symm
  |     1 => h1.symm
  | n + 2 => by
      show (ORingStructure.numeral (n + 1) : M) + 1 = f (n + 2);
      rw [numeral_eq_of_succ h0 h1 hs (n + 1)];
      exact (hs (n + 1)).symm;

private lemma eq_or_lt_iff_eq_or_exists_lt {x n : ℕ} : x = n ∨ x < n ↔ x = n ∨ ∃ i < n, x = i := by
  constructor;
  . rintro (rfl | hx);
    . left; rfl;
    . right; exact ⟨x, hx, rfl⟩;
  . rintro (rfl | ⟨i, hi, rfl⟩);
    . left; rfl;
    . right; exact hi;

private lemma eq_or_le_iff_eq_or_exists_lt {x n : ℕ} : x = n ∨ x ≤ n ↔ x = n ∨ ∃ i < n, x = i := by
  constructor;
  . rintro (rfl | hx);
    . left; rfl;
    . rcases eq_or_lt_of_le hx with rfl | hlt;
      . left; rfl;
      . right; exact ⟨x, hlt, rfl⟩;
  . rintro (rfl | ⟨i, hi, rfl⟩);
    . left; rfl;
    . right; exact hi.le;

end Countermodel

def Ω₁Scheme : ArithmeticTheory := {σ | ∃ n m : ℕ, σ = “↑n + ↑m = ↑(n + m)”}

namespace Countermodel

def NatSucc := ℕ

instance : ORingStructure NatSucc where
  zero := (0 : ℕ)
  one := (1 : ℕ)
  add a _b := Nat.add a 1
  mul a b := Nat.mul a b
  lt a b := Nat.lt a b

namespace NatSucc

@[simp] private lemma numeral_eq (n : ℕ) : (ORingStructure.numeral n : NatSucc) = n :=
  numeral_eq_of_succ (M := NatSucc) (f := fun k : ℕ => (k : NatSucc)) rfl rfl (fun _ => rfl) n

end NatSucc

instance : NatSucc↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₁Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | ⟨n, m, h⟩ | n | n;
  . have : NatSucc↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  . exact absurd ⟨n, m, rfl⟩ hn;
  . suffices (ORingStructure.numeral n : NatSucc) * ORingStructure.numeral m
      = ORingStructure.numeral (n * m) by simpa [models_iff];
    simp only [NatSucc.numeral_eq];
    rfl;
  . suffices (n : NatSucc) ≠ (m : NatSucc) by simpa [models_iff];
    exact h;
  . suffices ∀ x : NatSucc, (x = n ∨ x < n) ↔ (x = n ∨ ∃ i < n, x = i) by
      simpa [models_iff, Structure.le_iff_of_eq_of_lt, -existsAndEq];
    intro x;
    exact eq_or_lt_iff_eq_or_exists_lt;
  . suffices ∀ x : NatSucc, ¬ x < x by simpa [models_iff] using this n;
    intro x;
    exact Nat.lt_irrefl x;⟩

end Countermodel

theorem Ω₁_independent : 𝗥₀ \ Ω₁Scheme ⊬ “↑0 + ↑0 = ↑0” :=
  unprovable_of_countermodel _ (M := Countermodel.NatSucc) <| by
    simp [notModels_iff];

def Ω₂Scheme : ArithmeticTheory := {σ | ∃ n m : ℕ, σ = “↑n * ↑m = ↑(n * m)”}

namespace Countermodel

def NatZeroMul := ℕ

instance : ORingStructure NatZeroMul where
  zero := (0 : ℕ)
  one := (1 : ℕ)
  add a b := Nat.add a b
  mul _ _ := (0 : ℕ)
  lt a b := Nat.lt a b

namespace NatZeroMul

@[simp] private lemma numeral_eq (n : ℕ) : (ORingStructure.numeral n : NatZeroMul) = n :=
  numeral_eq_of_succ (M := NatZeroMul) (f := fun k : ℕ => (k : NatZeroMul)) rfl rfl (fun _ => rfl) n

end NatZeroMul

instance : NatZeroMul↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₂Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | ⟨n, m, h⟩ | n | n;
  . have : NatZeroMul↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  . suffices (ORingStructure.numeral n : NatZeroMul) + ORingStructure.numeral m
      = ORingStructure.numeral (n + m) by simpa [models_iff];
    simp only [NatZeroMul.numeral_eq];
    rfl;
  . exact absurd ⟨n, m, rfl⟩ hn;
  . suffices (n : NatZeroMul) ≠ (m : NatZeroMul) by simpa [models_iff];
    exact h;
  . suffices ∀ x : NatZeroMul, (x = n ∨ x < n) ↔ (x = n ∨ ∃ i < n, x = i) by
      simpa [models_iff, Structure.le_iff_of_eq_of_lt, -existsAndEq];
    intro x;
    exact eq_or_lt_iff_eq_or_exists_lt;
  . suffices ∀ x : NatZeroMul, ¬ x < x by simpa [models_iff] using this n;
    intro x;
    exact Nat.lt_irrefl x;⟩

end Countermodel

theorem Ω₂_independent : 𝗥₀ \ Ω₂Scheme ⊬ “↑1 * ↑1 = ↑1” :=
  unprovable_of_countermodel _ (M := Countermodel.NatZeroMul) <| by
    simp [notModels_iff];

def Ω₃Scheme : ArithmeticTheory := {σ | ∃ n m : ℕ, n ≠ m ∧ σ = “↑n ≠ ↑m”}

namespace Countermodel

def Trivial := Unit

instance : ORingStructure Trivial where
  zero := ()
  one := ()
  add _ _ := ()
  mul _ _ := ()
  lt _ _ := False

instance : Subsingleton Trivial := ⟨fun _ _ ↦ rfl⟩

namespace Trivial

@[simp] private lemma eq_iff (a b : Trivial) : a = b ↔ True := eq_iff_true_of_subsingleton a b

@[simp] private lemma not_lt (a b : Trivial) : ¬ a < b := id

end Trivial

instance : Trivial↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₃Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h;
  case equal h =>
    have : Trivial↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    exact models_theory_iff.mp this _ h;
  case Ω₃ n m h => exact absurd ⟨n, m, h, rfl⟩ hn;
  all_goals simp [models_iff, Structure.le_iff_of_eq_of_lt];⟩

end Countermodel

theorem Ω₃_independent : 𝗥₀ \ Ω₃Scheme ⊬ “↑0 ≠ ↑1” :=
  unprovable_of_countermodel _ (M := Countermodel.Trivial) <| by
    simp [notModels_iff];

def Ω₄Scheme : ArithmeticTheory := {σ | ∃ n : ℕ, σ = “∀ x, x ≤ ↑n ↔ ⋁ i < n + 1, x = ↑i”}

namespace Countermodel

def NatNoLt := ℕ

instance : ORingStructure NatNoLt where
  zero := (0 : ℕ)
  one := (1 : ℕ)
  add a b := Nat.add a b
  mul a b := Nat.mul a b
  lt _ _ := False

namespace NatNoLt

@[simp] private lemma numeral_eq (n : ℕ) : (ORingStructure.numeral n : NatNoLt) = n :=
  numeral_eq_of_succ (M := NatNoLt) (f := fun k : ℕ => (k : NatNoLt)) rfl rfl (fun _ => rfl) n

@[simp] private lemma not_lt (a b : NatNoLt) : ¬ a < b := id

end NatNoLt

instance : NatNoLt↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₄Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | ⟨n, m, h⟩ | n | n;
  . have : NatNoLt↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  . suffices (ORingStructure.numeral n : NatNoLt) + ORingStructure.numeral m
      = ORingStructure.numeral (n + m) by simpa [models_iff];
    simp only [NatNoLt.numeral_eq];
    rfl;
  . suffices (ORingStructure.numeral n : NatNoLt) * ORingStructure.numeral m
      = ORingStructure.numeral (n * m) by simpa [models_iff];
    simp only [NatNoLt.numeral_eq];
    rfl;
  . suffices (n : NatNoLt) ≠ (m : NatNoLt) by simpa [models_iff];
    exact h;
  . exact absurd ⟨n, rfl⟩ hn;
  . suffices ∀ x : NatNoLt, ¬ x < x by simpa [models_iff] using this n;
    intro x;
    exact NatNoLt.not_lt x x;⟩

end Countermodel

theorem Ω₄_independent : 𝗥₀ \ Ω₄Scheme ⊬ “∀ x, x ≤ ↑1 ↔ ⋁ i < 2, x = ↑i” :=
  unprovable_of_countermodel _ (M := Countermodel.NatNoLt) <| by
    simp [notModels_iff, Structure.le_iff_of_eq_of_lt];

def Ω₅Scheme : ArithmeticTheory := {σ | ∃ n : ℕ, σ = “¬ ↑n < ↑n”}

namespace Countermodel

def NatLE := ℕ

instance : ORingStructure NatLE where
  zero := (0 : ℕ)
  one := (1 : ℕ)
  add a b := Nat.add a b
  mul a b := Nat.mul a b
  lt a b := Nat.le a b

namespace NatLE

private def toNat (x : NatLE) : ℕ := x

@[simp] private lemma numeral_eq (n : ℕ) : (ORingStructure.numeral n : NatLE) = n :=
  numeral_eq_of_succ (M := NatLE) (f := fun k : ℕ => (k : NatLE)) rfl rfl (fun _ => rfl) n

@[simp] private lemma lt_iff {a b : NatLE} : a < b ↔ a.toNat ≤ b.toNat := Iff.rfl

end NatLE

instance : NatLE↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₅Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | ⟨n, m, h⟩ | n | n;
  . have : NatLE↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  . suffices (ORingStructure.numeral n : NatLE) + ORingStructure.numeral m
      = ORingStructure.numeral (n + m) by simpa [models_iff];
    simp only [NatLE.numeral_eq];
    rfl;
  . suffices (ORingStructure.numeral n : NatLE) * ORingStructure.numeral m
      = ORingStructure.numeral (n * m) by simpa [models_iff];
    simp only [NatLE.numeral_eq];
    rfl;
  . suffices (n : NatLE) ≠ (m : NatLE) by simpa [models_iff];
    exact h;
  . suffices ∀ x : NatLE, (x = n ∨ x < n) ↔ (x = n ∨ ∃ i < n, x = i) by
      simpa [models_iff, Structure.le_iff_of_eq_of_lt, -existsAndEq];
    intro x;
    exact eq_or_le_iff_eq_or_exists_lt;
  . exact absurd ⟨n, rfl⟩ hn;⟩

end Countermodel

theorem Ω₅_independent : 𝗥₀ \ Ω₅Scheme ⊬ “¬ ↑0 < ↑0” :=
  unprovable_of_countermodel _ (M := Countermodel.NatLE) <| by
    simp [notModels_iff, Countermodel.NatLE.lt_iff];

end FFL.FirstOrder.Arithmetic.R0

end
