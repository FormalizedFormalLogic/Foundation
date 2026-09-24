module

public import Foundation.FirstOrder.Arithmetic.R0.Basic

/-!
# Independence of `Ω₁`, `Ω₂` and `Ω₃` in $\mathsf{R_0}$
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
      change (ORingStructure.numeral (n + 1) : M) + 1 = f (n + 2);
      rw [numeral_eq_of_succ h0 h1 hs (n + 1)];
      exact (hs (n + 1)).symm;

private lemma lt_iff_exists_lt {x n : ℕ} : x < n ↔ ∃ i < n, x = i := by
  constructor;
  · intro hx; exact ⟨x, hx, rfl⟩;
  · rintro ⟨i, hi, rfl⟩; exact hi;

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
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | n;
  · have : NatSucc↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  · exact absurd ⟨n, m, rfl⟩ hn;
  · suffices (ORingStructure.numeral n : NatSucc) * ORingStructure.numeral m
      = ORingStructure.numeral (n * m) by simpa [models_iff];
    simp only [NatSucc.numeral_eq];
    rfl;
  · suffices ∀ x : NatSucc, x < (n : NatSucc) ↔ ∃ i < n, x = (i : NatSucc) by
      simpa [models_iff, -existsAndEq];
    intro x;
    exact lt_iff_exists_lt;⟩

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
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | n;
  · have : NatZeroMul↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  · suffices (ORingStructure.numeral n : NatZeroMul) + ORingStructure.numeral m
      = ORingStructure.numeral (n + m) by simpa [models_iff];
    simp only [NatZeroMul.numeral_eq];
    rfl;
  · exact absurd ⟨n, m, rfl⟩ hn;
  · suffices ∀ x : NatZeroMul, x < (n : NatZeroMul) ↔ ∃ i < n, x = (i : NatZeroMul) by
      simpa [models_iff, -existsAndEq];
    intro x;
    exact lt_iff_exists_lt;⟩

end Countermodel

theorem Ω₂_independent : 𝗥₀ \ Ω₂Scheme ⊬ “↑1 * ↑1 = ↑1” :=
  unprovable_of_countermodel _ (M := Countermodel.NatZeroMul) <| by
    simp [notModels_iff];

def Ω₃Scheme : ArithmeticTheory := {σ | ∃ n : ℕ, σ = “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”}

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

instance : NatNoLt↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₃Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | n;
  · have : NatNoLt↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  · suffices (ORingStructure.numeral n : NatNoLt) + ORingStructure.numeral m
      = ORingStructure.numeral (n + m) by simpa [models_iff];
    simp only [NatNoLt.numeral_eq];
    rfl;
  · suffices (ORingStructure.numeral n : NatNoLt) * ORingStructure.numeral m
      = ORingStructure.numeral (n * m) by simpa [models_iff];
    simp only [NatNoLt.numeral_eq];
    rfl;
  · exact absurd ⟨n, rfl⟩ hn;⟩

end Countermodel

theorem Ω₃_independent : 𝗥₀ \ Ω₃Scheme ⊬ “∀ x, x < ↑1 ↔ ⋁ i < 1, x = ↑i” :=
  unprovable_of_countermodel _ (M := Countermodel.NatNoLt) <| by
    simp [notModels_iff];

end FFL.FirstOrder.Arithmetic.R0

end
