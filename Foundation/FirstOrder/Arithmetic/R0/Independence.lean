module

public import Foundation.FirstOrder.Arithmetic.R0.Basic

/-!
# Independence of `Ω₃` and `Ω₅` in $\mathsf{R_0}$

`Ω₃` is not derivable from the other axioms of `𝗥₀` (the one-element structure with empty `<`
is a countermodel), and neither is `Ω₅` (`ℕ` with `<` interpreted as `≤` is a countermodel).
-/

@[expose] public section

noncomputable section

namespace FFL.FirstOrder.Arithmetic.R0

def Ω₃Scheme : ArithmeticTheory := {σ | ∃ n m : ℕ, n ≠ m ∧ σ = “↑n ≠ ↑m”}

def Ω₅Scheme : ArithmeticTheory := {σ | ∃ n : ℕ, σ = “¬ ↑n < ↑n”}

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

@[simp] lemma eq_iff (a b : Trivial) : a = b ↔ True := eq_iff_true_of_subsingleton a b

@[simp] lemma not_lt (a b : Trivial) : ¬ a < b := id

end Trivial

-- `simp [models_iff]` is used as a non-terminal simp to discharge most axiom cases at once;
-- the flexible-simp linter is silenced for this instance only.
set_option linter.flexible false in
instance : Trivial↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₃Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h <;> simp [models_iff, Structure.le_iff_of_eq_of_lt];
  case equal h =>
    have : Trivial↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    exact models_theory_iff.mp this _ h;
  case Ω₃ n m h => exact absurd ⟨n, m, h, rfl⟩ hn;⟩

def NatLE := ℕ

instance : ORingStructure NatLE where
  zero := (0 : ℕ)
  one := (1 : ℕ)
  add a b := Nat.add a b
  mul a b := Nat.mul a b
  lt a b := Nat.le a b

namespace NatLE

def toNat (x : NatLE) : ℕ := x

@[simp] lemma numeral_eq (n : ℕ) : (ORingStructure.numeral n : NatLE) = n :=
  match n with
  |     0 => rfl
  |     1 => rfl
  | n + 2 => by
      show (ORingStructure.numeral (n + 1) : NatLE) + 1 = (n + 2 : ℕ);
      rw [numeral_eq (n + 1)];
      show n + 1 + 1 = n + 2;
      omega;

@[simp] lemma lt_iff {a b : NatLE} : a < b ↔ a.toNat ≤ b.toNat := Iff.rfl

end NatLE

-- `simp [models_iff]` is used as a non-terminal simp to discharge the operator/quantifier
-- unfolding before finishing each case by hand; the flexible-simp linter is silenced for this
-- instance only.
set_option linter.flexible false in
instance : NatLE↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₅Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | ⟨n, m, h⟩ | n | n;
  . have : NatLE↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  . simp [models_iff, Structure.numeral_eq_numeral];
    rfl;
  . simp [models_iff, Structure.numeral_eq_numeral];
    rfl;
  . simp [models_iff];
    exact h;
  . simp [models_iff, -existsAndEq];
    intro x;
    refine Structure.le_iff_of_eq_of_lt.trans ?_;
    constructor;
    . rintro (rfl | hx);
      . left; rfl;
      . rcases eq_or_lt_of_le (show x.toNat ≤ n from hx) with rfl | hlt;
        . left; rfl;
        . right; exact ⟨x, hlt, rfl⟩;
    . rintro (rfl | ⟨i, hi, rfl⟩);
      . left; rfl;
      . right; exact hi.le;
  . exact absurd ⟨n, rfl⟩ hn;⟩

end Countermodel

theorem Ω₃_independent : 𝗥₀ \ Ω₃Scheme ⊬ “↑0 ≠ ↑1” :=
  unprovable_of_countermodel _ (M := Countermodel.Trivial) <| by
    simp [notModels_iff];

theorem Ω₅_independent : 𝗥₀ \ Ω₅Scheme ⊬ “¬ ↑0 < ↑0” :=
  unprovable_of_countermodel _ (M := Countermodel.NatLE) <| by
    simp [notModels_iff, Countermodel.NatLE.lt_iff];

end FFL.FirstOrder.Arithmetic.R0

end
