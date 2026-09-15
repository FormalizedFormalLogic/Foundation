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

instance : Trivial↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₃Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | ⟨n, m, h⟩ | n | n;
  . have : Trivial↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  . simp only [models_iff];
    exact Subsingleton.elim _ _;
  . simp only [models_iff];
    exact Subsingleton.elim _ _;
  . exact absurd ⟨n, m, h, rfl⟩ hn;
  . simp only [Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue, disjLt_succ, models_iff, Semiformula.eval_all,
      Nat.succ_eq_add_one, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator, Matrix.comp₂,
      Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral,
      Structure.le_iff_of_eq_of_lt, LogicalConnective.HomClass.map_or, Structure.eq_iff_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, hom_disj_prop, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.iff_eq];
    intro x;
    exact ⟨fun _ ↦ Or.inl (Subsingleton.elim _ _), fun _ ↦ Or.inl (Subsingleton.elim _ _)⟩;
  . simp only [models_iff];
    exact id;⟩

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

lemma lt_iff {a b : NatLE} : a < b ↔ a.toNat ≤ b.toNat := Iff.rfl

end NatLE

instance : NatLE↓[ℒₒᵣ] ⊧* (𝗥₀ \ Ω₅Scheme) := ⟨by
  intro σ ⟨h, hn⟩;
  rcases h with ⟨_, h⟩ | ⟨n, m⟩ | ⟨n, m⟩ | ⟨n, m, h⟩ | n | n;
  . have : NatLE↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance;
    simpa [models_iff] using models_theory_iff.mp this _ h;
  . simp only [models_iff, Semiformula.eval_operator, Matrix.comp₂, Nat.succ_eq_add_one, Nat.reduceAdd,
      Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral, Structure.Add.add, Structure.eq_iff_eq,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one];
    rw [NatLE.numeral_eq, NatLE.numeral_eq, NatLE.numeral_eq];
    rfl;
  . simp only [models_iff, Semiformula.eval_operator, Matrix.comp₂, Nat.succ_eq_add_one, Nat.reduceAdd,
      Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral, Structure.Mul.mul, Structure.eq_iff_eq,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one];
    rw [NatLE.numeral_eq, NatLE.numeral_eq, NatLE.numeral_eq];
    rfl;
  . simp only [Semantics.Not.models_not, models_iff, Semiformula.eval_operator, Matrix.comp₂, Nat.succ_eq_add_one,
      Nat.reduceAdd, Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral, NatLE.numeral_eq,
      Structure.eq_iff_eq, Fin.isValue, Matrix.cons_val];
    exact h;
  . simp only [Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue, disjLt_succ, models_iff, Semiformula.eval_all,
      Nat.succ_eq_add_one, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator, Matrix.comp₂,
      Semiterm.val_bvar, Matrix.cons_val_fin_one, Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral,
      Structure.le_iff_of_eq_of_lt, LogicalConnective.HomClass.map_or, Structure.eq_iff_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, hom_disj_prop, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.iff_eq];
    intro x;
    rw [NatLE.lt_iff];
    simp only [NatLE.numeral_eq];
    show x.toNat = n ∨ x.toNat ≤ n ↔ x.toNat = n ∨ ∃ i < n, x.toNat = i;
    constructor;
    . rintro (rfl | h);
      . left; rfl;
      . rcases eq_or_lt_of_le h with rfl | h;
        . left; rfl;
        . right; exact ⟨x.toNat, h, rfl⟩;
    . rintro (h | ⟨i, hi, h⟩);
      . left; exact h;
      . right; omega;
  . exact absurd ⟨n, rfl⟩ hn;⟩

end Countermodel

theorem Ω₃_independent : 𝗥₀ \ Ω₃Scheme ⊬ “↑0 ≠ ↑1” :=
  unprovable_of_countermodel _ (M := Countermodel.Trivial) <| by
    simp only [notModels_iff, LogicalConnective.HomClass.map_neg, Semiformula.eval_operator, Matrix.comp₂,
      Nat.succ_eq_add_one, Nat.reduceAdd, Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral,
      ORingStructure.zero_eq_zero, ORingStructure.one_eq_one, Structure.eq_iff_eq, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
      LogicalConnective.Prop.neg_eq, Decidable.not_not];
    exact Subsingleton.elim _ _;

theorem Ω₅_independent : 𝗥₀ \ Ω₅Scheme ⊬ “¬ ↑0 < ↑0” :=
  unprovable_of_countermodel _ (M := Countermodel.NatLE) <| by
    simp [notModels_iff, Countermodel.NatLE.lt_iff];

end FFL.FirstOrder.Arithmetic.R0

end
