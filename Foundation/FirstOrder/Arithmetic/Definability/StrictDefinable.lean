module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.Definability.Definable

/-!
# Definability by strict-hierarchy formulas

`StrictDefinableRel Γ s R` says the binary relation `R` on `V` is defined by a `StrictHierarchy Γ s`
formula, with the parameters supplied as bound variables.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s : ℕ}

/-- `R` is defined by a `StrictHierarchy Γ s` formula whose two leading bound variables are the
witness and the index, the remaining ones carrying the parameters. -/
def StrictDefinableRel (Γ : Polarity) (s : ℕ) (R : V → V → Prop) : Prop :=
  ∃ (m : ℕ) (θ : ArithmeticSemisentence (m + 2)) (e : Fin m → V),
    StrictHierarchy Γ s θ ∧ ∀ x y, R x y ↔ V ⊧/(y :> x :> e) θ

namespace StrictDefinableRel

lemma of_strictHierarchy {m : ℕ} {θ : ArithmeticSemisentence (m + 2)}
    (hθ : StrictHierarchy Γ s θ) (e : Fin m → V) :
    StrictDefinableRel Γ s fun x y ↦ V ⊧/(y :> x :> e) θ :=
  ⟨m, θ, e, hθ, fun _ _ ↦ Iff.rfl⟩

lemma exists_eval_iff {R : V → V → Prop} (hR : StrictDefinableRel Γ s R) :
    ∃ (e : ℕ → V) (φ : ArithmeticSemiformula ℕ 2),
      StrictHierarchy Γ s φ ∧ ∀ x y, R x y ↔ φ.Eval ![x, y] e := by
  obtain ⟨m, θ, e, hθ, hiff⟩ := hR;
  use fun i ↦ if hi : i < m then e ⟨i, hi⟩ else 0,
    Rew.embSubsts (#1 :> #0 :> fun i : Fin m ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ θ;
  and_intros;
  . exact hθ.rew _;
  . intro x y;
    rw [hiff x y];
    simp only [Semiformula.eval_embSubsts];
    apply Iff.of_eq;
    apply congrArg (fun b ↦ Semiformula.Evalb (M := V) b θ);
    funext i;
    cases i using Fin.cases with
    | zero => simp;
    | succ i =>
      cases i using Fin.cases with
      | zero => simp;
      | succ i => simp [i.isLt];

lemma definableRel {R : V → V → Prop} (hR : StrictDefinableRel Γ s R) : Γ-[s].DefinableRel R := by
  obtain ⟨e, φ, hφ, hiff⟩ := hR.exists_eval_iff;
  exact (definableRel_of_hierarchy hφ.hierarchy e).of_iff fun v ↦ hiff (v 0) (v 1);

end StrictDefinableRel

end FFL.FirstOrder.Arithmetic
