module

public import Foundation.FirstOrder.Arithmetic.Basic.PrenexHierarchy
public import Foundation.FirstOrder.Arithmetic.Definability.Definable

/-!
# Definability by prenex formulas
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {k : ℕ}

variable (Γ : Polarity) (s : ℕ)

structure IsPrenexDefinedBy (R : (Fin k → V) → Prop)
    (φ : ArithmeticSemisentence k) : Prop where
  prenexHierarchy : PrenexHierarchy Γ s φ
  defined : FirstOrder.IsDefinedBy R φ

structure IsPrenexDefinedByWithParam (R : (Fin k → V) → Prop) (φ : ArithmeticSemiformula V k) :
    Prop where
  prenexHierarchy : PrenexHierarchy Γ s φ
  defined : FirstOrder.IsDefinedByWithParam R φ

abbrev PrenexDefinable {k} (P : (Fin k → V) → Prop) :=
  ∃ φ, IsPrenexDefinedByWithParam Γ s P φ

abbrev PrenexDefinablePred (P : V → Prop) : Prop :=
  PrenexDefinable Γ s (k := 1) fun v ↦ P (v 0)

abbrev PrenexDefinableRel (R : V → V → Prop) : Prop :=
  PrenexDefinable Γ s (k := 2) fun v ↦ R (v 0) (v 1)

abbrev PrenexDefinableRel₃ (R : V → V → V → Prop) : Prop :=
  PrenexDefinable Γ s (k := 3) fun v ↦ R (v 0) (v 1) (v 2)

abbrev PrenexDefinableRel₄ (R : V → V → V → V → Prop) : Prop :=
  PrenexDefinable Γ s (k := 4) fun v ↦ R (v 0) (v 1) (v 2) (v 3)

variable {Γ s}

namespace PrenexDefinable

lemma of_iff {P Q : (Fin k → V) → Prop} (h : PrenexDefinable Γ s Q) (H : ∀ v, P v ↔ Q v) :
    PrenexDefinable Γ s P := by
  rwa [show P = Q from by funext v; simp [H]];

lemma definable {P : (Fin k → V) → Prop} (h : PrenexDefinable Γ s P) :
    Γᴬ-[s].Definable P := by
  obtain ⟨φ, hs, hφ⟩ := h;
  exact .mkPolarity φ hs.hierarchy fun v ↦ (hφ v).symm;

lemma exists_eval_iff {P : (Fin k → V) → Prop} (h : PrenexDefinable Γ s P) :
    ∃ (e : ℕ → V) (φ : ArithmeticSemiformula ℕ k),
      PrenexHierarchy Γ s φ ∧ ∀ v, P v ↔ φ.Eval v e := by
  classical
  obtain ⟨φ, hs, hφ⟩ := h;
  have : Inhabited V := Classical.inhabited_of_nonempty';
  use φ.enumerateFVar, Rew.rewriteMap φ.idxOfFVar ▹ φ;
  and_intros;
  · exact hs.rew _;
  · intro v;
    simp [Semiformula.eval_rewriteMap, hφ];

lemma of_prenexHierarchy {ξ : Type*} {m : ℕ} {θ : ArithmeticSemiformula ξ (m + 2)}
    (hθ : PrenexHierarchy Γ s θ) (e : Fin m → V) (f : ξ → V) :
    PrenexDefinableRel Γ s fun x y ↦ Semiformula.Eval (y :> x :> e) f θ := by
  use Rew.bind (#1 :> #0 :> fun i : Fin m ↦ (&(e i) : ArithmeticSemiterm V 2))
    (fun x : ξ ↦ (&(f x) : ArithmeticSemiterm V 2)) ▹ θ;
  constructor;
  · exact hθ.rew _;
  · intro v;
    simp only [Semiformula.eval_rew];
    have hb : (Semiterm.val (L := ℒₒᵣ) (M := V) v id) ∘
        (Rew.bind (#1 :> #0 :> fun i : Fin m ↦ (&(e i) : ArithmeticSemiterm V 2))
          (fun x : ξ ↦ (&(f x) : ArithmeticSemiterm V 2))) ∘ Semiterm.bvar
        = (v 1 :> v 0 :> e : Fin (m + 2) → V) := by
      funext i;
      cases i using Fin.cases with
      | zero => simp;
      | succ i =>
        cases i using Fin.cases with
        | zero => simp;
        | succ i => simp;
    have hf : (Semiterm.val (L := ℒₒᵣ) (M := V) v id) ∘
        (Rew.bind (#1 :> #0 :> fun i : Fin m ↦ (&(e i) : ArithmeticSemiterm V 2))
          (fun x : ξ ↦ (&(f x) : ArithmeticSemiterm V 2))) ∘ Semiterm.fvar
        = f := by
      funext x; simp;
    rw [hb, hf];

end PrenexDefinable

end FFL.FirstOrder.Arithmetic
