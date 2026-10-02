module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Bounded
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy
public import Foundation.FirstOrder.Arithmetic.Prenex
import Foundation.Meta.ClProver

/-!
# Satisfaction and partial truth for prenex formulas with a $\Delta_0$ matrix

`HierarchicalSatisfaction Γ s p e` says that `Q₀ x₀ ⋯ Q_{s-1} x_{s-1} θ` holds under the
assignment `e`, where `p` codes the $\Delta_0$ matrix `θ` and the quantifiers alternate starting
with `Γ`. `PartialTruth Γ s` is the partial truth predicate for the codes of such sentences.

## References

- [HP98, 0.30, 1.64, 1.66, Lemma I.1.68, Theorem I.1.70, Definition I.1.74, Theorem I.1.75,
  Corollary I.1.76]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def HierarchicalSatisfaction : Polarity → ℕ → V → V → Prop
  | _, 0 => BoundedSatisfaction
  | 𝚺, s + 1 => fun p e ↦ ∃ x, HierarchicalSatisfaction 𝚷 s p (x ∷ e)
  | 𝚷, s + 1 => fun p e ↦ ∀ x, HierarchicalSatisfaction 𝚺 s p (x ∷ e)

section
variable {Γ : Polarity} {s : ℕ} {p e : V}

@[simp] lemma HierarchicalSatisfaction.zero_iff :
    HierarchicalSatisfaction Γ 0 p e ↔ BoundedSatisfaction p e := by
  cases Γ <;> rfl

@[simp] lemma HierarchicalSatisfaction.sigma_succ_iff :
    HierarchicalSatisfaction 𝚺 (s + 1) p e ↔ ∃ x, HierarchicalSatisfaction 𝚷 s p (x ∷ e) :=
  Iff.rfl

@[simp] lemma HierarchicalSatisfaction.pi_succ_iff :
    HierarchicalSatisfaction 𝚷 (s + 1) p e ↔ ∀ x, HierarchicalSatisfaction 𝚺 s p (x ∷ e) :=
  Iff.rfl

end

noncomputable def hierarchicalSatisfaction' :
    (Γ : Polarity) → (s : ℕ) → Γᴬ-[s + 1].Semisentence 2
  | 𝚺, 0 => .mkSigma “p e. ∃ x e', !adjoinDef e' x e ∧ !boundedSatisfaction.sigma p e'”
  | 𝚷, 0 => .mkPi “p e. ∀ x e', !adjoinDef e' x e → !boundedSatisfaction.pi p e'”
  | 𝚺, s + 1 => .mkSigma
      “p e. ∃ x e', !adjoinDef e' x e ∧ !(hierarchicalSatisfaction' 𝚷 s).val p e'”
      (by simpa using (hierarchicalSatisfaction' 𝚷 s).polarity_prop.accum 𝚺)
  | 𝚷, s + 1 => .mkPi
      “p e. ∀ x e', !adjoinDef e' x e → !(hierarchicalSatisfaction' 𝚺 s).val p e'”
      (by simpa using (hierarchicalSatisfaction' 𝚺 s).polarity_prop.accum 𝚷)

noncomputable def hierarchicalSatisfaction (Γ : Polarity) :
    (s : ℕ) → [NeZero s] → Γᴬ-[s].Semisentence 2
  | 0, h => absurd rfl h.out
  | s + 1, _ => hierarchicalSatisfaction' Γ s

mutual

instance HierarchicalSatisfaction.sigma_defined' : (s : ℕ) →
    𝚺ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚺 (s + 1) : V → V → Prop)
      via hierarchicalSatisfaction' 𝚺 s
  | 0 => .mk fun v ↦ by simp [hierarchicalSatisfaction']
  | s + 1 => .mk fun v ↦ by simp [hierarchicalSatisfaction', (pi_defined' s).df]

instance HierarchicalSatisfaction.pi_defined' : (s : ℕ) →
    𝚷ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚷 (s + 1) : V → V → Prop)
      via hierarchicalSatisfaction' 𝚷 s
  | 0 => .mk fun v ↦ by simp [hierarchicalSatisfaction']
  | s + 1 => .mk fun v ↦ by simp [hierarchicalSatisfaction', (sigma_defined' s).df]

end

instance HierarchicalSatisfaction.sigma_defined : (s : ℕ) → [NeZero s] →
    𝚺ᴬ-[s]-Relation (HierarchicalSatisfaction 𝚺 s : V → V → Prop)
      via hierarchicalSatisfaction 𝚺 s
  | 0, h => absurd rfl h.out
  | s + 1, _ => sigma_defined' s

instance HierarchicalSatisfaction.pi_defined : (s : ℕ) → [NeZero s] →
    𝚷ᴬ-[s]-Relation (HierarchicalSatisfaction 𝚷 s : V → V → Prop)
      via hierarchicalSatisfaction 𝚷 s
  | 0, h => absurd rfl h.out
  | s + 1, _ => pi_defined' s

instance HierarchicalSatisfaction.sigma_definable (s : ℕ) [NeZero s] :
    𝚺ᴬ-[s]-Relation (HierarchicalSatisfaction 𝚺 s : V → V → Prop) :=
  (sigma_defined s).to_definable

instance HierarchicalSatisfaction.pi_definable (s : ℕ) [NeZero s] :
    𝚷ᴬ-[s]-Relation (HierarchicalSatisfaction 𝚷 s : V → V → Prop) :=
  (pi_defined s).to_definable

/-! ## Partial truth -/

def PartialTruth (Γ : Polarity) (s : ℕ) (x : V) : Prop :=
  ∃ θ ≤ x, x = qqToPrenex Γ s θ ∧ HierarchicalSatisfaction Γ s θ 0

noncomputable def partialTruth' (Γ : Polarity) (s : ℕ) : Γᴬ-[s + 1].Semisentence 1 :=
  .mkPolarity
    “x. ∃ θ <⁺ x, !(qqToPrenexDef Γ (s + 1)) x θ ∧ !(hierarchicalSatisfaction' Γ s).val θ 0” Γ
    (by simp)

private lemma eval_partialTruth' {Γ : Polarity} {s : ℕ} (v : Fin 1 → V) :
    V ⊧/v (partialTruth' Γ s).val ↔ PartialTruth Γ (s + 1) (v 0) := by
  simp only [partialTruth', HierarchySymbol.Semiformula.val_mkPolarity];
  cases Γ <;> simp [PartialTruth, (HierarchicalSatisfaction.sigma_defined' s).df,
    (HierarchicalSatisfaction.pi_defined' s).df]

noncomputable def partialTruth (Γ : Polarity) : (s : ℕ) → [NeZero s] → Γᴬ-[s].Semisentence 1
  | 0, h => absurd rfl h.out
  | s + 1, _ => partialTruth' Γ s

instance PartialTruth.sigma_defined : (s : ℕ) → [NeZero s] →
    𝚺ᴬ-[s]-Predicate (PartialTruth 𝚺 s : V → Prop) via partialTruth 𝚺 s
  | 0, h => absurd rfl h.out
  | _ + 1, _ => .mk fun v ↦ eval_partialTruth' v

instance PartialTruth.pi_defined : (s : ℕ) → [NeZero s] →
    𝚷ᴬ-[s]-Predicate (PartialTruth 𝚷 s : V → Prop) via partialTruth 𝚷 s
  | 0, h => absurd rfl h.out
  | _ + 1, _ => .mk fun v ↦ eval_partialTruth' v

instance PartialTruth.sigma_definable (s : ℕ) [NeZero s] :
    𝚺ᴬ-[s]-Predicate (PartialTruth 𝚺 s : V → Prop) :=
  (PartialTruth.sigma_defined s).to_definable

instance PartialTruth.pi_definable (s : ℕ) [NeZero s] :
    𝚷ᴬ-[s]-Predicate (PartialTruth 𝚷 s : V → Prop) :=
  (PartialTruth.pi_defined s).to_definable

@[simp] lemma PartialTruth.zero_iff {Γ : Polarity} {x : V} :
    PartialTruth Γ 0 x ↔ BoundedTruth x := by
  simp [PartialTruth, BoundedTruth]

/-! ## Agreement with truth in models of `𝗜𝚺₁` -/

private lemma hierarchicalSatisfaction_quote_toPrenex_iff : ∀ {Γ : Polarity} {s k : ℕ}
    {θ : ArithmeticSemisentence (k + s)}, ℬ[<, ℒₒᵣ].Closure θ → ∀ v : Fin k → V,
      HierarchicalSatisfaction Γ s (⌜θ⌝ : V) (matrixToVec v) ↔ V ⊧/v (θ.toPrenex Γ s)
  | _, 0, _, _, hθ, v => by simpa using boundedSatisfaction_quote_iff hθ v
  | 𝚺, s + 1, k, θ, hθ, v => by
    have ih := hierarchicalSatisfaction_quote_toPrenex_iff (Γ := 𝚷)
      (closure_cast (Nat.succ_add k s).symm hθ);
    simp [Polarity.quantItr_succ, ← ih, quote_cast (Nat.succ_add k s).symm];
  | 𝚷, s + 1, k, θ, hθ, v => by
    have ih := hierarchicalSatisfaction_quote_toPrenex_iff (Γ := 𝚺)
      (closure_cast (Nat.succ_add k s).symm hθ);
    simp [Polarity.quantItr_succ, ← ih, quote_cast (Nat.succ_add k s).symm];

theorem hierarchicalSatisfaction_quote_iff {Γ : Polarity} {s k : ℕ}
    (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty k) (v : Fin k → V) :
    HierarchicalSatisfaction Γ s (⌜φ.matrix.val⌝ : V) (matrixToVec v) ↔ V ⊧/v φ.val :=
  hierarchicalSatisfaction_quote_toPrenex_iff φ.matrix.bounded v

lemma quote_toPrenex : ∀ {Γ : Polarity} {s n : ℕ} (θ : ArithmeticSemisentence (n + s)),
    (⌜θ.toPrenex Γ s⌝ : V) = qqToPrenex Γ s ⌜θ⌝
  | _, 0, _, _ => by simp
  | Γ, s + 1, n, θ => by
    cases Γ <;> simp [Polarity.quantItr_succ, quote_toPrenex, quote_cast (Nat.succ_add n s).symm]

theorem partialTruth_quote_iff {Γ : Polarity} {s : ℕ} (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0) :
    PartialTruth Γ s (⌜φ.val⌝ : V) ↔ V↓[ℒₒᵣ] ⊧ φ.val := by
  have h := hierarchicalSatisfaction_quote_iff (V := V) φ ![];
  rw [matrixToVec_nil] at h;
  simpa [PartialTruth, Bounding.Prenex.val, quote_toPrenex, models_iff] using h

theorem _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_partialTruth_iff {Γ : Polarity} {s : ℕ}
    [NeZero s] (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0) :
    𝗜𝚺₁ ⊢ (partialTruth Γ s).val/[⌜φ.val⌝] 🡘 φ.val :=
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ by
    cases Γ <;> simpa [models_iff, (PartialTruth.sigma_defined s).df,
      (PartialTruth.pi_defined s).df] using partialTruth_quote_iff φ

section prenex

variable {Γ : Polarity} {s : ℕ} [NeZero s] {σ : ArithmeticSentence}

theorem provable_partialTruth_iff_of_hierarchy (T : ArithmeticTheory) [𝗕𝚺s ⪯ T] [𝗜𝚺₁ ⪯ T]
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s σ) :
    ∃ φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0,
      T ⊢ σ 🡘 φ.val ∧ T ⊢ (partialTruth Γ s).val/[⌜φ.val⌝] 🡘 σ := by
  obtain ⟨φ, hφ⟩ := exists_prenex_of_hierarchy T h;
  have h₁ : T ⊢ σ 🡘 φ.val := hφ;
  have h₂ : T ⊢ (partialTruth Γ s).val/[⌜φ.val⌝] 🡘 φ.val :=
    Entailment.WeakerThan.pbl (ISigma1.provable_partialTruth_iff φ);
  exact ⟨φ, h₁, by cl_prover [h₁, h₂]⟩

lemma _root_.FFL.FirstOrder.Arithmetic.Peano.provable_partialTruth_iff_of_hierarchy
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s σ) :
    ∃ φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0,
      𝗣𝗔 ⊢ σ 🡘 φ.val ∧ 𝗣𝗔 ⊢ (partialTruth Γ s).val/[⌜φ.val⌝] 🡘 σ :=
  Bootstrapping.provable_partialTruth_iff_of_hierarchy 𝗣𝗔 h

lemma _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_partialTruth_iff_of_hierarchy
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ 1 σ) :
    ∃ φ : ℬ[<, ℒₒᵣ].Prenex Γ 1 Empty 0,
      𝗜𝚺₁ ⊢ σ 🡘 φ.val ∧ 𝗜𝚺₁ ⊢ (partialTruth Γ 1).val/[⌜φ.val⌝] 🡘 σ :=
  Bootstrapping.provable_partialTruth_iff_of_hierarchy 𝗜𝚺₁ h

theorem provable_boundedTruth_iff_of_hierarchy (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T]
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ 0 σ) : T ⊢ boundedTruth.val/[⌜σ⌝] 🡘 σ :=
  Entailment.WeakerThan.pbl <|
    ISigma1.provable_boundedTruth_iff (Bounding.Hierarchy.zero_iff_bounded.mp h)

end prenex

end FFL.FirstOrder.Arithmetic.Bootstrapping
