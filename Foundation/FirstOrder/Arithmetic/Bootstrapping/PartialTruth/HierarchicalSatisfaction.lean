module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.BoundedSatisfaction
public import Foundation.FirstOrder.Arithmetic.Prenex
import Foundation.Meta.ClProver

/-!
# Satisfaction and partial truth for prenex formulas with a $\Delta_0$ matrix

`HierarchicalSatisfaction Γ s p e` says that `Q₀ x₀ ⋯ Q_{s-1} x_{s-1} θ` holds under the
assignment `e`, where `p` codes the $\Delta_0$ matrix `θ` and the quantifiers alternate starting
with `Γ`; the value of `x_i` is pushed onto the front of `e`. The partial truth predicate
`PartialTruth Γ s` holds of the code of such a sentence exactly when its matrix is satisfied. For
`s ≥ 1` both are definable at level `Γ`-`s`. In every model of `𝗜𝚺₁` they agree with truth, so
`𝗜𝚺₁` proves the Tarski biconditional `partialTruthDef Γ s (⌜φ⌝) ↔ φ`; by the prenex normal form
theorem, over any theory containing `𝗕𝚺 s` and `𝗜𝚺₁` every sentence of level `Γ`-`s` of the
bounded hierarchy is equivalent to the partial truth of the code of a prenex form of it.

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

noncomputable def hierarchicalSatisfactionDef (Γ : Polarity) : ℕ → ArithmeticSemisentence 2
  | 0 => boundedSatisfaction.val
  | s + 1 => (hierarchicalSatisfaction Γ (s + 1)).val

lemma eval_hierarchicalSatisfactionDef {Γ : Polarity} {s : ℕ} (p e : V) :
    V ⊧/![p, e] (hierarchicalSatisfactionDef Γ s) ↔ HierarchicalSatisfaction Γ s p e := by
  rcases s with _ | s;
  · simp [hierarchicalSatisfactionDef];
  · cases Γ;
    · simpa [hierarchicalSatisfactionDef] using
        (HierarchicalSatisfaction.sigma_defined (s + 1)).df ![p, e];
    · simpa [hierarchicalSatisfactionDef] using
        (HierarchicalSatisfaction.pi_defined (s + 1)).df ![p, e];

/-! ## Partial truth -/

noncomputable def qqToPrenex : Polarity → ℕ → V → V
  | _, 0, θ => θ
  | 𝚺, s + 1, θ => ^∃ qqToPrenex 𝚷 s θ
  | 𝚷, s + 1, θ => ^∀ qqToPrenex 𝚺 s θ

def _root_.FFL.FirstOrder.Arithmetic.qqToPrenexDef : Polarity → ℕ → 𝚺ᴬ₀.Semisentence 2
  | _, 0 => .mkSigma “y θ. y = θ”
  | 𝚺, s + 1 => .mkSigma “y θ. ∃ z < y, !qqExsDef y z ∧ !(qqToPrenexDef 𝚷 s) z θ”
  | 𝚷, s + 1 => .mkSigma “y θ. ∃ z < y, !qqAllDef y z ∧ !(qqToPrenexDef 𝚺 s) z θ”

section
variable {Γ : Polarity} {s : ℕ} {θ θ' : V}

@[simp] lemma qqToPrenex_zero : qqToPrenex Γ 0 θ = θ := by cases Γ <;> rfl

@[simp] lemma qqToPrenex_sigma_succ : qqToPrenex 𝚺 (s + 1) θ = ^∃ qqToPrenex 𝚷 s θ := rfl

@[simp] lemma qqToPrenex_pi_succ : qqToPrenex 𝚷 (s + 1) θ = ^∀ qqToPrenex 𝚺 s θ := rfl

@[simp] lemma qqToPrenex_inj : qqToPrenex Γ s θ = qqToPrenex Γ s θ' ↔ θ = θ' := by
  induction s generalizing Γ with
  | zero => simp;
  | succ s ih => cases Γ <;> simp [ih];

@[simp] lemma le_qqToPrenex : θ ≤ qqToPrenex Γ s θ := by
  induction s generalizing Γ with
  | zero => simp;
  | succ s ih =>
    cases Γ;
    · exact ih.trans (lt_exists _).le;
    · exact ih.trans (lt_forall _).le;

end

instance qqToPrenex_defined : (Γ : Polarity) → (s : ℕ) →
    𝚺ᴬ₀-Function₁ (qqToPrenex Γ s : V → V) via qqToPrenexDef Γ s
  | _, 0 => .mk fun v ↦ by simp [qqToPrenexDef]
  | 𝚺, s + 1 => .mk fun v ↦ by
    simp +contextual [qqToPrenexDef, (qqToPrenex_defined 𝚷 s).df, lt_exists]
  | 𝚷, s + 1 => .mk fun v ↦ by
    simp +contextual [qqToPrenexDef, (qqToPrenex_defined 𝚺 s).df, lt_forall]

def PartialTruth (Γ : Polarity) (s : ℕ) (x : V) : Prop :=
  ∃ θ ≤ x, x = qqToPrenex Γ s θ ∧ HierarchicalSatisfaction Γ s θ 0

noncomputable def partialTruthDef (Γ : Polarity) (s : ℕ) : ArithmeticSemisentence 1 :=
  “x. ∃ θ <⁺ x, !(qqToPrenexDef Γ s) x θ ∧ !(hierarchicalSatisfactionDef Γ s) θ 0”

lemma eval_partialTruthDef {Γ : Polarity} {s : ℕ} (v : Fin 1 → V) :
    V ⊧/v (partialTruthDef Γ s) ↔ PartialTruth Γ s (v 0) := by
  simp [partialTruthDef, PartialTruth, eval_hierarchicalSatisfactionDef];

noncomputable def partialTruth' (Γ : Polarity) (s : ℕ) : Γᴬ-[s + 1].Semisentence 1 :=
  .mkPolarity (partialTruthDef Γ (s + 1)) Γ (by
    simp [partialTruthDef, hierarchicalSatisfactionDef, hierarchicalSatisfaction])

noncomputable def partialTruth (Γ : Polarity) : (s : ℕ) → [NeZero s] → Γᴬ-[s].Semisentence 1
  | 0, h => absurd rfl h.out
  | s + 1, _ => partialTruth' Γ s

instance PartialTruth.sigma_defined : (s : ℕ) → [NeZero s] →
    𝚺ᴬ-[s]-Predicate (PartialTruth 𝚺 s : V → Prop) via partialTruth 𝚺 s
  | 0, h => absurd rfl h.out
  | _ + 1, _ => .mk fun v ↦ eval_partialTruthDef v

instance PartialTruth.pi_defined : (s : ℕ) → [NeZero s] →
    𝚷ᴬ-[s]-Predicate (PartialTruth 𝚷 s : V → Prop) via partialTruth 𝚷 s
  | 0, h => absurd rfl h.out
  | _ + 1, _ => .mk fun v ↦ eval_partialTruthDef v

instance PartialTruth.sigma_definable (s : ℕ) [NeZero s] :
    𝚺ᴬ-[s]-Predicate (PartialTruth 𝚺 s : V → Prop) :=
  (PartialTruth.sigma_defined s).to_definable

instance PartialTruth.pi_definable (s : ℕ) [NeZero s] :
    𝚷ᴬ-[s]-Predicate (PartialTruth 𝚷 s : V → Prop) :=
  (PartialTruth.pi_defined s).to_definable

/-! ## Agreement with truth in models of `𝗜𝚺₁` -/

section
variable {a b : ℕ} (h : a = b) {θ : ArithmeticSemisentence a}

private lemma closure_cast (hθ : ℬ[<, ℒₒᵣ].Closure θ) :
    ℬ[<, ℒₒᵣ].Closure (cast (congrArg ArithmeticSemisentence h) θ) := by
  subst h; exact hθ

private lemma quote_cast : (⌜cast (congrArg ArithmeticSemisentence h) θ⌝ : V) = ⌜θ⌝ := by
  subst h; rfl

end

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

theorem hierarchicalSatisfaction_quote_iff {Γ : Polarity} {s k : ℕ} (φ : Prenex Γ s Empty k)
    (v : Fin k → V) :
    HierarchicalSatisfaction Γ s (⌜φ.matrix.val⌝ : V) (matrixToVec v) ↔ V ⊧/v φ.val :=
  hierarchicalSatisfaction_quote_toPrenex_iff φ.matrix.bounded v

lemma quote_toPrenex : ∀ {Γ : Polarity} {s n : ℕ} (θ : ArithmeticSemisentence (n + s)),
    (⌜θ.toPrenex Γ s⌝ : V) = qqToPrenex Γ s ⌜θ⌝
  | _, 0, _, _ => by simp
  | 𝚺, s + 1, n, θ => by
    simp [Polarity.quantItr_succ, quote_toPrenex (Γ := 𝚷), quote_cast (Nat.succ_add n s).symm]
  | 𝚷, s + 1, n, θ => by
    simp [Polarity.quantItr_succ, quote_toPrenex (Γ := 𝚺), quote_cast (Nat.succ_add n s).symm]

theorem partialTruth_quote_iff {Γ : Polarity} {s : ℕ} (φ : Prenex Γ s Empty 0) :
    PartialTruth Γ s (⌜φ.val⌝ : V) ↔ V↓[ℒₒᵣ] ⊧ φ.val := by
  have h := hierarchicalSatisfaction_quote_iff (V := V) φ ![];
  rw [matrixToVec_nil] at h;
  simpa [PartialTruth, Prenex.val, quote_toPrenex, models_iff] using h

theorem _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_partialTruth_iff {Γ : Polarity} {s : ℕ}
    (φ : Prenex Γ s Empty 0) :
    𝗜𝚺₁ ⊢ (partialTruthDef Γ s)/[⌜φ.val⌝] 🡘 φ.val :=
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ by
    simpa [models_iff, eval_partialTruthDef] using partialTruth_quote_iff φ

section prenex

variable {Γ : Polarity} {s : ℕ} {σ : ArithmeticSentence}

theorem provable_partialTruth_iff_of_hierarchy (T : ArithmeticTheory) [𝗕𝚺s ⪯ T] [𝗜𝚺₁ ⪯ T]
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s σ) :
    ∃ φ : Prenex Γ s Empty 0,
      T ⊢ σ 🡘 φ.val ∧ T ⊢ (partialTruthDef Γ s)/[⌜φ.val⌝] 🡘 σ := by
  obtain ⟨φ, hφ⟩ := exists_prenex_of_hierarchy T h;
  have h₁ : T ⊢ σ 🡘 φ.val := hφ;
  have h₂ : T ⊢ (partialTruthDef Γ s)/[⌜φ.val⌝] 🡘 φ.val :=
    Entailment.WeakerThan.pbl (ISigma1.provable_partialTruth_iff φ);
  exact ⟨φ, h₁, by cl_prover [h₁, h₂]⟩

lemma _root_.FFL.FirstOrder.Arithmetic.Peano.provable_partialTruth_iff_of_hierarchy
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s σ) :
    ∃ φ : Prenex Γ s Empty 0,
      𝗣𝗔 ⊢ σ 🡘 φ.val ∧ 𝗣𝗔 ⊢ (partialTruthDef Γ s)/[⌜φ.val⌝] 🡘 σ :=
  Bootstrapping.provable_partialTruth_iff_of_hierarchy 𝗣𝗔 h

lemma _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_partialTruth_iff_of_hierarchy
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ 1 σ) :
    ∃ φ : Prenex Γ 1 Empty 0,
      𝗜𝚺₁ ⊢ σ 🡘 φ.val ∧ 𝗜𝚺₁ ⊢ (partialTruthDef Γ 1)/[⌜φ.val⌝] 🡘 σ :=
  Bootstrapping.provable_partialTruth_iff_of_hierarchy 𝗜𝚺₁ h

end prenex

end FFL.FirstOrder.Arithmetic.Bootstrapping
