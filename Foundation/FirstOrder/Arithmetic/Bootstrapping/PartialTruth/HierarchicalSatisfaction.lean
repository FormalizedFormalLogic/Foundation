module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.BoundedSatisfaction

/-!
# Satisfaction and partial truth for prenex formulas with a $\Delta_0$ matrix

`HierarchicalSatisfaction Γ s p e` says that `Q₀ x₀ ⋯ Q_{s-1} x_{s-1} θ` holds under the
assignment `e`, where `p` codes the $\Delta_0$ matrix `θ` and the quantifiers alternate starting
with `Γ`; the value of `x_i` is pushed onto the front of `e`. The partial truth predicate
`Truth Γ s` holds of the code of such a sentence exactly when its matrix is satisfied. For
`s ≥ 1` both are definable at level `Γ`-`s`.

## References

- [HP98, 1.64, Definition I.1.74, Theorem I.1.75]
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

noncomputable def hierarchicalSatisfaction : (Γ : Polarity) → (s : ℕ) → Γᴬ-[s + 1].Semisentence 2
  | 𝚺, 0 => .mkSigma “p e. ∃ x e', !adjoinDef e' x e ∧ !boundedSatisfaction.sigma p e'”
  | 𝚷, 0 => .mkPi “p e. ∀ x e', !adjoinDef e' x e → !boundedSatisfaction.pi p e'”
  | 𝚺, s + 1 => .mkSigma
      “p e. ∃ x e', !adjoinDef e' x e ∧ !(hierarchicalSatisfaction 𝚷 s).val p e'”
      (by simpa using (hierarchicalSatisfaction 𝚷 s).polarity_prop.accum 𝚺)
  | 𝚷, s + 1 => .mkPi
      “p e. ∀ x e', !adjoinDef e' x e → !(hierarchicalSatisfaction 𝚺 s).val p e'”
      (by simpa using (hierarchicalSatisfaction 𝚺 s).polarity_prop.accum 𝚷)

mutual

instance HierarchicalSatisfaction.sigma_defined : (s : ℕ) →
    𝚺ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚺 (s + 1) : V → V → Prop)
      via hierarchicalSatisfaction 𝚺 s
  | 0 => .mk fun v ↦ by simp [hierarchicalSatisfaction]
  | s + 1 => .mk fun v ↦ by simp [hierarchicalSatisfaction, (pi_defined s).df]

instance HierarchicalSatisfaction.pi_defined : (s : ℕ) →
    𝚷ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚷 (s + 1) : V → V → Prop)
      via hierarchicalSatisfaction 𝚷 s
  | 0 => .mk fun v ↦ by simp [hierarchicalSatisfaction]
  | s + 1 => .mk fun v ↦ by simp [hierarchicalSatisfaction, (sigma_defined s).df]

end

instance HierarchicalSatisfaction.sigma_definable (s : ℕ) :
    𝚺ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚺 (s + 1) : V → V → Prop) :=
  (sigma_defined s).to_definable

instance HierarchicalSatisfaction.pi_definable (s : ℕ) :
    𝚷ᴬ-[s + 1]-Relation (HierarchicalSatisfaction 𝚷 (s + 1) : V → V → Prop) :=
  (pi_defined s).to_definable

noncomputable def hierarchicalSatisfactionDef (Γ : Polarity) : ℕ → ArithmeticSemisentence 2
  | 0 => boundedSatisfaction.val
  | s + 1 => (hierarchicalSatisfaction Γ s).val

lemma eval_hierarchicalSatisfactionDef {Γ : Polarity} {s : ℕ} (p e : V) :
    V ⊧/![p, e] (hierarchicalSatisfactionDef Γ s) ↔ HierarchicalSatisfaction Γ s p e := by
  rcases s with _ | s;
  · simp [hierarchicalSatisfactionDef];
  · cases Γ;
    · simpa [hierarchicalSatisfactionDef] using
        (HierarchicalSatisfaction.sigma_defined s).df ![p, e];
    · simpa [hierarchicalSatisfactionDef] using
        (HierarchicalSatisfaction.pi_defined s).df ![p, e];

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

def Truth (Γ : Polarity) (s : ℕ) (x : V) : Prop :=
  ∃ θ ≤ x, x = qqToPrenex Γ s θ ∧ HierarchicalSatisfaction Γ s θ 0

noncomputable def truthDef (Γ : Polarity) (s : ℕ) : ArithmeticSemisentence 1 :=
  “x. ∃ θ <⁺ x, !(qqToPrenexDef Γ s) x θ ∧ !(hierarchicalSatisfactionDef Γ s) θ 0”

lemma eval_truthDef {Γ : Polarity} {s : ℕ} (v : Fin 1 → V) :
    V ⊧/v (truthDef Γ s) ↔ Truth Γ s (v 0) := by
  simp [truthDef, Truth, eval_hierarchicalSatisfactionDef];

noncomputable def truth (Γ : Polarity) (s : ℕ) : Γᴬ-[s + 1].Semisentence 1 :=
  .mkPolarity (truthDef Γ (s + 1)) Γ (by simp [truthDef, hierarchicalSatisfactionDef])

instance Truth.sigma_defined (s : ℕ) :
    𝚺ᴬ-[s + 1]-Predicate (Truth 𝚺 (s + 1) : V → Prop) via truth 𝚺 s :=
  .mk fun v ↦ eval_truthDef v

instance Truth.pi_defined (s : ℕ) :
    𝚷ᴬ-[s + 1]-Predicate (Truth 𝚷 (s + 1) : V → Prop) via truth 𝚷 s :=
  .mk fun v ↦ eval_truthDef v

instance Truth.sigma_definable (s : ℕ) : 𝚺ᴬ-[s + 1]-Predicate (Truth 𝚺 (s + 1) : V → Prop) :=
  (Truth.sigma_defined s).to_definable

instance Truth.pi_definable (s : ℕ) : 𝚷ᴬ-[s + 1]-Predicate (Truth 𝚷 (s + 1) : V → Prop) :=
  (Truth.pi_defined s).to_definable

end FFL.FirstOrder.Arithmetic.Bootstrapping
