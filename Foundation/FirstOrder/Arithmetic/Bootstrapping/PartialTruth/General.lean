module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Bounded
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy
public import Foundation.FirstOrder.Arithmetic.Prenex
import Foundation.Meta.ClProver

/-!
# Satisfaction and partial truth for prenex formulas with a $\Delta_0$ matrix

`PrenexSatisfied Γ s e p` says that `Q₀ x₀ ⋯ Q_{s-1} x_{s-1} θ` holds under the
assignment `e`, where `p` codes the $\Delta_0$ matrix `θ` and the quantifiers alternate starting
with `Γ`. `PrenexTrue Γ s` is the partial truth predicate for the codes of such sentences.

## References

- [HP98, 0.30, 1.64, 1.66, Lemma I.1.68, Theorem I.1.70, Definition I.1.74, Theorem I.1.75,
  Corollary I.1.76]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def PrenexSatisfied : Polarity → ℕ → V → V → Prop
  | _, 0 => BoundedSatisfied
  | 𝚺, s + 1 => fun e p ↦ ∃ x, PrenexSatisfied 𝚷 s (x ∷ e) p
  | 𝚷, s + 1 => fun e p ↦ ∀ x, PrenexSatisfied 𝚺 s (x ∷ e) p

section
variable {Γ : Polarity} {s : ℕ} {e p : V}

@[simp] lemma PrenexSatisfied.zero_iff :
    PrenexSatisfied Γ 0 e p ↔ BoundedSatisfied e p := by
  cases Γ <;> rfl

@[simp] lemma PrenexSatisfied.sigma_succ_iff :
    PrenexSatisfied 𝚺 (s + 1) e p ↔ ∃ x, PrenexSatisfied 𝚷 s (x ∷ e) p :=
  Iff.rfl

@[simp] lemma PrenexSatisfied.pi_succ_iff :
    PrenexSatisfied 𝚷 (s + 1) e p ↔ ∀ x, PrenexSatisfied 𝚺 s (x ∷ e) p :=
  Iff.rfl

lemma not_prenexSatisfied_of_not_isBounded (h : ¬IsBounded p) : ¬PrenexSatisfied Γ s e p := by
  induction s generalizing Γ e with
  | zero => exact fun h' ↦ h (PrenexSatisfied.zero_iff.mp h').dom.1;
  | succ s ih => cases Γ <;> simp [ih];

end

noncomputable def prenexSatisfied' :
    (Γ : Polarity) → (s : ℕ) → Γᴬ-[s + 1].Semisentence 2
  | 𝚺, 0 => .mkSigma “e p. ∃ x e', !adjoinDef e' x e ∧ !boundedSatisfied.sigma e' p”
  | 𝚷, 0 => .mkPi “e p. ∀ x e', !adjoinDef e' x e → !boundedSatisfied.pi e' p”
  | 𝚺, s + 1 => .mkSigma
      “e p. ∃ x e', !adjoinDef e' x e ∧ !(prenexSatisfied' 𝚷 s).val e' p”
      (by simpa using (prenexSatisfied' 𝚷 s).polarity_prop.accum 𝚺)
  | 𝚷, s + 1 => .mkPi
      “e p. ∀ x e', !adjoinDef e' x e → !(prenexSatisfied' 𝚺 s).val e' p”
      (by simpa using (prenexSatisfied' 𝚺 s).polarity_prop.accum 𝚷)

noncomputable def prenexSatisfied (Γ : Polarity) :
    (s : ℕ) → [NeZero s] → Γᴬ-[s].Semisentence 2
  | 0, h => absurd rfl h.out
  | s + 1, _ => prenexSatisfied' Γ s

mutual

instance PrenexSatisfied.sigma_defined' : (s : ℕ) →
    𝚺ᴬ-[s + 1]-Relation (PrenexSatisfied 𝚺 (s + 1) : V → V → Prop)
      via prenexSatisfied' 𝚺 s
  | 0 => .mk fun v ↦ by simp [prenexSatisfied']
  | s + 1 => .mk fun v ↦ by simp [prenexSatisfied', (pi_defined' s).df]

instance PrenexSatisfied.pi_defined' : (s : ℕ) →
    𝚷ᴬ-[s + 1]-Relation (PrenexSatisfied 𝚷 (s + 1) : V → V → Prop)
      via prenexSatisfied' 𝚷 s
  | 0 => .mk fun v ↦ by simp [prenexSatisfied']
  | s + 1 => .mk fun v ↦ by simp [prenexSatisfied', (sigma_defined' s).df]

end

instance PrenexSatisfied.sigma_defined : (s : ℕ) → [NeZero s] →
    𝚺ᴬ-[s]-Relation (PrenexSatisfied 𝚺 s : V → V → Prop)
      via prenexSatisfied 𝚺 s
  | 0, h => absurd rfl h.out
  | s + 1, _ => sigma_defined' s

instance PrenexSatisfied.pi_defined : (s : ℕ) → [NeZero s] →
    𝚷ᴬ-[s]-Relation (PrenexSatisfied 𝚷 s : V → V → Prop)
      via prenexSatisfied 𝚷 s
  | 0, h => absurd rfl h.out
  | s + 1, _ => pi_defined' s

instance PrenexSatisfied.sigma_definable (s : ℕ) [NeZero s] :
    𝚺ᴬ-[s]-Relation (PrenexSatisfied 𝚺 s : V → V → Prop) :=
  (sigma_defined s).to_definable

instance PrenexSatisfied.pi_definable (s : ℕ) [NeZero s] :
    𝚷ᴬ-[s]-Relation (PrenexSatisfied 𝚷 s : V → V → Prop) :=
  (pi_defined s).to_definable

/-! ## Partial truth -/

def PrenexTrue (Γ : Polarity) (s : ℕ) (x : V) : Prop :=
  ∃ θ ≤ x, x = qqToPrenex Γ s θ ∧ PrenexSatisfied Γ s 0 θ

noncomputable def prenexTrue' (Γ : Polarity) (s : ℕ) : Γᴬ-[s + 1].Semisentence 1 :=
  .mkPolarity
    “x. ∃ θ <⁺ x, !(qqToPrenexDef Γ (s + 1)) x θ ∧ !(prenexSatisfied' Γ s).val 0 θ” Γ
    (by simp)

private lemma eval_prenexTrue' {Γ : Polarity} {s : ℕ} (v : Fin 1 → V) :
    V ⊧/v (prenexTrue' Γ s).val ↔ PrenexTrue Γ (s + 1) (v 0) := by
  simp only [prenexTrue', HierarchySymbol.Semiformula.val_mkPolarity];
  cases Γ <;> simp [PrenexTrue, (PrenexSatisfied.sigma_defined' s).df,
    (PrenexSatisfied.pi_defined' s).df]

noncomputable def prenexTrue (Γ : Polarity) : (s : ℕ) → [NeZero s] → Γᴬ-[s].Semisentence 1
  | 0, h => absurd rfl h.out
  | s + 1, _ => prenexTrue' Γ s

instance PrenexTrue.sigma_defined : (s : ℕ) → [NeZero s] →
    𝚺ᴬ-[s]-Predicate (PrenexTrue 𝚺 s : V → Prop) via prenexTrue 𝚺 s
  | 0, h => absurd rfl h.out
  | _ + 1, _ => .mk fun v ↦ eval_prenexTrue' v

instance PrenexTrue.pi_defined : (s : ℕ) → [NeZero s] →
    𝚷ᴬ-[s]-Predicate (PrenexTrue 𝚷 s : V → Prop) via prenexTrue 𝚷 s
  | 0, h => absurd rfl h.out
  | _ + 1, _ => .mk fun v ↦ eval_prenexTrue' v

instance PrenexTrue.sigma_definable (s : ℕ) [NeZero s] :
    𝚺ᴬ-[s]-Predicate (PrenexTrue 𝚺 s : V → Prop) :=
  (PrenexTrue.sigma_defined s).to_definable

instance PrenexTrue.pi_definable (s : ℕ) [NeZero s] :
    𝚷ᴬ-[s]-Predicate (PrenexTrue 𝚷 s : V → Prop) :=
  (PrenexTrue.pi_defined s).to_definable

@[simp] lemma PrenexTrue.zero_iff {Γ : Polarity} {x : V} :
    PrenexTrue Γ 0 x ↔ BoundedTrue x := by
  simp [PrenexTrue, BoundedTrue]

/-! ## Agreement with truth in models of `𝗜𝚺₁` -/

private lemma prenexSatisfied_quote_toPrenex_iff : ∀ {Γ : Polarity} {s k : ℕ}
    {θ : ArithmeticSemisentence (k + s)}, ℬ[<, ℒₒᵣ].Closure θ → ∀ v : Fin k → V,
      PrenexSatisfied Γ s (matrixToVec v) (⌜θ⌝ : V) ↔ V ⊧/v (θ.toPrenex Γ s)
  | _, 0, _, _, hθ, v => by simpa using boundedSatisfied_quote_iff hθ v
  | 𝚺, s + 1, k, θ, hθ, v => by
    have ih := prenexSatisfied_quote_toPrenex_iff (Γ := 𝚷)
      (closure_cast (Nat.succ_add k s).symm hθ);
    simp [Polarity.quantItr_succ, ← ih, quote_cast (Nat.succ_add k s).symm];
  | 𝚷, s + 1, k, θ, hθ, v => by
    have ih := prenexSatisfied_quote_toPrenex_iff (Γ := 𝚺)
      (closure_cast (Nat.succ_add k s).symm hθ);
    simp [Polarity.quantItr_succ, ← ih, quote_cast (Nat.succ_add k s).symm];

theorem prenexSatisfied_quote_iff {Γ : Polarity} {s k : ℕ}
    (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty k) (v : Fin k → V) :
    PrenexSatisfied Γ s (matrixToVec v) (⌜φ.matrix.val⌝ : V) ↔ V ⊧/v φ.val :=
  prenexSatisfied_quote_toPrenex_iff φ.matrix.bounded v

lemma quote_toPrenex : ∀ {Γ : Polarity} {s n : ℕ} (θ : ArithmeticSemisentence (n + s)),
    (⌜θ.toPrenex Γ s⌝ : V) = qqToPrenex Γ s ⌜θ⌝
  | _, 0, _, _ => by simp
  | Γ, s + 1, n, θ => by
    cases Γ <;> simp [Polarity.quantItr_succ, quote_toPrenex, quote_cast (Nat.succ_add n s).symm]

theorem prenexTrue_quote_iff {Γ : Polarity} {s : ℕ} (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0) :
    PrenexTrue Γ s (⌜φ.val⌝ : V) ↔ V↓[ℒₒᵣ] ⊧ φ.val := by
  have h := prenexSatisfied_quote_iff (V := V) φ ![];
  rw [matrixToVec_nil] at h;
  simpa [PrenexTrue, Bounding.Prenex.val, quote_toPrenex, models_iff] using h

theorem _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_prenexTrue_iff {Γ : Polarity} {s : ℕ}
    [NeZero s] (φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0) :
    𝗜𝚺₁ ⊢ (prenexTrue Γ s).val/[⌜φ.val⌝] 🡘 φ.val :=
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ by
    cases Γ <;> simpa [models_iff, (PrenexTrue.sigma_defined s).df,
      (PrenexTrue.pi_defined s).df] using prenexTrue_quote_iff φ

section prenex

variable {Γ : Polarity} {s : ℕ} [NeZero s] {σ : ArithmeticSentence}

theorem provable_prenexTrue_iff_of_hierarchy (T : ArithmeticTheory) [𝗕𝚺s ⪯ T] [𝗜𝚺₁ ⪯ T]
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s σ) :
    ∃ φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0,
      T ⊢ σ 🡘 φ.val ∧ T ⊢ (prenexTrue Γ s).val/[⌜φ.val⌝] 🡘 σ := by
  obtain ⟨φ, hφ⟩ := exists_prenex_of_hierarchy T h;
  have h₁ : T ⊢ σ 🡘 φ.val := hφ;
  have h₂ : T ⊢ (prenexTrue Γ s).val/[⌜φ.val⌝] 🡘 φ.val :=
    Entailment.WeakerThan.pbl (ISigma1.provable_prenexTrue_iff φ);
  exact ⟨φ, h₁, by cl_prover [h₁, h₂]⟩

lemma _root_.FFL.FirstOrder.Arithmetic.Peano.provable_prenexTrue_iff_of_hierarchy
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s σ) :
    ∃ φ : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0,
      𝗣𝗔 ⊢ σ 🡘 φ.val ∧ 𝗣𝗔 ⊢ (prenexTrue Γ s).val/[⌜φ.val⌝] 🡘 σ :=
  Bootstrapping.provable_prenexTrue_iff_of_hierarchy 𝗣𝗔 h

lemma _root_.FFL.FirstOrder.Arithmetic.ISigma1.provable_prenexTrue_iff_of_hierarchy
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ 1 σ) :
    ∃ φ : ℬ[<, ℒₒᵣ].Prenex Γ 1 Empty 0,
      𝗜𝚺₁ ⊢ σ 🡘 φ.val ∧ 𝗜𝚺₁ ⊢ (prenexTrue Γ 1).val/[⌜φ.val⌝] 🡘 σ :=
  Bootstrapping.provable_prenexTrue_iff_of_hierarchy 𝗜𝚺₁ h

theorem provable_boundedTrue_iff_of_hierarchy (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T]
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ 0 σ) : T ⊢ boundedTrue.val/[⌜σ⌝] 🡘 σ :=
  Entailment.WeakerThan.pbl <|
    ISigma1.provable_boundedTrue_iff (Bounding.Hierarchy.zero_iff_bounded.mp h)

end prenex

end FFL.FirstOrder.Arithmetic.Bootstrapping
