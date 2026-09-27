module

public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic

/-!
# Arithmetical definability

This module specializes the common definability API to the strict-order bounding on
the language of arithmetic.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.HierarchySymbol.DefinableRel

open FFL.FirstOrder.Arithmetic
open PeanoMinus
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

@[simp] instance arithmetic_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableRel (LE.le : V → V → Prop) :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 ≤ #1” (by simp)) ⟨by intro _; simp⟩

end FFL.FirstOrder.Bounding.HierarchySymbol.DefinableRel

namespace FFL.FirstOrder.Bounding.HierarchySymbol.DefinableFunction₂

open FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

@[simp] instance arithmetic_add {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ ((· + ·) : V → V → V) :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 + #2” (by simp)) ⟨by intro _; simp⟩

@[simp] instance arithmetic_mul {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ ((· * ·) : V → V → V) :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #2” (by simp)) ⟨by intro _; simp⟩

@[simp] instance arithmetic_hAdd {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ (HAdd.hAdd : V → V → V) := arithmetic_add

@[simp] instance arithmetic_hMul {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ (HMul.hMul : V → V → V) := arithmetic_mul

end FFL.FirstOrder.Bounding.HierarchySymbol.DefinableFunction₂

namespace FFL.FirstOrder.Bounding.HierarchySymbol.DefinableFunction₁

open FFL.FirstOrder.Arithmetic
open PeanoMinus
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

@[simp] protected instance arithmetic_sq [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 2 :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1” (by simp)) ⟨by intro _; simp [sq]⟩

@[simp] instance arithmetic_pow3 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 3 :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1 * #1” (by simp))
    ⟨by intro _; simp [Arithmetic.pow_three]⟩

@[simp] instance arithmetic_pow4 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 4 :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1 * #1 * #1” (by simp))
    ⟨by intro _; simp [pow_four]⟩

end FFL.FirstOrder.Bounding.HierarchySymbol.DefinableFunction₁

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Definable

open FFL.FirstOrder.Arithmetic
open PeanoMinus
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {k : ℕ} {Γ : SigmaPiDelta} {m : ℕ}

lemma arithmetic_ball {P : (Fin k → V) → V → Prop}
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P v x :=
  Bounding.HierarchySymbol.Definable.ball
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) h t

lemma arithmetic_bexs {P : (Fin k → V) → V → Prop}
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P v x :=
  Bounding.HierarchySymbol.Definable.bexs
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) h t

lemma arithmetic_ball' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x ≤ t.val v id, P v x :=
  (arithmetic_ball h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma arithmetic_bexs' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x ≤ t.val v id, P v x :=
  (arithmetic_bexs h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma arithmetic_ballCons {P : (Fin (k + 1) → V) → Prop}
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} (h : ℌ.Definable P)
    (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P (x :> v) :=
  arithmetic_ball (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma arithmetic_bexsCons {P : (Fin (k + 1) → V) → Prop}
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} (h : ℌ.Definable P)
    (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P (x :> v) :=
  arithmetic_bexs (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma arithmetic_ball_lt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∀ x < f v, P v x :=
  Bounding.HierarchySymbol.Definable.ball_operator
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) hf h

lemma arithmetic_bexs_lt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∃ x < f v, P v x :=
  Bounding.HierarchySymbol.Definable.bexs_operator
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) hf h

lemma arithmetic_ball_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ-[m + 1].Definable (fun v ↦ ∀ x ≤ f v, P v x) := by
  have h₁ : Γᴬ-[m + 1].Definable (fun v ↦ ∀ x < f v + 1, P v x) :=
    arithmetic_ball_lt (Bounding.HierarchySymbol.DefinableFunction₂.comp hf
      (Bounding.HierarchySymbol.DefinableFunction.const 1)) h
  exact h₁.of_iff fun v ↦ by simp [lt_succ_iff_le]

lemma arithmetic_bexs_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ-[m + 1].Definable (fun v ↦ ∃ x ≤ f v, P v x) := by
  have h₁ : Γᴬ-[m + 1].Definable (fun v ↦ ∃ x < f v + 1, P v x) :=
    arithmetic_bexs_lt (Bounding.HierarchySymbol.DefinableFunction₂.comp hf
      (Bounding.HierarchySymbol.DefinableFunction.const 1)) h
  exact h₁.of_iff fun v ↦ by simp [lt_succ_iff_le]

lemma arithmetic_ball_lt' {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∀ {x}, x < f v → P v x := arithmetic_ball_lt hf h

lemma arithmetic_ball_le' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∀ {x}, x ≤ f v → P v x := arithmetic_ball_le hf h

@[elab_as_elim]
theorem arithmetic_sigma_succ_induction
    {motive : (k : ℕ) → (P : (Fin k → V) → Prop) → 𝚺ᴬ-[m + 1].Definable P → Prop}
    (pi : ∀ {k} {P : (Fin k → V) → Prop} (hP : 𝚷ᴬ-[m].Definable P),
      motive k P (hP.of_lt (Nat.lt_succ_self m)))
    (and : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺ᴬ-[m + 1].Definable P) (hQ : 𝚺ᴬ-[m + 1].Definable Q),
      motive k P hP → motive k Q hQ → motive k (fun v ↦ P v ∧ Q v) (.and hP hQ))
    (or : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺ᴬ-[m + 1].Definable P) (hQ : 𝚺ᴬ-[m + 1].Definable Q),
      motive k P hP → motive k Q hQ → motive k (fun v ↦ P v ∨ Q v) (.or hP hQ))
    (ball : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (t : ArithmeticSemiterm V k)
      (hP : 𝚺ᴬ-[m + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∀ x < t.val v id, P (x :> v))
        (arithmetic_ballCons hP t))
    (bexs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (t : ArithmeticSemiterm V k)
      (hP : 𝚺ᴬ-[m + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∃ x < t.val v id, P (x :> v))
        (arithmetic_bexsCons hP t))
    (exs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (hP : 𝚺ᴬ-[m + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∃ x, P (x :> v)) (.exsCons hP))
    (k : ℕ) (P : (Fin k → V) → Prop) (hP : 𝚺ᴬ-[m + 1].Definable P) : motive k P hP := by
  apply Bounding.HierarchySymbol.Definable.sigma_succ_induction
    (motive := motive) pi and or ?_ ?_ exs k P hP
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using ball t hP ih
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using bexs t hP ih

attribute [aesop 8 (rule_sets := [Definability]) safe]
  arithmetic_ball_lt arithmetic_ball_le arithmetic_bexs_lt arithmetic_bexs_le

end FFL.FirstOrder.Bounding.HierarchySymbol.Definable
