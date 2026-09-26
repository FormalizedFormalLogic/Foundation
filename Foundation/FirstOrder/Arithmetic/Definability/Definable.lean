module

public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic

/-!
# Arithmetical definability

This module specializes the common definability API to the strict-order bounding on
the language of arithmetic.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical

open FFL.FirstOrder.Arithmetic
open PeanoMinus
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {k : ℕ}

namespace DefinableRel

@[simp] instance le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableRel (LE.le : V → V → Prop) :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 ≤ #1” (by simp)) ⟨by intro _; simp⟩

end DefinableRel

namespace DefinableFunction₂

@[simp] instance add {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ ((· + ·) : V → V → V) :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 + #2” (by simp)) ⟨by intro _; simp⟩

@[simp] instance mul {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ ((· * ·) : V → V → V) :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #2” (by simp)) ⟨by intro _; simp⟩

@[simp] instance hAdd {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ (HAdd.hAdd : V → V → V) := add

@[simp] instance hMul {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ (HMul.hMul : V → V → V) := mul

end DefinableFunction₂

namespace DefinableFunction₁

@[simp] protected instance sq [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 2 :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1” (by simp)) ⟨by intro _; simp [sq]⟩

@[simp] instance pow3 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 3 :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1 * #1” (by simp))
    ⟨by intro _; simp [Arithmetic.pow_three]⟩

@[simp] instance pow4 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 4 :=
  Bounding.HierarchySymbol.Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1 * #1 * #1” (by simp))
    ⟨by intro _; simp [pow_four]⟩

end DefinableFunction₁

end FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Definable

open FFL.FirstOrder.Arithmetic
open PeanoMinus
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {k : ℕ} {Γ : SigmaPiDelta} {m : ℕ}

lemma ball {P : (Fin k → V) → V → Prop} {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P v x :=
  Bounding.HierarchySymbol.Definable.ball
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) h t

lemma bexs {P : (Fin k → V) → V → Prop} {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P v x :=
  Bounding.HierarchySymbol.Definable.bexs
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) h t

lemma ball' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x ≤ t.val v id, P v x :=
  (ball h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma bexs' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x ≤ t.val v id, P v x :=
  (bexs h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma ballCons {P : (Fin (k + 1) → V) → Prop}
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} (h : ℌ.Definable P)
    (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P (x :> v) :=
  ball (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma bexsCons {P : (Fin (k + 1) → V) → Prop}
    {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]} (h : ℌ.Definable P)
    (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P (x :> v) :=
  bexs (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma ball_lt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∀ x < f v, P v x :=
  Bounding.HierarchySymbol.Definable.ball_operator
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) hf h

lemma bexs_lt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∃ x < f v, P v x :=
  Bounding.HierarchySymbol.Definable.bexs_operator
    (R := FFL.FirstOrder.Semiformula.Operator.LT.lt) (by rfl) hf h

lemma ball_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ-[m + 1].Definable (fun v ↦ ∀ x ≤ f v, P v x) := by
  have h₁ : Γᴬ-[m + 1].Definable (fun v ↦ ∀ x < f v + 1, P v x) :=
    ball_lt (Bounding.HierarchySymbol.DefinableFunction₂.comp hf
      (Bounding.HierarchySymbol.DefinableFunction.const 1)) h
  exact h₁.of_iff fun v ↦ by simp [lt_succ_iff_le]

lemma bexs_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ-[m + 1].Definable (fun v ↦ ∃ x ≤ f v, P v x) := by
  have h₁ : Γᴬ-[m + 1].Definable (fun v ↦ ∃ x < f v + 1, P v x) :=
    bexs_lt (Bounding.HierarchySymbol.DefinableFunction₂.comp hf
      (Bounding.HierarchySymbol.DefinableFunction.const 1)) h
  exact h₁.of_iff fun v ↦ by simp [lt_succ_iff_le]

lemma ball_lt' {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∀ {x}, x < f v → P v x := ball_lt hf h

lemma ball_le' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∀ {x}, x ≤ f v → P v x := ball_le hf h

@[elab_as_elim]
theorem sigma_succ_induction
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
        (ballCons hP t))
    (bexs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (t : ArithmeticSemiterm V k)
      (hP : 𝚺ᴬ-[m + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∃ x < t.val v id, P (x :> v))
        (bexsCons hP t))
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
  ball_lt ball_le bexs_lt bexs_le

end FFL.FirstOrder.Bounding.HierarchySymbol.Arithmetical.Definable
