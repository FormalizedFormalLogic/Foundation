module

public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic

/-!
# Arithmetical definability
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.HierarchySymbol

open FFL.FirstOrder.Arithmetic
open PeanoMinus
open FFL.FirstOrder.Semiformula (Operator)
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

namespace DefinableRel

@[simp] instance arithmetic_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableRel (LE.le : V → V → Prop) :=
  Defined.to_definable₀
    (φ := .mkSigma “#0 ≤ #1” (by simp)) ⟨by intro _; simp⟩

end DefinableRel

namespace DefinableFunction₂

@[simp] instance arithmetic_add {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ ((· + ·) : V → V → V) :=
  Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 + #2” (by simp)) ⟨by intro _; simp⟩

@[simp] instance arithmetic_mul {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ ((· * ·) : V → V → V) :=
  Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #2” (by simp)) ⟨by intro _; simp⟩

@[simp] instance arithmetic_hAdd {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ (HAdd.hAdd : V → V → V) := arithmetic_add

@[simp] instance arithmetic_hMul {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₂ (HMul.hMul : V → V → V) := arithmetic_mul

end DefinableFunction₂

namespace DefinableFunction₁

@[simp] protected instance arithmetic_sq [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 2 :=
  Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1” (by simp)) ⟨by intro _; simp [sq]⟩

@[simp] instance arithmetic_pow3 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 3 :=
  Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1 * #1” (by simp))
    ⟨by intro _; simp [Arithmetic.pow_three]⟩

@[simp] instance arithmetic_pow4 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} :
    ℌ.DefinableFunction₁ fun x : V ↦ x ^ 4 :=
  Defined.to_definable₀
    (φ := .mkSigma “#0 = #1 * #1 * #1 * #1” (by simp))
    ⟨by intro _; simp [pow_four]⟩

end DefinableFunction₁

namespace Definable

variable {k : ℕ} {Γ : SigmaPiDelta} {m : ℕ}

lemma arithmetic_ball {P : (Fin k → V) → V → Prop}
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P v x :=
  ball (R := Operator.LT.lt) (by rfl) h t

lemma arithmetic_bexs {P : (Fin k → V) → V → Prop}
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P v x :=
  bexs (R := Operator.LT.lt) (by rfl) h t

lemma arithmetic_ball' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x ≤ t.val v id, P v x :=
  (arithmetic_ball h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma arithmetic_bexs' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x ≤ t.val v id, P v x :=
  (arithmetic_bexs h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma arithmetic_ballCons {P : (Fin (k + 1) → V) → Prop}
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} (h : ℌ.Definable P)
    (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P (x :> v) :=
  arithmetic_ball (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma arithmetic_bexsCons {P : (Fin (k + 1) → V) → Prop}
    {ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]} (h : ℌ.Definable P)
    (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P (x :> v) :=
  arithmetic_bexs (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma arithmetic_ball_lt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∀ x < f v, P v x :=
  ball_operator (R := Operator.LT.lt) (by rfl) hf h

lemma arithmetic_bexs_lt {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γᴬ-[m + 1].Definable fun v ↦ ∃ x < f v, P v x :=
  bexs_operator (R := Operator.LT.lt) (by rfl) hf h

lemma arithmetic_ball_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ-[m + 1].Definable (fun v ↦ ∀ x ≤ f v, P v x) := by
  have h₁ : Γᴬ-[m + 1].Definable (fun v ↦ ∀ x < f v + 1, P v x) :=
    arithmetic_ball_lt (DefinableFunction₂.comp hf (.const 1)) h
  exact h₁.of_iff fun v ↦ by simp [lt_succ_iff_le]

lemma arithmetic_bexs_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺ᴬ-[m + 1].DefinableFunction f)
    (h : Γᴬ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ-[m + 1].Definable (fun v ↦ ∃ x ≤ f v, P v x) := by
  have h₁ : Γᴬ-[m + 1].Definable (fun v ↦ ∃ x < f v + 1, P v x) :=
    arithmetic_bexs_lt (DefinableFunction₂.comp hf (.const 1)) h
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
  apply sigma_succ_induction
    (motive := motive) pi and or ?_ ?_ exs k P hP
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using ball t hP ih
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using bexs t hP ih

attribute [aesop 8 (rule_sets := [Definability]) safe]
  arithmetic_ball_lt arithmetic_ball_le arithmetic_bexs_lt arithmetic_bexs_le

end Definable

end FFL.FirstOrder.Bounding.HierarchySymbol
