module

public import Foundation.FirstOrder.SetTheory.Definability.Definable

/-!
# Bounded definability in a bounding hierarchy
-/

@[expose] public section

namespace FFL.FirstOrder

variable {V : Type*} [SetStructure V]

namespace SetTheory

variable {k l : ℕ}

class Bounded (f : (Fin k → V) → V) : Prop where
  bounded : ∃ i : Fin k, ∀ v, f v ⊆ v i

abbrev Bounded₁ (f : V → V) : Prop :=
  Bounded (fun v : Fin 1 → V ↦ f (v 0))

abbrev Bounded₂ (f : V → V → V) : Prop :=
  Bounded (fun v : Fin 2 → V ↦ f (v 0) (v 1))

abbrev Bounded₃ (f : V → V → V → V) : Prop :=
  Bounded (fun v : Fin 3 → V ↦ f (v 0) (v 1) (v 2))

def DefinableBoundedFunction {k} (f : (Fin k → V) → V) :=
  Bounded f ∧ 𝚺ᴸ₀.ExtDefinedFunction f

abbrev DefinableBoundedFunction₁ (f : V → V) : Prop :=
  DefinableBoundedFunction (k := 1) (fun v => f (v 0))

abbrev DefinableBoundedFunction₂ (f : V → V → V) : Prop :=
  DefinableBoundedFunction (k := 2) (fun v => f (v 0) (v 1))

abbrev DefinableBoundedFunction₃ (f : V → V → V → V) : Prop :=
  DefinableBoundedFunction (k := 3) (fun v => f (v 0) (v 1) (v 2))

lemma DefinableBoundedFunction.bounded {f : (Fin k → V) → V} (h : DefinableBoundedFunction f) :
    Bounded f := h.1

lemma DefinableBoundedFunction₁.bounded {f : V → V} (h : DefinableBoundedFunction₁ f) :
    Bounded₁ f := h.1

lemma DefinableBoundedFunction₂.bounded {f : V → V → V} (h : DefinableBoundedFunction₂ f) :
    Bounded₂ f := h.1

lemma DefinableBoundedFunction₃.bounded {f : V → V → V → V} (h : DefinableBoundedFunction₃ f) :
    Bounded₃ f := h.1

variable {ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol}

lemma DefinableBoundedFunction.definable {f : (Fin k → V) → V} (h : DefinableBoundedFunction f) :
    ℌ.ExtDefinedFunction f := .of_zero h.2

lemma DefinableBoundedFunction₁.definable {f : V → V} (h : DefinableBoundedFunction₁ f) :
    ℌ.ExtDefinedFunction (fun v : Fin 1 → V ↦ f (v 0)) := .of_zero h.2

lemma DefinableBoundedFunction₂.definable {f : V → V → V} (h : DefinableBoundedFunction₂ f) :
    ℌ.ExtDefinedFunction (fun v : Fin 2 → V ↦ f (v 0) (v 1)) := .of_zero h.2

lemma DefinableBoundedFunction₃.definable {f : V → V → V → V} (h : DefinableBoundedFunction₃ f) :
    ℌ.ExtDefinedFunction (fun v : Fin 3 → V ↦ f (v 0) (v 1) (v 2)) := .of_zero h.2

end SetTheory

namespace Bounding.HierarchySymbol

open SetTheory

variable {ℌ : ℬ[∈, ℒₛₑₜ].HierarchySymbol}

namespace Definable

/-- refer to the proof of `arithmetic_ball_blt` in Arithmetic/Definability/BoundedDefinable.lean -/
lemma lévy_ball_mem {k} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∀ x ∈ f v, P v x := sorry

lemma lévy_bexs_mem {k} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) :
    ℌ.Definable fun v ↦ ∃ x ∈ f v, P v x := sorry

variable {k} {P : (Fin k → V) → Prop}
/-- refer to the proof of `arithmetic_bounded_substitution` -/
lemma lévy_bounded_substitution {l} {f : Fin k → (Fin l → V) → V}
    (hP : ℌ.Definable P) (hf : ∀ i, DefinableBoundedFunction (f i)) :
    ℌ.Definable fun z ↦ P (f · z) := sorry

lemma lévy_bounded_comp₁ {k} {P : V → Prop} {f : (Fin k → V) → V}
    [hP : ℌ.DefinablePred P]
    (hf : DefinableBoundedFunction f) :
    ℌ.Definable fun v ↦ P (f v) := sorry

lemma lévy_bounded_comp₂ {k} {R : V → V → Prop} {f₁ f₂ : (Fin k → V) → V}
    [hR : ℌ.DefinableRel R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    ℌ.Definable fun v ↦ R (f₁ v) (f₂ v) := sorry

lemma lévy_bounded_comp₃ {k} {R : V → V → V → Prop}
    {f₁ f₂ f₃ : (Fin k → V) → V}
    [hR : ℌ.DefinableRel₃ R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    ℌ.Definable fun v ↦ R (f₁ v) (f₂ v) (f₃ v) := sorry

lemma lévy_bounded_comp₄ {k} {R : V → V → V → V → Prop}
    {f₁ f₂ f₃ f₄ : (Fin k → V) → V} [hR : ℌ.DefinableRel₄ R]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) (hf₄ : DefinableBoundedFunction f₄) :
    ℌ.Definable fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v) := sorry

end Definable

variable {k l : ℕ}

lemma DefinableFunction.lévy_bounded_comp {k} {F : (Fin l → V) → V}
    {f : Fin l → (Fin k → V) → V}
    (hF : ℌ.DefinableFunction F) (hf : ∀ i, DefinableBoundedFunction (f i)) :
    ℌ.DefinableFunction (fun v ↦ F (f · v)) := sorry

lemma DefinableFunction₁.lévy_bounded_comp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₁ F) (hf : DefinableBoundedFunction f) :
    ℌ.DefinableFunction (fun v ↦ F (f v)) := sorry

lemma DefinableFunction₂.lévy_bounded_comp {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₂ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    ℌ.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v)) := sorry

lemma DefinableFunction₃.lévy_bounded_comp {k} {F : V → V → V → V}
    {f₁ f₂ f₃ : (Fin k → V) → V}
    (hF : ℌ.DefinableFunction₃ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    ℌ.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) := sorry

end Bounding.HierarchySymbol

namespace SetTheory

open Bounding.HierarchySymbol

lemma DefinableBoundedFunction₁.comp {k} {F : V → V} {f : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₁ F) (hf : DefinableBoundedFunction f) :
    DefinableBoundedFunction (fun v ↦ F (f v)) := sorry

lemma DefinableBoundedFunction₂.comp {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₂ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) := sorry

lemma DefinableBoundedFunction₃.comp {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    (hF : DefinableBoundedFunction₃ F)
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) := sorry

lemma DefinableBoundedFunction.comp₁ {k} {F : V → V} {f : (Fin k → V) → V}
    [hFb : Bounded₁ F] [hFd : 𝚺ᴸ₀.DefinableFunction₁ F]
    (hf : DefinableBoundedFunction f) :
    DefinableBoundedFunction (fun v ↦ F (f v)) := DefinableBoundedFunction₁.comp ⟨hFb, hFd⟩ hf

lemma DefinableBoundedFunction.comp₂ {k} {F : V → V → V} {f₁ f₂ : (Fin k → V) → V}
    [hFb : Bounded₂ F] [hFd : 𝚺ᴸ₀.DefinableFunction₂ F]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  DefinableBoundedFunction₂.comp ⟨hFb, hFd⟩ hf₁ hf₂

lemma DefinableBoundedFunction.comp₃ {k} {F : V → V → V → V} {f₁ f₂ f₃ : (Fin k → V) → V}
    [hFb : Bounded₃ F] [hFd : 𝚺ᴸ₀.DefinableFunction₃ F]
    (hf₁ : DefinableBoundedFunction f₁) (hf₂ : DefinableBoundedFunction f₂)
    (hf₃ : DefinableBoundedFunction f₃) :
    DefinableBoundedFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  DefinableBoundedFunction₃.comp ⟨hFb, hFd⟩ hf₁ hf₂ hf₃

section

attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableBoundedFunction.comp₁
  DefinableBoundedFunction.comp₂
  DefinableBoundedFunction.comp₃

attribute [aesop 6 (rule_sets := [Definability]) safe]
  Definable.lévy_bounded_comp₁
  Definable.lévy_bounded_comp₂
  Definable.lévy_bounded_comp₃
  Definable.lévy_bounded_comp₄

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Definable.lévy_ball_mem
  Definable.lévy_bexs_mem

section test

example (c : V) : DefinableBoundedFunction₂ (fun x y : V ↦ x) := by definability

example {ex : V → V} [h : 𝚫ᴸ₁.DefinableFunction₁ ex] :
    𝚺ᴸ₁.DefinableRel (fun x y : V ↦ ∃ z, x ∈ y ↔ ex (ex (ex (ex x))) = z) := by
  definability

example {ex : V → V} [h : 𝚺ᴸ₁.DefinableFunction₁ ex] :
    𝚺ᴸ₁.DefinableRel (fun x y : V ↦ ∀ z ∈ ex y, x ∈ y ↔ ex (ex x) = z) := by
  definability

end test

end

end SetTheory

end FFL.FirstOrder
