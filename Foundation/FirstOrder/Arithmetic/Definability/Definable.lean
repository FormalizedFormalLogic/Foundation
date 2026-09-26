module

public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic

@[expose] public section
set_option autoImplicit true
namespace FFL.FirstOrder.Arithmetic

namespace HierarchySymbol

variable (ξ : Type*) (n : ℕ)

open PeanoMinus

variable {V : Type*} [ORingStructure V]

abbrev IsDefinedBy (R : (Fin k → V) → Prop) {ℌ : HierarchySymbol} (φ : ℌ.Semisentence k) : Prop :=
  Bounding.HierarchySymbol.IsDefinedBy R φ

abbrev IsDefinedByWithParam (R : (Fin k → V) → Prop) {ℌ : HierarchySymbol}
    (φ : ℌ.Semiformula V k) : Prop :=
  Bounding.HierarchySymbol.IsDefinedByWithParam R φ

abbrev Defined (R : (Fin k → V) → Prop) {ℌ : HierarchySymbol} (φ : ℌ.Semisentence k) :=
  Bounding.HierarchySymbol.Defined R φ

variable {ℌ : HierarchySymbol} {Γ : SigmaPiDelta}

variable (ℌ)

abbrev Definable {k} (P : (Fin k → V) → Prop) : Prop :=
  Bounding.HierarchySymbol.Definable ℬ[<, ℒₒᵣ] ℌ P

abbrev DefinedPred (P : V → Prop) (φ : ℌ.Semisentence 1) : Prop :=
  Defined (fun v ↦ P (v 0)) φ

abbrev DefinedRel (R : V → V → Prop) (φ : ℌ.Semisentence 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ

abbrev DefinedRel₃ (R : V → V → V → Prop) (φ : ℌ.Semisentence 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ

abbrev DefinedRel₄ (R : V → V → V → V → Prop) (φ : ℌ.Semisentence 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ

variable {ℌ}

abbrev DefinedFunction {k} (f : (Fin k → V) → V) (φ : ℌ.Semisentence (k + 1)) : Prop :=
  Bounding.HierarchySymbol.DefinedFunction f φ

namespace DefinedFunction

lemma graph_delta [Semiformula.Operator.Eq ℒₒᵣ] [Tarski.Structure.Eq ℒₒᵣ V]
    {k} {f : (Fin k → V) → V} {m} {φ : 𝚺-[m].Semisentence (k + 1)}
    (h : DefinedFunction (ℌ := 𝚺-[m]) f φ) :
    DefinedFunction (ℌ := 𝚫-[m]) f φ.graphDelta :=
  Bounding.HierarchySymbol.DefinedFunction.graph_delta (ℬ := ℬ[<, ℒₒᵣ]) h

end DefinedFunction

variable (ℌ)

abbrev DefinedFunction₀ (c : V) (φ : ℌ.Semisentence 1) : Prop :=
  DefinedFunction (fun _ => c) φ

abbrev DefinedFunction₁ (f : V → V) (φ : ℌ.Semisentence 2) : Prop :=
  DefinedFunction (fun v => f (v 0)) φ

abbrev DefinedFunction₂ (f : V → V → V) (φ : ℌ.Semisentence 3) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1)) φ

abbrev DefinedFunction₃ (f : V → V → V → V) (φ : ℌ.Semisentence 4) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2)) φ

abbrev DefinedFunction₄ (f : V → V → V → V → V) (φ : ℌ.Semisentence 5) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3)) φ

abbrev DefinedFunction₅ (f : V → V → V → V → V → V) (φ : ℌ.Semisentence 6) : Prop :=
  DefinedFunction (fun v => f (v 0) (v 1) (v 2) (v 3) (v 4)) φ

abbrev DefinablePred (P : V → Prop) : Prop := Bounding.HierarchySymbol.DefinablePred ℬ[<, ℒₒᵣ] ℌ P

abbrev DefinableRel (P : V → V → Prop) : Prop := Bounding.HierarchySymbol.DefinableRel ℬ[<, ℒₒᵣ] ℌ P

abbrev DefinableRel₃ (P : V → V → V → Prop) : Prop := Bounding.HierarchySymbol.DefinableRel₃ ℬ[<,
  ℒₒᵣ] ℌ P

abbrev DefinableRel₄ (P : V → V → V → V → Prop) : Prop :=
  Bounding.HierarchySymbol.DefinableRel₄ ℬ[<, ℒₒᵣ] ℌ P

abbrev DefinableRel₅ (P : V → V → V → V → V → Prop) : Prop :=
  Bounding.HierarchySymbol.DefinableRel₅ ℬ[<, ℒₒᵣ] ℌ P

abbrev DefinableRel₆ (P : V → V → V → V → V → V → Prop) : Prop :=
  Bounding.HierarchySymbol.DefinableRel₆ ℬ[<, ℒₒᵣ] ℌ P

abbrev DefinableFunction (f : (Fin k → V) → V) : Prop :=
  Bounding.HierarchySymbol.DefinableFunction ℬ[<, ℒₒᵣ] ℌ f

abbrev DefinableFunction₀ (c : V) : Prop :=
  Bounding.HierarchySymbol.DefinableFunction ℬ[<, ℒₒᵣ] ℌ (fun _ : Fin 0 → V ↦ c)

abbrev DefinableFunction₁ (f : V → V) : Prop :=
  Bounding.HierarchySymbol.DefinableFunction ℬ[<, ℒₒᵣ] ℌ (fun v : Fin 1 → V ↦ f (v 0))

abbrev DefinableFunction₂ (f : V → V → V) : Prop :=
  Bounding.HierarchySymbol.DefinableFunction ℬ[<, ℒₒᵣ] ℌ (fun v : Fin 2 → V ↦ f (v 0) (v 1))

abbrev DefinableFunction₃ (f : V → V → V → V) : Prop :=
  Bounding.HierarchySymbol.DefinableFunction ℬ[<, ℒₒᵣ] ℌ (fun v : Fin 3 → V ↦ f (v 0) (v 1) (v 2))

abbrev DefinableFunction₄ (f : V → V → V → V → V) : Prop :=
  Bounding.HierarchySymbol.DefinableFunction ℬ[<,
    ℒₒᵣ] ℌ (fun v : Fin 4 → V ↦ f (v 0) (v 1) (v 2) (v 3))

abbrev DefinableFunction₅ (f : V → V → V → V → V → V) : Prop :=
  Bounding.HierarchySymbol.DefinableFunction ℬ[<,
    ℒₒᵣ] ℌ (fun v : Fin 5 → V ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))

variable {ℌ}

notation Γ "-Predicate " P " via " φ => DefinedPred Γ P φ

notation Γ "-Relation " P " via " φ => DefinedRel Γ P φ

notation Γ "-Relation₃ " P " via " φ => DefinedRel₃ Γ P φ

notation Γ "-Relation₄ " P " via " φ => DefinedRel₄ Γ P φ

notation Γ "-Function₀ " c " via " φ => DefinedFunction₀ Γ c φ

notation Γ "-Function₁ " f " via " φ => DefinedFunction₁ Γ f φ

notation Γ "-Function₂ " f " via " φ => DefinedFunction₂ Γ f φ

notation Γ "-Function₃ " f " via " φ => DefinedFunction₃ Γ f φ

notation Γ "-Function₄ " f " via " φ => DefinedFunction₄ Γ f φ

notation Γ "-Function₅ " f " via " φ => DefinedFunction₅ Γ f φ

notation Γ "-Predicate " P => DefinablePred Γ P

notation Γ "-Relation " P => DefinableRel Γ P

notation Γ "-Relation₃ " P => DefinableRel₃ Γ P

notation Γ "-Relation₄ " P => DefinableRel₄ Γ P

notation Γ "-Relation₅ " P => DefinableRel₅ Γ P

notation Γ "-Function₁ " f => DefinableFunction₁ Γ f

notation Γ "-Function₂ " f => DefinableFunction₂ Γ f

notation Γ "-Function₃ " f => DefinableFunction₃ Γ f

notation Γ "-Function₄ " f => DefinableFunction₄ Γ f


notation Γ "-Predicate[" V "] " P " via " φ => DefinedPred (V := V) Γ P φ

notation Γ "-Relation[" V "] " P " via " φ => DefinedRel (V := V) Γ P φ

notation Γ "-Relation₃[" V "] " P " via " φ => DefinedRel₃ (V := V) Γ P φ

notation Γ "-Relation₄[" V "] " P " via " φ => DefinedRel₄ (V := V) Γ P φ

notation Γ "-Function₀[" V "] " c " via " φ => DefinedFunction₀ (V := V) Γ c φ

notation Γ "-Function₁[" V "] " f " via " φ => DefinedFunction₁ (V := V) Γ f φ

notation Γ "-Function₂[" V "] " f " via " φ => DefinedFunction₂ (V := V) Γ f φ

notation Γ "-Function₃[" V "] " f " via " φ => DefinedFunction₃ (V := V) Γ f φ

notation Γ "-Function₄[" V "] " f " via " φ => DefinedFunction₄ (V := V) Γ f φ

notation Γ "-Function₅[" V "] " f " via " φ => DefinedFunction₅ (V := V) Γ f φ

notation Γ "-Predicate[" V "] " P => DefinablePred (V := V) Γ P

notation Γ "-Relation[" V "] " P => DefinableRel (V := V) Γ P

notation Γ "-Relation₃[" V "] " P => DefinableRel₃ (V := V) Γ P

notation Γ "-Relation₄[" V "] " P => DefinableRel₄ (V := V) Γ P

notation Γ "-Relation₅[" V "] " P => DefinableRel₅ (V := V) Γ P

notation Γ "-Function₁[" V "] " f => DefinableFunction₁ (V := V) Γ f

notation Γ "-Function₂[" V "] " f => DefinableFunction₂ (V := V) Γ f

notation Γ "-Function₃[" V "] " f => DefinableFunction₃ (V := V) Γ f

notation Γ "-Function₄[" V "] " f => DefinableFunction₄ (V := V) Γ f

variable {k} {P Q : (Fin k → V) → Prop}

namespace DefinableRel

@[simp] instance le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {ℌ : HierarchySymbol} : ℌ.DefinableRel (LE.le : V
  → V → Prop) :=
  Bounding.HierarchySymbol.Defined.to_definable₀ (φ := .mkSigma “#0 ≤ #1” (by simp))
    ⟨by intro _; simp⟩

end DefinableRel

namespace DefinableFunction₂

@[simp] instance add {ℌ : HierarchySymbol} : ℌ.DefinableFunction₂ ((· + ·) : V → V → V) :=
  Bounding.HierarchySymbol.Defined.to_definable₀ (φ := .mkSigma “#0 = #1 + #2” (by
    simp)) ⟨by intro _; simp⟩

@[simp] instance mul {ℌ : HierarchySymbol} : ℌ.DefinableFunction₂ ((· * ·) : V → V → V) :=
  Bounding.HierarchySymbol.Defined.to_definable₀ (φ := .mkSigma “#0 = #1 * #2” (by
    simp)) ⟨by intro _; simp⟩

@[simp] instance hAdd {ℌ : HierarchySymbol} : ℌ.DefinableFunction₂ (HAdd.hAdd : V → V → V) := add

@[simp] instance hMul {ℌ : HierarchySymbol} : ℌ.DefinableFunction₂ (HMul.hMul : V → V → V) := mul

@[simp] protected instance sq [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {ℌ : HierarchySymbol} :
    ℌ.DefinableFunction₁ fun x : V ↦ x^2 :=
  Bounding.HierarchySymbol.Defined.to_definable₀ (φ := .mkSigma “#0 = #1 * #1” (by
    simp)) ⟨by intro _; simp [sq]⟩

@[simp] instance pow3 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {ℌ : HierarchySymbol} :
    ℌ.DefinableFunction₁ fun x : V ↦ x^3 :=
  Bounding.HierarchySymbol.Defined.to_definable₀ (φ := .mkSigma “#0 = #1 * #1 * #1”
    (by simp)) ⟨by intro _; simp [Arithmetic.pow_three]⟩

@[simp] instance pow4 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {ℌ : HierarchySymbol} :
    ℌ.DefinableFunction₁ fun x : V ↦ x^4 :=
  Bounding.HierarchySymbol.Defined.to_definable₀ (φ := .mkSigma “#0 = #1 * #1 * #1 *
    #1” (by simp)) ⟨by intro _; simp [pow_four]⟩

end DefinableFunction₂

namespace DefinableFunction₃

lemma comp [Semiformula.Operator.Eq ℒₒᵣ] [Tarski.Structure.Eq ℒₒᵣ V]
    {Γ : SigmaPiDelta} {m} {k} {F : V → V → V → V}
    {f g h : (Fin k → V) → V} [Γ-[m + 1].DefinableFunction₃ F]
    (hf : 𝚺-[m + 1].DefinableFunction f) (hg : 𝚺-[m + 1].DefinableFunction g)
    (hh : 𝚺-[m + 1].DefinableFunction h) :
    Γ-[m + 1].DefinableFunction fun v ↦ F (f v) (g v) (h v) :=
  Bounding.HierarchySymbol.DefinableFunction₃.comp (ℬ := ℬ[<, ℒₒᵣ]) hf hg hh

end DefinableFunction₃

namespace DefinableFunction₄

lemma comp [Semiformula.Operator.Eq ℒₒᵣ] [Tarski.Structure.Eq ℒₒᵣ V]
    {Γ : SigmaPiDelta} {m} {k} {F : V → V → V → V → V}
    {f g h i : (Fin k → V) → V} [Γ-[m + 1].DefinableFunction₄ F]
    (hf : 𝚺-[m + 1].DefinableFunction f) (hg : 𝚺-[m + 1].DefinableFunction g)
    (hh : 𝚺-[m + 1].DefinableFunction h) (hi : 𝚺-[m + 1].DefinableFunction i) :
    Γ-[m + 1].DefinableFunction fun v ↦ F (f v) (g v) (h v) (i v) :=
  Bounding.HierarchySymbol.DefinableFunction₄.comp (ℬ := ℬ[<, ℒₒᵣ]) hf hg hh hi

end DefinableFunction₄

namespace Definable

lemma and {Γ : SigmaPiDelta} {m} {P Q : (Fin k → V) → Prop}
    (hP : Γ-[m].Definable P) (hQ : Γ-[m].Definable Q) : Γ-[m].Definable fun v ↦ P v ∧ Q v :=
  Bounding.HierarchySymbol.Definable.and (ℬ := ℬ[<, ℒₒᵣ]) hP hQ

lemma or {Γ : SigmaPiDelta} {m} {P Q : (Fin k → V) → Prop}
    (hP : Γ-[m].Definable P) (hQ : Γ-[m].Definable Q) : Γ-[m].Definable fun v ↦ P v ∨ Q v :=
  Bounding.HierarchySymbol.Definable.or (ℬ := ℬ[<, ℒₒᵣ]) hP hQ

lemma exs {P : (Fin k → V) → V → Prop} {m}
    (h : 𝚺-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    𝚺-[m + 1].Definable fun v ↦ ∃ x, P v x :=
  Bounding.HierarchySymbol.Definable.exs (ℬ := ℬ[<, ℒₒᵣ]) h

lemma comp₁ {Γ : SigmaPiDelta} {m} {P : V → Prop} {f : (Fin k → V) → V}
    [Γ-[m + 1].DefinablePred P] (hf : 𝚺-[m + 1].DefinableFunction f) :
    Γ-[m + 1].Definable fun v ↦ P (f v) :=
  Bounding.HierarchySymbol.Definable.comp₁ (ℬ := ℬ[<, ℒₒᵣ]) hf

lemma imp {Γ : SigmaPiDelta} {m} {P Q : (Fin k → V) → Prop}
    (hP : Γ.alt-[m].Definable P) (hQ : Γ-[m].Definable Q) :
    Γ-[m].Definable fun v ↦ P v → Q v :=
  Bounding.HierarchySymbol.Definable.imp (ℬ := ℬ[<, ℒₒᵣ]) hP hQ

lemma comp₂ {Γ : SigmaPiDelta} {m} {P : V → V → Prop}
    [Γ-[m + 1].DefinableRel P] {f g : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (hg : 𝚺-[m + 1].DefinableFunction g) :
    Γ-[m + 1].Definable fun v ↦ P (f v) (g v) :=
  Bounding.HierarchySymbol.Definable.comp₂ (ℬ := ℬ[<, ℒₒᵣ]) hf hg

lemma comp₃ {Γ : SigmaPiDelta} {m} {P : V → V → V → Prop}
    [Γ-[m + 1].DefinableRel₃ P] {f g h : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (hg : 𝚺-[m + 1].DefinableFunction g)
    (hh : 𝚺-[m + 1].DefinableFunction h) :
    Γ-[m + 1].Definable fun v ↦ P (f v) (g v) (h v) :=
  Bounding.HierarchySymbol.Definable.comp₃ (ℬ := ℬ[<, ℒₒᵣ]) hf hg hh

lemma comp₄ {Γ : SigmaPiDelta} {m} {P : V → V → V → V → Prop}
    [Γ-[m + 1].DefinableRel₄ P] {f g h i : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (hg : 𝚺-[m + 1].DefinableFunction g)
    (hh : 𝚺-[m + 1].DefinableFunction h) (hi : 𝚺-[m + 1].DefinableFunction i) :
    Γ-[m + 1].Definable fun v ↦ P (f v) (g v) (h v) (i v) :=
  Bounding.HierarchySymbol.Definable.comp₄ (ℬ := ℬ[<, ℒₒᵣ]) hf hg hh hi

lemma ball {P : (Fin k → V) → V → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P v x :=
  Bounding.HierarchySymbol.Definable.ball (ℬ := ℬ[<, ℒₒᵣ]) (R := Semiformula.Operator.LT.lt)
    (by rfl) h t

lemma bexs {P : (Fin k → V) → V → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P v x :=
  Bounding.HierarchySymbol.Definable.bexs (ℬ := ℬ[<, ℒₒᵣ]) (R := Semiformula.Operator.LT.lt)
    (by rfl) h t

lemma ball' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {P : (Fin k → V) → V → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x ≤ t.val v id, P v x :=
  (ball h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma bexs' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {P : (Fin k → V) → V → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable fun w ↦ P (w ·.succ) (w 0)) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x ≤ t.val v id, P v x :=
  (bexs h ‘!!t + 1’).of_iff fun _ ↦ by simp [lt_succ_iff_le]

lemma ballCons {P : (Fin (k + 1) → V) → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable P) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∀ x < t.val v id, P (x :> v) :=
  ball (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma bexsCons {P : (Fin (k + 1) → V) → Prop} {ℌ : HierarchySymbol}
    (h : ℌ.Definable P) (t : ArithmeticSemiterm V k) :
    ℌ.Definable fun v ↦ ∃ x < t.val v id, P (x :> v) :=
  bexs (P := fun v x ↦ P (x :> v)) (h.of_iff fun _ ↦ by simp) t

lemma ball_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[m + 1].Definable fun v ↦ ∀ x < f v, P v x :=
  Bounding.HierarchySymbol.Definable.ball_operator (ℬ := ℬ[<,
    ℒₒᵣ]) (R := Semiformula.Operator.LT.lt)
    (by rfl) hf h

lemma bexs_lt {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[m + 1].Definable fun v ↦ ∃ x < f v, P v x :=
  Bounding.HierarchySymbol.Definable.bexs_operator (ℬ := ℬ[<,
    ℒₒᵣ]) (R := Semiformula.Operator.LT.lt)
    (by rfl) hf h

lemma ball_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Definable (fun v ↦ ∀ x ≤ f v, P v x) := by
  have : Γ-[m + 1].Definable (fun v ↦ ∀ x < f v + 1,
    P v x) := ball_lt (Bounding.HierarchySymbol.DefinableFunction₂.comp hf
      (Bounding.HierarchySymbol.DefinableFunction.const 1)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma bexs_le [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γ-[m + 1].Definable (fun v ↦ ∃ x ≤ f v, P v x) := by
  have : Γ-[m + 1].Definable (fun v ↦ ∃ x < f v + 1,
    P v x) := bexs_lt (Bounding.HierarchySymbol.DefinableFunction₂.comp hf
      (Bounding.HierarchySymbol.DefinableFunction.const 1)) h
  exact this.of_iff <| by intro v; simp [lt_succ_iff_le]

lemma ball_lt' {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[m + 1].Definable fun v ↦ ∀ {x}, x < f v → P v x := ball_lt hf h

lemma ball_le' [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {Γ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : 𝚺-[m + 1].DefinableFunction f) (h : Γ-[m + 1].Definable fun w ↦ P (w ·.succ) (w 0)) :
    Γ-[m + 1].Definable fun v ↦ ∀ {x}, x ≤ f v → P v x := ball_le hf h

end Definable

namespace DefinableFunction

variable {ℌ : HierarchySymbol}

lemma var {k} [Semiformula.Operator.Eq ℒₒᵣ] [Tarski.Structure.Eq ℒₒᵣ V] (i : Fin k) :
    ℌ.DefinableFunction (fun v : Fin k → V ↦ v i) :=
  Bounding.HierarchySymbol.DefinableFunction.var (ℬ := ℬ[<, ℒₒᵣ]) i

lemma const {k} [Semiformula.Operator.Eq ℒₒᵣ] [Tarski.Structure.Eq ℒₒᵣ V] (c : V) :
    ℌ.DefinableFunction (fun _ : Fin k → V ↦ c) :=
  Bounding.HierarchySymbol.DefinableFunction.const (ℬ := ℬ[<, ℒₒᵣ]) c

end DefinableFunction

namespace DefinableFunction₁

lemma comp [Semiformula.Operator.Eq ℒₒᵣ] [Tarski.Structure.Eq ℒₒᵣ V] {Γ : SigmaPiDelta} {m} {k}
    {F : V → V} {f : (Fin k → V) → V} [Γ-[m + 1].DefinableFunction₁ F]
    (hf : 𝚺-[m + 1].DefinableFunction f) : Γ-[m + 1].DefinableFunction fun v ↦ F (f v) :=
  Bounding.HierarchySymbol.DefinableFunction₁.comp (ℬ := ℬ[<, ℒₒᵣ]) hf

end DefinableFunction₁

namespace DefinableFunction₂

lemma comp [Semiformula.Operator.Eq ℒₒᵣ] [Tarski.Structure.Eq ℒₒᵣ V] {Γ : SigmaPiDelta} {m} {k}
    {F : V → V → V} {f g : (Fin k → V) → V} [Γ-[m + 1].DefinableFunction₂ F]
    (hf : 𝚺-[m + 1].DefinableFunction f) (hg : 𝚺-[m + 1].DefinableFunction g) :
    Γ-[m + 1].DefinableFunction fun v ↦ F (f v) (g v) :=
  Bounding.HierarchySymbol.DefinableFunction₂.comp (ℬ := ℬ[<, ℒₒᵣ]) hf hg

end DefinableFunction₂

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Definable.ball_lt
  Definable.ball_le
  Definable.bexs_lt
  Definable.bexs_le

end HierarchySymbol

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s k : ℕ}

lemma definable_of_hierarchy {φ : ArithmeticSemiformula ℕ k} (hφ : Hierarchy Γ s φ) (e : ℕ → V) :
    Γ-[s].Definable fun v ↦ φ.Eval v e :=
  Bounding.definable_of_hierarchy (ℬ := ℬ[<, ℒₒᵣ]) hφ e

lemma definablePred_of_hierarchy {φ : ArithmeticSemiformula ℕ 1} (hφ : Hierarchy Γ s φ)
    (e : ℕ → V) : Γ-[s].DefinablePred fun x ↦ φ.Eval ![x] e :=
  Bounding.definablePred_of_hierarchy (ℬ := ℬ[<, ℒₒᵣ]) hφ e

lemma definableRel_of_hierarchy {φ : ArithmeticSemiformula ℕ 2} (hφ : Hierarchy Γ s φ)
    (e : ℕ → V) : Γ-[s].DefinableRel fun x y ↦ φ.Eval ![x, y] e :=
  Bounding.definableRel_of_hierarchy (ℬ := ℬ[<, ℒₒᵣ]) hφ e

namespace HierarchySymbol.Definable

@[elab_as_elim]
theorem sigma_succ_induction {V : Type*} [ORingStructure V] {s : ℕ}
    {motive : (k : ℕ) → (P : (Fin k → V) → Prop) → 𝚺-[s + 1].Definable P → Prop}
    (pi : ∀ {k} {P : (Fin k → V) → Prop} (hP : 𝚷-[s].Definable P),
      motive k P (hP.of_lt (Nat.lt_succ_self s)))
    (and : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺-[s + 1].Definable P)
      (hQ : 𝚺-[s + 1].Definable Q),
      motive k P hP → motive k Q hQ →
      motive k (fun v ↦ P v ∧ Q v) (.and hP hQ))
    (or : ∀ {k} {P Q : (Fin k → V) → Prop}
      (hP : 𝚺-[s + 1].Definable P)
      (hQ : 𝚺-[s + 1].Definable Q),
      motive k P hP → motive k Q hQ →
      motive k (fun v ↦ P v ∨ Q v) (.or hP hQ))
    (ball : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (t : ArithmeticSemiterm V k)
      (hP : 𝚺-[s + 1].Definable P),
      motive (k + 1) P hP →
      motive k (fun v ↦ ∀ x < t.val v id, P (x :> v)) (.ballCons hP t))
    (bexs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (t : ArithmeticSemiterm V k)
      (hP : 𝚺-[s + 1].Definable P),
      motive (k + 1) P hP →
      motive k (fun v ↦ ∃ x < t.val v id, P (x :> v)) (.bexsCons hP t))
    (exs : ∀ {k} {P : (Fin (k + 1) → V) → Prop} (hP : 𝚺-[s + 1].Definable P),
      motive (k + 1) P hP → motive k (fun v ↦ ∃ x, P (x :> v)) (.exsCons hP))
    (k : ℕ) (P : (Fin k → V) → Prop) (hP : 𝚺-[s + 1].Definable P) : motive k P hP := by
  apply Bounding.HierarchySymbol.Definable.sigma_succ_induction (motive := motive) pi
    and or ?_ ?_ exs k P hP
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using ball t hP ih
  · intro k R hR P t hP ih
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa using bexs t hP ih

end HierarchySymbol.Definable

end FFL.FirstOrder.Arithmetic
