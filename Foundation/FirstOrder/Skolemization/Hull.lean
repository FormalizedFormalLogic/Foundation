module

public import Foundation.FirstOrder.Basic
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section
/-! # Skolem hull -/

namespace LO.FirstOrder

/-- Skolem function of rank 1 -/
def Language.skolemFunction₁ (L : Language) : Language where
  Func k := Semisentence L (k + 1)
  Rel _ := PEmpty

abbrev Semisentence.skolem₁ {L : Language} (φ : Semisentence L (k + 1)) : L.skolemFunction₁.Func k := φ

instance (L : Language) [L.Encodable] : L.skolemFunction₁.Encodable where
  func k := inferInstanceAs (Encodable (Semisentence L (k + 1)))
  rel _ := inferInstanceAs (Encodable PEmpty)

namespace Structure

variable (L : Language.{u})

variable (M : Type v) [Nonempty M] [𝓼 : Structure L M]

noncomputable instance skolem : Structure L.skolemFunction₁ M where
  func _ φ v := Classical.epsilon fun z ↦ φ.Evalb (z :> v)
  rel _ r _ := PEmpty.elim r

variable {L M}

@[simp] lemma val_skolem_func (φ : Semisentence L (k + 1)) :
    (skolem L M).func φ.skolem₁ v = Classical.epsilon fun z ↦ φ.Evalb (z :> v) := rfl

variable (L)

/-- The Skolem hull of subset of structure. -/
def SkolemHull (s : Set M) : Set M := Set.range fun t : Term L.skolemFunction₁ s ↦ t.val ![] (↑)

variable (M)

abbrev SkolemHull₀ := SkolemHull L (M := M) ∅

variable {L M}

namespace SkolemHull

open Semiformula

variable {s : Set M}

lemma mem_iff :
    x ∈ SkolemHull L s ↔ ∃ t : Term L.skolemFunction₁ s, t.val ![] (↑) = x := by
  simp [SkolemHull]

@[simp] lemma val_mem (t : Term L.skolemFunction₁ s) : t.val ![] (↑) ∈ SkolemHull L s := by simp [SkolemHull]

lemma subset : s ⊆ SkolemHull L s := fun x hx ↦ by
  let t : Term L.skolemFunction₁ s := &⟨x, hx⟩
  have : x = t.val ![] (↑) := by simp [t]
  simp [this]

lemma closed {v : Fin k → M} (hv : ∀ i, v i ∈ SkolemHull L s)
    {φ : Semisentence L (k + 1)} (H : ∃ z, φ.Evalb (z :> v)) :
    ∃ z ∈ SkolemHull L s, φ.Evalb (z :> v) := by
  choose u hu using fun i ↦ mem_iff.mp (hv i)
  let t : Term L.skolemFunction₁ s := .func φ.skolem₁ u
  refine ⟨t.val ![] (↑), by simp, ?_⟩
  suffices φ.Evalb ((Classical.epsilon fun z ↦ φ.Evalb (z :> v)) :> v) by
    simpa [t, Semiterm.val_func, Function.comp_def, hu]
  exact Classical.epsilon_spec H

variable [L.Eq] [Structure.Eq L M]

lemma closed_func {v : Fin k → M} (hv : ∀ i, v i ∈ SkolemHull L s)
    {f : L.Func k} : Structure.func f v ∈ SkolemHull L s := by
  have : ∃ z ∈ SkolemHull L s, “#0 = !!(Semiterm.func f fun i ↦ #i.succ)”.Evalb (z :> v) :=
    closed hv (φ := “#0 = !!(Semiterm.func f fun i ↦ #i.succ)”)
      (by simp [Semiterm.val_func]; simp [Function.comp_def])
  rcases this with ⟨z, hz, e⟩
  have : z = func f v := by simpa [Semiterm.val_func] using e
  rcases this; assumption

variable (𝓼 s)

instance (priority := 50) str : Structure L (SkolemHull L s) where
  func k f v := ⟨func f fun i ↦ (v i : M), closed_func (by simp)⟩
  rel k R v := Structure.rel R fun i ↦ (v i : M)

instance set_nonempty : (SkolemHull L s).Nonempty := by
  have : ∃ z : M, (⊤ : Semisentence L 1).Evalb ![z] := by simp
  have : ∃ z, z ∈ SkolemHull L s := by
    simpa using closed (s := s) (by simp) this
  exact this

instance nonempty : Nonempty (SkolemHull L s) :=
  Set.Nonempty.to_subtype (set_nonempty _ _)

variable {𝓼 s}

@[simp] lemma str_func_def (f : L.Func k) (v : Fin k → SkolemHull L s) :
    (str 𝓼 s).func f v = ⟨𝓼.func f fun i ↦ (v i : M), closed_func (by simp)⟩ := rfl

@[simp] lemma str_rel_def (R : L.Rel k) (v : Fin k → SkolemHull L s) :
    (str 𝓼 s).rel R v ↔ 𝓼.rel R fun i ↦ (v i : M) := by rfl

@[simp] lemma str_val (t : Semiterm L ξ n) (b : Fin n → SkolemHull L s) (f : ξ → SkolemHull L s) :
    (t.val (M := SkolemHull L s) (s := str 𝓼 s) b f : M) = t.val (s := 𝓼) (b ·) (f ·) :=
  match t with
  |        #x => by simp
  |        &x => by simp
  | .func F v => by simp [Semiterm.val_func, str_val, Function.comp_def]

@[simp] lemma str_eval {φ : Semisentence L n} :
    φ.Evalb (M := SkolemHull L s) b ↔ φ.Evalb (M := M) (b ·) :=
  match φ with
  | .rel R v | .nrel R v => by simp [Semiformula.eval_rel, Semiformula.eval_nrel, Empty.eq_elim, Function.comp_def]
  | ⊤ | ⊥ => by simp
  | φ ⋏ ψ | φ ⋎ ψ => by simp [str_eval (φ := φ), str_eval (φ := ψ)]
  | ∀⁰ φ => by
    suffices
        (∃ x ∈ SkolemHull L s, (∼φ).Evalb (x :> (b ·))) ↔ (∃ x : M, (∼φ).Evalb (x :> (b ·))) by
      apply not_iff_not.mp
      simpa [str_eval (φ := φ), Matrix.comp_vecCons']
    constructor
    · rintro ⟨x, _, H⟩
      exact ⟨x, H⟩
    · intro h
      exact closed (s := s) (by simp) h
  | ∃⁰ φ => by
    suffices
        (∃ x ∈ SkolemHull L s, φ.Evalb (x :> (b ·))) ↔ (∃ x : M, φ.Evalb (x :> (b ·))) by
      simpa [str_eval (φ := φ), Matrix.comp_vecCons']
    constructor
    · rintro ⟨x, _, H⟩
      exact ⟨x, H⟩
    · intro h
      exact closed (s := s) (by simp) h

/-- Downward Löwenheim-Skolem theorem for countable language (1) -/
instance (priority := 50) elementaryEquiv : (SkolemHull L s) ≡ₑ[L] M where
  models {φ} := by simp [models_iff, Matrix.empty_eq]

instance (priority := 50) eq : Structure.Eq L (SkolemHull L s) := ⟨fun x y ↦ by
  simp [Operator.val, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  simpa [-Eq.eq, Subtype.ext_iff] using Structure.Eq.eq (L := L) x.val y.val⟩

section mem

variable [Operator.Mem L] [Membership M M] [Structure.Mem L M]

instance (priority := 50) membership :
  Membership (SkolemHull L s) (SkolemHull L s) := ⟨fun y x ↦ x.val ∈ y.val⟩

instance (priority := 50) mem [Operator.Mem L] [Membership M M] [Structure.Mem L M] :
    Structure.Mem L (SkolemHull L s) := ⟨fun x y ↦ by
  simp [Operator.val, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  simpa [-Mem.mem, Subtype.ext_iff] using Structure.Mem.mem (L := L) x.val y.val⟩

end mem

end SkolemHull

namespace SkolemHull

open Cardinal

variable [L.Encodable] {s : Set M}

instance set_countable (hs : s.Countable) : (SkolemHull L s).Countable := by
  have : Countable s := hs
  have : Countable (Term L.skolemFunction₁ s) := Semiterm.countable
  exact Set.countable_range _

instance countable (hs : s.Countable) : Countable (SkolemHull L s) := set_countable hs

instance countable₀ : Countable (SkolemHull₀ L M) := set_countable (by simp)

/-- Downward Löwenheim-Skolem theorem for countable language (2) -/
lemma card_le_aleph0 (hs : s.Countable) : #(SkolemHull L s) ≤ ℵ₀ :=
  have : Countable (SkolemHull L s) := countable hs
  Set.Countable.le_aleph0 this

end SkolemHull

end Structure

end LO.FirstOrder
