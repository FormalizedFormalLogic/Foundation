import Foundation.FirstOrder.Basic

namespace LO.FirstOrder

/-- Skolem function of rank 1 -/
def Language.skolemFunction₁ (L : Language) : Language where
  Func k := Semisentence L (k + 1)
  Rel _ := PEmpty

abbrev Semisentence.skolem₁ {L : Language} (φ : Semisentence L (k + 1)) : L.skolemFunction₁.Func k := φ

namespace Structure

variable (L : Language)

variable (M : Type*) [Nonempty M] [𝓼 : Structure L M]

noncomputable instance skolem : Structure L.skolemFunction₁ M where
  func _ φ v := Classical.epsilon fun z ↦ Semiformula.Evalb 𝓼 (z :> v) φ
  rel _ r _ := PEmpty.elim r

variable {L M}

@[simp] lemma val_skolem_func (φ : Semisentence L (k + 1)) :
    (skolem L M).func φ.skolem₁ v = Classical.epsilon fun z ↦ φ.Evalb 𝓼 (z :> v) := rfl

variable (L)

def SkolemHull (s : Set M) : Set M := Set.range fun t : Term L.skolemFunction₁ s ↦ t.valm M ![] (↑)

variable {L}

namespace SkolemHull

open Semiformula

variable {s : Set M}

lemma mem_iff :
    x ∈ SkolemHull L s ↔ ∃ t : Term L.skolemFunction₁ s, t.valm M ![] (↑) = x := by
  simp [SkolemHull]

@[simp] lemma val_mem (t : Term L.skolemFunction₁ s) : t.valm M ![] (↑) ∈ SkolemHull L s := by simp [SkolemHull]

lemma subset : s ⊆ SkolemHull L s := fun x hx ↦ by
  let t : Term L.skolemFunction₁ s := &⟨x, hx⟩
  have : x = t.valm M ![] (↑) := by simp [t]
  simp [this]

lemma closed {v : Fin k → M} (hv : ∀ i, v i ∈ SkolemHull L s)
    {φ : Semisentence L (k + 1)} (H : ∃ z, M ⊧/(z :> v) φ) :
    ∃ z ∈ SkolemHull L s, M ⊧/(z :> v) φ := by
  choose u hu using fun i ↦ mem_iff.mp (hv i)
  let t : Term L.skolemFunction₁ s := .func φ.skolem₁ u
  refine ⟨t.valm M ![] (↑), by simp, ?_⟩
  suffices M ⊧/((Classical.epsilon fun z ↦ M ⊧/(z :> v) φ) :> v) φ by
    simpa [t, Semiterm.val_func, hu]
  exact Classical.epsilon_spec H

variable [Operator.Eq L] [Structure.Eq L M]

lemma closed_func {v : Fin k → M} (hv : ∀ i, v i ∈ SkolemHull L s)
    {f : L.Func k} : Structure.func f v ∈ SkolemHull L s := by
  have : ∃ z ∈ SkolemHull L s, M ⊧/(z :> v) “#0 = !!(Semiterm.func f fun i ↦ #i.succ)” :=
    closed hv (φ := “#0 = !!(Semiterm.func f fun i ↦ #i.succ)”)
      (by simp [Semiterm.val_func])
  rcases this with ⟨z, hz, e⟩
  have : z = func f v := by simpa [Semiterm.val_func] using e
  rcases this; assumption

variable (𝓼 s)

instance str : Structure L (SkolemHull L s) where
  func k f v := ⟨func f fun i ↦ (v i : M), closed_func (by simp)⟩
  rel k R v := Structure.rel R fun i ↦ (v i : M)

instance set_nonempty : (SkolemHull L s).Nonempty := by
  have : ∃ z, M ⊧/![z] (⊤ : Semisentence L 1) := by simp
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
    (t.val (M := SkolemHull L s) (str 𝓼 s) b f : M) = t.val 𝓼 (b ·) (f ·) :=
  match t with
  |        #x => by simp
  |        &x => by simp
  | .func F v => by simp [Semiterm.val_func, str_val]

@[simp] lemma str_eval {φ : Semisentence L n} :
    (SkolemHull L s) ⊧/b φ ↔ M ⊧/(b ·) φ :=
  match φ with
  | .rel R v | .nrel R v => by simp [Semiformula.eval_rel, Semiformula.eval_nrel, Empty.eq_elim]
  | ⊤ | ⊥ => by simp
  | φ ⋏ ψ | φ ⋎ ψ => by simp [str_eval (φ := φ), str_eval (φ := ψ)]
  | ∀' φ => by
    suffices
        (∃ x ∈ SkolemHull L s, (∼φ).Evalb 𝓼 (x :> (b ·))) ↔ (∃ x, (∼φ).Evalb 𝓼 (x :> (b ·))) by
      apply not_iff_not.mp
      simpa [str_eval (φ := φ), Matrix.comp_vecCons']
    constructor
    · rintro ⟨x, _, H⟩
      exact ⟨x, H⟩
    · intro h
      exact closed (s := s) (by simp) h
  | ∃' φ => by
    suffices
        (∃ x ∈ SkolemHull L s, φ.Evalb 𝓼 (x :> (b ·))) ↔ (∃ x, φ.Evalb 𝓼 (x :> (b ·))) by
      simpa [str_eval (φ := φ), Matrix.comp_vecCons']
    constructor
    · rintro ⟨x, _, H⟩
      exact ⟨x, H⟩
    · intro h
      exact closed (s := s) (by simp) h

instance elementary : (SkolemHull L s) ≡ₑ[L] M where
  models {φ} := by simp [models_iff, Matrix.empty_eq]

end SkolemHull

end Structure

end LO.FirstOrder
