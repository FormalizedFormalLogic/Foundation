import Foundation.FirstOrder.Arith.Representation
import Foundation.FirstOrder.Arith.PeanoMinus
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.Sub.Basic

namespace LO

namespace FirstOrder

namespace Arith

attribute [simp] Semiformula.eval_substs Semiformula.eval_embSubsts
  Matrix.vecHead Matrix.vecTail Matrix.comp_vecCons' Matrix.constant_eq_singleton

section ToString

variable [ToString μ]

open Semiterm Semiformula

def termToStr : Semiterm ℒₒᵣ μ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _   => "1"
  | func Language.Add.add v   => "(" ++ termToStr (v 0) ++ " + " ++ termToStr (v 1) ++ ")"
  | func Language.Mul.mul v   => "(" ++ termToStr (v 0) ++ " \\cdot " ++ termToStr (v 1) ++ ")"

instance : Repr (Semiterm ℒₒᵣ μ n) := ⟨fun t _ => termToStr t⟩

instance : ToString (Semiterm ℒₒᵣ μ n) := ⟨termToStr⟩

def formulaToStr : ∀ {n}, Semiformula ℒₒᵣ μ n → String
  | _, ⊤                             => "\\top"
  | _, ⊥                             => "\\bot"
  | _, rel Language.Eq.eq v          => termToStr (v 0) ++ " = " ++ termToStr (v 1)
  | _, rel Language.LT.lt v          => termToStr (v 0) ++ " < " ++ termToStr (v 1)
  | _, nrel Language.Eq.eq v         => termToStr (v 0) ++ " \\not = " ++ termToStr (v 1)
  | _, nrel Language.LT.lt v         => termToStr (v 0) ++ " \\not < " ++ termToStr (v 1)
  | _, φ ⋏ ψ                         => "[" ++ formulaToStr φ ++ "]" ++ " \\land " ++ "[" ++ formulaToStr ψ ++ "]"
  | _, φ ⋎ ψ                         => "[" ++ formulaToStr φ ++ "]" ++ " \\lor "  ++ "[" ++ formulaToStr ψ ++ "]"
  | n, ∀' (rel Language.LT.lt v ➝ φ) => "(\\forall x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr φ ++ "]"
  | n, ∃' (rel Language.LT.lt v ⋏ φ) => "(\\exists x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr φ  ++ "]"
  | n, ∀' φ                          => "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr φ ++ "]"
  | n, ∃' φ                          => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr φ ++ "]"

instance : Repr (Semiformula ℒₒᵣ μ n) := ⟨fun t _ => formulaToStr t⟩

instance : ToString (Semiformula ℒₒᵣ μ n) := ⟨formulaToStr⟩

end ToString

section model

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ⪯ T]

variable (M : Type*) [ORingStruc M] [M ⊧ₘ* T]

instance indScheme_of_indH (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃Γ n] :
    M ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ n) := models_indScheme_of_models_indH Γ n

end model

end Arith

section

variable {L : Language}

namespace Semiformula

variable {M : Type*} {s : Structure L M}

variable {n : ℕ} {ε : ξ → M}

@[simp] lemma eval_operator₃ {o : Operator L 3} {t₁ t₂ t₃ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε] := by
  simp [eval_operator]

@[simp] lemma eval_operator₄ {o : Operator L 4} {t₁ t₂ t₃ t₄ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃, t₄]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε, t₄.val s e ε] := by
  simp [eval_operator]

end Semiformula

end

section

variable {M : Type*} [Nonempty M] [Structure L M]

abbrev Semiterm.Rlz (t : Semiterm L M n) (e : Fin n → M) : M := t.valm M e id

abbrev Semiformula.Rlz (φ : Semiformula L M n) (e : Fin n → M) : Prop := Evalm M e id φ

@[simp] lemma models₀_not_iff (σ : Sentence L) : M ⊧ₘ₀ (∼σ) ↔ ¬M ⊧ₘ₀ σ := by simp [models₀_iff]

@[simp] lemma models₀_or_iff (σ π : Sentence L) : M ⊧ₘ₀ (σ ⋎ π) ↔ M ⊧ₘ₀ σ ∨ M ⊧ₘ₀ π := by simp [models₀_iff]

@[simp] lemma models₀_imply_iff (σ π : Sentence L) : M ⊧ₘ₀ (σ ➝ π) ↔ M ⊧ₘ₀ σ → M ⊧ₘ₀ π := by simp [models₀_iff]

end

namespace Arith

namespace Hierarchy

section
variable {L : FirstOrder.Language} [L.LT] {μ : Type v}

@[simp]
lemma exItr {n} : {k : ℕ} → {φ : Semiformula L μ (n + k)} → Hierarchy 𝚺 (s + 1) (∃^[k] φ) ↔ Hierarchy 𝚺 (s + 1) φ
  | 0,     φ => by simp
  | k + 1, φ => by simp [LO.exItr_succ, exItr]

@[simp]
lemma univItr {n} : {k : ℕ} → {φ : Semiformula L μ (n + k)} → Hierarchy 𝚷 (s + 1) (∀^[k] φ) ↔ Hierarchy 𝚷 (s + 1) φ
  | 0,     φ => by simp
  | k + 1, φ => by simp [LO.univItr_succ, univItr]

end

end Hierarchy

variable (M : Type*) [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

instance : M ⊧ₘ* 𝐑₀ := by refine models_of_subtheory (T := 𝐏𝐀⁻) inferInstance

lemma nat_extention_sigmaOne {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ₀ σ → M ⊧ₘ₀ σ := fun h ↦ by
  simpa [Matrix.empty_eq] using LO.Arith.sigma_one_completeness (M := M) hσ h

lemma nat_extention_piOne {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚷 1 σ) :
    M ⊧ₘ₀ σ → ℕ ⊧ₘ₀ σ := by
  contrapose
  simpa using nat_extention_sigmaOne M (σ := ∼σ) (by simpa using hσ)

end Arith

end FirstOrder

end LO

namespace LO.Arith

open FirstOrder FirstOrder.Arith ORingStruc

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐑₀]

lemma bold_sigma_one_completeness' {n} {σ : Semisentence ℒₒᵣ n} (hσ : Hierarchy 𝚺 1 σ) {e} :
    Semiformula.Evalbm ℕ e σ → Semiformula.Evalbm M (fun x ↦ numeral (e x)) σ := fun h ↦ by
  simpa [Empty.eq_elim] using bold_sigma_one_completeness (M := M) (φ := σ) hσ (f := Empty.elim) (e := e) h

end LO.Arith

namespace List.Vector

variable {α : Type*}

@[simp] lemma nil_get (v : Vector α 0) : v.get = ![] := by
  ext i; exact i.elim0

end List.Vector
