import Logic.FirstOrder.Arith.PeanoMinus
import Logic.FirstOrder.Arith.EA.Basic

instance [Zero α] : Nonempty α := ⟨0⟩

notation "exp " x:90 => Exp.exp x

namespace Matrix

lemma forall_iff {n : ℕ} (p : (Fin (n + 1) → α) → Prop) :
    (∀ v, p v) ↔ (∀ a, ∀ v, p (a :> v)) :=
  ⟨fun h a v ↦ h (a :> v), fun h v ↦ by simpa [←eq_vecCons v] using h (v 0) (v ∘ Fin.succ)⟩

end Matrix

namespace Set

@[simp] lemma subset_union_three₁ (s t u : Set α) : s ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_left (by simp) _

@[simp] lemma subset_union_three₂ (s t u : Set α) : t ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_left (by simp) _

@[simp] lemma subset_union_three₃ (s t u : Set α) : u ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_right (by rfl) _

end Set

namespace Matrix

lemma fun_eq_vec₃ {v : Fin 3 → α} : v = ![v 0, v 1, v 2] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]

lemma fun_eq_vec₄ {v : Fin 4 → α} : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  rfl

@[simp] lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) : (a :> s) 4 = s 3 := rfl

@[simp] lemma cons_app_five {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ → α) : (a :> s) 5 = s 4 := rfl

@[simp] lemma cons_app_six {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ → α) : (a :> s) 6 = s 5 := rfl

@[simp] lemma cons_app_seven {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 7 = s 6 := rfl

@[simp] lemma cons_app_eight {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ → α) : (a :> s) 8 = s 7 := rfl

lemma eq_vecCons' (s : Fin (n + 1) → C) : s 0 :> (s ·.succ) = s :=
   funext $ Fin.cases (by simp) (by simp)

end Matrix

lemma forall_fin_iff_zero_and_forall_succ {P : Fin (k + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin k, P i.succ :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, by
    rintro ⟨hz, hs⟩ i
    cases' i using Fin.cases with i
    · exact hz
    · exact hs i⟩

lemma exists_fin_iff_zero_or_exists_succ {P : Fin (k + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin k, P i.succ :=
  ⟨by rintro ⟨i, hi⟩
      cases i using Fin.cases
      · left; exact hi
      · right; exact ⟨_, hi⟩,
   by rintro (hz | ⟨i, h⟩)
      · exact ⟨0, hz⟩
      · exact ⟨_, h⟩⟩

lemma forall_vec_iff_forall_forall_vec {P : (Fin (k + 1) → α) → Prop} :
    (∀ v : Fin (k + 1) → α, P v) ↔ ∀ x, ∀ v : Fin k → α, P (x :> v) := by
  constructor
  · intro h x v; exact h _
  · intro h v; simpa using h (v 0) (v ·.succ)

lemma exists_vec_iff_exists_exists_vec {P : (Fin (k + 1) → α) → Prop} :
    (∃ v : Fin (k + 1) → α, P v) ↔ ∃ x, ∃ v : Fin k → α, P (x :> v) := by
  constructor
  · rintro ⟨v, h⟩; exact ⟨v 0, (v ·.succ), by simpa using h⟩
  · rintro ⟨x, v, h⟩; exact ⟨_, h⟩

lemma exists_le_vec_iff_exists_le_exists_vec [LE α] {P : (Fin (k + 1) → α) → Prop} {f : Fin (k + 1) → α} :
    (∃ v ≤ f, P v) ↔ ∃ x ≤ f 0, ∃ v ≤ (f ·.succ), P (x :> v) := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w 0, hw 0, (w ·.succ), fun i ↦ hw i.succ, by simpa using h⟩
  · rintro ⟨x, hx, v, hv, h⟩
    refine ⟨x :> v, ?_, h⟩
    intro i; cases' i using Fin.cases with i
    · exact hx
    · exact hv i

lemma forall_le_vec_iff_forall_le_forall_vec [LE α] {P : (Fin (k + 1) → α) → Prop} {f : Fin (k + 1) → α} :
    (∀ v ≤ f, P v) ↔ ∀ x ≤ f 0, ∀ v ≤ (f ·.succ), P (x :> v) := by
  constructor
  · intro h x hx v hv
    refine h (x :> v) ?_
    intro i; cases' i using Fin.cases with i
    · exact hx
    · exact hv i
  · intro h v hv
    simpa using h (v 0) (hv 0) (v ·.succ) (hv ·.succ)

instance : ToString Empty := ⟨Empty.elim⟩

class Hash (α : Type*) where
  hash : α → α → α

infix:80 " # " => Hash.hash

class Length (α : Type*) where
  length : α → α

notation "‖" x "‖" => Length.length x

namespace LO

namespace Polarity

variable {α : Type*} [SigmaSymbol α] [PiSymbol α]

protected def coe : Polarity → α
 | 𝚺 => 𝚺
 | 𝚷 => 𝚷

instance : Coe Polarity α := ⟨Polarity.coe⟩

@[simp] lemma coe_sigma : ((𝚺 : Polarity) : α) = 𝚺 := rfl

@[simp] lemma coe_pi : ((𝚷 : Polarity) : α) = 𝚷 := rfl

end Polarity

namespace SigmaPiDelta

@[simp] lemma alt_coe (Γ : Polarity) : SigmaPiDelta.alt Γ = (Γ.alt : SigmaPiDelta) := by cases Γ <;> simp

end SigmaPiDelta

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
  | _, p ⋏ q                         => "[" ++ formulaToStr p ++ "]" ++ " \\land " ++ "[" ++ formulaToStr q ++ "]"
  | _, p ⋎ q                         => "[" ++ formulaToStr p ++ "]" ++ " \\lor "  ++ "[" ++ formulaToStr q ++ "]"
  | n, ∀' (rel Language.LT.lt v ⟶ p) => "(\\forall x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr p ++ "]"
  | n, ∃' (rel Language.LT.lt v ⋏ p) => "(\\exists x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr p  ++ "]"
  | n, ∀' p                          => "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr p ++ "]"
  | n, ∃' p                          => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr p ++ "]"

instance : Repr (Semiformula ℒₒᵣ μ n) := ⟨fun t _ => formulaToStr t⟩

instance : ToString (Semiformula ℒₒᵣ μ n) := ⟨formulaToStr⟩

end ToString

section model

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ≼ T]

variable (M : Type*) [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* T]

lemma oring_sound {σ : Sentence ℒₒᵣ} (h : T ⊢! σ) : M ⊧ₘ σ := (consequence_iff' (T := T)).mp (LO.Sound.sound h) M

instance indScheme_of_indH (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃Γ n] :
    M ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ n) := models_indScheme_of_models_indH Γ n

end model

end Arith

section

variable {L : Language}

namespace Semiformula

variable {M : Type*} [Nonempty M] {s : Structure L M}

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

abbrev Semiformula.Rlz (p : Semiformula L M n) (e : Fin n → M) : Prop := Evalm M e id p

end

namespace Arith

namespace Hierarchy

section
variable {L : FirstOrder.Language} [L.LT] {μ : Type v}

@[simp]
lemma exItr {n} : {k : ℕ} → {p : Semiformula L μ (n + k)} → Hierarchy 𝚺 (s + 1) (∃^[k] p) ↔ Hierarchy 𝚺 (s + 1) p
  | 0,     p => by simp
  | k + 1, p => by simp [LO.exItr_succ, exItr]

@[simp]
lemma univItr {n} : {k : ℕ} → {p : Semiformula L μ (n + k)} → Hierarchy 𝚷 (s + 1) (∀^[k] p) ↔ Hierarchy 𝚷 (s + 1) p
  | 0,     p => by simp
  | k + 1, p => by simp [LO.univItr_succ, univItr]

end

end Hierarchy

variable (M : Type*) [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]

lemma nat_extention_sigmaOne {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ σ → M ⊧ₘ σ := fun h ↦ by
  simpa [Matrix.empty_eq] using Arith.bold_sigma_one_completeness (M := M) hσ h

lemma nat_extention_piOne {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚷 1 σ) :
    M ⊧ₘ σ → ℕ ⊧ₘ σ := by
  contrapose
  simpa using nat_extention_sigmaOne M (σ := ~σ) (by simpa using hσ)

end Arith

section

variable (M : Type*) [Nonempty M] [Structure L M]

abbrev ModelsWithParam {k} (v : Fin k → M) (p : Semisentence L k) : Prop := Semiformula.Evalbm M v p

notation M:45 " ⊧ₘ[" v "] " p:46 => ModelsWithParam M v p

end

end FirstOrder

end LO
