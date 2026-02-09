module

public import Foundation.LinearLogic.FirstOrder.Rew

/-! # One-sided sequent calculus for first-Order linear logic -/

@[expose] public section

namespace LO.FirstOrder.LinearLogic

abbrev Sequent (L : Language) := List (Statement L)

abbrev Sequent.IsQuest (Γ : Sequent L) : Prop := ∀ φ ∈ Γ, φ.IsQuest

variable {L : Language}

/-- Derivation of first-Order linear logic -/
inductive Derivation : Sequent L → Type _ where
  | protected id (r : L.Rel k) (v) : Derivation [.rel r v, .nrel r v]
  | cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
  | exchange : Derivation Γ → Γ.Perm Δ → Derivation Δ
  | one : Derivation [1]
  | falsum : Derivation Γ → Derivation (⊥ :: Γ)
  | tensor : Derivation (φ :: Γ) → Derivation (ψ :: Δ) → Derivation (φ ⨂ ψ :: Γ ++ Δ)
  | par : Derivation (φ :: ψ :: Γ) → Derivation (φ ⅋ ψ :: Γ)
  | verum (Γ) : Derivation (⊤ :: Γ)
  | with : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ＆ ψ :: Γ)
  | plusLeft : Derivation (ψ :: Γ) → (φ : Statement L) → Derivation (φ ⨁ ψ :: Γ)
  | plusRight : Derivation (φ :: Γ) → (ψ : Statement L) → Derivation (φ ⨁ ψ :: Γ)
  | ofCourse : Derivation (φ :: Γ) → Sequent.IsQuest Γ → Derivation (！φ :: Γ)
  | weakening : Derivation Γ → Derivation (？φ :: Γ)
  | dereliction : Derivation (φ :: Γ) → Derivation (？φ :: Γ)
  | contraction : Derivation (？φ :: ？φ :: Γ) → Derivation (？φ :: Γ)
  | all : Derivation (φ.free :: Γ⁺) → Derivation ((∀' φ) :: Γ)
  | ex (t) : Derivation (φ/[t] :: Γ) → Derivation ((∃' φ) :: Γ)

abbrev Statement.Proof (φ : Statement L) : Type _ := Derivation [φ]

abbrev Sentence.Proof (σ : Sentence L) : Type _ := Derivation [(σ : Statement L)]

inductive SymbolFV (L : Language) where
  | symbol : SymbolFV L

abbrev SymbolFV.symbol' (L : Language) : SymbolFV L := .symbol

notation "𝐋𝐋𝐕" => SymbolFV.symbol'

instance : Entailment (SymbolFV L) (Statement L) := ⟨fun _ ↦ Statement.Proof⟩

inductive Symbol (L : Language) where
  | symbol : Symbol L

abbrev Symbol.symbol' (L : Language) : Symbol L := .symbol

notation "𝐋𝐋" => Symbol.symbol'

instance : Entailment (Symbol L) (Sentence L) := ⟨fun _ ↦ Sentence.Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent L) : Prop := Nonempty (⊢! Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

variable {Γ Δ : Sequent L}

def cast (d : ⊢! Γ) (e : Γ = Δ) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! φ :: Γ) : ⊢! Γ ++ [φ] :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def height {Γ : Sequent L} : ⊢! Γ → ℕ
  |       .id _ _ => 0
  |     cut d₁ d₂ => max (height d₁) (height d₂) + 1
  |  exchange d _ => height d
  |           one => 0
  |      falsum d => height d + 1
  |  tensor d₁ d₂ => max (height d₁) (height d₂) + 1
  |         par d => height d + 1
  |       verum _ => 0
  |   .with d₁ d₂ => max (height d₁) (height d₂) + 1
  |  plusLeft d _ => height d + 1
  | plusRight d _ => height d + 1
  |  ofCourse d _ => height d + 1
  |   weakening d => height d + 1
  | dereliction d => height d + 1
  | contraction d => height d + 1
  |         all d => height d + 1
  |        ex _ d => height d + 1

section height

@[simp] lemma height_id (r : L.Rel k) (v) :
    (Derivation.id r v).height = 0 := rfl

@[simp] lemma height_cut (d₁ : ⊢! φ :: Γ) (d₂ : ⊢! ∼φ :: Δ) :
    (d₁.cut d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_exchange (d : ⊢! Γ) (p : Γ.Perm Δ) :
    (d.exchange p).height = d.height := rfl

@[simp] lemma height_one :
    (one (L := L)).height = 0 := rfl

@[simp] lemma height_falsum (d : ⊢! Γ) :
    d.falsum.height = d.height + 1 := rfl

@[simp] lemma height_tensor (d₁ : ⊢! φ :: Γ) (d₂ : ⊢! ψ :: Δ) :
    (d₁.tensor d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_par (d : ⊢! φ :: ψ :: Γ) :
    d.par.height = d.height + 1 := rfl

@[simp] lemma height_verum (Γ : Sequent L) :
    (verum Γ).height = 0 := rfl

@[simp] lemma height_with (d₁ : ⊢! φ :: Γ) (d₂ : ⊢! ψ :: Γ) :
    (d₁.with d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_plusLeft (d : ⊢! φ :: Γ) (ψ) :
    (d.plusLeft ψ).height = d.height + 1 := rfl

@[simp] lemma height_plusRight (d : ⊢! ψ :: Γ) (φ) :
    (d.plusRight φ).height = d.height + 1 := rfl

@[simp] lemma height_ofCourse (d : ⊢! φ :: Γ) (hΓ : Sequent.IsQuest Γ) :
    (d.ofCourse hΓ).height = d.height + 1 := rfl

@[simp] lemma height_weakening (d : ⊢! Γ) (φ) :
    (d.weakening (φ := φ)).height = d.height + 1 := rfl

@[simp] lemma height_dereliction (d : ⊢! φ :: Γ) :
    d.dereliction.height = d.height + 1 := rfl

@[simp] lemma height_contraction (d : ⊢! ？φ :: ？φ :: Γ) :
    d.contraction.height = d.height + 1 := rfl

@[simp] lemma height_all {φ : Semistatement L 1} (d : ⊢! φ.free :: Γ⁺) :
    d.all.height = d.height + 1 := rfl

@[simp] lemma height_ex {φ : Semistatement L 1} {t} (d : ⊢! φ/[t] :: Γ) :
    (d.ex t).height = d.height + 1 := rfl

@[simp] lemma height_cast (d : ⊢! Γ) (e : Γ = Δ) :
    (d.cast e).height = d.height := by rcases e; rfl

end height

def identity : (φ : Statement L) → ⊢! [φ, ∼φ]
  |  .rel r v => Derivation.id r v
  | .nrel r v => (Derivation.id r v).rotate
  |         1 => one.falsum.rotate
  |         ⊥ => one.falsum
  |     φ ⨂ ψ => ((identity φ).tensor (identity ψ)).rotate.par.rotate
  |     φ ⅋ ψ => ((identity φ).rotate.tensor (identity ψ).rotate).rotate.par
  |         ⊤ => verum _
  |         0 => (verum [0]).rotate
  |     φ ＆ ψ => ((identity φ).rotate.plusRight (∼ψ)).rotate.with ((identity ψ).rotate.plusLeft (∼φ)).rotate
  |     φ ⨁ ψ => (((identity φ).plusRight ψ).rotate.with ((identity ψ).plusLeft φ).rotate).rotate
  |        ！φ => (identity φ).rotate.dereliction.rotate.ofCourse (by simp [Sequent.IsQuest])
  |        ？φ => (identity φ).dereliction.rotate.ofCourse (by simp [Sequent.IsQuest]) |>.rotate
  |      ∀' φ =>
    have : ⊢! [(∼φ.shift)/[&0], φ.free] := (identity φ.free).rotate.cast (by simp)
    have : ⊢! φ.free :: [∃' ∼φ]⁺ := (this.ex _).rotate.cast (by simp)
    this.all
  |      ∃' φ =>
    have : ⊢! [φ.shift/[&0], ∼φ.free] := (identity φ.free).cast (by simp)
    have : ⊢! (∼φ).free :: [∃' φ]⁺ := (this.ex _).rotate.cast (by simp)
    this.all.rotate
  termination_by φ => φ.complexity

end Derivation

end LO.FirstOrder.LinearLogic
