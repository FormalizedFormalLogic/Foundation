module

public import Foundation.Vorspiel.List.Perm
public import Foundation.LinearLogic.FirstOrder.Rew

/-! # One-sided sequent calculus for first-order linear logic -/

@[expose] public section

namespace LO.FirstOrder.LinearLogic

variable {L : Language}

abbrev Sequent (L : Language) := List (Proposition L)

def Sequent.IsQuest (Γ : Sequent L) : Prop := ∀ φ ∈ Γ, φ.IsQuest

def Sequent.Negative (Γ : Sequent L) : Prop := ∀ φ ∈ Γ, φ.Negative

namespace Sequent

namespace IsQuest

@[simp] lemma nil : Sequent.IsQuest ([] : Sequent L) := by simp [Sequent.IsQuest]

@[simp] lemma cons (φ : Proposition L) (Γ : Sequent L) :
    Sequent.IsQuest (φ :: Γ) ↔ φ.IsQuest ∧ Sequent.IsQuest Γ := by simp [Sequent.IsQuest]

end IsQuest

namespace Negative

@[simp] lemma nil : Sequent.Negative ([] : Sequent L) := by simp [Sequent.Negative]

@[simp] lemma cons (φ : Proposition L) (Γ : Sequent L) :
    Sequent.Negative (φ :: Γ) ↔ φ.Negative ∧ Sequent.Negative Γ := by simp [Sequent.Negative]

end Negative

def quest (Γ : Sequent L) : Sequent L := Γ.map (？·)

instance : Quest (Sequent L) := ⟨quest⟩

lemma quest_def (Γ : Sequent L) : ？Γ = Γ.map (？·) := rfl

@[simp] lemma quest_nil : ？([] : Sequent L) = [] := rfl

@[simp] lemma quest_cons (φ : Proposition L) (Γ : Sequent L) :
    ？(φ :: Γ) = ？φ :: ？Γ := rfl

@[simp] lemma quest_append (Γ Δ : Sequent L) :
    ？(Γ ++ Δ) = ？Γ ++ ？Δ := by simp [quest_def]

@[simp] lemma quest_isQuest (Γ : Sequent L) : Sequent.IsQuest (？Γ) := by simp [Sequent.IsQuest, quest_def]

end Sequent

/-- Derivation of first-order linear logic -/
inductive Derivation : Sequent L → Type _ where
  | identity (φ) : Derivation [φ, ∼φ]
  | cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) → Derivation (Γ ++ Δ)
  | exchange : Derivation Γ → Γ.Perm Δ → Derivation Δ
  | one : Derivation [1]
  | falsum : Derivation Γ → Derivation (⊥ :: Γ)
  | tensor : Derivation (φ :: Γ) → Derivation (ψ :: Δ) → Derivation (φ ⨂ ψ :: (Γ ++ Δ))
  | par : Derivation (φ :: ψ :: Γ) → Derivation (φ ⅋ ψ :: Γ)
  | verum (Γ) : Derivation (⊤ :: Γ)
  | with : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ＆ ψ :: Γ)
  | plusLeft : Derivation (ψ :: Γ) → (φ : Proposition L) → Derivation (φ ⨁ ψ :: Γ)
  | plusRight : Derivation (φ :: Γ) → (ψ : Proposition L) → Derivation (φ ⨁ ψ :: Γ)
  | ofCourse : Derivation (φ :: Γ) → Sequent.IsQuest Γ → Derivation (！φ :: Γ)
  | weakening : Derivation Γ → (φ : Proposition L) → Derivation (？φ :: Γ)
  | dereliction : Derivation (φ :: Γ) → Derivation (？φ :: Γ)
  | contraction : Derivation (？φ :: ？φ :: Γ) → Derivation (？φ :: Γ)
  | all : Derivation (φ.free :: Γ⁺) → Derivation ((∀⁰ φ) :: Γ)
  | exs (t) : Derivation (φ/[t] :: Γ) → Derivation ((∃⁰ φ) :: Γ)

abbrev Proposition.Proof (φ : Proposition L) : Type _ := Derivation [φ]

abbrev Sentence.Proof (σ : Sentence L) : Type _ := Derivation [(σ : Proposition L)]

inductive SymbolFV (L : Language) where
  | symbol : SymbolFV L

notation "𝐋𝐋₀" => SymbolFV.symbol

instance : Entailment (SymbolFV L) (Proposition L) := ⟨fun _ ↦ Proposition.Proof⟩

inductive Symbol (L : Language) where
  | symbol : Symbol L

notation "𝐋𝐋" => Symbol.symbol

instance : Entailment (Symbol L) (Sentence L) := ⟨fun _ ↦ Sentence.Proof⟩

scoped prefix:45 "⊢ᴸ " => Derivation

namespace Derivation

variable {Γ Δ : Sequent L}

def cast (d : ⊢ᴸ Γ) (e : Γ = Δ) : ⊢ᴸ Δ := e ▸ d

def rotate (d : ⊢ᴸ φ :: Γ) : ⊢ᴸ Γ ++ [φ] :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def invRotate (d : ⊢ᴸ Γ ++ [φ]) : ⊢ᴸ φ :: Γ :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def height {Γ : Sequent L} : ⊢ᴸ Γ → ℕ
  |    identity _ => 0
  |     cut d₁ d₂ => max d₁.height d₂.height + 1
  |  exchange d _ => d.height
  |           one => 0
  |      falsum d => d.height + 1
  |  tensor d₁ d₂ => max d₁.height d₂.height + 1
  |         par d => d.height + 1
  |       verum _ => 0
  |   .with d₁ d₂ => max d₁.height d₂.height + 1
  |  plusLeft d _ => d.height + 1
  | plusRight d _ => d.height + 1
  |  ofCourse d _ => d.height + 1
  | weakening d _ => d.height + 1
  | dereliction d => d.height + 1
  | contraction d => d.height + 1
  |         all d => d.height + 1
  |       exs _ d => d.height + 1

section height

@[simp] lemma height_id (φ : Proposition L) :
    (identity φ).height = 0 := rfl

@[simp] lemma height_cut (d₁ : ⊢ᴸ φ :: Γ) (d₂ : ⊢ᴸ ∼φ :: Δ) :
    (d₁.cut d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_exchange (d : ⊢ᴸ Γ) (p : Γ.Perm Δ) :
    (d.exchange p).height = d.height := rfl

@[simp] lemma height_one :
    (one (L := L)).height = 0 := rfl

@[simp] lemma height_falsum (d : ⊢ᴸ Γ) :
    d.falsum.height = d.height + 1 := rfl

@[simp] lemma height_tensor (d₁ : ⊢ᴸ φ :: Γ) (d₂ : ⊢ᴸ ψ :: Δ) :
    (d₁.tensor d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_par (d : ⊢ᴸ φ :: ψ :: Γ) :
    d.par.height = d.height + 1 := rfl

@[simp] lemma height_verum (Γ : Sequent L) :
    (verum Γ).height = 0 := rfl

@[simp] lemma height_with (d₁ : ⊢ᴸ φ :: Γ) (d₂ : ⊢ᴸ ψ :: Γ) :
    (d₁.with d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_plusLeft (d : ⊢ᴸ φ :: Γ) (ψ) :
    (d.plusLeft ψ).height = d.height + 1 := rfl

@[simp] lemma height_plusRight (d : ⊢ᴸ ψ :: Γ) (φ) :
    (d.plusRight φ).height = d.height + 1 := rfl

@[simp] lemma height_ofCourse (d : ⊢ᴸ φ :: Γ) (hΓ : Sequent.IsQuest Γ) :
    (d.ofCourse hΓ).height = d.height + 1 := rfl

@[simp] lemma height_weakening (d : ⊢ᴸ Γ) (φ) :
    (d.weakening φ).height = d.height + 1 := rfl

@[simp] lemma height_dereliction (d : ⊢ᴸ φ :: Γ) :
    d.dereliction.height = d.height + 1 := rfl

@[simp] lemma height_contraction (d : ⊢ᴸ ？φ :: ？φ :: Γ) :
    d.contraction.height = d.height + 1 := rfl

@[simp] lemma height_all {φ : Semiproposition L 1} (d : ⊢ᴸ φ.free :: Γ⁺) :
    d.all.height = d.height + 1 := rfl

@[simp] lemma height_exs {φ : Semiproposition L 1} {t} (d : ⊢ᴸ φ/[t] :: Γ) :
    (d.exs t).height = d.height + 1 := rfl

@[simp] lemma height_cast (d : ⊢ᴸ Γ) (e : Γ = Δ) :
    (d.cast e).height = d.height := by rcases e; rfl

end height

def eta : (φ : Proposition L) → ⊢ᴸ [φ, ∼φ]
  |  .rel r v => identity _
  | .nrel r v => identity _
  |         1 => one.falsum.rotate
  |         ⊥ => one.falsum
  |     φ ⨂ ψ => ((eta φ).tensor (eta ψ)).rotate.par.rotate
  |     φ ⅋ ψ => ((eta φ).rotate.tensor (eta ψ).rotate).rotate.par
  |         ⊤ => verum _
  |         0 => (verum [0]).rotate
  |     φ ＆ ψ => ((eta φ).rotate.plusRight (∼ψ)).rotate.with ((eta ψ).rotate.plusLeft (∼φ)).rotate
  |     φ ⨁ ψ => (((eta φ).plusRight ψ).rotate.with ((eta ψ).plusLeft φ).rotate).rotate
  |        ！φ => (eta φ).rotate.dereliction.rotate.ofCourse (by simp)
  |        ？φ => (eta φ).dereliction.rotate.ofCourse (by simp) |>.rotate
  |      ∀⁰ φ =>
    have : ⊢ᴸ [(∼φ.shift)/[&0], φ.free] := (eta φ.free).rotate.cast (by simp)
    have : ⊢ᴸ φ.free :: [∃⁰ ∼φ]⁺ := (this.exs _).rotate.cast (by simp)
    this.all
  |      ∃⁰ φ =>
    have : ⊢ᴸ [φ.shift/[&0], ∼φ.free] := (eta φ.free).cast (by simp)
    have : ⊢ᴸ (∼φ).free :: [∃⁰ φ]⁺ := (this.exs _).rotate.cast (by simp)
    this.all.rotate
  termination_by φ => φ.complexity

def expComm (φ ψ : Proposition L) : ⊢ᴸ [！∼φ ⨂ ！∼ψ, ？(φ ⨁ ψ)] :=
  have dφ : ⊢ᴸ [！∼φ, ？(φ ⨁ ψ)] := ((identity φ).plusRight ψ).dereliction.rotate.ofCourse (by simp)
  have dψ : ⊢ᴸ [！∼ψ, ？(φ ⨁ ψ)] := ((identity ψ).plusLeft φ).dereliction.rotate.ofCourse (by simp)
  have : ⊢ᴸ [！∼φ ⨂ ！∼ψ, ？(φ ⨁ ψ), ？(φ ⨁ ψ)] := dφ.tensor dψ
  this.rotate.contraction.rotate

def ofNegative : (ν : Proposition L) → ν.Negative → ⊢ᴸ [∼？ν, ν]
  |    ？φ, h => (identity (？φ)).rotate.ofCourse (by simp)
  |     ⊥, h => (one.ofCourse (by simp)).falsum.rotate
  |     ⊤, h => (verum [！0]).rotate
  | ν ⅋ μ, h =>
    have ihν : ⊢ᴸ [∼？ν, ν] := ofNegative ν (by rcases h; assumption)
    have ihμ : ⊢ᴸ [∼？μ, μ] := ofNegative μ (by rcases h; assumption)
    have : ⊢ᴸ [！(∼ν ⨂ ∼μ), ？ν, ？μ] :=
      (((identity ν).rotate.tensor (identity μ).rotate).rotate.dereliction.rotate.dereliction.rotate).ofCourse (by simp)
    have : ⊢ᴸ [！(∼ν ⨂ ∼μ), ν, μ] := (this.rotate.cut ihν).cut ihμ
    this.rotate.par.rotate
  | ν ＆ μ, h =>
    have ihν : ⊢ᴸ [∼？ν, ν] := ofNegative ν (by rcases h; assumption)
    have ihμ : ⊢ᴸ [∼？μ, μ] := ofNegative μ (by rcases h; assumption)
    have : ⊢ᴸ [！(∼ν ⨁ ∼μ), ？ν] := ((identity ν).rotate.plusRight (∼μ)).rotate.dereliction.rotate.ofCourse (by simp)
    have dν : ⊢ᴸ [ν, ！(∼ν ⨁ ∼μ)] := (this.rotate.cut ihν).rotate
    have : ⊢ᴸ [！(∼ν ⨁ ∼μ), ？μ] := ((identity μ).rotate.plusLeft (∼ν)).rotate.dereliction.rotate.ofCourse (by simp)
    have dμ : ⊢ᴸ [μ, ！(∼ν ⨁ ∼μ)] := (this.rotate.cut ihμ).rotate
    (dν.with dμ).rotate
  |   ∀⁰ ν, h =>
    have ih : ⊢ᴸ [∼？ν.free, ν.free] := ofNegative ν.free (by rcases h; simpa)
    have : ⊢ᴸ [！(∃⁰ ∼ν.shift), ？ν.free] := (exs &0 <| (identity ν.free).dereliction.rotate.cast (by simp)).ofCourse (by simp)
    have : ⊢ᴸ (ν).free :: [∼？(∀⁰ ν)]⁺ := (this.rotate.cut ih).rotate.cast (by simp)
    this.all.rotate
  termination_by ν => ν.complexity

def removeQuest (h : ν.Negative) (d : ⊢ᴸ ？ν :: Γ) : ⊢ᴸ ν :: Γ :=
  (d.cut (ofNegative ν h)).invRotate

def negativeWeakening {ν : Proposition L} (h : ν.Negative) (d : ⊢ᴸ Γ) :
    ⊢ᴸ ν :: Γ := ((d.weakening ν).cut (ofNegative ν h)).invRotate

def negativeContraction {ν : Proposition L} (h : ν.Negative) (d : ⊢ᴸ ν :: ν :: Γ) :
    ⊢ᴸ ν :: Γ :=
  have : ⊢ᴸ ？ν :: ？ν :: Γ := d.dereliction.rotate.dereliction.exchange (by simp)
  have : ⊢ᴸ ？ν :: Γ := this.contraction
  this.cut (ofNegative ν h) |>.invRotate

def negativeWk [L.DecidableEq] (d : ⊢ᴸ Γ) (ss : Γ ⊆ Δ) (hΔ : Δ.Negative) :
    ⊢ᴸ Δ :=
  let rec wk {Γ Δ : Sequent L} (c : Γ.CompSubset Δ) (d : ⊢ᴸ Γ) (hΔ : ∀ ν ∈ Δ, ν.Negative) :
      ⊢ᴸ Δ :=
    match c with
    |            .refl _ => d
    |         .perm c hp => (wk c d (by grind)).exchange hp
    |           .add ν c =>
      have : ν.Negative := hΔ ν (by simp)
      (wk c d (by grind)).negativeWeakening this
    | .double (a := ν) c =>
      have : ν.Negative := hΔ ν (by simp)
      (wk c d (by grind)).negativeContraction this
  wk (List.Subset.toCompSubst ss) d hΔ

def addQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸ Γ ++ Δ) : ⊢ᴸ Γ ++ ？Δ :=
  match Δ with
  |      [] => d
  | ν :: Δ =>
    have : ⊢ᴸ ν :: Γ ++ Δ := d.exchange (by simp)
    have : ⊢ᴸ ？ν :: Γ ++ ？Δ := (addQuestAppendRight this).dereliction
    this.exchange (by simpa using List.Perm.symm List.perm_middle)

def addQuestTail {Γ : Sequent L} (d : ⊢ᴸ φ :: Γ) : ⊢ᴸ φ :: ？Γ :=
  have : ⊢ᴸ [φ] ++ Γ := d
  addQuestAppendRight this

def removeQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸ Γ ++ ？Δ) (h : Δ.Negative) : ⊢ᴸ Γ ++ Δ :=
  match Δ with
  |      [] => d
  | ν :: Δ =>
    have hν : ν.Negative := h ν (by simp)
    have hΔ : Sequent.Negative Δ := by simp [Sequent.Negative] at h; tauto
    have : ⊢ᴸ ？ν :: Γ ++ ？Δ := d.exchange (by simp)
    have : ⊢ᴸ ν :: Γ ++ Δ := (removeQuestAppendRight this hΔ).cut (ofNegative ν hν) |>.invRotate
    this.exchange (by simpa using List.Perm.symm List.perm_middle)

def removeQuestTail {Γ : Sequent L} (d : ⊢ᴸ φ :: ？Γ) (h : Γ.Negative) : ⊢ᴸ φ :: Γ :=
  have : ⊢ᴸ [φ] ++ ？Γ := d
  removeQuestAppendRight this h

def negativeOfCourse {Γ : Sequent L} (d : ⊢ᴸ φ :: Γ) (h : Γ.Negative) : ⊢ᴸ ！φ :: Γ :=
  have : ⊢ᴸ ！φ :: ？Γ := d.addQuestTail.ofCourse (by simp)
  this.removeQuestTail h

end Derivation

end LO.FirstOrder.LinearLogic
