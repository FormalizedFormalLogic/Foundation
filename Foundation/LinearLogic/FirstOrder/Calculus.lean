module

public import Foundation.LinearLogic.FirstOrder.Rew

/-! # One-sided sequent calculus for first-order linear logic -/

@[expose] public section

namespace List

variable {α : Type*}

lemma Perm.two_iff {a b : α} {l : List α} :
    l ~ [a, b] ↔ l = [a, b] ∨ l = [b, a] := by
  constructor
  · intro h
    have hlen : l.length = 2 := List.Perm.length_eq h
    rcases List.length_eq_two.mp hlen with ⟨x, y, rfl⟩
    have ha : a = x ∨ a = y := by
      have : a ∈ [x, y] := (List.Perm.mem_iff h.symm).mp (by simp)
      simpa using this
    have hb : b = x ∨ b = y := by
      have : b ∈ [x, y] := (List.Perm.mem_iff h.symm).mp (by simp)
      simpa using this
    rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
    · have : b = y := by simpa using replicate_perm (n := 2) (a := b) |>.mp h.symm
      simp_all
    · simp
    · simp
    · have : b = x := by simpa using List.replicate_perm (n := 2) (a := b) |>.mp h.symm
      simp_all
  · intro h
    rcases h with (rfl | rfl)
    · simp
    · exact swap _ _ []

inductive CompSubset : List α → List α → Type _
  | refl (l) : CompSubset l l
  | perm : CompSubset l₁ l₂ → l₂ ~ l₃ → CompSubset l₁ l₃
  | add (a : α) :
    CompSubset l₁ l₂ → CompSubset l₁ (a :: l₂)
  | double {a : α} :
    CompSubset l₁ (a :: a :: l₂) → CompSubset l₁ (a :: l₂)

variable [DecidableEq α]

lemma remove_def (a b : α) (l : List α) : remove a (b :: l) = if a = b then remove a l else b :: remove a l := by
  simp [remove, List.filter]; grind

lemma count_def (a b : α) (l : List α) : count a (b :: l) = if a = b then count a l + 1 else count a l := by
  simp [count]; grind

lemma perm_normalize (l : List α) (a : α) : l ~ replicate (l.count a) a ++ l.remove a :=
  match l with
  |     [] => by simp
  | b :: l => by
    by_cases h : a = b
    · simp [h, List.replicate, perm_normalize l]
    · suffices b :: l ~ replicate (count a l) a ++ b :: remove a l by simpa [h, remove_def, count_def]
      calc
        b :: l ~ b :: (replicate (l.count a) a ++ l.remove a) := by simp [perm_normalize l]
             _ ~ replicate (count a l) a ++ b :: remove a l   := Perm.symm perm_middle

namespace CompSubset

def iterated_double {l₁ l₂ : List α} {a : α} (h : k > 0)
    (c : l₁.CompSubset (replicate k a ++ l₂)) : l₁.CompSubset (a :: l₂) :=
  match k with
  |     1 => c
  | k + 2 => iterated_double (k := k + 1) (by simp) c.double

def trans {l₁ l₂ l₃ : List α} (c₁ : l₁.CompSubset l₂) (c₂ : l₂.CompSubset l₃) : l₁.CompSubset l₃ :=
  match c₂ with
  |     refl _ => c₁
  | perm c₂ hp => (c₁.trans c₂).perm hp
  |   add b c₂ => (c₁.trans c₂).add b
  |  double c₂ => (c₁.trans c₂).double

def cons {l₁ l₂ : List α} (c : l₁.CompSubset l₂) (a) : (a :: l₁).CompSubset (a :: l₂) :=
  match c with
  |     refl _ => CompSubset.refl _
  | perm c₂ hp => (CompSubset.cons c₂ a).perm (by simp [hp])
  |   add b c₂ => ((c₂.cons a).add b).perm (Perm.swap a b _)
  |  double (a := b) (l₂ := l₂) c₂ =>
    have : (a :: l₁).CompSubset (b :: b :: a :: l₂) := (c₂.cons a).perm (by grind)
    this.double.perm (Perm.swap a b l₂)

end CompSubset

def Subset.toCompSubst {l₁ l₂ : List α} (h : l₁ ⊆ l₂) : l₁.CompSubset l₂ :=
  match l₂ with
  |      [] =>
    have : l₁ = [] := by simpa using h
    this ▸ CompSubset.refl []
  | a :: l₂ =>
    if ha : a ∈ l₁ then
      have : l₁.CompSubset (replicate (l₁.count a) a ++ l₁.remove a) := (CompSubset.refl l₁).perm (perm_normalize l₁ a)
      have c₁ : l₁.CompSubset (a :: remove a l₁) := this.iterated_double (count_pos_iff.mpr ha)
      have : remove a l₁ ⊆ l₂ := by grind only [= subset_def, usr eq_or_mem_of_mem_cons, mem_remove_iff]
      have c₂ : (remove a l₁).CompSubset l₂ := Subset.toCompSubst this
      c₁.trans (c₂.cons a)
    else
      have : l₁ ⊆ l₂ := by grind
      CompSubset.add _ (Subset.toCompSubst this)

end List

namespace LO.FirstOrder.LinearLogic

variable {L : Language}

abbrev Sequent (L : Language) := List (Statement L)

def Sequent.IsQuest (Γ : Sequent L) : Prop := ∀ φ ∈ Γ, φ.IsQuest

namespace Sequent.IsQuest

@[simp] lemma nil : Sequent.IsQuest ([] : Sequent L) := by simp [Sequent.IsQuest]

@[simp] lemma cons (φ : Statement L) (Γ : Sequent L) :
    Sequent.IsQuest (φ :: Γ) ↔ φ.IsQuest ∧ Sequent.IsQuest Γ := by simp [Sequent.IsQuest]

end Sequent.IsQuest

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
  | plusLeft : Derivation (ψ :: Γ) → (φ : Statement L) → Derivation (φ ⨁ ψ :: Γ)
  | plusRight : Derivation (φ :: Γ) → (ψ : Statement L) → Derivation (φ ⨁ ψ :: Γ)
  | ofCourse : Derivation (φ :: Γ) → Sequent.IsQuest Γ → Derivation (！φ :: Γ)
  | weakening : Derivation Γ → (φ : Statement L) → Derivation (？φ :: Γ)
  | dereliction : Derivation (φ :: Γ) → Derivation (？φ :: Γ)
  | contraction : Derivation (？φ :: ？φ :: Γ) → Derivation (？φ :: Γ)
  | all : Derivation (φ.free :: Γ⁺) → Derivation ((∀⁰ φ) :: Γ)
  | exs (t) : Derivation (φ/[t] :: Γ) → Derivation ((∃⁰ φ) :: Γ)

abbrev Statement.Proof (φ : Statement L) : Type _ := Derivation [φ]

abbrev Sentence.Proof (σ : Sentence L) : Type _ := Derivation [(σ : Statement L)]

inductive SymbolFV (L : Language) where
  | symbol : SymbolFV L

notation "𝐋𝐋₀" => SymbolFV.symbol

instance : Entailment (SymbolFV L) (Statement L) := ⟨fun _ ↦ Statement.Proof⟩

inductive Symbol (L : Language) where
  | symbol : Symbol L

notation "𝐋𝐋" => Symbol.symbol

instance : Entailment (Symbol L) (Sentence L) := ⟨fun _ ↦ Sentence.Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent L) : Prop := Nonempty (⊢! Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

variable {Γ Δ : Sequent L}

def cast (d : ⊢! Γ) (e : Γ = Δ) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! φ :: Γ) : ⊢! Γ ++ [φ] :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def invRotate (d : ⊢! Γ ++ [φ]) : ⊢! φ :: Γ :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def height {Γ : Sequent L} : ⊢! Γ → ℕ
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

@[simp] lemma height_id (φ : Statement L) :
    (identity φ).height = 0 := rfl

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
    (d.weakening φ).height = d.height + 1 := rfl

@[simp] lemma height_dereliction (d : ⊢! φ :: Γ) :
    d.dereliction.height = d.height + 1 := rfl

@[simp] lemma height_contraction (d : ⊢! ？φ :: ？φ :: Γ) :
    d.contraction.height = d.height + 1 := rfl

@[simp] lemma height_all {φ : Semistatement L 1} (d : ⊢! φ.free :: Γ⁺) :
    d.all.height = d.height + 1 := rfl

@[simp] lemma height_exs {φ : Semistatement L 1} {t} (d : ⊢! φ/[t] :: Γ) :
    (d.exs t).height = d.height + 1 := rfl

@[simp] lemma height_cast (d : ⊢! Γ) (e : Γ = Δ) :
    (d.cast e).height = d.height := by rcases e; rfl

end height

def eta : (φ : Statement L) → ⊢! [φ, ∼φ]
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
    have : ⊢! [(∼φ.shift)/[&0], φ.free] := (eta φ.free).rotate.cast (by simp)
    have : ⊢! φ.free :: [∃⁰ ∼φ]⁺ := (this.exs _).rotate.cast (by simp)
    this.all
  |      ∃⁰ φ =>
    have : ⊢! [φ.shift/[&0], ∼φ.free] := (eta φ.free).cast (by simp)
    have : ⊢! (∼φ).free :: [∃⁰ φ]⁺ := (this.exs _).rotate.cast (by simp)
    this.all.rotate
  termination_by φ => φ.complexity

def ofNegative : (ν : Statement L) → ν.Negative → ⊢! [∼？ν, ν]
  |    ？φ, h => (identity (？φ)).rotate.ofCourse (by simp)
  |     ⊥, h => (one.ofCourse (by simp)).falsum.rotate
  |     ⊤, h => (verum [！0]).rotate
  | ν ⅋ μ, h =>
    have ihν : ⊢! [∼？ν, ν] := ofNegative ν (by rcases h; assumption)
    have ihμ : ⊢! [∼？μ, μ] := ofNegative μ (by rcases h; assumption)
    have : ⊢! [！(∼ν ⨂ ∼μ), ？ν, ？μ] :=
      (((identity ν).rotate.tensor (identity μ).rotate).rotate.dereliction.rotate.dereliction.rotate).ofCourse (by simp)
    have : ⊢! [！(∼ν ⨂ ∼μ), ν, μ] := (this.rotate.cut ihν).cut ihμ
    this.rotate.par.rotate
  | ν ＆ μ, h =>
    have ihν : ⊢! [∼？ν, ν] := ofNegative ν (by rcases h; assumption)
    have ihμ : ⊢! [∼？μ, μ] := ofNegative μ (by rcases h; assumption)
    have : ⊢! [！(∼ν ⨁ ∼μ), ？ν] := ((identity ν).rotate.plusRight (∼μ)).rotate.dereliction.rotate.ofCourse (by simp)
    have dν : ⊢! [ν, ！(∼ν ⨁ ∼μ)] := (this.rotate.cut ihν).rotate
    have : ⊢! [！(∼ν ⨁ ∼μ), ？μ] := ((identity μ).rotate.plusLeft (∼ν)).rotate.dereliction.rotate.ofCourse (by simp)
    have dμ : ⊢! [μ, ！(∼ν ⨁ ∼μ)] := (this.rotate.cut ihμ).rotate
    (dν.with dμ).rotate
  |   ∀⁰ ν, h =>
    have ih : ⊢! [∼？ν.free, ν.free] := ofNegative ν.free (by rcases h; simpa)
    have : ⊢! [！(∃⁰ ∼ν.shift), ？ν.free] := (exs &0 <| (identity ν.free).dereliction.rotate.cast (by simp)).ofCourse (by simp)
    have : ⊢! (ν).free :: [∼？(∀⁰ ν)]⁺ := (this.rotate.cut ih).rotate.cast (by simp)
    this.all.rotate
  termination_by ν => ν.complexity

def negativeWeakening {ν : Statement L} (h : ν.Negative) (d : ⊢! Γ) :
    ⊢! ν :: Γ := ((d.weakening ν).cut (ofNegative ν h)).invRotate

def negativeContraction {ν : Statement L} (h : ν.Negative) (d : ⊢! ν :: ν :: Γ) :
    ⊢! ν :: Γ :=
  have : ⊢! ？ν :: ？ν :: Γ := d.dereliction.rotate.dereliction.exchange (by simp)
  have : ⊢! ？ν :: Γ := this.contraction
  this.cut (ofNegative ν h) |>.invRotate

def negativeWk [L.DecidableEq] {Γ Δ : Sequent L} (hΔ : ∀ ν ∈ Δ, ν.Negative) (ss : Γ ⊆ Δ) (d : ⊢! Γ) :
    ⊢! Δ :=
  let rec wk {Γ Δ : Sequent L} (c : Γ.CompSubset Δ) (d : ⊢! Γ) (hΔ : ∀ ν ∈ Δ, ν.Negative) :
      ⊢! Δ :=
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

end Derivation

end LO.FirstOrder.LinearLogic
