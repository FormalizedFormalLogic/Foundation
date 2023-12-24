import Logic.Logic.Calculus
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

variable {α : Type*}

abbrev Sequent (α : Type*) := List (Formula α)

def Sequent.box (Δ : Sequent α) : Sequent α := Δ.map Formula.box
prefix:50 "□" => Sequent.box

def Sequent.dia (Δ : Sequent α) : Sequent α := Δ.map Formula.dia
prefix:50 "◇" => Sequent.dia

inductive DerivationCR (P : Formula α → Prop) : Sequent α → Sequent α → Type _
| ax (Γ Δ p)            : DerivationCR P (p :: Γ) (p :: Δ)
| verum (Γ Δ)           : DerivationCR P Γ (⊤ :: Δ)
| negLeft {Γ Δ p}       : DerivationCR P Γ (p :: Δ) → DerivationCR P (~p :: Γ) Δ
| negRight {Γ Δ p}      : DerivationCR P (p :: Γ) Δ → DerivationCR P Γ (~p :: Δ)
| andLeft {Γ Δ p q}     : DerivationCR P (p :: q :: Γ) Δ → DerivationCR P (p ⋏ q :: Γ) Δ
| andRight {Γ Δ p q}    : DerivationCR P Γ (p :: Δ) → DerivationCR P Γ (q :: Δ) → DerivationCR P Γ (p ⋏ q :: Δ)
| orLeft {Γ Δ p q}      : DerivationCR P (p :: Γ) Δ → DerivationCR P (q :: Γ) Δ → DerivationCR P (p ⋎ q :: Γ) Δ
| orRight {Γ Δ p q}     : DerivationCR P Γ (p :: q :: Δ) → DerivationCR P Γ (p ⋎ q :: Δ)
| implyLeft {Γ Δ p q}   : DerivationCR P Γ (p :: Δ) → DerivationCR P (q :: Γ) Δ → DerivationCR P ((p ⟶ q) :: Γ) Δ
| implyRight {Γ Δ p q}  : DerivationCR P (p :: Γ) (q :: Δ) → DerivationCR P Γ ((p ⟶ q) :: Δ)
| wk {Γ Γ' Δ Δ'}        : DerivationCR P Γ Δ → Γ ⊆ Γ' → Δ ⊆ Δ' → DerivationCR P Γ' Δ'
| cut {Δ p}             : P p → DerivationCR P Γ (p :: Δ) → DerivationCR P (p :: Γ) Δ → DerivationCR P Γ Δ
| K {Γ} {p : Formula α} : DerivationCR P Γ [p] → DerivationCR P Γ.box [□p]

scoped notation:45 Γ:45 " ⊢ᴷ[" P "] " Δ:45 => DerivationCR P Γ Δ

abbrev Derivation : Sequent α → Sequent α → Type _ := DerivationCR (fun _ => False)

scoped infix:45 " ⊢ᴷ " => Derivation

abbrev DerivationC : Sequent α → Sequent α → Type _ := DerivationCR (fun _ => True)

abbrev DerivationClx (c : ℕ) : Sequent α → Sequent α → Type _ := DerivationCR (·.complexity < c)

scoped notation:45 Γ:45 "⊢ᴷ[< " c "] " Δ:45 => DerivationClx c Γ Δ

instance : TwoSided (Formula α) := ⟨DerivationC⟩

namespace DerivationCR

variable {P : Formula α → Prop} {Δ Δ₁ Δ₂ Γ : Sequent α}

def length {Γ Δ} : DerivationCR P Γ Δ → ℕ
  | ax _ _ _        => 0
  | verum _ _       => 0
  | negLeft d       => d.length.succ
  | negRight d      => d.length.succ
  | andLeft d       => d.length.succ
  | andRight dp dq  => (max dp.length dq.length).succ
  | orLeft dp dq    => (max dp.length dq.length).succ
  | orRight d       => d.length.succ
  | implyLeft dp dq => (max dp.length dq.length).succ
  | implyRight d    => d.length.succ
  | wk d _ _        => d.length
  | cut _ dp dn     => (max dp.length dn.length).succ
  | K d             => d.length.succ

protected def cast (d : Γ ⊢ᴷ[P] Δ) (e₁ : Γ = Γ') (e₂ : Δ = Δ') : Γ' ⊢ᴷ[P] Δ' := cast (by simp [e₁, e₂]) d

@[simp] lemma length_cast (d : Γ ⊢ᴷ[P] Δ) (e₁ : Γ = Γ') (e₂ : Δ = Δ') : (d.cast e₁ e₂).length = d.length := by
  rcases e₁ with rfl; rcases e₂ with rfl; simp [DerivationCR.cast]

protected def castL (d : Γ ⊢ᴷ[P] Δ) (e : Γ = Γ') : Γ' ⊢ᴷ[P] Δ := DerivationCR.cast d e rfl

@[simp] lemma length_castL (d : Γ ⊢ᴷ[P] Δ) (e : Γ = Γ') : (d.castL e).length = d.length := length_cast d e rfl

protected def castR (d : Γ ⊢ᴷ[P] Δ) (e : Δ = Δ') : Γ ⊢ᴷ[P] Δ' := DerivationCR.cast d rfl e

@[simp] lemma length_castR (d : Γ ⊢ᴷ[P] Δ) (e : Δ = Δ') : (d.castR e).length = d.length := length_cast d rfl e

def cutWeakening {P Q : Formula α → Prop} (h : ∀ p, P p → Q p) {Γ Δ} : Γ ⊢ᴷ[P] Δ → Γ ⊢ᴷ[Q] Δ
  | ax _ _ _        => ax _ _ _
  | verum _ _       => verum _ _
  | negLeft d       => negLeft (d.cutWeakening h)
  | negRight d      => negRight (d.cutWeakening h)
  | andLeft d       => andLeft (d.cutWeakening h)
  | andRight dp dq  => andRight (dp.cutWeakening h) (dq.cutWeakening h)
  | orLeft dp dq    => orLeft (dp.cutWeakening h) (dq.cutWeakening h)
  | orRight d       => orRight (d.cutWeakening h)
  | implyLeft dp dq => implyLeft (dp.cutWeakening h) (dq.cutWeakening h)
  | implyRight d    => implyRight (d.cutWeakening h)
  | cut hp d₁ d₂    => cut (h _ hp) (d₁.cutWeakening h) (d₂.cutWeakening h)
  | wk d p₁ p₂      => wk (d.cutWeakening h) p₁ p₂
  | K d             => K (d.cutWeakening h)

def em (hΓ : p ∈ Γ) (hΔ : p ∈ Δ) : Γ ⊢ᴷ[P] Δ := (ax Γ Δ p).wk (by simp[hΓ]) (by simp[hΔ])

def falsum (Γ Δ) : (⊥ :: Γ) ⊢ᴷ[P] Δ := negLeft $ verum Γ _

def cCut (d₁ : Γ ⊢² p :: Δ) (d₂ : p :: Γ ⊢² Δ) : Γ ⊢² Δ := cut trivial d₁ d₂

end DerivationCR

instance : Gentzen (Formula α) where
  verum := DerivationCR.verum
  falsum := DerivationCR.falsum
  negLeft := DerivationCR.negLeft
  negRight := DerivationCR.negRight
  andLeft := DerivationCR.andLeft
  andRight := DerivationCR.andRight
  orLeft := DerivationCR.orLeft
  orRight := DerivationCR.orRight
  implyLeft := DerivationCR.implyLeft
  implyRight := DerivationCR.implyRight
  wk := DerivationCR.wk
  em := DerivationCR.em

instance : Gentzen.Cut (Formula α) := ⟨DerivationCR.cCut⟩

end Modal

end LO
