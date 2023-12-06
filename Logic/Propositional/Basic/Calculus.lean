import Logic.Propositional.Basic.Formula
import Logic.Logic.System

namespace LO

namespace Propositional

variable {α : Type*} [DecidableEq α]

abbrev Sequent (α : Type*) := Finset (Formula α)

inductive DerivationCR (P : Formula α → Prop) : Sequent α → Type _
| axL   : ∀ (Δ : Sequent α) (a : α),
    Formula.atom a ∈ Δ → Formula.natom a ∈ Δ → DerivationCR P Δ
| verum : ∀ (Δ : Sequent α), ⊤ ∈ Δ → DerivationCR P Δ
| or    : ∀ (Δ : Sequent α) (p q : Formula α),
    DerivationCR P (insert p $ insert q Δ) → DerivationCR P (insert (p ⋎ q) Δ)
| and   : ∀ (Δ : Sequent α) (p q : Formula α),
    DerivationCR P (insert p Δ) → DerivationCR P (insert q Δ) → DerivationCR P (insert (p ⋏ q) Δ)
| cut   : ∀ (Δ Γ : Sequent α) (p : Formula α), P p →
    DerivationCR P (insert p Δ) → DerivationCR P (insert (~p) Γ) → DerivationCR P (Δ ∪ Γ)

scoped notation :45 "⊢ᴾᶜ[" P "] " Γ:45 => DerivationCR P Γ

abbrev Derivation : Sequent α → Type _ := DerivationCR (fun _ => False)

scoped prefix:45 "⊢ᴾᵀ " => Derivation

abbrev DerivationC : Sequent α → Type _ := DerivationCR (fun _ => True)

scoped prefix:45 "⊢ᴾᶜ " => DerivationC

abbrev DerivationClx (c : ℕ) : Sequent α → Type _ := DerivationCR (·.complexity < c)

scoped notation :45 "⊢ᴾᶜ[< " c "] " Γ:45 => DerivationClx c Γ

namespace DerivationCR

variable {P : Formula α → Prop} {Δ Δ₁ Δ₂ Γ : Sequent α}

def length : {Δ : Sequent α} → DerivationCR P Δ → ℕ
  | _, axL _ _ _ _       => 0
  | _, verum Δ _         => 0
  | _, or _ _ _ d        => d.length.succ
  | _, and _ _ _ dp dq   => (max dp.length dq.length).succ
  | _, cut _ _ _ _ dp dn => (max dp.length dn.length).succ

section

@[simp] lemma length_axL {a : α} (hpos : Formula.atom a ∈ Δ) (hneg : Formula.natom a ∈ Δ) :
  (axL (P := P) Δ a hpos hneg).length = 0 := rfl

@[simp] lemma length_verum (h : ⊤ ∈ Δ) : (verum (P := P) Δ h).length = 0 := rfl

@[simp] lemma length_and {p q} (dp : ⊢ᴾᶜ[P] insert p Δ) (dq : ⊢ᴾᶜ[P] insert q Δ) : (and Δ p q dp dq).length = (max dp.length dq.length).succ := rfl

@[simp] lemma length_or {p q} (d : ⊢ᴾᶜ[P] (insert p $ insert q Δ)) : (or Δ p q d).length = d.length.succ := rfl

@[simp] lemma length_cut {p} (hp : P p) (dp : ⊢ᴾᶜ[P] insert p Δ) (dn : ⊢ᴾᶜ[P] insert (~p) Γ) :
  (cut _ _ p hp dp dn).length = (max dp.length dn.length).succ := rfl

end

protected def cast (d : ⊢ᴾᶜ[P] Δ) (e : Δ = Γ) : ⊢ᴾᶜ[P] Γ := cast (by simp[HasVdash.vdash, e]) d

@[simp] lemma length_cast (d : ⊢ᴾᶜ[P] Δ) (e : Δ = Γ) : (d.cast e).length = d.length := by
  rcases e with rfl; simp[DerivationCR.cast]

def weakening : ∀ {Δ}, ⊢ᴾᶜ[P] Δ → ∀ {Γ : Sequent α}, Δ ⊆ Γ → ⊢ᴾᶜ[P] Γ
  | _, axL Δ a hrel hnrel, Γ,   h => axL Γ a (h hrel) (h hnrel)
  | _, verum Δ htop,         Γ, h => verum Γ (h htop)
  | _, or Δ p q d,           Γ, h =>
      have : ⊢ᴾᶜ[P] (insert p $ insert q Γ) :=
        weakening d (Finset.insert_subset_insert p $ Finset.insert_subset_insert q (Finset.insert_subset_iff.mp h).2)
      have : ⊢ᴾᶜ[P] insert (p ⋎ q) Γ := or Γ p q this
      this.cast (by simp; exact (Finset.insert_subset_iff.mp h).1)
  | _, and Δ p q dp dq,      Γ, h =>
      have dp : ⊢ᴾᶜ[P] insert p Γ := dp.weakening (Finset.insert_subset_insert p (Finset.insert_subset_iff.mp h).2)
      have dq : ⊢ᴾᶜ[P] insert q Γ := dq.weakening (Finset.insert_subset_insert q (Finset.insert_subset_iff.mp h).2)
      have : ⊢ᴾᶜ[P] insert (p ⋏ q) Γ := and Γ p q dp dq
      this.cast (by simp; exact (Finset.insert_subset_iff.mp h).1)
  | _, cut Δ₁ Δ₂ p hp d₁ d₂, Γ, h =>
      have d₁ : ⊢ᴾᶜ[P] insert p Γ := d₁.weakening (Finset.insert_subset_insert _ (Finset.union_subset_left h))
      have d₂ : ⊢ᴾᶜ[P] insert (~p) Γ := d₂.weakening (Finset.insert_subset_insert _ (Finset.union_subset_right h))
      (cut Γ Γ p hp d₁ d₂).cast (by simp)

@[simp] lemma length_weakening {Δ} (d : ⊢ᴾᶜ[P] Δ) {Γ : Sequent α} (h : Δ ⊆ Γ) : (d.weakening h).length = d.length :=
  by induction d generalizing Γ <;> simp[*, weakening]

def or' {p q : Formula α} (h : p ⋎ q ∈ Δ) (d : ⊢ᴾᶜ[P] (insert p $ insert q $ Δ.erase (p ⋎ q))) : ⊢ᴾᶜ[P] Δ :=
  (or _ p q d).cast (by simp[Finset.insert_erase h])

def and' {p q : Formula α} (h : p ⋏ q ∈ Δ)
    (dp : ⊢ᴾᶜ[P] insert p (Δ.erase (p ⋏ q))) (dq : ⊢ᴾᶜ[P] insert q (Δ.erase (p ⋏ q))) : ⊢ᴾᶜ[P] Δ :=
  (and _ p q dp dq).cast (by simp[Finset.insert_erase h])

def em {p : Formula α} {Δ : Sequent α} (hpos : p ∈ Δ) (hneg : ~p ∈ Δ) : ⊢ᴾᶜ[P] Δ := by
  induction p using Formula.rec' generalizing Δ
  case hverum           => exact verum Δ hpos
  case hfalsum          => exact verum Δ hneg
  case hrel a           => exact axL Δ a hpos hneg
  case hnrel a          => exact axL Δ a hneg hpos
  case hand p q ihp ihq =>
    simp at hneg
    exact or' hneg (and' (p := p) (q := q) (by simp[hpos])
      (ihp (by simp) (by simp; exact Or.inr $ Formula.ne_of_ne_complexity (by simp)))
      (ihq (by simp) (by simp; exact Or.inr $ Formula.ne_of_ne_complexity (by simp))))
  case hor p q ihp ihq  =>
    simp at hneg
    exact or' hpos (and' (p := ~p) (q := ~q) (by simp[hneg])
      (ihp (by simp; exact Or.inr $ Formula.ne_of_ne_complexity (by simp)) (by simp))
      (ihq (by simp; exact Or.inr $ Formula.ne_of_ne_complexity (by simp)) (by simp)))

end DerivationCR

structure DerivationCRWA (P : Formula α → Prop) (T : Theory α) (Δ : Sequent α) where
  leftHand : Finset (Formula α)
  hleftHand : (leftHand : Set (Formula α)) ⊆ (~·) '' T
  derivation : ⊢ᴾᶜ[P] Δ ∪ leftHand

scoped notation :45 T " ⊢ᴾᶜ[" P "] " Γ:45 => DerivationCRWA P T Γ

abbrev DerivationCWA (T : Theory α) (Δ : Sequent α) := DerivationCRWA (fun _ => True) T Δ

scoped infix:45 " ⊢' " => DerivationCWA

instance Proof : System (Formula α) where
  Bew := fun T σ => T ⊢' {σ}
  axm := fun {f σ} hσ =>
    { leftHand := {~σ}
      hleftHand := by simp[hσ]
      derivation := DerivationCR.em (p := σ) (by simp) (by simp) }
  weakening' := fun {T U} f h b =>
    { leftHand := b.leftHand,
      hleftHand := Set.Subset.trans b.hleftHand (Set.image_subset _ h),
      derivation := b.derivation }

end Propositional

end LO
