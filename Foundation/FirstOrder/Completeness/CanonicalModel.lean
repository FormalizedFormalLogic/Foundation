module

public import Foundation.FirstOrder.Hauptsatz
public import Foundation.Logic.ForcingRelation

@[expose] public section

/-!
# Canonical model for classical first-order logic

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/

namespace LO.FirstOrder.Derivation.Canonical

variable {L : Language}

local notation "ℙ" => Sequent L

instance : LE ℙ := ⟨fun q p ↦ Nonempty (q ≼ p)⟩

instance : Preorder ℙ where
  le_refl p := ⟨StrongerThan.refl p⟩
  le_trans p q r := by
    rintro ⟨hqp⟩ ⟨hrq⟩
    exact ⟨StrongerThan.trans hqp hrq⟩

variable (L)

def ConsistentSequent := {Γ : Sequent L // IsEmpty (⊢ᴸᴷ¹ ∼Γ)}

variable {L}

local notation "ℙ⁻" => ConsistentSequent L

namespace ConsistentSequent

instance : Preorder ℙ⁻ where
  le q p := q.val ≤ p.val
  le_refl p := by simp
  le_trans p q r := le_trans

def nil : ℙ⁻ := ⟨[], by simp⟩

instance : OrderTop ℙ⁻ where
  top := nil
  le_top := by
    rintro ⟨Γ, hΓ⟩
    exact ⟨StrongerThan.ofSubset <| List.nil_subset Γ⟩

def ofUnprovable (φ : Proposition L) (h : 𝐋𝐊¹ ⊬ ∼φ) : ℙ⁻ := ⟨[φ], by simpa [LK.Proof.unprovable_def] using h⟩

end ConsistentSequent

abbrev IsForced (p : ℙ⁻) (φ : Propositionᵢ L) := Nonempty (Forces p.val φ)

instance : ForcingRelation ℙ⁻ (Propositionᵢ L) := ⟨IsForced⟩

instance : WeakForcingRelation ℙ⁻ (Proposition L) := ⟨fun p φ ↦ p ⊩ φᴺ⟩

open Classical

namespace IsForced

@[simp] lemma rel {p : ℙ⁻} {k} {R : L.Rel k} {v} : p ⊩ .rel R v ↔ Nonempty (⊢ᴸᴷ¹ .rel R v :: ∼p.val) := by
  constructor
  · rintro ⟨b⟩
    have ⟨d, hd⟩ := b.relEquiv
    exact ⟨d⟩
  · rintro ⟨d⟩
    let ⟨b, hb⟩ := hauptsatz d
    exact ⟨Forces.relEquiv.symm ⟨b, hb⟩⟩

@[simp] lemma fal {p : ℙ⁻} : p ⊩ ∀⁰ φ ↔ ∀ t, p ⊩ φ/[t] := by
  constructor
  · rintro ⟨b⟩ t
    exact ⟨b.allEquiv t⟩
  · rintro h
    exact ⟨Forces.allEquiv.symm fun t ↦ (h t).some⟩

@[simp] lemma and {p : ℙ⁻} {φ ψ : Propositionᵢ L} : p ⊩ φ ⋏ ψ ↔ p ⊩ φ ∧ p ⊩ ψ := by
  constructor
  · rintro ⟨b⟩
    have ⟨bφ, bψ⟩ := b.andEquiv
    exact ⟨⟨bφ⟩, ⟨bψ⟩⟩
  · rintro ⟨⟨bφ⟩, ⟨bψ⟩⟩
    exact ⟨Forces.andEquiv.symm ⟨bφ, bψ⟩⟩

@[simp] lemma or {p : ℙ⁻} {φ ψ : Propositionᵢ L} : p ⊩ φ ⋎ ψ ↔ p ⊩ φ ∨ p ⊩ ψ := by
  constructor
  · rintro ⟨b⟩
    have b' := b.orEquiv
    exact b'.rec (fun bφ ↦ .inl ⟨bφ⟩) (fun bψ ↦ .inr ⟨bψ⟩)
  · rintro (⟨⟨hφ⟩⟩ | ⟨⟨hψ⟩⟩)
    · exact ⟨Forces.orEquiv.symm <| .inl hφ⟩
    · exact ⟨Forces.orEquiv.symm <| .inr hψ⟩

@[simp] lemma not_falsum (p : ℙ⁻) : ¬p ⊩ ⊥ := by
  rintro ⟨b⟩
  have ⟨d, hd⟩ := b.falsumEquiv
  exact p.prop.false d

lemma imply {p : ℙ⁻} {φ ψ : Propositionᵢ L} : p ⊩ φ 🡒 ψ ↔ (∀ q ≤ p, q ⊩ φ → q ⊩ ψ) := by
  constructor
  · rintro ⟨b⟩ q ⟨sqp⟩ ⟨bφ⟩
    exact ⟨b.implyEquiv _ sqp bφ⟩
  · rintro h
    refine ⟨Forces.implyEquiv.symm fun q sqp hφ ↦ ?_⟩
    by_cases hq : IsEmpty (⊢ᴸᴷ¹ ∼q)
    · exact (h ⟨q, hq⟩ ⟨sqp⟩ ⟨hφ⟩).some
    · have : Nonempty (⊢ᴸᴷ¹ ∼q) := by simpa using hq
      have d : ⊢ᴸᴷ¹ ∼q := this.some
      let ⟨b, hb⟩ := hauptsatz d
      exact Forces.implyEquiv (Forces.efq ψ p.val) q sqp (Forces.falsumEquiv.symm ⟨b, hb⟩)

lemma not {p : ℙ⁻} {φ : Propositionᵢ L} : p ⊩ ∼φ ↔ (∀ q ≤ p, ¬q ⊩ φ) := by
  simp [Semiformulaᵢ.neg_def, imply]

@[simp] lemma exs {p : ℙ⁻} : p ⊩ ∃⁰ φ ↔ ∃ t, p ⊩ φ/[t] := by
  constructor
  · rintro ⟨b⟩
    have ⟨t, f⟩ := b.exsEquiv
    exact ⟨t, ⟨f⟩⟩
  · rintro ⟨t, h⟩
    exact ⟨Forces.exsEquiv.symm ⟨t, h.some⟩⟩

lemma monotone {p q : ℙ⁻} (hqp : q ≤ p) {φ : Propositionᵢ L} (hφ : p ⊩ φ) : q ⊩ φ :=
  ⟨Forces.monotone hqp.some hφ.some⟩

instance : ForcingRelation.IntKripke ℙ⁻ (· ≥ ·) where
  verum _ := ⟨Forces.implyEquiv.symm fun _ _ d ↦ d⟩
  falsum _ := by simp
  and _ := and
  or _ := or
  imply _ := imply
  not _ := not
  monotone hφ _ hpq := hφ.monotone hpq

lemma sound_minimal {φ : Propositionᵢ L} : 𝗠𝗶𝗻¹ ⊢ φ → ℙ⁻ ∀⊩ φ := by
  rintro ⟨d⟩ p; exact ⟨Forces.sound d p.val⟩

end IsForced

namespace IsWeaklyForced

open IsForced

lemma iff_isForced {φ : Proposition L} {p : ℙ⁻} : p ⊩ᶜ φ ↔ p ⊩ φᴺ := by rfl

lemma dn_neg_iff {φ : Proposition L} {p : ℙ⁻} : p ⊩ᶜ ∼φ ↔ p ⊩ ∼φᴺ := by
  have := by simpa using (sound_minimal (Derivation.neg_doubleNegation φ) p)
  exact (this p (by simp)).symm

@[simp] lemma verum (p : ℙ⁻) : p ⊩ᶜ ⊤ := by simp [iff_isForced, IsForced.not]

@[simp] lemma falsum (p : ℙ⁻) : ¬p ⊩ᶜ ⊥ := by simp [iff_isForced]

@[simp] lemma not {φ : Proposition L} {p : ℙ⁻} : p ⊩ᶜ ∼φ ↔ ∀ q ≤ p, ¬q ⊩ᶜ φ := by
  simp [IsForced.not, dn_neg_iff,]; rfl

@[simp] lemma and {φ ψ : Proposition L} {p : ℙ⁻} : p ⊩ᶜ φ ⋏ ψ ↔ p ⊩ᶜ φ ∧ p ⊩ᶜ ψ := by
  simp [iff_isForced, ]

@[simp] lemma or {φ ψ : Proposition L} {p : ℙ⁻} : p ⊩ᶜ φ ⋎ ψ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ ∨ r ⊩ᶜ ψ := by
  simp [iff_isForced, IsForced.not, ]; grind

@[simp] lemma all {φ : Semiproposition L 1} {p : ℙ⁻} : p ⊩ᶜ ∀⁰ φ ↔ ∀ t, p ⊩ᶜ φ/[t] := by
  simp [iff_isForced, Semiformula.subst_doubleNegation]

@[simp] lemma exs {φ : Semiproposition L 1} {p : ℙ⁻} : p ⊩ᶜ ∃⁰ φ ↔ ∀ q ≤ p, ∃ r ≤ q, ∃ t, r ⊩ᶜ φ/[t] := by
  simp [iff_isForced, IsForced.not, Semiformula.subst_doubleNegation]; grind

lemma monotone {φ : Proposition L} {p q : ℙ⁻} (h : q ≤ p) : p ⊩ᶜ φ → q ⊩ᶜ φ := IsForced.monotone h

lemma gnericity {φ : Proposition L} {p : ℙ⁻} : p ⊩ᶜ φ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ := calc
  p ⊩ᶜ φ ↔ p ⊩ᶜ ∼∼φ := by simp
  _      ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ := by rw [not]; simp [not]

lemma complete {φ : Proposition L} : ℙ⁻ ∀⊩ᶜ φ ↔ 𝐋𝐊¹ ⊢ φ := by
  constructor
  · intro h
    by_contra b
    let p : ℙ⁻ := ⟨[∼φ], ⟨fun bφ ↦ b ⟨by simpa using! bφ⟩⟩⟩
    have hp : p ⊩ φᴺ := h p
    have hn : p ⊩ᶜ ∼φ := ⟨Forces.refl (∼φ)⟩
    have : ∀ q ≤ p, ¬q ⊩ φᴺ := by simpa [not] using! hn
    have : ¬p ⊩ φᴺ := this p (by simp)
    contradiction
  · intro b
    exact sound_minimal <| Provable.gödel_gentzen b

protected lemma refl (φ : Proposition L) (h : 𝐋𝐊¹ ⊬ ∼φ) :
    ConsistentSequent.ofUnprovable φ h ⊩ᶜ φ := ⟨Forces.refl φ⟩

end IsWeaklyForced

end Canonical

end LO.FirstOrder.Derivation
