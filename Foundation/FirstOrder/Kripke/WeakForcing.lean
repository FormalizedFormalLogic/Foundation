import Foundation.FirstOrder.Kripke.Intuitionistic
import Foundation.FirstOrder.NegationTranslation.GoedelGentzen

/-! # Weak forcing

Main reference: Jeremy Avigad, "Forcing in proof theory"
-/

namespace LO.FirstOrder.KripkeModel

variable {L : Language} [L.Relational] {ℙ : KripkeModel L}

def WeaklyForces (p : ℙ) (bv : Fin n → ℙ.Name) (fv : ξ → ℙ.Name) (φ : Semiformula L ξ n) : Prop := ℙ.Forces p bv fv φᴺ

local notation:45 p " ⊩[" bv "|" fv "] " φ:46 => WeaklyForces p bv fv φ

@[simp] lemma exists_le {α : Type*} [Preorder α] (a : α) : ∃ x, x ≤ a := ⟨a, by rfl⟩
namespace WeaklyForces

variable {bv : Fin n → ℙ.Name} {fv : ξ → ℙ.Name}

@[simp] lemma rel {R : L.Rel k} {t : Fin k → Semiterm L ξ n} :
    p ⊩[bv|fv] Semiformula.rel R t ↔ ∀ q ≤ p, ∃ r ≤ q, ℙ.Rel r R fun i ↦ (t i).relationalVal bv fv := by simp [WeaklyForces]

@[simp] lemma nrel {R : L.Rel k} {t : Fin k → Semiterm L ξ n} :
    p ⊩[bv|fv] Semiformula.nrel R t ↔ ∀ q ≤ p, ¬ℙ.Rel q R fun i ↦ (t i).relationalVal bv fv := by simp [WeaklyForces]

@[simp] lemma verum : p ⊩[bv|fv] (⊤ : Semiformula L ξ n) := by simp [WeaklyForces]

@[simp] lemma falsum : ¬p ⊩[bv|fv] (⊥ : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma and {φ ψ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ⋏ ψ ↔ p ⊩[bv|fv] φ ∧ p ⊩[bv|fv] ψ := by simp [WeaklyForces]

@[simp] lemma or {φ ψ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ⋎ ψ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩[bv|fv] φ ∨ r ⊩[bv|fv] ψ := by
  suffices
      (∀ q ≤ p, (∃ r ≤ q, Forces r bv fv φᴺ) ∨ ∃ r ≤ q, Forces r bv fv ψᴺ) ↔
      ∀ q ≤ p, ∃ r ≤ q, Forces r bv fv φᴺ ∨ Forces r bv fv ψᴺ by
    simpa [WeaklyForces, -not_and, not_and_or]
  grind

@[simp] lemma all {φ : Semiformula L ξ (n + 1)} :
    p ⊩[bv|fv] ∀' φ ↔ ∀ q ≤ p, ∀ x : q, WeaklyForces q (x :> bv) fv φ := by simp [WeaklyForces]

@[simp] lemma ex {φ : Semiformula L ξ (n + 1)} :
    p ⊩[bv|fv] ∃' φ ↔ ∀ q ≤ p, ∃ r ≤ q, ∃ x : r, r ⊩[x :> bv|fv] φ := by
  suffices
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ ℙ.Domain r, ∃ s ≤ r, s ⊩[x :> bv|fv] φ) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ ℙ.Domain r, r ⊩[x :> bv|fv] φ) by
    simpa [WeaklyForces]
  constructor
  · intro h q hqp
    rcases h q hqp with ⟨r, hrq, x, hx, s, hsr, H⟩
    exact ⟨s, le_trans hsr hrq, x, ℙ.domain_antimonotone hsr hx, H⟩
  · intro h q hqp
    rcases h q hqp with ⟨r, hrq, x, hx, H⟩
    exact ⟨r, hrq, x, hx, r, by rfl, H⟩

lemma monotone {φ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ → ∀ q ≤ p, q ⊩[bv|fv] φ := fun h ↦ Forces.monotone h

lemma genricity {n} {bv : Fin n → ℙ.Name} {fv : ξ → ℙ.Name} {φ : Semiformula L ξ n} :
    (∀ q ≤ p, ∃ r ≤ q, r ⊩[bv|fv] φ) → p ⊩[bv|fv] φ :=
  match φ with
  | .rel R v => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∃ s ≤ q, ℙ.Rel s R fun i ↦ (v i).relationalVal bv fv) →
      (∀ q ≤ p, ∃ r ≤ q, ℙ.Rel r R fun i ↦ (v i).relationalVal bv fv) by simpa
    intro h q hqp
    rcases h q hqp with ⟨r, hrq, H⟩
    rcases H r (by rfl) with ⟨s, hsr, Hs⟩
    exact ⟨s, le_trans hsr hrq, Hs⟩
  | .nrel R v => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ¬ℙ.Rel s R fun i ↦ (v i).relationalVal bv fv) →
      (∀ q ≤ p, ¬ℙ.Rel q R fun i ↦ (v i).relationalVal bv fv) by simpa
    intro h q hqp hR
    rcases h q hqp with ⟨r, hrq, Hr⟩
    exact Hr r (by rfl) (ℙ.rel_monotone hR r hrq)
  | ⊤ => by simp
  | ⊥ => by simp
  | φ ⋏ ψ => by
    suffices (∀ q ≤ p, ∃ r ≤ q, r ⊩[bv|fv] φ ∧ r ⊩[bv|fv] ψ) → p ⊩[bv|fv] φ ∧ p ⊩[bv|fv] ψ by simpa
    intro h
    refine ⟨genricity fun q hqp ↦ ?_, genricity fun q hqp ↦ ?_⟩
    · rcases h q hqp with ⟨r, hrq, h, _⟩
      exact ⟨r, hrq, h⟩
    · rcases h q hqp with ⟨r, hrq, _, h⟩
      exact ⟨r, hrq, h⟩
  | φ ⋎ ψ => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∃ r ≤ q, r ⊩[bv|fv] φ ∨ r ⊩[bv|fv] ψ) →
      (∀ q ≤ p, ∃ r ≤ q, r ⊩[bv|fv] φ ∨ r ⊩[bv|fv] ψ) by simpa
    intro h q hqp
    rcases h q hqp with ⟨r, hrq, H⟩
    rcases H r (by rfl) with ⟨s, hsr, Hs⟩
    exact ⟨s, le_trans hsr hrq, Hs⟩
  | ∀' φ => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∀ a ∈ ℙ.Domain q, q ⊩[a :> bv|fv] φ) →
      (∀ q ≤ p, ∀ x ∈ ℙ.Domain q, q ⊩[x :> bv|fv] φ) by simpa
    intro h q hqp x hx
    apply genricity
    intro r hrq
    rcases h r (le_trans hrq hqp) with ⟨s, hsr, Hs⟩
    exact ⟨s, hsr, Hs s (by rfl) x (ℙ.domain_antimonotone' hx _ (le_trans hsr hrq))⟩
  | ∃' φ => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∃ r ≤ q, ∃ x ∈ ℙ.Domain r, r ⊩[x :> bv|fv] φ) →
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ ℙ.Domain r, r ⊩[x :> bv|fv] φ) by simpa
    intro h q hqp
    rcases h q hqp with ⟨r, hrq, H⟩
    rcases H r (by rfl) with ⟨s, hsr, x, hx, H⟩
    exact ⟨s, le_trans hsr hrq, x, hx, H⟩

lemma genricity_iff {φ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩[bv|fv] φ :=
  ⟨fun H q hqp ↦ ⟨q, by rfl, H.monotone q hqp⟩, genricity⟩

lemma genricity_iff_not {φ : Semiformula L ξ n} :
    ¬p ⊩[bv|fv] φ ↔ ∃ q ≤ p, ∀ r ≤ q, ¬r ⊩[bv|fv] φ := by simpa using genricity_iff.not

@[simp] lemma not {n} {bv : Fin n → ℙ.Name} {fv : ξ → ℙ.Name} {φ : Semiformula L ξ n} :
    p ⊩[bv|fv] ∼φ ↔ ∀ q ≤ p, ¬q ⊩[bv|fv] φ :=
  match φ with
  | .rel R v => by
    suffices
      (∀ q ≤ p, ¬ℙ.Rel q R fun i ↦ (v i).relationalVal bv fv) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ¬ℙ.Rel s R fun i ↦ (v i).relationalVal bv fv) by simpa
    constructor
    · intro h q hqp
      exact ⟨q, by rfl, fun r hrq ↦ h r (le_trans hrq hqp)⟩
    · intro h q hqp H
      rcases h q hqp with ⟨r, hrq, Hr⟩
      exact Hr r (by rfl) (ℙ.rel_monotone H _ hrq)
  | .nrel R v => by simp
  | ⊤ => by simp
  | ⊥ => by simp
  | φ ⋏ ψ => by
    suffices
        (∀ q ≤ p, ∃ r ≤ q, r ⊩[bv|fv] ∼φ ∨ r ⊩[bv|fv] ∼ψ) ↔
        (∀ q ≤ p, ¬q ⊩[bv|fv] φ ∨ ¬q ⊩[bv|fv] ψ) by
      simpa [-not_and, not_and_or]
    constructor
    · intro h q hqp
      rcases h q hqp with ⟨r, hrq, (H | H)⟩
      · left; intro Hqφ
        exact WeaklyForces.not.mp H r (by rfl) (Hqφ.monotone _ hrq)
      · right; intro Hqψ
        exact WeaklyForces.not.mp H r (by rfl) (Hqψ.monotone _ hrq)
    · intro h q hqp
      rcases h q hqp with (C | C)
      · rcases genricity_iff_not.mp C with ⟨r, hrq, Hr⟩
        refine ⟨r, hrq, ?_⟩
        left; apply WeaklyForces.not.mpr Hr
      · rcases genricity_iff_not.mp C with ⟨r, hrq, Hr⟩
        refine ⟨r, hrq, ?_⟩
        right; apply WeaklyForces.not.mpr Hr
  | φ ⋎ ψ => by
    suffices
      p ⊩[bv|fv] ∼φ ∧ p ⊩[bv|fv] ∼ψ ↔
      ∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ¬s ⊩[bv|fv] φ ∧ ¬s ⊩[bv|fv] ψ by simpa
    constructor
    · intro h q hqp
      refine ⟨q, by rfl, fun r hrq ↦ ⟨?_, ?_⟩⟩
      · exact WeaklyForces.not.mp h.1 r (le_trans hrq hqp)
      · exact WeaklyForces.not.mp h.2 r (le_trans hrq hqp)
    · intro h
      constructor
      · apply WeaklyForces.not.mpr
        intro q hqp Hq
        rcases h q hqp with ⟨r, hrq, H⟩
        exact (H r (by rfl)).1 (Hq.monotone _ hrq)
      · apply WeaklyForces.not.mpr
        intro q hqp Hq
        rcases h q hqp with ⟨r, hrq, H⟩
        exact (H r (by rfl)).2 (Hq.monotone _ hrq)
  | ∀' φ => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∃ a ∈ ℙ.Domain r, r ⊩[a :> bv|fv] ∼φ) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ ℙ.Domain r, ¬r ⊩[x :> bv|fv] φ) by simpa
    constructor
    · intro h q hqp
      rcases h q hqp with ⟨r, hrq, x, hx, Hr⟩
      exact ⟨r, hrq, x, hx, WeaklyForces.not.mp Hr r (by rfl)⟩
    · intro h q hqp
      rcases h q hqp with ⟨r, hrq, x, hx, H⟩
      rcases genricity_iff_not.mp H with ⟨s, hsr, Hs⟩
      exact ⟨s, le_trans hsr hrq, x, ℙ.domain_antimonotone hsr hx, WeaklyForces.not.mpr Hs⟩
  | ∃' φ => by
    suffices
      (∀ q ≤ p, ∀ a ∈ ℙ.Domain q, q ⊩[a :> bv|fv] ∼φ) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ∀ x ∈ ℙ.Domain s, ¬s ⊩[x :> bv|fv] φ) by simpa
    constructor
    · intro h q hqp
      refine ⟨q, by rfl, ?_⟩
      intro r hrq x hx
      exact WeaklyForces.not.mp (h r (le_trans hrq hqp) x hx) r (by rfl)
    · intro h q hqp x hx
      apply WeaklyForces.not.mpr
      intro r hrq Hr
      rcases h r (le_trans hrq hqp) with ⟨s, hsr, H⟩
      have : ¬s ⊩[x :> bv|fv] φ := H s (by rfl) x (ℙ.domain_antimonotone (le_trans hsr hrq) hx)
      exact this (Hr.monotone _ hsr)

lemma genricity_iff_not' {φ : Semiformula L ξ n} :
    ¬p ⊩[bv|fv] φ ↔ ∃ q ≤ p, q ⊩[bv|fv] ∼φ := by simpa using genricity_iff.not

@[simp] lemma imply {φ ψ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ➝ ψ ↔ ∀ q ≤ p, q ⊩[bv|fv] φ → q ⊩[bv|fv] ψ := by
  suffices
    (∀ q ≤ p, ∃ r ≤ q, (∀ q ≤ r, ¬q ⊩[bv|fv] φ) ∨ r ⊩[bv|fv] ψ) ↔
    (∀ q ≤ p, q ⊩[bv|fv] φ → q ⊩[bv|fv] ψ) by simpa [DeMorgan.imply]
  constructor
  · intro h q hqp Hqφ
    by_contra! Hqψ
    rcases genricity_iff_not.mp Hqψ with ⟨r, hrq, Hr⟩
    rcases h r (le_trans hrq hqp) with ⟨s, hsr, (H | H)⟩
    · exact H s (by rfl) (Hqφ.monotone s (le_trans hsr hrq))
    · exact Hr s hsr H
  · intro h q hqp
    have : ¬q ⊩[bv|fv] φ ∨ q ⊩[bv|fv] ψ := not_or_of_imp (h q hqp)
    rcases this with (H | H)
    · rcases genricity_iff_not.mp H with ⟨r, hrq, H⟩
      exact ⟨r, hrq, Or.inl H⟩
    · exact ⟨q, by rfl, Or.inr H⟩

@[simp] lemma iff {φ ψ : Semiformula L ξ n} :
    p ⊩[bv|fv] φ ⭤ ψ ↔ ∀ q ≤ p, q ⊩[bv|fv] φ ↔ q ⊩[bv|fv] ψ := by
  simp [LogicalConnective.iff]; grind

end WeaklyForces

abbrev WeaklyForces₀ (p : ℙ) (φ : Sentence L) : Prop := p ⊩[![]|Empty.elim] ↑φ

instance : WeakForcingRelation ℙ (Sentence L) := ⟨WeaklyForces₀⟩

lemma WeaklyForces₀.def {p : ℙ} {φ : Sentence L} : p ⊩ᶜ φ ↔ p ⊩[![]|Empty.elim] φ := by rfl

lemma weaklyForces_iff_forces {p : ℙ} {φ : Sentence L} :
    p ⊩ᶜ φ ↔ p ⊩ φᴺ := by rfl

instance : WeakForcingRelation.ClassicalKripke ℙ (· ≥ ·) where
  verum w := by simp [WeaklyForces₀.def]
  falsum w := by simp [WeaklyForces₀.def, WeakForcingRelation.NotForces]
  and w := by simp [WeaklyForces₀.def]
  or w := by simp [WeaklyForces₀.def]
  imply w := by simp [WeaklyForces₀.def]
  not w := by simp [WeaklyForces₀.def, WeakForcingRelation.NotForces]

end KripkeModel
