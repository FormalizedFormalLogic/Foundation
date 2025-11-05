import Foundation.FirstOrder.Kripke.Intuitionistic
import Foundation.FirstOrder.NegationTranslation.GoedelGentzen

/-! # Weak forcing

Main reference: Jeremy Avigad, "Forcing in proof theory"
-/

namespace LO.FirstOrder

variable {L : Language} [L.Relational]

namespace KripkeModel

variable {ℙ : Type*} [Preorder ℙ] {Name : Type*} [KripkeModel L ℙ Name]

def WeaklyForces (p : ℙ) (bv : Fin n → Name) (fv : ξ → Name) (φ : Semiformula L ξ n) : Prop := Forces p bv fv φᴺ

scoped notation:45 p " ⊩ᶜ[" bv "|" fv "] " φ:46 => WeaklyForces p bv fv φ

@[simp] lemma exists_le {α : Type*} [Preorder α] (a : α) : ∃ x, x ≤ a := ⟨a, by rfl⟩

namespace WeaklyForces

variable {p q r : ℙ} {bv : Fin n → Name} {fv : ξ → Name}

@[simp] lemma rel {R : L.Rel k} {t : Fin k → Semiterm L ξ n} :
    p ⊩ᶜ[bv|fv] Semiformula.rel R t ↔ ∀ q ≤ p, ∃ r ≤ q, Rel r R fun i ↦ (t i).relationalVal bv fv := by simp [WeaklyForces]

@[simp] lemma nrel {R : L.Rel k} {t : Fin k → Semiterm L ξ n} :
    p ⊩ᶜ[bv|fv] Semiformula.nrel R t ↔ ∀ q ≤ p, ¬Rel q R fun i ↦ (t i).relationalVal bv fv := by simp [WeaklyForces]

@[simp] lemma verum : p ⊩ᶜ[bv|fv] (⊤ : Semiformula L ξ n) := by simp [WeaklyForces]

@[simp] lemma falsum : ¬p ⊩ᶜ[bv|fv] (⊥ : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma and {φ ψ : Semiformula L ξ n} :
    p ⊩ᶜ[bv|fv] φ ⋏ ψ ↔ p ⊩ᶜ[bv|fv] φ ∧ p ⊩ᶜ[bv|fv] ψ := by simp [WeaklyForces]

@[simp] lemma or {φ ψ : Semiformula L ξ n} :
    p ⊩ᶜ[bv|fv] φ ⋎ ψ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ[bv|fv] φ ∨ r ⊩ᶜ[bv|fv] ψ := by
  suffices
      (∀ q ≤ p, (∃ r ≤ q, Forces r bv fv φᴺ) ∨ ∃ r ≤ q, Forces r bv fv ψᴺ) ↔
      ∀ q ≤ p, ∃ r ≤ q, Forces r bv fv φᴺ ∨ Forces r bv fv ψᴺ by
    simpa [WeaklyForces, -not_and, not_and_or]
  grind

@[simp] lemma all {φ : Semiformula L ξ (n + 1)} :
    p ⊩ᶜ[bv|fv] ∀' φ ↔ ∀ q ≤ p, ∀ x : q, WeaklyForces q (↑x :> bv) fv φ := by simp [WeaklyForces]

@[simp] lemma ex {φ : Semiformula L ξ (n + 1)} :
    p ⊩ᶜ[bv|fv] ∃' φ ↔ ∀ q ≤ p, ∃ r ≤ q, ∃ x : r, r ⊩ᶜ[↑x :> bv|fv] φ := by
  suffices
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ Domain r, ∃ s ≤ r, s ⊩ᶜ[x :> bv|fv] φ) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ Domain r, r ⊩ᶜ[x :> bv|fv] φ) by
    simpa [WeaklyForces]
  constructor
  · intro h q hqp
    rcases h q hqp with ⟨r, hrq, x, hx, s, hsr, H⟩
    exact ⟨s, le_trans hsr hrq, x, domain_antimonotone hsr hx, H⟩
  · intro h q hqp
    rcases h q hqp with ⟨r, hrq, x, hx, H⟩
    exact ⟨r, hrq, x, hx, r, by rfl, H⟩

lemma monotone {φ : Semiformula L ξ n} :
    p ⊩ᶜ[bv|fv] φ → ∀ q ≤ p, q ⊩ᶜ[bv|fv] φ := fun h ↦ Forces.monotone h

lemma generic {p : ℙ} {n} {bv : Fin n → Name} {fv : ξ → Name} {φ : Semiformula L ξ n} :
    (∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ[bv|fv] φ) → p ⊩ᶜ[bv|fv] φ :=
  match φ with
  | .rel R v => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∃ s ≤ q, Rel s R fun i ↦ (v i).relationalVal bv fv) →
      (∀ q ≤ p, ∃ r ≤ q, Rel r R fun i ↦ (v i).relationalVal bv fv) by simpa
    intro h q hqp
    rcases h q hqp with ⟨r, hrq, H⟩
    rcases H r (by rfl) with ⟨s, hsr, Hs⟩
    exact ⟨s, le_trans hsr hrq, Hs⟩
  | .nrel R v => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ¬Rel s R fun i ↦ (v i).relationalVal bv fv) →
      (∀ q ≤ p, ¬Rel q R fun i ↦ (v i).relationalVal bv fv) by simpa
    intro h q hqp hR
    rcases h q hqp with ⟨r, hrq, Hr⟩
    exact Hr r (by rfl) (rel_monotone hR r hrq)
  | ⊤ => by simp
  | ⊥ => by simp
  | φ ⋏ ψ => by
    suffices (∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ[bv|fv] φ ∧ r ⊩ᶜ[bv|fv] ψ) → p ⊩ᶜ[bv|fv] φ ∧ p ⊩ᶜ[bv|fv] ψ by simpa
    intro h
    refine ⟨generic fun q hqp ↦ ?_, generic fun q hqp ↦ ?_⟩
    · rcases h q hqp with ⟨r, hrq, h, _⟩
      exact ⟨r, hrq, h⟩
    · rcases h q hqp with ⟨r, hrq, _, h⟩
      exact ⟨r, hrq, h⟩
  | φ ⋎ ψ => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∃ r ≤ q, r ⊩ᶜ[bv|fv] φ ∨ r ⊩ᶜ[bv|fv] ψ) →
      (∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ[bv|fv] φ ∨ r ⊩ᶜ[bv|fv] ψ) by simpa
    intro h q hqp
    rcases h q hqp with ⟨r, hrq, H⟩
    rcases H r (by rfl) with ⟨s, hsr, Hs⟩
    exact ⟨s, le_trans hsr hrq, Hs⟩
  | ∀' φ => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∀ a ∈ Domain q, q ⊩ᶜ[a :> bv|fv] φ) →
      (∀ q ≤ p, ∀ x ∈ Domain q, q ⊩ᶜ[x :> bv|fv] φ) by simpa
    intro h q hqp x hx
    apply generic
    intro r hrq
    rcases h r (le_trans hrq hqp) with ⟨s, hsr, Hs⟩
    exact ⟨s, hsr, Hs s (by rfl) x (domain_monotone hx _ (le_trans hsr hrq))⟩
  | ∃' φ => by
    suffices
      (∀ q ≤ p, ∃ r ≤ q, ∀ q ≤ r, ∃ r ≤ q, ∃ x ∈ Domain r, r ⊩ᶜ[x :> bv|fv] φ) →
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ Domain r, r ⊩ᶜ[x :> bv|fv] φ) by simpa
    intro h q hqp
    rcases h q hqp with ⟨r, hrq, H⟩
    rcases H r (by rfl) with ⟨s, hsr, x, hx, H⟩
    exact ⟨s, le_trans hsr hrq, x, hx, H⟩

lemma generic_iff {φ : Semiformula L ξ n} :
    p ⊩ᶜ[bv|fv] φ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ[bv|fv] φ :=
  ⟨fun H q hqp ↦ ⟨q, by rfl, H.monotone q hqp⟩, generic⟩

lemma generic_iff_not {φ : Semiformula L ξ n} :
    ¬p ⊩ᶜ[bv|fv] φ ↔ ∃ q ≤ p, ∀ r ≤ q, ¬r ⊩ᶜ[bv|fv] φ := by simpa using generic_iff.not

@[simp] lemma not {p : ℙ} {n} {bv : Fin n → Name} {fv : ξ → Name} {φ : Semiformula L ξ n} :
    p ⊩ᶜ[bv|fv] ∼φ ↔ ∀ q ≤ p, ¬q ⊩ᶜ[bv|fv] φ :=
  match φ with
  | .rel R v => by
    suffices
      (∀ q ≤ p, ¬Rel q R fun i ↦ (v i).relationalVal bv fv) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ¬Rel s R fun i ↦ (v i).relationalVal bv fv) by simpa
    constructor
    · intro h q hqp
      exact ⟨q, by rfl, fun r hrq ↦ h r (le_trans hrq hqp)⟩
    · intro h q hqp H
      rcases h q hqp with ⟨r, hrq, Hr⟩
      exact Hr r (by rfl) (rel_monotone H _ hrq)
  | .nrel R v => by simp
  | ⊤ => by simp
  | ⊥ => by simp
  | φ ⋏ ψ => by
    suffices
        (∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ[bv|fv] ∼φ ∨ r ⊩ᶜ[bv|fv] ∼ψ) ↔
        (∀ q ≤ p, ¬q ⊩ᶜ[bv|fv] φ ∨ ¬q ⊩ᶜ[bv|fv] ψ) by
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
      · rcases generic_iff_not.mp C with ⟨r, hrq, Hr⟩
        refine ⟨r, hrq, ?_⟩
        left; apply WeaklyForces.not.mpr Hr
      · rcases generic_iff_not.mp C with ⟨r, hrq, Hr⟩
        refine ⟨r, hrq, ?_⟩
        right; apply WeaklyForces.not.mpr Hr
  | φ ⋎ ψ => by
    suffices
      p ⊩ᶜ[bv|fv] ∼φ ∧ p ⊩ᶜ[bv|fv] ∼ψ ↔
      ∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ¬s ⊩ᶜ[bv|fv] φ ∧ ¬s ⊩ᶜ[bv|fv] ψ by simpa
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
      (∀ q ≤ p, ∃ r ≤ q, ∃ a ∈ Domain r, r ⊩ᶜ[a :> bv|fv] ∼φ) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∃ x ∈ Domain r, ¬r ⊩ᶜ[x :> bv|fv] φ) by simpa
    constructor
    · intro h q hqp
      rcases h q hqp with ⟨r, hrq, x, hx, Hr⟩
      exact ⟨r, hrq, x, hx, WeaklyForces.not.mp Hr r (by rfl)⟩
    · intro h q hqp
      rcases h q hqp with ⟨r, hrq, x, hx, H⟩
      rcases generic_iff_not.mp H with ⟨s, hsr, Hs⟩
      exact ⟨s, le_trans hsr hrq, x, domain_antimonotone hsr hx, WeaklyForces.not.mpr Hs⟩
  | ∃' φ => by
    suffices
      (∀ q ≤ p, ∀ a ∈ Domain q, q ⊩ᶜ[a :> bv|fv] ∼φ) ↔
      (∀ q ≤ p, ∃ r ≤ q, ∀ s ≤ r, ∀ x ∈ Domain s, ¬s ⊩ᶜ[x :> bv|fv] φ) by simpa
    constructor
    · intro h q hqp
      refine ⟨q, by rfl, ?_⟩
      intro r hrq x hx
      exact WeaklyForces.not.mp (h r (le_trans hrq hqp) x hx) r (by rfl)
    · intro h q hqp x hx
      apply WeaklyForces.not.mpr
      intro r hrq Hr
      rcases h r (le_trans hrq hqp) with ⟨s, hsr, H⟩
      have : ¬s ⊩ᶜ[x :> bv|fv] φ := H s (by rfl) x (domain_antimonotone (le_trans hsr hrq) hx)
      exact this (Hr.monotone _ hsr)

lemma generic_iff_not' {φ : Semiformula L ξ n} :
    ¬p ⊩ᶜ[bv|fv] φ ↔ ∃ q ≤ p, q ⊩ᶜ[bv|fv] ∼φ := by simpa using generic_iff.not

@[simp] lemma imply {φ ψ : Semiformula L ξ n} :
    p ⊩ᶜ[bv|fv] φ ➝ ψ ↔ ∀ q ≤ p, q ⊩ᶜ[bv|fv] φ → q ⊩ᶜ[bv|fv] ψ := by
  suffices
    (∀ q ≤ p, ∃ r ≤ q, (∀ q ≤ r, ¬q ⊩ᶜ[bv|fv] φ) ∨ r ⊩ᶜ[bv|fv] ψ) ↔
    (∀ q ≤ p, q ⊩ᶜ[bv|fv] φ → q ⊩ᶜ[bv|fv] ψ) by simpa [DeMorgan.imply]
  constructor
  · intro h q hqp Hqφ
    by_contra! Hqψ
    rcases generic_iff_not.mp Hqψ with ⟨r, hrq, Hr⟩
    rcases h r (le_trans hrq hqp) with ⟨s, hsr, (H | H)⟩
    · exact H s (by rfl) (Hqφ.monotone s (le_trans hsr hrq))
    · exact Hr s hsr H
  · intro h q hqp
    have : ¬q ⊩ᶜ[bv|fv] φ ∨ q ⊩ᶜ[bv|fv] ψ := not_or_of_imp (h q hqp)
    rcases this with (H | H)
    · rcases generic_iff_not.mp H with ⟨r, hrq, H⟩
      exact ⟨r, hrq, Or.inl H⟩
    · exact ⟨q, by rfl, Or.inr H⟩

@[simp] lemma iff {φ ψ : Semiformula L ξ n} :
    p ⊩ᶜ[bv|fv] φ ⭤ ψ ↔ ∀ q ≤ p, q ⊩ᶜ[bv|fv] φ ↔ q ⊩ᶜ[bv|fv] ψ := by
  simp [LogicalConnective.iff]; grind

end WeaklyForces

abbrev WeaklyForces₀ (p : ℙ) (φ : Sentence L) : Prop := p ⊩ᶜ[![]|Empty.elim] ↑φ

instance : WeakForcingRelation ℙ (Sentence L) := ⟨WeaklyForces₀⟩

lemma weaklyForces₀_def {p : ℙ} {φ : Sentence L} : p ⊩ᶜ φ ↔ p ⊩ᶜ[![]|Empty.elim] φ := by rfl

lemma weaklyForces₀_iff_forces {p : ℙ} {φ : Sentence L} :
    p ⊩ᶜ φ ↔ p ⊩ φᴺ := by rfl

namespace WeaklyForces₀

lemma monotone {p : ℙ} : p ⊩ᶜ φ → ∀ q ≤ p, q ⊩ᶜ φ := WeaklyForces.monotone

lemma generic {p : ℙ} :
    (∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ) → p ⊩ᶜ φ := WeaklyForces.generic

lemma generic_iff {p : ℙ} :
    p ⊩ᶜ φ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ := WeaklyForces.generic_iff

instance : WeakForcingRelation.ClassicalKripke ℙ (· ≥ ·) where
  verum w := by simp [weaklyForces₀_def]
  falsum w := by simp [weaklyForces₀_def]
  and w := by simp [weaklyForces₀_def]
  or w := by simp [weaklyForces₀_def]
  imply w := by simp [weaklyForces₀_def]
  not w := by simp [weaklyForces₀_def]
  monotone := monotone
  generic := generic

lemma sound {T : Theory L} (b : T ⊢ φ) : ℙ ∀⊩ᶜ* T → ℙ ∀⊩ᶜ φ := fun H ↦
  Forces₀.sound (W := ℙ) (gödel_gentzen b (Λ := 𝗜𝗻𝘁¹)) fun φ hφ ↦ (by
    rcases show ∃ ψ ∈ T, ψᴺ = φ by simpa [Theory.ToTheoryᵢ] using hφ with ⟨ψ, hψ, rfl⟩
    exact H ψ hψ)

end WeaklyForces₀

end KripkeModel

/-- Kripke model for classical first-order logic -/
def ForcingNotion (L : Language) [L.Relational] := IntKripke L

namespace ForcingNotion

variable (ℙ : ForcingNotion L)

abbrev Condition := ℙ.World

abbrev Name := ℙ.Carrier

instance : CoeSort (ForcingNotion L) (Type _) := ⟨fun ℙ ↦ ℙ.Condition⟩

instance : CoeSort ℙ (Type _) := ⟨fun p ↦ ℙ.Domain p⟩

instance : Nonempty ℙ := ℙ.nonempty

instance : Preorder ℙ := ℙ.preorder

instance kripke : KripkeModel L ℙ ℙ.Name := IntKripke.kripke ℙ

variable {ℙ}

open KripkeModel

instance : Semantics (ForcingNotion L) (Sentence L) := ⟨fun ℙ φ ↦ ℙ ∀⊩ᶜ φ⟩

lemma models_def : ℙ ⊧ φ ↔ ℙ ∀⊩ᶜ φ := by rfl

lemma sound {T : Theory L} (b : T ⊢ φ) : ℙ ⊧* T → ℙ ⊧ φ := fun H ↦
  WeaklyForces₀.sound (ℙ := ℙ) b fun _ hφ ↦ H.models_set hφ

instance (T : Theory L) : Sound T (Semantics.models (ForcingNotion L) T) := ⟨fun b _ H ↦ sound b H⟩

end ForcingNotion
