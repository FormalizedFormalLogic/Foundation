import Foundation.FirstOrder.Intuitionistic.Deduction
import Foundation.FirstOrder.Kripke.Basic
import Foundation.Logic.Predicate.Relational
import Foundation.Logic.ForcingRelation

namespace LO.FirstOrder

namespace KripkeModel

variable {L : Language} [L.Relational] {𝓚 : KripkeModel L}

def Forces {n} (w : 𝓚) (bv : Fin n → Name 𝓚) (fv : ξ → Name 𝓚) : Semiformulaᵢ L ξ n → Prop
  | .rel R t => 𝓚.Rel w R fun i ↦ (t i).relationalVal bv fv
  |        ⊤ => True
  |        ⊥ => False
  |    φ ⋏ ψ => Forces w bv fv φ ∧ Forces w bv fv ψ
  |    φ ⋎ ψ => Forces w bv fv φ ∨ Forces w bv fv ψ
  |    φ ➝ ψ => ∀ v ≤ w, Forces v bv fv φ → Forces v bv fv ψ
  |     ∀' φ => ∀ v ≤ w, ∀ x : v, Forces v (x.val :> bv) fv φ
  |     ∃' φ => ∃ x : w, Forces w (x.val :> bv) fv φ

local notation:45 w " ⊩[" bv "|" fv "] " φ:46 => Forces w bv fv φ

abbrev Forcesb {n} (w : 𝓚) (bv : Fin n → Name 𝓚) : Semisentenceᵢ L n → Prop := 𝓚.Forces w bv Empty.elim

scoped notation:45 w " ⊩/" bv φ:46 => Forcesb w bv φ

namespace Forces

variable (w : 𝓚) (bv : Fin n → Name 𝓚) (fv : ξ → Name 𝓚)

@[simp] lemma verum : w ⊩[bv|fv] ⊤ := by trivial

@[simp] lemma falsum : ¬w ⊩[bv|fv] ⊥ := by rintro ⟨⟩

variable {w bv fv}

@[simp] lemma rel {k} {R : L.Rel k} {t} :
    w ⊩[bv|fv] .rel R t ↔ 𝓚.Rel w R fun i ↦ (t i).relationalVal bv fv := by rfl

@[simp] lemma and {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋏ ψ ↔ w ⊩[bv|fv] φ ∧ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma or {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋎ ψ ↔ w ⊩[bv|fv] φ ∨ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma imply {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] φ ➝ ψ ↔ ∀ v ≤ w, Forces v bv fv φ → Forces v bv fv ψ := by rfl

@[simp] lemma not {φ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] ∼φ ↔ ∀ v ≤ w, ¬Forces v bv fv φ := by rfl

@[simp] lemma iff {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] φ ⭤ ψ ↔ ∀ v ≤ w, Forces v bv fv φ ↔ Forces v bv fv ψ := by
  simp [LogicalConnective.iff]; grind

@[simp] lemma all {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∀' φ ↔ ∀ v ≤ w, ∀ x : v, Forces v (x.val :> bv) fv φ := by rfl

@[simp] lemma ex {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∃' φ ↔ ∃ x : w, w ⊩[x :> bv|fv] φ := by rfl

@[simp] lemma conj {Γ : List (Semiformulaᵢ L ξ n)} :
    w ⊩[bv|fv] ⋀Γ ↔ ∀ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [conj (Γ := ψ :: Γ)]

@[simp] lemma disj {Γ : List (Semiformulaᵢ L ξ n)} :
    w ⊩[bv|fv] ⋁Γ ↔ ∃ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [disj (Γ := ψ :: Γ)]

lemma rew {bv : Fin n₂ → Name 𝓚} {fv : ξ₂ → Name 𝓚} {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
    w ⊩[bv|fv] (ω ▹ φ) ↔
    w ⊩[fun x ↦ (ω #x).relationalVal bv fv|fun x ↦ (ω &x).relationalVal bv fv] φ := by
  induction φ using Semiformulaᵢ.rec' generalizing n₂ w
  case hRel k R t =>
    simp only [Semiformulaᵢ.rew_rel, rel]
    apply iff_of_eq; congr; funext x
    simp [Semiterm.relationalVal_rew ω (t x), Function.comp_def]
  case hImp φ ψ ihφ ihψ =>
    simp [*]
  case hAnd φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hOr φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hVerum => simp
  case hFalsum => simp
  case hAll φ ih =>
    have (x : Name 𝓚) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]
  case hEx φ ih =>
    have (x : Name 𝓚) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]

@[simp] lemma free {fv : ℕ → 𝓚.Name} {φ : SyntacticSemiformulaᵢ L (n + 1)} :
    v ⊩[bv|↑x :>ₙ fv] Rewriting.free φ ↔ v ⊩[bv <: x|fv] φ := by
  have : (fun i ↦ Semiterm.relationalVal (L := L) bv (x :>ₙ fv) (Rew.free #i)) = (bv <: x) := by
    ext i; cases i using Fin.lastCases <;> simp
  simp [Rewriting.free, Forces.rew, this]

lemma subst (w : Fin k → Semiterm L ξ n) (φ : Semiformulaᵢ L ξ k) :
    v ⊩[bv|fv] (φ ⇜ w) ↔ v ⊩[fun i ↦ (w i).relationalVal bv fv|fv] φ := by
  simp [Rewriting.subst, Forces.rew]

@[simp] lemma subst₀ (φ : Formulaᵢ L ξ) :
    v ⊩[bv|fv] φ/[] ↔ v ⊩[![]|fv] φ := by
  simp [Forces.subst, Matrix.empty_eq]

@[simp] lemma forces_subst₁ (t : Semiterm L ξ n) (φ : Semiformulaᵢ L ξ 1) :
    v ⊩[bv|fv] φ/[t] ↔ v ⊩[![t.relationalVal bv fv]|fv] φ := by
  simp [Forces.subst, Matrix.constant_eq_singleton]

@[simp] lemma forces_emb {φ : Semisentenceᵢ L n} :
    v ⊩[bv|fv] (Rewriting.emb φ) ↔ v ⊩[bv|Empty.elim] φ := by
  simp [Rewriting.emb, Forces.rew, Empty.eq_elim]

lemma monotone
    {n} {bv : Fin n → Name 𝓚} {fv : ξ → Name 𝓚} {φ} : w ⊩[bv|fv] φ → ∀ v ≤ w, v ⊩[bv|fv] φ :=
  match φ with
  | .rel R v => 𝓚.rel_monotone
  |        ⊤ => fun _ _ _ ↦ trivial
  |        ⊥ => by rintro ⟨⟩
  |    φ ⋏ ψ => by
    rintro ⟨hl, hr⟩ v h
    exact ⟨hl.monotone _ h, hr.monotone _ h⟩
  |    φ ⋎ ψ => by
    rintro (hl | hr) v h
    · left; exact hl.monotone _ h
    · right; exact hr.monotone _ h
  |    φ ➝ ψ => fun Hw v' h v hvv' Hv ↦
    Hw v (le_trans hvv' h) Hv
  |    ∀' φ => fun Hw w h v' hvv' x ↦ Hw v' (le_trans hvv' h) x
  |    ∃' φ => by
    rintro ⟨x, Hw⟩ v h
    exact ⟨⟨x, 𝓚.domain_antimonotone h x.prop⟩, Hw.monotone _ h⟩

@[simp] lemma triple_negation_elim {φ : Semiformulaᵢ L ξ n} :
    (∀ v ≤ w, ∃ x ≤ v, ∀ y ≤ x, ¬y ⊩[bv|fv] φ) ↔ (∀ v ≤ w, ¬v ⊩[bv|fv] φ) := by
  constructor
  · intro h v hvw Hv
    rcases h v hvw with ⟨x, hxv, Hx⟩
    exact Hx x (by rfl) (Hv.monotone x hxv)
  · intro h v hvw
    refine ⟨v, by rfl, fun x hxv ↦ h x (le_trans hxv hvw)⟩

end Forces

instance : ForcingRelation 𝓚 (Sentenceᵢ L) := ⟨fun w φ ↦ w ⊩[![]|Empty.elim] φ⟩

lemma Forces₀.def {w : 𝓚} {φ : Sentenceᵢ L} : w ⊩ φ ↔ w ⊩[![]|Empty.elim] φ := by rfl

lemma Forces₀.not_def {w : 𝓚} {φ : Sentenceᵢ L} : w ⊮ φ ↔ ¬w ⊩ φ := by rfl

instance : ForcingRelation.IntKripke 𝓚 (· ≥ ·) where
  verum w := trivial
  falsum w := by rintro ⟨⟩
  and w := by simp [Forces₀.def]
  or w := by simp [Forces₀.def]
  imply w := by simp [Forces₀.def, Forces.imply]
  not w := by simp [Forces₀.def, Forces₀.not_def, Forces.not]

lemma Forces₀.monotone {w : 𝓚} {φ} : w ⊩ φ → ∀ v ≤ w, v ⊩ φ :=
  fun h hw ↦ Forces.monotone h hw

variable (𝓚)

abbrev Models (φ : Sentenceᵢ L) : Prop := ∀ w : 𝓚, w ⊩ φ

instance : Semantics (KripkeModel L) (Sentenceᵢ L) := ⟨fun 𝓚 φ ↦ 𝓚.Models φ⟩

variable {𝓚}

variable {Λ : Hilbertᵢ L}

open HilbertProofᵢ Semantics

lemma sound!_forces (w : 𝓚) (fv : ℕ → 𝓚.Name) (hfv : ∀ i, w ⊩↓ fv i) {φ} : 𝗜𝗻𝘁¹ ⊢! φ → w ⊩[![]|fv] φ
  |     eaxm h => by
    have : ∃ ψ, Axioms.EFQ ψ = φ := by simpa [Hilbertᵢ.Intuitionistic] using h
    rcases this with ⟨ψ, rfl⟩
    rintro v hvw ⟨⟩
  | mdp bφψ bφ => by simpa using sound!_forces w fv hfv bφψ w (by simp) (sound!_forces w fv hfv bφ)
  |      gen b => fun v hwv x ↦ by
    simpa using sound!_forces v (x :>ₙ fv)
      (by rintro (i | i) <;> simp [fun i ↦ 𝓚.domain_antimonotone' (hfv i) _ hwv]) b
  | verum => by simp
  | imply₁ φ ψ => by
    intro w₁ hw₁w₀ hw₁φ w₂ hw₁w₂ hw₂φ
    exact hw₁φ.monotone _ hw₁w₂
  | imply₂ φ ψ χ => by
    intro w₁ hw₁w₀ hw₁ w₂ hw₂w₁ hw₂ w₃ hw₃w₂ hw₃
    have : w₃ ⊩[![]|fv] ψ := hw₂ w₃ hw₃w₂ hw₃
    exact hw₁ w₃ (le_trans hw₃w₂ hw₂w₁) hw₃ w₃ (by rfl) this
  | and₁ φ ψ => by
    rintro v hvw ⟨hφ, hψ⟩
    exact hφ
  | and₂ φ ψ => by
    rintro v hvw ⟨hφ, hψ⟩
    exact hψ
  | and₃ φ ψ => by
    intro v₁ hv₁w hφ v₂ hv₂v₁ hψ
    exact ⟨hφ.monotone _ hv₂v₁, hψ⟩
  | or₁ φ ψ => by
    intro v hvw hφ
    left; exact hφ
  | or₂ φ ψ => by
    intro v hvw hψ
    right; exact hψ
  | or₃ φ ψ χ => by
    rintro w₁ hw₁w hφχ w₂ hw₂w₁ hψχ w₃ hw₃w₂ (hφ | hψ)
    · exact hφχ w₃ (le_trans hw₃w₂ hw₂w₁) hφ
    · exact hψχ w₃ hw₃w₂ hψ
  | all₁ φ t => by
    rcases t.fvar_of_relational with ⟨x, rfl⟩
    intro v hvw hφ
    suffices v ⊩[![fv x]|fv] φ by simpa [Forces.subst, Matrix.constant_eq_singleton]
    simpa using hφ v (by rfl) ⟨fv x, 𝓚.domain_antimonotone hvw (hfv x)⟩
  | all₂ φ ψ => by
    intro w₁ hw₁ H w₂ hw₂₁ hφ w₃ hw₃₂ x
    exact H w₃ (le_trans hw₃₂ hw₂₁) x w₃ (by rfl) (by simpa using hφ.monotone _ hw₃₂)
  | ex₁ t φ => by
    rcases t.fvar_of_relational with ⟨x, rfl⟩
    intro v hvw hφ
    have : v ⊩[![fv x]|fv] φ := by simpa using hφ
    exact ⟨⟨fv x, 𝓚.domain_antimonotone hvw (hfv x)⟩, by simpa using this⟩
  | ex₂ φ ψ => by
    rintro w₁ hw₁ H w₂ hw₂₁ ⟨x, hφ⟩
    simpa using H w₂ hw₂₁ x w₂ (by rfl) hφ

lemma sound {T : Theoryᵢ L 𝗜𝗻𝘁¹} (b : T ⊢ φ) : 𝓚 ⊧* T → 𝓚 ⊧ φ := fun H w ↦ by
  rcases 𝓚.domain_nonempty' w with ⟨x, hx⟩
  have : (Rewriting.emb '' T.theory) *⊢[𝗜𝗻𝘁¹] ↑φ := b
  rcases Entailment.Context.provable_iff.mp this with ⟨Γ, HΓ, b⟩
  have : w ⊩[![]|fun _ ↦ x] ⋀Γ ➝ ↑φ := sound!_forces (L := L) w (fun _ ↦ x) (by simpa using hx) b.get
  have : w ⊩[![]|fun _ : ℕ ↦ x] ↑φ := by
    apply this w (by rfl)
    suffices ∀ φ ∈ Γ, w ⊩[![]|fun _ ↦ x] φ by simpa
    intro φ hφ
    rcases show ∃ x ∈ T.theory, ↑x = φ by simpa using HΓ φ hφ with ⟨φ, hφ', rfl⟩
    simpa using H.models_set hφ' w
  simpa using this

instance (T : Theoryᵢ L 𝗜𝗻𝘁¹) : Sound T (Semantics.models (KripkeModel L) T) := ⟨fun b _ H ↦ sound b H⟩

lemma sound_empty (b : (∅ : Theoryᵢ L 𝗜𝗻𝘁¹) ⊢ φ) : 𝓚 ⊧ φ := 𝓚.sound b (by simp)

end KripkeModel

end LO.FirstOrder
