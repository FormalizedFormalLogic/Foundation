import Foundation.FirstOrder.Intuitionistic.Deduction
import Foundation.FirstOrder.Kripke.Basic
import Foundation.Logic.Predicate.Relational
import Foundation.Logic.ForcingRelation

/-! # Kripke semantics for intuitionistic first-order logic -/

namespace LO.FirstOrder

variable {L : Language} [L.Relational]

namespace KripkeModel

variable {W : Type*} [Preorder W] {C : Type*} [KripkeModel L W C]

def Forces {n} (w : W) (bv : Fin n → C) (fv : ξ → C) : Semiformulaᵢ L ξ n → Prop
  | .rel R t => Rel w R fun i ↦ (t i).relationalVal bv fv
  |        ⊥ => False
  |    φ ⋏ ψ => Forces w bv fv φ ∧ Forces w bv fv ψ
  |    φ ⋎ ψ => Forces w bv fv φ ∨ Forces w bv fv ψ
  |    φ ➝ ψ => ∀ v ≤ w, Forces v bv fv φ → Forces v bv fv ψ
  |     ∀' φ => ∀ v ≤ w, ∀ x : v, Forces v (x.val :> bv) fv φ
  |     ∃' φ => ∃ x : w, Forces w (x.val :> bv) fv φ

scoped notation:45 w " ⊩[" bv "|" fv "] " φ:46 => Forces w bv fv φ

abbrev Forcesb {n} (w : W) (bv : Fin n → C) : Semisentenceᵢ L n → Prop := Forces w bv Empty.elim

scoped notation:45 w " ⊩/" bv φ:46 => Forcesb w bv φ

namespace Forces

variable (w v : W) (bv : Fin n → C) (fv : ξ → C)

@[simp] lemma verum : w ⊩[bv|fv] ⊤ := fun v _ ↦ by rintro ⟨⟩

@[simp] lemma falsum : ¬w ⊩[bv|fv] ⊥ := by rintro ⟨⟩

variable {w v bv fv}

@[simp] lemma rel {k} {R : L.Rel k} {t} :
    w ⊩[bv|fv] .rel R t ↔ Rel w R fun i ↦ (t i).relationalVal bv fv := by rfl

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
    w ⊩[bv|fv] ∃' φ ↔ ∃ x : w, w ⊩[↑x :> bv|fv] φ := by rfl

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

lemma rew {bv : Fin n₂ → C} {fv : ξ₂ → C} {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
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
  case hFalsum => simp
  case hAll φ ih =>
    have (x : C) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]
  case hEx φ ih =>
    have (x : C) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]

@[simp] lemma free {v : W} {fv : ℕ → C} {φ : SyntacticSemiformulaᵢ L (n + 1)} :
    v ⊩[bv|↑x :>ₙ fv] Rewriting.free φ ↔ v ⊩[bv <: x|fv] φ := by
  have : (fun i ↦ Semiterm.relationalVal (L := L) bv (x :>ₙ fv) (Rew.free #i)) = (bv <: x) := by
    ext i; cases i using Fin.lastCases <;> simp
  simp [Rewriting.free, Forces.rew, this]

lemma subst {v : W} (w : Fin k → Semiterm L ξ n) (φ : Semiformulaᵢ L ξ k) :
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
    {n} {bv : Fin n → C} {fv : ξ → C} {φ} : w ⊩[bv|fv] φ → ∀ v ≤ w, v ⊩[bv|fv] φ :=
  match φ with
  | .rel R v => rel_monotone
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
    exact ⟨⟨x, domain_antimonotone h x.prop⟩, Hw.monotone _ h⟩

@[simp] lemma triple_negation_elim {φ : Semiformulaᵢ L ξ n} :
    (∀ v ≤ w, ∃ x ≤ v, ∀ y ≤ x, ¬y ⊩[bv|fv] φ) ↔ (∀ v ≤ w, ¬v ⊩[bv|fv] φ) := by
  constructor
  · intro h v hvw Hv
    rcases h v hvw with ⟨x, hxv, Hx⟩
    exact Hx x (by rfl) (Hv.monotone x hxv)
  · intro h v hvw
    refine ⟨v, by rfl, fun x hxv ↦ h x (le_trans hxv hvw)⟩

open HilbertProofᵢ Semantics

lemma sound! (w : W) (fv : ℕ → C) (hfv : ∀ i, w ⊩↓ fv i) {φ} : 𝗜𝗻𝘁¹ ⊢! φ → w ⊩[![]|fv] φ
  |     eaxm h => by
    have : ∃ ψ, Axioms.EFQ ψ = φ := by simpa [Hilbertᵢ.Intuitionistic] using h
    rcases this with ⟨ψ, rfl⟩
    rintro v hvw ⟨⟩
  | mdp bφψ bφ => by simpa using sound! w fv hfv bφψ w (by simp) (sound! w fv hfv bφ)
  |      gen b => fun v hwv x ↦ by
    simpa using sound! v (x :>ₙ fv)
      (by rintro (i | i) <;> simp [fun i ↦ domain_monotone (hfv i) _ hwv]) b
  | .verum => by simp
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
    simpa using hφ v (by rfl) ⟨fv x, domain_antimonotone hvw (hfv x)⟩
  | all₂ φ ψ => by
    intro w₁ hw₁ H w₂ hw₂₁ hφ w₃ hw₃₂ x
    exact H w₃ (le_trans hw₃₂ hw₂₁) x w₃ (by rfl) (by simpa using hφ.monotone _ hw₃₂)
  | ex₁ t φ => by
    rcases t.fvar_of_relational with ⟨x, rfl⟩
    intro v hvw hφ
    have : v ⊩[![fv x]|fv] φ := by simpa using hφ
    exact ⟨⟨fv x, domain_antimonotone hvw (hfv x)⟩, by simpa using this⟩
  | ex₂ φ ψ => by
    rintro w₁ hw₁ H w₂ hw₂₁ ⟨x, hφ⟩
    simpa using H w₂ hw₂₁ x w₂ (by rfl) hφ

lemma sound (w : W) (fv : ℕ → C) (hfv : ∀ i, w ⊩↓ fv i) {φ} :
    𝗜𝗻𝘁¹ ⊢ φ → w ⊩[![]|fv] φ := fun b ↦ sound! w fv hfv b.get

end Forces

abbrev Forces₀ (w : W) (φ : Sentenceᵢ L) : Prop := w ⊩[![]|Empty.elim] φ

instance : ForcingRelation W (Sentenceᵢ L) := ⟨Forces₀⟩

lemma forces₀_def {w : W} {φ : Sentenceᵢ L} : w ⊩ φ ↔ w ⊩[![]|Empty.elim] φ := by rfl

namespace Forces₀

lemma monotone {w : W} {φ} : w ⊩ φ → ∀ v ≤ w, v ⊩ φ :=
  fun h hw ↦ Forces.monotone h hw

instance : ForcingRelation.IntKripke W (· ≥ ·) where
  verum w := by rintro _ _ ⟨⟩
  falsum w := by rintro ⟨⟩
  and w := by simp [forces₀_def]
  or w := by simp [forces₀_def]
  imply w := by simp [forces₀_def, Forces.imply]
  not w := by simp [forces₀_def, Forces.not]
  monotone := monotone

open HilbertProofᵢ Semantics

lemma sound {T : Theoryᵢ L 𝗜𝗻𝘁¹} (b : T ⊢ φ) : W ∀⊩* T → W ∀⊩ φ := fun H w ↦ by
  rcases domain_nonempty' w with ⟨x, hx⟩
  have : (Rewriting.emb '' T.theory) *⊢[𝗜𝗻𝘁¹] ↑φ := b
  rcases Entailment.Context.provable_iff.mp this with ⟨Γ, HΓ, b⟩
  have : w ⊩[![]|fun _ ↦ x] ⋀Γ ➝ ↑φ := Forces.sound (L := L) w (fun _ ↦ x) (by simpa using hx) b
  have : w ⊩[![]|fun _ : ℕ ↦ x] ↑φ := by
    apply this w (by rfl)
    suffices ∀ φ ∈ Γ, w ⊩[![]|fun _ ↦ x] φ by simpa
    intro φ hφ
    rcases show ∃ x ∈ T.theory, ↑x = φ by simpa using HΓ φ hφ with ⟨φ, hφ', rfl⟩
    simpa using H _ hφ' w
  simpa using this

end Forces₀

end KripkeModel

/-- Kripke model for intuitionistic first-order logic -/
structure IntKripke (L : Language) [L.Relational] where
  World : Type*
  [nonempty : Nonempty World]
  [preorder : Preorder World]
  Carrier : Type*
  Domain : World → Set Carrier
  domain_nonempty : ∀ w, ∃ x, x ∈ Domain w
  domain_antimonotone : w ≥ v → Domain w ⊆ Domain v
  Rel (w : World) {k : ℕ} (R : L.Rel k) : (Fin k → Name) → Prop
  rel_monotone : Rel w R t → ∀ v ≤ w, Rel v R t

namespace IntKripke

variable (𝓚 : IntKripke L)

instance : CoeSort (IntKripke L) (Type _) := ⟨fun 𝓚 ↦ 𝓚.World⟩

instance : CoeSort 𝓚 (Type _) := ⟨fun w ↦ 𝓚.Domain w⟩

instance : Nonempty 𝓚 := 𝓚.nonempty

instance : Preorder 𝓚 := 𝓚.preorder

instance : ForcingExists 𝓚 𝓚.Carrier := ⟨fun p x ↦ x ∈ 𝓚.Domain p⟩

instance kripke : KripkeModel L 𝓚 𝓚.Carrier where
  Domain := 𝓚.Domain
  domain_nonempty := 𝓚.domain_nonempty
  domain_antimonotone := 𝓚.domain_antimonotone
  Rel := 𝓚.Rel
  rel_monotone := 𝓚.rel_monotone

open KripkeModel

instance : Semantics (IntKripke L) (Sentenceᵢ L) := ⟨fun 𝓚 φ ↦ 𝓚 ∀⊩ φ⟩

variable {𝓚}

lemma models_def : 𝓚 ⊧ φ ↔ 𝓚 ∀⊩ φ := by rfl

lemma sound {T : Theoryᵢ L 𝗜𝗻𝘁¹} (b : T ⊢ φ) : 𝓚 ⊧* T → 𝓚 ⊧ φ := fun H ↦
  Forces₀.sound (W := 𝓚) b fun _ hφ ↦ H.models_set hφ

instance (T : Theoryᵢ L 𝗜𝗻𝘁¹) : Sound T (Semantics.models (IntKripke L) T) := ⟨fun b _ H ↦ sound b H⟩

lemma sound_empty (b : (∅ : Theoryᵢ L 𝗜𝗻𝘁¹) ⊢ φ) : 𝓚 ⊧ φ := 𝓚.sound b (by simp)

instance : Semantics.Top (IntKripke L) := ⟨fun 𝓚 ↦ by simpa [models_def] using ForcingRelation.AllForces.verum⟩

instance : Semantics.Bot (IntKripke L) := ⟨fun 𝓚 ↦ by
  have : Inhabited 𝓚 := Classical.inhabited_of_nonempty'
  simp [models_def]⟩

instance : Semantics.And (IntKripke L) := ⟨by simp [models_def]⟩

end IntKripke

end LO.FirstOrder
