import Foundation.FirstOrder.Completeness.Corollaries

/-! # Preperations for set theory

- *NOTE*:
  To avoid the duplicate definitions of `Structure ℒₛₑₜ` for models,
  we basically use `SetStructure`, and generated `standardStructure` instead of `Structure ℒₛₑₜ` itself.
  If you wish to use a type with `Structure ℒₛₑₜ`, use `NormalizedModel`.
-/

namespace LO.FirstOrder

namespace Language

namespace Set

abbrev Func : ℕ → Type := fun _ ↦ Empty

inductive Rel : ℕ → Type
  | eq : Rel 2
  | mem : Rel 2

end Set

/-- Language of set theory -/
@[reducible]
def set : Language where
  Func := Set.Func
  Rel := Set.Rel

notation "ℒₛₑₜ" => set

namespace Set

instance (k) : DecidableEq (Set.Func k) := inferInstance

instance (k) : DecidableEq (Set.Rel k) := fun a b => by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (Set.Func k) := inferInstance

instance (k) : Encodable (Set.Rel k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.mem => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.mem
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance : (ℒₛₑₜ).DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒₛₑₜ).Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒₛₑₜ).Eq := ⟨Rel.eq⟩

instance : (ℒₛₑₜ).Mem := ⟨Rel.mem⟩

lemma rel_eq_eq_or_mem (R : (ℒₛₑₜ).Rel k) : k = 2 ∧ (R ≍ (Eq.eq : (ℒₛₑₜ).Rel 2) ∨ R ≍ (Mem.mem : (ℒₛₑₜ).Rel 2)) :=
  match R with
  | Rel.eq => ⟨rfl, Or.inl <| by rfl⟩
  | Rel.mem => ⟨by rfl, Or.inr <| by rfl⟩

end Set

end Language

abbrev SetTheory := Theory ℒₛₑₜ

variable [ToString ξ]

def Semiterm.toStringSet : Semiterm ℒₛₑₜ ξ n → String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "a_{" ++ toString x ++ "}"

instance : Repr (Semiterm ℒₛₑₜ ξ n) := ⟨fun t _ ↦ t.toStringSet⟩

instance : ToString (Semiterm ℒₛₑₜ ξ n) := ⟨fun t ↦ t.toStringSet⟩

def Semiformula.toStringSet : ∀ {n}, Semiformula ℒₛₑₜ ξ n → String
  | _,                               ⊤ => "⊤"
  | _,                               ⊥ => "⊥"
  | _,            .rel Language.Eq.eq v => s!"{(v 0).toStringSet} = {(v 1).toStringSet}"
  | _,          .rel Language.Mem.mem v => s!"{(v 0).toStringSet} ∈ {(v 1).toStringSet}"
  | _,           .nrel Language.Eq.eq v => s!"{(v 0).toStringSet} ≠ {(v 1).toStringSet}"
  | _,         .nrel Language.Mem.mem v => s!"{(v 0).toStringSet} ∉ {(v 1).toStringSet}"
  | _,                           φ ⋏ ψ => s!"[{φ.toStringSet}] ∧ [{ψ.toStringSet}]"
  | _,                           φ ⋎ ψ => s!"[{φ.toStringSet}] ∨ [{ψ.toStringSet}]"
  | n, ∀' (rel Language.Mem.mem v ➝ φ) => s!"(∀ x{toString n} ∈ {(v 1).toStringSet}) [{φ.toStringSet}]"
  | n, ∃' (rel Language.Mem.mem v ⋏ φ) => s!"(∃ x{toString n} ∈ {(v 1).toStringSet}) [{φ.toStringSet}]"
  | n,                            ∀' φ => s!"(∀ x{toString n}) [{φ.toStringSet}]"
  | n,                            ∃' φ => s!"(∃ x{toString n}) [{φ.toStringSet}]"

instance : Repr (Semiformula ℒₛₑₜ ξ n) := ⟨fun φ _ ↦ φ.toStringSet⟩

instance : ToString (Semiformula ℒₛₑₜ ξ n) := ⟨fun φ ↦ φ.toStringSet⟩

abbrev _root_.LO.SetStructure (V : Type*) := Membership V V

class Structure.Set (M : Type w) [SetStructure M] [Structure ℒₛₑₜ M] extends Structure.Eq ℒₛₑₜ M, Structure.Mem ℒₛₑₜ M

attribute [instance] Structure.Set.mk

namespace SetTheory

private lemma consequence_of_aux (T : SetTheory) [𝗘𝗤 ⪯ T] (φ : Sentence ℒₛₑₜ)
    (H : ∀ (M : Type w)
           [SetStructure M]
           [Structure ℒₛₑₜ M]
           [Structure.Set M]
           [Nonempty M]
           [M ⊧ₘ* T],
           M ⊧ₘ φ) :
    T ⊨ φ := consequence_iff_consequence.{_, w}.mp <| consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : Structure.Model ℒₛₑₜ M ⊧ₘ* T := Structure.ElementaryEquiv.modelsTheory.mp hT
  Structure.ElementaryEquiv.models.mpr (H (Structure.Model ℒₛₑₜ M))
section semantics

variable (M : Type*) [SetStructure M]

instance (priority := 100) standardStructure : Structure ℒₛₑₜ M where
  func := fun _ f ↦ Empty.elim f
  rel := fun _ r ↦
    match r with
    | Language.Set.Rel.eq => fun v ↦ v 0 = v 1
    | Language.Set.Rel.mem => fun v ↦ v 0 ∈ v 1

instance : Structure.Eq ℒₛₑₜ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Structure.Mem ℒₛₑₜ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

lemma standardStructure_unique' (s : Structure ℒₛₑₜ M)
    (hEq : Structure.Eq ℒₛₑₜ M) (hMem : Structure.Mem ℒₛₑₜ M) : s = standardStructure M := Structure.ext
  (funext₃ fun k f ↦ Empty.elim f)
  (funext₃ fun k r _ =>
    match k, r with
    | _, Language.Eq.eq => by simp
    | _, Language.Mem.mem => by simp)

lemma standardStructure_unique (s : Structure ℒₛₑₜ M) [hEq : Structure.Eq ℒₛₑₜ M] [hMem : Structure.Mem ℒₛₑₜ M] : s = standardStructure M :=
  standardStructure_unique' M s hEq hMem

structure NormalizedModel (M : Type*) [Structure ℒₛₑₜ M] [Nonempty M] [M ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ)] : Type _ where
  toQuot : Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M)

namespace NormalizedModel

variable {M : Type*} [s : Structure ℒₛₑₜ M] [Nonempty M] [M ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ)]

def equiv : NormalizedModel M ≃ Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M) where
  toFun x := x.toQuot
  invFun x := ⟨x⟩

instance : Nonempty (NormalizedModel M) :=
  have : Nonempty (Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M)) := inferInstance
  ⟨equiv.symm this.some⟩

instance : SetStructure (NormalizedModel M) where
  mem y x := equiv x ∈ equiv y

lemma mem_def (x y : NormalizedModel M) : x ∈ y ↔ equiv x ∈ equiv y := by rfl

open Structure

instance elementary_equiv : NormalizedModel M ≡ₑ[ℒₛₑₜ] M :=
  have h₁ : NormalizedModel M ≡ₑ[ℒₛₑₜ] Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M) := by
    apply ElementaryEquiv.of_equiv equiv
    · intro k R v₁ v₂ h
      rcases Language.Set.rel_eq_eq_or_mem R with ⟨rfl, (rfl | rfl)⟩
      · simp only [eq_lang, Fin.isValue]
        rw [←(equiv (M := M)).apply_eq_iff_eq]
        simp only [h]
      · simp [mem_def, h]
    · intro _ f
      exact IsEmpty.elim' inferInstance f
  have h₂ : Structure.Model ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M) ≡ₑ[ℒₛₑₜ] M :=
    Structure.ElementaryEquiv.trans
      (Structure.Model.elementaryEquiv ℒₛₑₜ (Structure.Eq.QuotEq ℒₛₑₜ M)).symm
      (Structure.Eq.QuotEq.elementaryEquiv ℒₛₑₜ M)
  h₁.trans h₂

end NormalizedModel

end semantics

lemma consequence_of_models (T : SetTheory) [𝗘𝗤 ⪯ T] (φ : Sentence ℒₛₑₜ) (H : ∀ (M : Type*) [SetStructure M] [Nonempty M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊨ φ := consequence_of_aux T φ fun M _ s _ _ ↦ by
  rcases standardStructure_unique M s
  exact H M

lemma provable_of_models (T : SetTheory) [𝗘𝗤 ⪯ T] (φ : Sentence ℒₛₑₜ) (H : ∀ (M : Type*) [SetStructure M] [Nonempty M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊢ φ := complete <| consequence_of_models _ _ H

end SetTheory

namespace SetTheory

end LO.FirstOrder.SetTheory
