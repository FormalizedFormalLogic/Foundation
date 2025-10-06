import Foundation.FirstOrder.Completeness.Corollaries

namespace LO.FirstOrder

namespace Language

namespace Set

abbrev Func : ℕ → Type := fun _ ↦ Empty

inductive Rel : ℕ → Type
  | eq : Rel 2
  | mem : Rel 2

end Set

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

section

variable (T : SetTheory)

lemma consequence_of [𝗘𝗤 ⪯ T] (φ : Sentence ℒₛₑₜ)
    (H : ∀ (M : Type w)
           [SetStructure M]
           [Structure ℒₛₑₜ M]
           [Structure.Set M]
           [Nonempty M]
           [M ⊧ₘ* T],
           M ⊧ₘ φ) :
    T ⊨ φ := consequence_iff_consequence.{_, w}.mp <| consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : Structure.Model ℒₛₑₜ M ⊧ₘ* T :=
    ((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv ℒₛₑₜ M)).mp hT)
  (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv ℒₛₑₜ M)).mpr (H (Structure.Model ℒₛₑₜ M))

end

section semantics

variable (M : Type*) [SetStructure M]

instance standardStructure : Structure ℒₛₑₜ M where
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

end semantics

lemma consequence_of' (T : SetTheory) [𝗘𝗤 ⪯ T] (φ : Sentence ℒₛₑₜ) (H : ∀ (M : Type*) [SetStructure M] [Nonempty M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊨ φ := consequence_of T φ fun M _ s _ _ ↦ by
  rcases standardStructure_unique M s
  exact H M

lemma provable_of (T : SetTheory) [𝗘𝗤 ⪯ T] (φ : Sentence ℒₛₑₜ) (H : ∀ (M : Type*) [SetStructure M] [Nonempty M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊢ φ := complete <| consequence_of' _ _ H

end SetTheory

namespace SetTheory

end LO.FirstOrder.SetTheory
