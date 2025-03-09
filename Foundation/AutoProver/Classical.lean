import Foundation.Propositional.Classical.Basic
import Foundation.Propositional.Tait.Calculus
import Foundation.Propositional.Classical.Tait

namespace LO.Propositional

variable {α : Type*}

@[simp] lemma NNFormula.ne_neg (φ : NNFormula α) : ∼φ ≠ φ := by
  induction φ using NNFormula.rec' <;> simp

namespace Sequent

def complexity (Γ : Sequent α) : ℕ := (Γ.map NNFormula.complexity).sum

@[simp] lemma complexity_nil : complexity ([] : Sequent α) = 0 := by simp [complexity]

@[simp] lemma complexity_cons (φ) (Γ : Sequent α) : complexity (φ :: Γ) = φ.complexity + Γ.complexity := by
  simp [complexity]

inductive IsAtomic : Sequent α → Prop where
  | nil : IsAtomic []
  | atom : IsAtomic Γ → IsAtomic (.atom a :: Γ)
  | natom : IsAtomic Γ → IsAtomic (.natom a :: Γ)

attribute [simp] IsAtomic.nil

instance : DecidablePred (IsAtomic (α := α)) := List.rec
  (.isTrue .nil)
  fun φ Γ d ↦
    match φ with
    | .atom a =>
      match d with
      | .isFalse h => .isFalse <| by rintro ⟨⟩; contradiction
      |  .isTrue h => .isTrue <| .atom h
    | .natom a =>
      match d with
      | .isFalse h => .isFalse <| by rintro ⟨⟩; contradiction
      |  .isTrue h => .isTrue <| .natom h
    |     ⊤ => .isFalse <| by rintro ⟨⟩
    |     ⊥ => .isFalse <| by rintro ⟨⟩
    | _ ⋏ _ => .isFalse <| by rintro ⟨⟩
    | _ ⋎ _ => .isFalse <| by rintro ⟨⟩

@[simp] lemma IsAtomic.cons_atom_iff : IsAtomic (.atom a :: Γ) ↔ IsAtomic Γ :=
  ⟨by rintro (_ | _); assumption, .atom⟩

@[simp] lemma IsAtomic.cons_natom_iff : IsAtomic (.natom a :: Γ) ↔ IsAtomic Γ :=
  ⟨by rintro (_ | _); assumption, .natom⟩

@[simp] lemma IsAtomic.not_cons_verum : ¬IsAtomic (⊤ :: Γ) := by rintro ⟨⟩
@[simp] lemma IsAtomic.not_cons_falsum : ¬IsAtomic (⊥ :: Γ) := by rintro ⟨⟩
@[simp] lemma IsAtomic.not_cons_and : ¬IsAtomic (φ ⋏ ψ :: Γ) := by rintro ⟨⟩
@[simp] lemma IsAtomic.not_cons_or : ¬IsAtomic (φ ⋎ ψ :: Γ) := by rintro ⟨⟩

lemma isAtomic_iff_complexity_eq_zero :
    IsAtomic Γ ↔ complexity Γ = 0 := by
  match Γ with
  |            [] => simp
  |  .atom a :: Γ => simp [isAtomic_iff_complexity_eq_zero (Γ := Γ)]
  | .natom a :: Γ => simp [isAtomic_iff_complexity_eq_zero (Γ := Γ)]
  |        ⊤ :: Γ => simp
  |        ⊥ :: Γ => simp
  |    _ ⋏ _ :: Γ => simp
  |    _ ⋎ _ :: Γ => simp

end Sequent

abbrev Sequents (α : Type*) := List (Sequent α)

abbrev Derivations (T : Theory α) (S : Sequents α) := ∀ Γ ∈ S, T ⟹ Γ

namespace Derivations

variable {T : Theory α} {S₁ S₂ : Sequents α}

def ofSubset (ss : S₁ ⊆ S₂) : Derivations T S₂ → Derivations T S₁ := fun d Γ hΓ ↦ d Γ (ss hΓ)

def nil : Derivations T [] := fun _ h ↦ False.elim <| by simp at h

end Derivations

def Sequent.IsClosed (Γ : Sequent α) : Prop := ∃ φ ∈ Γ, ∼φ ∈ Γ

lemma Sequent.IsClosed.cons_iff {Γ : Sequent α} :
    IsClosed (φ :: Γ) ↔ ∼φ ∈ Γ ∨ Γ.IsClosed := by
  simp [IsClosed]
  constructor
  · rintro (h | ⟨ψ, h, (rfl | hn)⟩)
    · simp [*]
    · simp [*]
    · right; exact ⟨ψ, by simp [*]⟩
  · rintro (h | ⟨ψ, h, hn⟩)
    · simp [*]
    · right; exact ⟨ψ, h, by simp [*]⟩

instance [DecidableEq α] : DecidablePred (Sequent.IsClosed (α := α)) :=
  List.rec
    (.isFalse <| by simp [Sequent.IsClosed])
    fun φ Γ d ↦
    if h : ∼φ ∈ Γ then .isTrue ⟨φ, by simp [h]⟩ else
    match d with
    | .isFalse hΓ => .isFalse <| by simp [Sequent.IsClosed.cons_iff, *]
    |  .isTrue hΓ => .isTrue <| by simp [Sequent.IsClosed.cons_iff, hΓ]

def Sequent.IsClosed.choose [DecidableEq α] : (Γ : Sequent α) → Γ.IsClosed → {φ // φ ∈ Γ ∧ ∼φ ∈ Γ}
  |     [], h => False.elim (by rcases h; simp_all)
  | φ :: Γ, h =>
    if hn : ∼φ ∈ Γ then ⟨φ, by simp [hn]⟩ else
    have : IsClosed Γ := by simpa [Sequent.IsClosed.cons_iff, hn] using h
    let ⟨ψ, hψ⟩ := this.choose
    ⟨ψ, by simp [hψ]⟩

def Sequent.prereduction : Sequent α → Sequents α
  |            [] => [[]]
  |  .atom a :: Γ => [Γ.concat (.atom a)]
  | .natom a :: Γ => [Γ.concat (.natom a)]
  |        ⊤ :: _ => []
  |        ⊥ :: Γ => [Γ]
  |    φ ⋏ ψ :: Γ => [Γ.concat φ, Γ.concat ψ]
  |    φ ⋎ ψ :: Γ => [(Γ.concat φ).concat ψ]

def Sequent.reduction [DecidableEq α] (Γ : Sequent α) : Sequents α :=
  if Γ.IsClosed then [] else Γ.prereduction

def Sequents.reduction [DecidableEq α] (S : Sequents α) : Sequents α :=
  S.flatMap Sequent.reduction

lemma Sequent.reduction_sublist [DecidableEq α] {Γ : Sequent α} {S : Sequents α}
    (h : Γ ∈ S) : Γ.reduction.Sublist S.reduction :=
  List.sublist_flatten_of_mem <| List.mem_map_of_mem reduction h

variable {T : Theory α} [DecidableEq α]

def Derivation.rotate (d : T ⟹ Γ.concat φ) : T ⟹ φ :: Γ := d.wk (by simp)

def Derivation.ofReduction {Γ : Sequent α}
    (d : Derivations T Γ.reduction) : T ⟹ Γ :=
  if hΓ : Γ.IsClosed then
    let ⟨φ, h, hn⟩ := hΓ.choose
    em h hn
  else
    match Γ with
    |            [] => d [] (by simp [Sequent.reduction, hΓ, Sequent.prereduction])
    |  .atom a :: Γ => rotate <| d (Γ.concat (.atom a)) (by simp [Sequent.reduction, hΓ, Sequent.prereduction])
    | .natom a :: Γ => rotate <| d (Γ.concat (.natom a)) (by simp [Sequent.reduction, hΓ, Sequent.prereduction])
    |        ⊤ :: _ => .verum _
    |        ⊥ :: Γ => Tait.wkTail <| d Γ (by simp [Sequent.reduction, hΓ, Sequent.prereduction])
    |    φ ⋏ ψ :: Γ =>
      (rotate <| d (Γ.concat φ) (by simp [Sequent.reduction, hΓ, Sequent.prereduction])).and
      (rotate <| d (Γ.concat ψ) (by simp [Sequent.reduction, hΓ, Sequent.prereduction]))
    |    φ ⋎ ψ :: Γ =>
      Tait.or (d ((Γ.concat φ).concat ψ) (by simp [Sequent.reduction, hΓ, Sequent.prereduction]) |>.wk (by simp))

def Derivations.ofReduction {S : Sequents α}
    (d : Derivations T S.reduction) : Derivations T S := fun _ hΓ ↦
  Derivation.ofReduction <| d.ofSubset <| (Sequent.reduction_sublist hΓ).subset

def Derivations.ofReductionIter {S : Sequents α}
    (d : Derivations T (Sequents.reduction^[n] S)) : Derivations T S :=
  match n with
  |     0 => d
  | n + 1 => d.ofReductionIter (n := n) |>.ofReduction

#eval Sequents.reduction^[3] (Sequent.reduction [((.atom 0 ➝ .atom 1) ➝ .atom 0) ➝ .atom 0])

end LO.Propositional
