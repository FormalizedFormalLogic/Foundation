module
public import Foundation.FirstOrder.Basic.Calculus
@[expose] public section

/-! # Alternative definition of proof -/

namespace LO.FirstOrder

variable {L : Language}

variable (L)

abbrev Sequent2 := Finset (Proposition L)

variable {L}

namespace Sequent2

def emb (Γ : Finset (Sentence L)) : Sequent2 L := Γ.map ⟨Rewriting.emb, Rewriting.emb_injective⟩

@[simp] lemma emb_empty : emb (∅ : Finset (Sentence L)) = ∅ := by simp [emb]

@[simp] lemma emb_insert [L.DecidableEq] (φ : Sentence L) (Γ : Finset (Sentence L)) :
    emb (insert φ Γ) = insert ↑φ (emb Γ) := by simp [emb]

@[simp] lemma emb_neg (Γ : Finset (Sentence L)) : emb (∼Γ) = ∼(emb Γ) := by
  ext φ
  suffices (∃ a, ∼a ∈ Γ ∧ Rewriting.emb a = φ) ↔ ∃ a ∈ Γ, Rewriting.emb a = ∼φ by
    simpa [emb]
  constructor
  · grind
  · rintro ⟨x, hx, eq⟩
    refine ⟨∼x, by simpa using hx, by simp [eq]⟩

def shifts (Γ : Sequent2 L) : Sequent2 L := Γ.map ⟨Rewriting.shift, LawfulSyntacticRewriting.shift_injective⟩

@[simp] lemma shifts_empty : shifts (∅ : Sequent2 L) = ∅ := by simp [shifts]

@[simp] lemma shifts_insert [L.DecidableEq] (φ : Proposition L) (Γ : Finset (Proposition L)) :
    shifts (insert φ Γ) = insert (Rewriting.shift φ) (shifts Γ) := by simp [shifts]

@[simp] lemma shifts_toFinset_eq_shifts [L.DecidableEq] (Γ : Sequent L) :
    (Γ⁺).toFinset = shifts Γ.toFinset := by ext φ; simp [shifts, Rewriting.shifts]

@[simp] lemma neg_toFinset [L.DecidableEq] (Γ : Sequent L) :
    (∼Γ).toFinset = ∼Γ.toFinset := by ext φ; simp

@[simp] lemma map_emb_toFinset_eq [L.DecidableEq] {Γ : List (Sentence L)} :
    (Γ.map Rewriting.emb).toFinset = emb Γ.toFinset := by ext; simp [emb]

end Sequent2

variable [L.DecidableEq]

section derivation2

inductive Derivation2 : Finset (Proposition L) → Type _
| identity (φ) : Derivation2 {φ, ∼φ}
| cut : Derivation2 (insert φ Γ) → Derivation2 (insert (∼φ) Δ) → Derivation2 (Γ ∪ Δ)
| contraction : Derivation2 Δ → Δ ⊆ Γ → Derivation2 Γ
| verum : Derivation2 {⊤}
| or : Derivation2 (insert φ (insert ψ Γ)) → Derivation2 (insert (φ ⋎ ψ) Γ)
| and : Derivation2 (insert φ Γ) → Derivation2 (insert ψ Γ) → Derivation2 (insert (φ ⋏ ψ) Γ)
| all : Derivation2 (insert (Rewriting.free φ) (Sequent2.shifts Γ)) → Derivation2 (insert (∀⁰ φ) Γ)
| exs : Derivation2 (insert (φ/[t]) Γ) → Derivation2 (insert (∃⁰ φ) Γ)

structure Theory.Proof2 (T : Theory L) (σ : Sentence L) where
  axioms : Finset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : Derivation2 (Sequent2.emb (insert σ (∼axioms)))

namespace Derivation2

def cast {Γ Δ : Sequent2 L} (d : Derivation2 Γ) (h : Γ = Δ := by simp) : Derivation2 Δ := by subst h; exact d

def contra {Γ Δ : Sequent2 L} (d : Derivation2 Δ) (h : Δ ⊆ Γ := by simp) : Derivation2 Γ := d.contraction h

end Derivation2

variable {T : Theory L}

lemma shifts_toFinset_eq_image_shift (Γ : Sequent L) :
    (Rewriting.shifts Γ).toFinset = Γ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shifts]

def Derivation.toDerivation2 {Γ : Sequent L} : ⊢ᴸᴷ¹ Γ → Derivation2 Γ.toFinset
  | .identity R v => (Derivation2.identity (.rel R v)).cast
  | .cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
    let b₁ : Derivation2 (insert φ Γ.toFinset) := d₁.toDerivation2.cast
    let b₂ : Derivation2 (insert (∼φ) Δ.toFinset) := d₂.toDerivation2.cast
    (b₁.cut b₂).cast
  | .contraction d h => d.toDerivation2.contra (List.toFinset_mono h)
  | .verum => Derivation2.verum.cast
  | .and (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ =>
    let b₁ : Derivation2 (insert φ Γ.toFinset) := d₁.toDerivation2.cast
    let b₂ : Derivation2 (insert ψ Γ.toFinset) := d₂.toDerivation2.cast
    (b₁.and b₂).cast
  | .or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    let b : Derivation2 (insert φ (insert ψ Γ.toFinset)) := d.toDerivation2.cast
    b.or.cast
  | .all (Γ := Γ) (φ := φ) dp =>
    let b : Derivation2 (insert (Rewriting.free φ) (Sequent2.shifts Γ.toFinset)) := dp.toDerivation2.cast
    b.all.cast
  | .exs (Γ := Γ) (φ := φ) (t := t) d =>
    let b : Derivation2 (insert (φ/[t]) Γ.toFinset) := d.toDerivation2.cast
    b.exs.cast

noncomputable def Derivation2.toDerivation {Γ : Sequent2 L} : Derivation2 Γ → ⊢ᴸᴷ¹ Γ.toList
| .identity φ => (Derivation.eta φ).contra
| .cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
  let b₁ : ⊢ᴸᴷ¹ φ :: Γ.toList := d₁.toDerivation.contra (by intro _; simp)
  let b₂ : ⊢ᴸᴷ¹ (∼φ) :: Δ.toList := d₂.toDerivation.contra (by intro _; simp)
  (b₁.cut b₂).contra (by intro _; simp)
| .contraction d h => d.toDerivation.contra (by intro _; simp; grind)
| .verum => Derivation.verum.contra
| .and (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ =>
  let b₁ : ⊢ᴸᴷ¹ φ :: Γ.toList := d₁.toDerivation.contra (by intro _; simp)
  let b₂ : ⊢ᴸᴷ¹ ψ :: Γ.toList := d₂.toDerivation.contra (by intro _; simp)
  (b₁.and b₂).contra (by intro _; simp)
| .or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
  let b : ⊢ᴸᴷ¹ φ :: ψ :: Γ.toList := d.toDerivation.contra (by intro _; simp)
  b.or.contra (by intro _; simp)
| .all (Γ := Γ) (φ := φ) d =>
  let b : ⊢ᴸᴷ¹ (Rewriting.free φ) :: Γ.toList⁺ :=
    d.toDerivation.contra (by intro _; simp [Rewriting.shifts, Sequent2.shifts])
  b.all.contra (by intro _; simp)
| .exs (Γ := Γ) (φ := φ) (t := t) d =>
  let b : ⊢ᴸᴷ¹ (φ/[t]) :: Γ.toList := d.toDerivation.contra (by intro _; simp)
  b.exs.contra (by intro _; simp)

lemma derivable_iff_derivable2 {Γ : Sequent L} :
    Nonempty (⊢ᴸᴷ¹ Γ) ↔ Nonempty (Derivation2 Γ.toFinset) := by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using d.toDerivation2⟩
  · rintro ⟨d⟩; exact ⟨d.toDerivation.contra (by intro _; simp)⟩

lemma provable_iff_provable2 {φ} : T ⊢ φ ↔ Nonempty (T.Proof2 φ) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨⟨d.axioms.toFinset, by simpa using d.axioms_mem,
      d.derivation.toDerivation2.contra (by simp)⟩⟩
  · rintro ⟨d⟩
    exact ⟨d.axioms.toList, by simpa using d.axioms_mem,
      d.derivation.toDerivation.contra (by intro _; simp [Sequent2.emb]; grind)⟩

end derivation2

end LO.FirstOrder
