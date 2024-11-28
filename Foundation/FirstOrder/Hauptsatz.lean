import Foundation.IntFO.Translation

/-!
#Algebraic Proofs of Cut Elimination

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination, The Journal of Logic and Algebraic Programming, Volume 49, Issues 1–2, 2001, Pages 15-30
 -/

namespace LO.FirstOrder

variable {L : Language}

namespace Derivation

inductive IsCutFree : {Γ : Sequent L} → ⊢ᵀ Γ → Prop
| axL (Γ) {k} (r : L.Rel k) (v)                 : IsCutFree (axL Γ r v)
| verum (Γ)                                     : IsCutFree (verum Γ)
| or {Γ φ ψ} {d : ⊢ᵀ φ :: ψ :: Γ}               : IsCutFree d → IsCutFree d.or
| and {Γ φ ψ} {dφ : ⊢ᵀ φ :: Γ} {dψ : ⊢ᵀ ψ :: Γ} : IsCutFree dφ → IsCutFree dψ → IsCutFree (dφ.and dψ)
| all {Γ φ} {d : ⊢ᵀ Rewriting.free φ :: Γ⁺}     : IsCutFree d → IsCutFree d.all
| ex {Γ φ} (t) {d : ⊢ᵀ φ/[t] :: Γ}              : IsCutFree d → IsCutFree d.ex
| wk {Δ Γ} {d : ⊢ᵀ Δ} (ss : Δ ⊆ Γ)              : IsCutFree d → IsCutFree (d.wk ss)

attribute [simp] IsCutFree.axL IsCutFree.verum

variable {Γ Δ : Sequent L}

@[simp] lemma isCutFree_or_iff {d : ⊢ᵀ φ :: ψ :: Γ} :
    IsCutFree d.or ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .or⟩

@[simp] lemma isCutFree_and_iff {dφ : ⊢ᵀ φ :: Γ} {dψ : ⊢ᵀ ψ :: Γ} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ :=
  ⟨by rintro ⟨⟩; constructor <;> assumption, by intro ⟨hφ, hψ⟩; exact hφ.and hψ⟩

@[simp] lemma isCutFree_all_iff {d : ⊢ᵀ Rewriting.free φ :: Γ⁺} :
    IsCutFree d.all ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .all⟩

@[simp] lemma isCutFree_ex_iff {d : ⊢ᵀ φ/[t] :: Γ} :
    IsCutFree d.ex ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .ex t⟩

@[simp] lemma isCutFree_wk_iff {d : ⊢ᵀ Δ} {ss : Δ ⊆ Γ} :
    IsCutFree (d.wk ss) ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .wk _⟩

end Derivation

inductive PositiveDerivationFrom (Ξ : Sequent L) : Sequent L → Type _
| verum (Γ)    : PositiveDerivationFrom Ξ (⊤ :: Γ)
| or {Γ φ ψ}   : PositiveDerivationFrom Ξ (φ :: ψ :: Γ) → PositiveDerivationFrom Ξ (φ ⋎ ψ :: Γ)
| ex {Γ φ} (t) : PositiveDerivationFrom Ξ (φ/[t] :: Γ) → PositiveDerivationFrom Ξ ((∃' φ) :: Γ)
| wk {Γ Δ}     : PositiveDerivationFrom Ξ Δ → Δ ⊆ Γ → PositiveDerivationFrom Ξ Γ
| protected id : PositiveDerivationFrom Ξ Ξ

infix:45 " ⟶⁺ " => PositiveDerivationFrom

namespace PositiveDerivationFrom

variable {Ξ Γ Δ : Sequent L}

def ofSubset (ss : Ξ ⊆ Γ) : Ξ ⟶⁺ Γ := wk .id ss

def trans {Ξ Γ Δ : Sequent L} : Ξ ⟶⁺ Γ → Γ ⟶⁺ Δ → Ξ ⟶⁺ Δ
  | _, verum Γ => verum Γ
  | b, or d    => or (b.trans d)
  | b, ex t d  => ex t (b.trans d)
  | b, wk d h  => wk (b.trans d) h
  | b, .id     => b

def cons {Ξ Γ : Sequent L} (φ) : Ξ ⟶⁺ Γ → φ :: Ξ ⟶⁺ φ :: Γ
  | verum Γ         => wk (verum Γ) (List.subset_cons_self _ _)
  | @or _ _ Γ ψ χ d =>
    have : φ :: Ξ ⟶⁺ ψ :: χ :: φ :: Γ := wk (cons φ d) (by simp; tauto)
    wk (or this) (by simp)
  | @ex _ Ξ Γ ψ t d =>
    have : φ :: Ξ ⟶⁺ ψ/[t] :: φ :: Γ := wk (cons φ d) (by simp)
    wk this.ex (by simp)
  | wk d h          => wk (d.cons φ) (by simp [h])
  | .id             => .id

def graft {Ξ Γ : Sequent L} (b : ⊢ᵀ Ξ) : Ξ ⟶⁺ Γ → ⊢ᵀ Γ
  | verum Γ => .verum Γ
  | or d    => .or (d.graft b)
  | ex t d  => .ex t (d.graft b)
  | wk d h  => .wk (d.graft b) h
  | .id     => b

lemma graft_isCutFree_of_isCutFree (b : ⊢ᵀ Ξ) (d : Ξ ⟶⁺ Γ) (hb : Derivation.IsCutFree b) : Derivation.IsCutFree (d.graft b) := by
  induction d <;> simp [graft, *]

end PositiveDerivationFrom

namespace Hauptsatz

local notation "ℙ" => Sequent L

structure StrongerThan (q p : ℙ) where
  val : ∼p ⟶⁺ ∼q

scoped infix:60 " ≼ " => StrongerThan

namespace StrongerThan

protected def refl (p : ℙ) : p ≼ p := ⟨.id⟩

def trans {r q p : ℙ} (srq : r ≼ q) (sqp : q ≼ p) : r ≼ p := ⟨sqp.val.trans srq.val⟩

def ofSubset {q p : ℙ} (h : q ⊇ p) : q ≼ p := ⟨.ofSubset <| List.map_subset _ h⟩

def and {p : ℙ} (φ ψ : SyntacticFormula L) : φ ⋏ ψ :: p ≼ φ :: ψ :: p := ⟨.or .id⟩

end StrongerThan

end Hauptsatz

end LO.FirstOrder
