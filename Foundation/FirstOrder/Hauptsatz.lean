import Foundation.IntFO.Translation

/-!
# Algebraic proofs of cut elimination

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination, The Journal of Logic and Algebraic Programming, Volume 49, Issues 1–2, 2001, Pages 15-30
 -/

namespace LO.FirstOrder

variable {L : Language.{u}}

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

@[simp] lemma IsCutFree.cast {d : ⊢ᵀ Γ} {e : Γ = Δ} :
    IsCutFree (.cast d e) ↔ IsCutFree d := by rcases e; rfl

@[simp] lemma IsCutFree.not_cut (dp : ⊢ᵀ φ :: Γ) (dn : ⊢ᵀ ∼φ :: Γ) : ¬IsCutFree (dp.cut dn) := by rintro ⟨⟩

@[simp] lemma isCutFree_rewrite_iff_isCutFree {f : ℕ → SyntacticTerm L} {d : ⊢ᵀ Γ} :
    IsCutFree (rewrite d f) ↔ IsCutFree d := by
  induction d generalizing f
  case axm => contradiction
  case _ => simp [rewrite, *]
  case _ => simp [rewrite, *]
  case _ => simp [rewrite, *]
  case _ => simp [rewrite, *]
  case _ => simp [rewrite, *]
  case _ => simp [rewrite, *]
  case _ => simp [rewrite, *]
  case _ => simp [rewrite, *]

@[simp] lemma isCutFree_map_iff_isCutFree {f : ℕ → ℕ} {d : ⊢ᵀ Γ} :
    IsCutFree (Derivation.map d f) ↔ IsCutFree d := isCutFree_rewrite_iff_isCutFree

@[simp] lemma IsCutFree.genelalizeByNewver_isCutFree {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : ⊢ᵀ φ/[&m] :: Δ) : IsCutFree (genelalizeByNewver hp hΔ d) ↔ IsCutFree d := by simp [genelalizeByNewver]

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

def append {Ξ Γ : Sequent L} : (Δ : Sequent L) → Ξ ⟶⁺ Γ → Δ ++ Ξ ⟶⁺ Δ ++ Γ
  | [],     d => d
  | φ :: Δ, d => (d.append Δ).cons φ

def add {Γ Δ Ξ Θ : Sequent L} : Γ ⟶⁺ Δ → Ξ ⟶⁺ Θ → Γ ++ Ξ ⟶⁺ Δ ++ Θ
  | verum Δ, d => verum _
  | or d,    b => or (d.add b)
  | ex t d,  b => ex t (d.add b)
  | wk d h,  b => wk (d.add b) (by simp [h])
  | .id,     b => b.append Γ

def graft {Ξ Γ : Sequent L} (b : ⊢ᵀ Ξ) : Ξ ⟶⁺ Γ → ⊢ᵀ Γ
  | verum Γ => .verum Γ
  | or d    => .or (d.graft b)
  | ex t d  => .ex t (d.graft b)
  | wk d h  => .wk (d.graft b) h
  | .id     => b

lemma graft_isCutFree_of_isCutFree {b : ⊢ᵀ Ξ} {d : Ξ ⟶⁺ Γ} (hb : Derivation.IsCutFree b) : Derivation.IsCutFree (d.graft b) := by
  induction d <;> simp [graft, *]

end PositiveDerivationFrom

namespace Hauptsatz

open Semiformulaᵢ

local notation "ℙ" => Sequent L

structure StrongerThan (q p : ℙ) where
  val : ∼p ⟶⁺ ∼q

scoped infix:60 " ≼ " => StrongerThan

scoped instance : Min ℙ := ⟨fun p q ↦ p ++ q⟩

lemma inf_def (p q : ℙ) : p ⊓ q = p ++ q := rfl

@[simp] lemma neg_inf_p_eq (p q : ℙ) : ∼(p ⊓ q) = ∼p ⊓ ∼q := List.map_append

namespace StrongerThan

protected def refl (p : ℙ) : p ≼ p := ⟨.id⟩

def trans {r q p : ℙ} (srq : r ≼ q) (sqp : q ≼ p) : r ≼ p := ⟨sqp.val.trans srq.val⟩

def ofSubset {q p : ℙ} (h : q ⊇ p) : q ≼ p := ⟨.ofSubset <| List.map_subset _ h⟩

def and {p : ℙ} (φ ψ : SyntacticFormula L) : φ ⋏ ψ :: p ≼ φ :: ψ :: p := ⟨.or .id⟩

def K_left {p : ℙ} (φ ψ : SyntacticFormula L) : φ ⋏ ψ :: p ≼ φ :: p := trans (and φ ψ) (ofSubset <| by simp)

def K_right {p : ℙ} (φ ψ : SyntacticFormula L) : φ ⋏ ψ :: p ≼ ψ :: p := trans (and φ ψ) (ofSubset <| by simp)

def all {p : ℙ} (φ : SyntacticSemiformula L 1) (t) : (∀' φ) :: p ≼ φ/[t] :: p := ⟨.ex t (by simpa [← Semiformula.neg_eq] using .id)⟩

def minLeLeft (p q : ℙ) : p ⊓ q ≼ p := ofSubset (by simp [inf_def])

def minLeRight (p q : ℙ) : p ⊓ q ≼ q := ofSubset (by simp [inf_def])

def leMinOfle (srp : r ≼ p) (srq : r ≼ q) : r ≼ p ⊓ q := ⟨
  let d : ∼p ++ ∼q ⟶⁺ ∼r := .wk (srp.val.add srq.val) (by simp)
  neg_inf_p_eq _ _ ▸ d⟩

def leMinRightOfLe (s : q ≼ p) : q ≼ p ⊓ q := leMinOfle s (.refl q)

end StrongerThan

abbrev Forces (p : ℙ) : SyntacticFormulaᵢ L → Type u
  | ⊤        => PUnit.{u+1}
  | ⊥        => { b : ⊢ᵀ ∼p // Derivation.IsCutFree b }
  | .rel R v => { b : ⊢ᵀ .rel R v :: ∼p // Derivation.IsCutFree b }
  | φ ⋏ ψ    => Forces p φ × Forces p ψ
  | φ ⋎ ψ    => Forces p φ ⊕ Forces p ψ
  | φ ➝ ψ    => (q : ℙ) → q ≼ p → Forces q φ → Forces q ψ
  | ∀' φ     => (t : SyntacticTerm L) → Forces p (φ/[t])
  | ∃' φ     => (t : SyntacticTerm L) × Forces p (φ/[t])
  termination_by φ => φ.complexity

scoped infix:45 " ⊩ " => Forces

abbrev allForces (φ : SyntacticFormulaᵢ L) := (p : ℙ) → p ⊩ φ

scoped prefix:45 "⊩ " => allForces

namespace Forces

def verumEquiv : p ⊩ ⊤ ≃ PUnit := .refl _

def falsumEquiv : p ⊩ ⊥ ≃ { b : ⊢ᵀ ∼p // Derivation.IsCutFree b} := .refl _

def relEquiv {k} {R : L.Rel k} {v} : p ⊩ .rel R v ≃ { b : ⊢ᵀ .rel R v :: ∼p // Derivation.IsCutFree b } := .refl _

def andEquiv {φ ψ : SyntacticFormulaᵢ L} : p ⊩ φ ⋏ ψ ≃ (p ⊩ φ) × (p ⊩ ψ) := .refl _

def orEquiv {φ ψ : SyntacticFormulaᵢ L} : p ⊩ φ ⋎ ψ ≃ (p ⊩ φ) ⊕ (p ⊩ ψ) := .refl _

def implyEquiv {φ ψ : SyntacticFormulaᵢ L} : p ⊩ φ ➝ ψ ≃ ((q : ℙ) → q ≼ p → q ⊩ φ → q ⊩ ψ) := .refl _

def allEquiv {φ} : p ⊩ ∀' φ ≃ ((t : SyntacticTerm L) → Forces p (φ/[t])) := .refl _

def exEquiv {φ} : p ⊩ ∃' φ ≃ ((t : SyntacticTerm L) × Forces p (φ/[t])) := .refl _

def cast {p : ℙ} (f : p ⊩ φ) (s : φ = ψ) : p ⊩ ψ := s ▸ f

def monotone {q p : ℙ} (s : q ≼ p) : {φ : SyntacticFormulaᵢ L} → p ⊩ φ → q ⊩ φ
  | ⊤,        _ => PUnit.unit
  | ⊥,        b =>
    let ⟨d, hd⟩ := b.falsumEquiv
    falsumEquiv.symm ⟨s.val.graft d, PositiveDerivationFrom.graft_isCutFree_of_isCutFree hd⟩
  | .rel R v, b =>
    let ⟨d, hd⟩ := b.relEquiv
    relEquiv.symm ⟨s.val.cons (.rel R v) |>.graft d, PositiveDerivationFrom.graft_isCutFree_of_isCutFree hd⟩
  | φ ⋏ ψ,    b => andEquiv.symm ⟨monotone s b.andEquiv.1, monotone s b.andEquiv.2⟩
  | φ ⋎ ψ,    b => orEquiv.symm <| b.orEquiv.rec (fun b ↦ .inl <| b.monotone s) (fun b ↦ .inr <| b.monotone s)
  | φ ➝ ψ,    b => implyEquiv.symm fun r srq bφ ↦ b.implyEquiv r (srq.trans s) bφ
  | ∀' φ,     b => allEquiv.symm fun t ↦ (b.allEquiv t).monotone s
  | ∃' φ,     b =>
    let ⟨t, d⟩ : (t : SyntacticTerm L) × p ⊩ φ/[t] := b.exEquiv
    exEquiv.symm ⟨t, d.monotone s⟩
  termination_by φ => φ.complexity

def explosion {p : ℙ} (b : p ⊩ ⊥) : (φ : SyntacticFormulaᵢ L) → p ⊩ φ
  | ⊤        => PUnit.unit
  | ⊥        => b
  | .rel R v =>
    let ⟨d, hd⟩ := b.falsumEquiv
    relEquiv.symm ⟨.wk d (by simp), by simp [hd]⟩
  | φ ⋏ ψ    => andEquiv.symm ⟨b.explosion φ, b.explosion ψ⟩
  | φ ⋎ ψ    => orEquiv.symm <| .inl <| b.explosion φ
  | φ ➝ ψ    => implyEquiv.symm fun q sqp dφ ↦ (b.monotone sqp).explosion ψ
  | ∀' φ     => allEquiv.symm fun t ↦ b.explosion (φ/[t])
  | ∃' φ     => exEquiv.symm ⟨default, b.explosion (φ/[default])⟩
  termination_by φ => φ.complexity

def efq (φ : SyntacticFormulaᵢ L) : ⊩ ⊥ ➝ φ := fun _ ↦ implyEquiv.symm fun _ _ d ↦ d.explosion φ

def implyOf {φ ψ : SyntacticFormulaᵢ L} (b : (q : ℙ) → q ⊩ φ → p ⊓ q ⊩ ψ) :
    p ⊩ φ ➝ ψ := implyEquiv.symm fun q sqp fφ ↦
  let fψ : p ⊓ q ⊩ ψ := b q fφ
  fψ.monotone (StrongerThan.leMinRightOfLe sqp)

open LawfulSyntacticRewriting

def modusPonens {φ ψ : SyntacticFormulaᵢ L} (f : p ⊩ φ ➝ ψ) (g : p ⊩ φ) : p ⊩ ψ :=
  f.implyEquiv p (StrongerThan.refl p) g

noncomputable
def ofMinimalProof {φ : SyntacticFormulaᵢ L} : 𝗠𝗶𝗻¹ ⊢ φ → ⊩ φ
  | .mdp (φ := ψ) b d => fun p ↦
    let b : p ⊩ ψ ➝ φ := ofMinimalProof b p
    let d : p ⊩ ψ := ofMinimalProof d p
    b.implyEquiv p (StrongerThan.refl p) d
  | .gen (φ := φ) b => fun p ↦ allEquiv.symm fun t ↦
    let d : 𝗠𝗶𝗻¹ ⊢ φ/[t] :=
      HilbertProofᵢ.cast (HilbertProofᵢ.rewrite (t :>ₙ fun x ↦ &x) b) (by simp [rewrite_free_eq_subst])
    ofMinimalProof d p
  | .verum => fun p ↦ PUnit.unit
  | .imply₁ φ ψ => fun p ↦ implyEquiv.symm fun q sqp bφ ↦ implyEquiv.symm fun r srq bψ ↦ bφ.monotone srq
  | .imply₂ φ ψ χ => fun p ↦
    implyEquiv.symm fun q sqp b₁ ↦
      implyEquiv.symm fun r srq b₂ ↦
        implyEquiv.symm fun s ssr b₃ ↦
          let d₁ : s ⊩ ψ ➝ χ := b₁.implyEquiv s (ssr.trans srq) b₃
          let d₂ : s ⊩ ψ := b₂.implyEquiv s ssr b₃
          d₁.implyEquiv s (StrongerThan.refl s) d₂
  | .and₁ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp b ↦
    let ⟨dφ, dψ⟩ : q ⊩ φ × q ⊩ ψ := b.andEquiv
    dφ
  | .and₂ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp b ↦
    let ⟨dφ, dψ⟩ : q ⊩ φ × q ⊩ ψ := b.andEquiv
    dψ
  | .and₃ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp bφ ↦
      implyEquiv.symm fun r srq bψ ↦
        andEquiv.symm ⟨bφ.monotone srq, bψ⟩
  | .or₁ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp bφ ↦ orEquiv.symm <| .inl bφ
  | .or₂ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp bψ ↦ orEquiv.symm <| .inr bψ
  | .or₃ φ ψ χ => fun p ↦
    implyEquiv.symm fun q sqp bφχ ↦
      implyEquiv.symm fun r srq bψχ ↦
        implyEquiv.symm fun s ssr b ↦
          let d : s ⊩ φ ⊕ s ⊩ ψ := b.orEquiv
          d.rec
            (fun dφ ↦ bφχ.implyEquiv s (ssr.trans srq) dφ)
            (fun dψ ↦ bψχ.implyEquiv s ssr dψ)
  | .all₁ φ t => fun p ↦ implyEquiv.symm fun q sqp b ↦ b.allEquiv t
  | .all₂ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp b ↦
      implyEquiv.symm fun r srq bφ ↦
        allEquiv.symm fun t ↦
      let d : q ⊩ φ ➝ ψ/[t] := by simpa using (b.allEquiv t)
      d.implyEquiv r srq bφ
  | .ex₁ t φ => fun p ↦
    implyEquiv.symm fun q sqp bφ ↦ exEquiv.symm ⟨t, bφ⟩
  | .ex₂ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp b ↦
      implyEquiv.symm fun r srq bφ ↦
        let ⟨t, dt⟩ : (t : SyntacticTerm L) × r ⊩ φ/[t] := bφ.exEquiv
        let d : q ⊩ φ/[t] ➝ ψ := by simpa using b.allEquiv t
      d.implyEquiv r srq dt
  termination_by b => HilbertProofᵢ.depth b

def relRefl {k} (R : L.Rel k) (v : Fin k → SyntacticTerm L) : [.rel R v] ⊩ rel R v :=
  relEquiv.symm ⟨Derivation.axL _ _ _, by simp⟩

private def refl.or (ihφ : [φ] ⊩ φᴺ) (ihψ : [ψ] ⊩ ψᴺ) : [φ ⋎ ψ] ⊩ (φ ⋎ ψ)ᴺ :=
  implyOf fun q dq ↦
    let ⟨dφ, dψ⟩ : q ⊩ ∼φᴺ × q ⊩ ∼ψᴺ := dq.andEquiv
    let ihφ : [φ] ⊩ φᴺ := ihφ
    let ihψ : [ψ] ⊩ ψᴺ := ihψ
    let bφ : [φ] ⊓ q ⊩ ⊥ := dφ.implyEquiv ([φ] ⊓ q) (.minLeRight _ _) (ihφ.monotone (.minLeLeft _ _))
    let bψ : [ψ] ⊓ q ⊩ ⊥ := dψ.implyEquiv ([ψ] ⊓ q) (.minLeRight _ _) (ihψ.monotone (.minLeLeft _ _))
    let ⟨bbφ, hbbφ⟩ := bφ.falsumEquiv
    let ⟨bbψ, hbbψ⟩ := bψ.falsumEquiv
    let band : ⊢ᵀ ∼φ ⋏ ∼ψ :: ∼q := Derivation.and
      (Derivation.cast bbφ (by simp [inf_def])) (Derivation.cast bbψ (by simp [inf_def]))
    falsumEquiv.symm ⟨Derivation.cast band (by simp [inf_def]), by simp [band, hbbφ, hbbψ]⟩

private def refl.ex (d : ∀ x, [φ/[&x]] ⊩ (φ/[&x])ᴺ) : [∃' φ] ⊩ (∃' φ)ᴺ :=
  implyOf fun q f ↦
    let x := newVar ((∀' ∼φ) :: ∼q)
    let ih : [φ/[&x]] ⊩ φᴺ/[&x] := cast (d x) (by simp [Semiformula.substitute_doubleNegation])
    let b : [φ/[&x]] ⊓ q ⊩ ⊥ :=
      (f.allEquiv &x).implyEquiv ([φ/[&x]] ⊓ q) (StrongerThan.minLeRight _ _) (ih.monotone (StrongerThan.minLeLeft _ _))
    let ⟨b, hb⟩ := b.falsumEquiv
    let ba : ⊢ᵀ (∀' ∼φ) :: ∼q :=
      Derivation.genelalizeByNewver (m := x)
        (by have : ¬Semiformula.FVar? (∀' ∼φ) x := not_fvar?_newVar (by simp)
            simpa using this)
        (fun ψ hψ ↦ not_fvar?_newVar (List.mem_cons_of_mem (∀' ∼φ) hψ))
        (Derivation.cast b (by simp [inf_def]))
    falsumEquiv.symm ⟨ba, by simp [ba, hb]⟩

protected def refl : (φ : SyntacticFormula L) → [φ] ⊩ φᴺ
  |         ⊤ => implyEquiv.symm fun q sqp dφ ↦ dφ
  |         ⊥ => falsumEquiv.symm ⟨Derivation.verum _, by simp⟩
  |  .rel R v => implyOf fun q dq ↦
    let b : [.rel R v] ⊓ q ⊩ rel R v := (relRefl R v).monotone (StrongerThan.minLeLeft _ _)
    dq.implyEquiv ([.rel R v] ⊓ q) (StrongerThan.minLeRight _ _) b
  | .nrel R v => implyOf fun q dq ↦
    let ⟨d, hd⟩ := dq.relEquiv
    falsumEquiv.symm ⟨Derivation.cast d (by simp [inf_def]), by simp [hd]⟩
  |     φ ⋏ ψ =>
    let ihφ : [φ] ⊩ φᴺ := Forces.refl φ
    let ihψ : [ψ] ⊩ ψᴺ := Forces.refl ψ
    andEquiv.symm ⟨ihφ.monotone (.K_left φ ψ), ihψ.monotone (.K_right φ ψ)⟩
  |     φ ⋎ ψ => refl.or (Forces.refl φ) (Forces.refl ψ)
  |      ∀' φ => allEquiv.symm fun t ↦
    let b : [φ/[t]] ⊩ φᴺ/[t] := by simpa [Semiformula.rew_doubleNegation] using Forces.refl (φ/[t])
    b.monotone (StrongerThan.all φ t)
  |      ∃' φ => refl.ex fun x ↦ Forces.refl (φ/[&x])
  termination_by φ => φ.complexity

def conj : {Γ : Sequentᵢ L} → (b : (φ : SyntacticFormulaᵢ L) → φ ∈ Γ → p ⊩ φ) → p ⊩ ⋀Γ
  | [],          _ => PUnit.unit
  | [φ],         b => b φ (by simp)
  | φ :: ψ :: Γ, b => andEquiv.symm ⟨b φ (by simp), conj (fun χ hχ ↦ b χ (List.mem_cons_of_mem φ hχ))⟩

def conj' : {Γ : Sequent L} → (b : (φ : SyntacticFormula L) → φ ∈ Γ → p ⊩ φᴺ) → p ⊩ ⋀Γᴺ'
  | [],          _ => PUnit.unit
  | [φ],         b => b φ (by simp)
  | φ :: ψ :: Γ, b => andEquiv.symm ⟨b φ (by simp), conj' (fun χ hχ ↦ b χ (List.mem_cons_of_mem φ hχ))⟩

end Forces

noncomputable
def main [L.DecidableEq] {Γ : Sequent L} : ⊢ᵀ Γ → {d : ⊢ᵀ Γ // Derivation.IsCutFree d} := fun d ↦
  let d : 𝗠𝗶𝗻¹ ⊢ ⋀(∼Γ)ᴺ' ➝ ⊥ := Entailment.FiniteContext.toDef (Derivation.goedelGentzen d)
  let ff : ∼Γ ⊩ ⋀(∼Γ)ᴺ' ➝ ⊥ := Forces.ofMinimalProof d (∼Γ)
  let fc : ∼Γ ⊩ ⋀(∼Γ)ᴺ' := Forces.conj' fun φ hφ ↦
    (Forces.refl φ).monotone (StrongerThan.ofSubset <| List.cons_subset.mpr ⟨hφ, by simp⟩)
  let b : ∼Γ ⊩ ⊥ := ff.modusPonens fc
  let ⟨b, hb⟩ := b.falsumEquiv
  ⟨Derivation.cast b (Sequent.neg_neg_eq Γ), by simp [hb]⟩

end Hauptsatz

alias hauptsatz := Hauptsatz.main

end LO.FirstOrder
