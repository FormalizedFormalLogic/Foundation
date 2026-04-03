module

public import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
public import Foundation.Logic.ForcingRelation
public import Foundation.Vorspiel.Order.Preorder

@[expose] public section
/-!
# Algebraic proofs of cut elimination

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/

namespace LO.FirstOrder

variable {L : Language.{u}}

namespace Derivation

inductive IsCutFree : {Γ : Sequent L} → ⊢ᴷ Γ → Prop
| axL (r : L.Rel k) (v) : IsCutFree (identity r v)
| verum : IsCutFree verum
| or {d : ⊢ᴷ φ :: ψ :: Γ} : IsCutFree d → IsCutFree d.or
| and {dφ : ⊢ᴷ φ :: Γ} {dψ : ⊢ᴷ ψ :: Γ} : IsCutFree dφ → IsCutFree dψ → IsCutFree (dφ.and dψ)
| all {d : ⊢ᴷ Rewriting.free φ :: Γ⁺} : IsCutFree d → IsCutFree d.all
| exs (t) {d : ⊢ᴷ φ/[t] :: Γ} : IsCutFree d → IsCutFree d.exs
| wk  {d : ⊢ᴷ Δ} (ss : Δ ⊆ Γ) : IsCutFree d → IsCutFree (d.wk ss)

attribute [simp] IsCutFree.axL IsCutFree.verum

variable {Γ Δ : Sequent L}

@[simp] lemma isCutFree_or_iff {d : ⊢ᴷ φ :: ψ :: Γ} :
    IsCutFree d.or ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .or⟩

@[simp] lemma isCutFree_and_iff {dφ : ⊢ᴷ φ :: Γ} {dψ : ⊢ᴷ ψ :: Γ} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ :=
  ⟨by rintro ⟨⟩; constructor <;> assumption, by intro ⟨hφ, hψ⟩; exact hφ.and hψ⟩

@[simp] lemma isCutFree_all_iff {d : ⊢ᴷ Rewriting.free φ :: Γ⁺} :
    IsCutFree d.all ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .all⟩

@[simp] lemma isCutFree_exs_iff {d : ⊢ᴷ φ/[t] :: Γ} :
    IsCutFree d.exs ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .exs t⟩

@[simp] lemma isCutFree_wk_iff {d : ⊢ᴷ Δ} {ss : Δ ⊆ Γ} :
    IsCutFree (d.wk ss) ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .wk _⟩

@[simp] lemma IsCutFree.cast {d : ⊢ᴷ Γ} {e : Γ = Δ} :
    IsCutFree (.cast d e) ↔ IsCutFree d := by rcases e; rfl

@[simp] lemma IsCutFree.not_cut (dp : ⊢ᴷ φ :: Γ) (dn : ⊢ᴷ ∼φ :: Δ) : ¬IsCutFree (dp.cut dn) := by
  intro h
  refine h.rec
    (motive := fun {_} d _ =>
      match d with
      | .cut _ _ => False
      | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp

@[simp] lemma isCutFree_rewrite_iff_isCutFree {f : ℕ → SyntacticTerm L} {d : ⊢ᴷ Γ} :
    IsCutFree (rewrite f d) ↔ IsCutFree d := by
  induction d generalizing f <;> simp [rewrite, *]

@[simp] lemma isCutFree_map_iff_isCutFree {f : ℕ → ℕ} {d : ⊢ᴷ Γ} :
    IsCutFree (Derivation.map d f) ↔ IsCutFree d := isCutFree_rewrite_iff_isCutFree

@[simp] lemma IsCutFree.genelalizeByNewver_isCutFree {φ : Semiproposition L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : ⊢ᴷ φ/[&m] :: Δ) : IsCutFree (genelalizeByNewver hp hΔ d) ↔ IsCutFree d := by simp [genelalizeByNewver]

end Derivation

inductive PositiveDerivationFrom (Ξ : Sequent L) : Sequent L → Type _
| or : PositiveDerivationFrom Ξ (φ :: ψ :: Γ) → PositiveDerivationFrom Ξ (φ ⋎ ψ :: Γ)
| exs : PositiveDerivationFrom Ξ (φ/[t] :: Γ) → PositiveDerivationFrom Ξ ((∃⁰ φ) :: Γ)
| wk : PositiveDerivationFrom Ξ Δ → Δ ⊆ Γ → PositiveDerivationFrom Ξ Γ
| protected id : PositiveDerivationFrom Ξ Ξ

infix:45 " ⟶⁺ " => PositiveDerivationFrom

namespace PositiveDerivationFrom

variable {Ξ Γ Δ : Sequent L}

def ofSubset (ss : Ξ ⊆ Γ) : Ξ ⟶⁺ Γ := wk .id ss

def trans {Ξ Γ Δ : Sequent L} : Ξ ⟶⁺ Γ → Γ ⟶⁺ Δ → Ξ ⟶⁺ Δ
  | b,    or d => or (b.trans d)
  | b,   exs d => exs (b.trans d)
  | b,  wk d h => wk (b.trans d) h
  | b,     .id => b

def cons {Ξ Γ : Sequent L} (φ) : Ξ ⟶⁺ Γ → φ :: Ξ ⟶⁺ φ :: Γ
  | or (Γ := Γ) (φ := ψ) (ψ := χ) d =>
    have : φ :: Ξ ⟶⁺ ψ :: χ :: φ :: Γ := wk (cons φ d) (by simp; tauto)
    wk (or this) (by simp)
  | exs (Ξ := Ξ) (Γ := Γ) (φ := ψ) (t := t) d =>
    have : φ :: Ξ ⟶⁺ ψ/[t] :: φ :: Γ := wk (cons φ d) (by simp)
    wk this.exs (by simp)
  | wk d h => wk (d.cons φ) (by simp [h])
  | .id => .id

def append {Ξ Γ : Sequent L} : (Δ : Sequent L) → Ξ ⟶⁺ Γ → Δ ++ Ξ ⟶⁺ Δ ++ Γ
  | [],     d => d
  | φ :: Δ, d => (d.append Δ).cons φ

def add {Γ Δ Ξ Θ : Sequent L} : Γ ⟶⁺ Δ → Ξ ⟶⁺ Θ → Γ ++ Ξ ⟶⁺ Δ ++ Θ
  |    or d, b => or (d.add b)
  |   exs d, b => exs (d.add b)
  |  wk d h, b => wk (d.add b) (by simp [h])
  |     .id, b => b.append Γ

def graft {Ξ Γ : Sequent L} (b : ⊢ᴷ Ξ) : Ξ ⟶⁺ Γ → ⊢ᴷ Γ
  |    or d => .or (d.graft b)
  |   exs d => .exs (d.graft b)
  |  wk d h => .wk (d.graft b) h
  |     .id => b

lemma graft_isCutFree_of_isCutFree {b : ⊢ᴷ Ξ} {d : Ξ ⟶⁺ Γ} (hb : Derivation.IsCutFree b) : Derivation.IsCutFree (d.graft b) := by
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

def and {p : ℙ} (φ ψ : Proposition L) : φ ⋏ ψ :: p ≼ φ :: ψ :: p := ⟨.or .id⟩

def K_left {p : ℙ} (φ ψ : Proposition L) : φ ⋏ ψ :: p ≼ φ :: p := trans (and φ ψ) (ofSubset <| by simp)

def K_right {p : ℙ} (φ ψ : Proposition L) : φ ⋏ ψ :: p ≼ ψ :: p := trans (and φ ψ) (ofSubset <| by simp)

def all {p : ℙ} (φ : Semiproposition L 1) (t) : (∀⁰ φ) :: p ≼ φ/[t] :: p := ⟨.exs (t := t) (by simpa [← Semiformula.neg_eq] using .id)⟩

def minLeLeft (p q : ℙ) : p ⊓ q ≼ p := ofSubset (by simp [inf_def])

def minLeRight (p q : ℙ) : p ⊓ q ≼ q := ofSubset (by simp [inf_def])

def leMinOfle (srp : r ≼ p) (srq : r ≼ q) : r ≼ p ⊓ q := ⟨
  let d : ∼p ++ ∼q ⟶⁺ ∼r := .wk (srp.val.add srq.val) (by simp)
  neg_inf_p_eq _ _ ▸ d⟩

def leMinRightOfLe (s : q ≼ p) : q ≼ p ⊓ q := leMinOfle s (.refl q)

instance : LE ℙ := ⟨fun q p ↦ Nonempty (q ≼ p)⟩

instance : Preorder ℙ where
  le_refl p := ⟨StrongerThan.refl p⟩
  le_trans p q r := by
    rintro ⟨hqp⟩ ⟨hrq⟩
    exact ⟨StrongerThan.trans hqp hrq⟩

end StrongerThan

def Forces (p : ℙ) : Propositionᵢ L → Type u
  |        ⊥ => { b : ⊢ᴷ ∼p // Derivation.IsCutFree b }
  | .rel R v => { b : ⊢ᴷ .rel R v :: ∼p // Derivation.IsCutFree b }
  |    φ ⋏ ψ => Forces p φ × Forces p ψ
  |    φ ⋎ ψ => Forces p φ ⊕ Forces p ψ
  |    φ ➝ ψ => (q : ℙ) → q ≼ p → Forces q φ → Forces q ψ
  |     ∀⁰ φ => (t : SyntacticTerm L) → Forces p (φ/[t])
  |     ∃⁰ φ => (t : SyntacticTerm L) × Forces p (φ/[t])
  termination_by φ => φ.complexity


abbrev allForces (φ : Propositionᵢ L) := (p : ℙ) → Forces p φ

namespace Forces

scoped infix:45 " ⊩ " => Forces

scoped prefix:45 "⊩ " => allForces


def falsumEquiv : p ⊩ ⊥ ≃ { b : ⊢ᴷ ∼p // Derivation.IsCutFree b} := by unfold Forces; exact .refl _

def relEquiv {k} {R : L.Rel k} {v} : p ⊩ .rel R v ≃ { b : ⊢ᴷ .rel R v :: ∼p // Derivation.IsCutFree b } := by
  unfold Forces; exact .refl _

def andEquiv {φ ψ : Propositionᵢ L} : p ⊩ φ ⋏ ψ ≃ (p ⊩ φ) × (p ⊩ ψ) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def orEquiv {φ ψ : Propositionᵢ L} : p ⊩ φ ⋎ ψ ≃ (p ⊩ φ) ⊕ (p ⊩ ψ) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def implyEquiv {φ ψ : Propositionᵢ L} : p ⊩ φ ➝ ψ ≃ ((q : ℙ) → q ≼ p → q ⊩ φ → q ⊩ ψ) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def allEquiv {φ} : p ⊩ ∀⁰ φ ≃ ((t : SyntacticTerm L) → Forces p (φ/[t])) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def exsEquiv {φ} : p ⊩ ∃⁰ φ ≃ ((t : SyntacticTerm L) × Forces p (φ/[t])) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def cast {p : ℙ} (f : p ⊩ φ) (s : φ = ψ) : p ⊩ ψ := s ▸ f

def monotone {q p : ℙ} (s : q ≼ p) : {φ : Propositionᵢ L} → p ⊩ φ → q ⊩ φ
  | ⊥, b =>
    let ⟨d, hd⟩ := b.falsumEquiv
    falsumEquiv.symm ⟨s.val.graft d, PositiveDerivationFrom.graft_isCutFree_of_isCutFree hd⟩
  | .rel R v, b =>
    let ⟨d, hd⟩ := b.relEquiv
    relEquiv.symm ⟨s.val.cons (.rel R v) |>.graft d, PositiveDerivationFrom.graft_isCutFree_of_isCutFree hd⟩
  | φ ⋏ ψ, b => andEquiv.symm ⟨monotone s b.andEquiv.1, monotone s b.andEquiv.2⟩
  | φ ⋎ ψ, b => orEquiv.symm <| b.orEquiv.rec (fun b ↦ .inl <| b.monotone s) (fun b ↦ .inr <| b.monotone s)
  | φ ➝ ψ, b => implyEquiv.symm fun r srq bφ ↦ b.implyEquiv r (srq.trans s) bφ
  | ∀⁰ φ, b => allEquiv.symm fun t ↦ (b.allEquiv t).monotone s
  | ∃⁰ φ, b =>
    let ⟨t, d⟩ : (t : SyntacticTerm L) × p ⊩ φ/[t] := b.exsEquiv
    exsEquiv.symm ⟨t, d.monotone s⟩
  termination_by φ => φ.complexity

def explosion {p : ℙ} (b : p ⊩ ⊥) : (φ : Propositionᵢ L) → p ⊩ φ
  | ⊥ => b
  | .rel R v =>
    let ⟨d, hd⟩ := b.falsumEquiv
    relEquiv.symm ⟨.wk d (by simp), by simp [hd]⟩
  | φ ⋏ ψ => andEquiv.symm ⟨b.explosion φ, b.explosion ψ⟩
  | φ ⋎ ψ => orEquiv.symm <| .inl <| b.explosion φ
  | φ ➝ ψ => implyEquiv.symm fun q sqp dφ ↦ (b.monotone sqp).explosion ψ
  | ∀⁰ φ => allEquiv.symm fun t ↦ b.explosion (φ/[t])
  | ∃⁰ φ => exsEquiv.symm ⟨default, b.explosion (φ/[default])⟩
  termination_by φ => φ.complexity

def efq (φ : Propositionᵢ L) : ⊩ ⊥ ➝ φ := fun _ ↦ implyEquiv.symm fun _ _ d ↦ d.explosion φ

def implyOf {φ ψ : Propositionᵢ L} (b : (q : ℙ) → q ⊩ φ → p ⊓ q ⊩ ψ) :
    p ⊩ φ ➝ ψ := implyEquiv.symm fun q sqp fφ ↦
  let fψ : p ⊓ q ⊩ ψ := b q fφ
  fψ.monotone (StrongerThan.leMinRightOfLe sqp)

open LawfulSyntacticRewriting

def modusPonens {φ ψ : Propositionᵢ L} (f : p ⊩ φ ➝ ψ) (g : p ⊩ φ) : p ⊩ ψ :=
  f.implyEquiv p (StrongerThan.refl p) g

def sound {φ : Propositionᵢ L} : 𝗠𝗶𝗻¹ ⊢! φ → ⊩ φ
  | .mdp (φ := ψ) b d => fun p ↦
    let b : p ⊩ ψ ➝ φ := sound b p
    let d : p ⊩ ψ := sound d p
    b.implyEquiv p (StrongerThan.refl p) d
  | .gen (φ := φ) b => fun p ↦ allEquiv.symm fun t ↦
    let d : 𝗠𝗶𝗻¹ ⊢! φ/[t] :=
      HilbertProofᵢ.cast (HilbertProofᵢ.rewrite (t :>ₙ fun x ↦ &x) b) (by simp [rewrite_free_eq_subst])
    sound d p
  | .verum => fun p ↦ implyEquiv.symm fun q sqp bφ ↦ bφ
  | .implyK φ ψ => fun p ↦ implyEquiv.symm fun q sqp bφ ↦ implyEquiv.symm fun r srq bψ ↦ bφ.monotone srq
  | .implyS φ ψ χ => fun p ↦
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
    implyEquiv.symm fun q sqp bφ ↦ exsEquiv.symm ⟨t, bφ⟩
  | .ex₂ φ ψ => fun p ↦
    implyEquiv.symm fun q sqp b ↦
      implyEquiv.symm fun r srq bφ ↦
        let ⟨t, dt⟩ : (t : SyntacticTerm L) × r ⊩ φ/[t] := bφ.exsEquiv
        let d : q ⊩ φ/[t] ➝ ψ := by simpa using b.allEquiv t
      d.implyEquiv r srq dt
  termination_by b => HilbertProofᵢ.depth b

def relRefl {k} (R : L.Rel k) (v : Fin k → SyntacticTerm L) : [.rel R v] ⊩ rel R v :=
  relEquiv.symm ⟨Derivation.identity _ _, by simp⟩

protected def refl.or (ihφ : [φ] ⊩ φᴺ) (ihψ : [ψ] ⊩ ψᴺ) : [φ ⋎ ψ] ⊩ (φ ⋎ ψ)ᴺ :=
  implyOf fun q dq ↦
    let ⟨dφ, dψ⟩ : q ⊩ ∼φᴺ × q ⊩ ∼ψᴺ := dq.andEquiv
    let ihφ : [φ] ⊩ φᴺ := ihφ
    let ihψ : [ψ] ⊩ ψᴺ := ihψ
    let bφ : [φ] ⊓ q ⊩ ⊥ := dφ.implyEquiv ([φ] ⊓ q) (.minLeRight _ _) (ihφ.monotone (.minLeLeft _ _))
    let bψ : [ψ] ⊓ q ⊩ ⊥ := dψ.implyEquiv ([ψ] ⊓ q) (.minLeRight _ _) (ihψ.monotone (.minLeLeft _ _))
    let ⟨bbφ, hbbφ⟩ := bφ.falsumEquiv
    let ⟨bbψ, hbbψ⟩ := bψ.falsumEquiv
    let band : ⊢ᴷ ∼φ ⋏ ∼ψ :: ∼q := Derivation.and
      (Derivation.cast bbφ (by simp [inf_def])) (Derivation.cast bbψ (by simp [inf_def]))
    falsumEquiv.symm ⟨Derivation.cast band (by simp [inf_def]), by simp [band, hbbφ, hbbψ]⟩

protected def refl.exs (d : ∀ x, [φ/[&x]] ⊩ (φ/[&x])ᴺ) : [∃⁰ φ] ⊩ (∃⁰ φ)ᴺ :=
  implyOf fun q f ↦
    let x := Sequent.newVar ((∀⁰ ∼φ) :: ∼q)
    let ih : [φ/[&x]] ⊩ φᴺ/[&x] := cast (d x) (by simp [Semiformula.subst_doubleNegation])
    let b : [φ/[&x]] ⊓ q ⊩ ⊥ :=
      (f.allEquiv &x).implyEquiv ([φ/[&x]] ⊓ q) (StrongerThan.minLeRight _ _) (ih.monotone (StrongerThan.minLeLeft _ _))
    let ⟨b, hb⟩ := b.falsumEquiv
    let ba : ⊢ᴷ (∀⁰ ∼φ) :: ∼q :=
      Derivation.genelalizeByNewver (m := x)
        (by have : ¬Semiformula.FVar? (∀⁰ ∼φ) x := Sequent.not_fvar?_newVar (by simp)
            simpa using this)
        (fun ψ hψ ↦ Sequent.not_fvar?_newVar (List.mem_cons_of_mem (∀⁰ ∼φ) hψ))
        (Derivation.cast b (by simp [inf_def]))
    falsumEquiv.symm ⟨ba, by simp [ba, hb]⟩

protected def refl : (φ : Proposition L) → [φ] ⊩ φᴺ
  |         ⊤ => implyEquiv.symm fun q sqp dφ ↦ dφ
  |         ⊥ => falsumEquiv.symm ⟨Derivation.verum, by simp⟩
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
  |      ∀⁰ φ => allEquiv.symm fun t ↦
    let b : [φ/[t]] ⊩ φᴺ/[t] := by simpa [Semiformula.rew_doubleNegation] using Forces.refl (φ/[t])
    b.monotone (StrongerThan.all φ t)
  |      ∃⁰ φ => refl.exs fun x ↦ Forces.refl (φ/[&x])
  termination_by φ => φ.complexity

def conj : {Γ : Sequentᵢ L} → (b : (φ : Propositionᵢ L) → φ ∈ Γ → p ⊩ φ) → p ⊩ ⋀Γ
  | [], _ => implyEquiv.symm fun q sqp bφ ↦ bφ
  | [φ], b => b φ (by simp)
  | φ :: ψ :: Γ, b => andEquiv.symm ⟨b φ (by simp), conj (fun χ hχ ↦ b χ (List.mem_cons_of_mem φ hχ))⟩

def conj' : {Γ : Sequent L} → (b : (φ : Proposition L) → φ ∈ Γ → p ⊩ φᴺ) → p ⊩ ⋀Γᴺ
  | [], _ => implyEquiv.symm fun q sqp bφ ↦ bφ
  | [φ], b => b φ (by simp)
  | φ :: ψ :: Γ, b => andEquiv.symm ⟨b φ (by simp), conj' (fun χ hχ ↦ b χ (List.mem_cons_of_mem φ hχ))⟩

end Forces

def main [L.DecidableEq] {Γ : Sequent L} : ⊢ᴷ Γ → {d : ⊢ᴷ Γ // Derivation.IsCutFree d} := fun d ↦
  let d : 𝗠𝗶𝗻¹ ⊢! ⋀(∼Γ)ᴺ ➝ ⊥ := Entailment.FiniteContext.toDef (Derivation.gödelGentzen d)
  let ff : Forces (∼Γ) (⋀(∼Γ)ᴺ ➝ ⊥) := Forces.sound d (∼Γ)
  let fc : Forces (∼Γ) (⋀(∼Γ)ᴺ) := Forces.conj' fun φ hφ ↦
    (Forces.refl φ).monotone (StrongerThan.ofSubset <| List.cons_subset.mpr ⟨hφ, by simp⟩)
  let b : Forces (∼Γ) ⊥ := ff.modusPonens fc
  let ⟨b, hb⟩ := b.falsumEquiv
  ⟨Derivation.cast b (by simp), by simp [hb]⟩

abbrev IsForced (p : ℙ) (φ : Propositionᵢ L) := Nonempty (Forces p φ)

instance : ForcingRelation ℙ (Propositionᵢ L) where
  Forces := IsForced

namespace IsForced

open Classical

@[simp] lemma rel {p : ℙ} {k} {R : L.Rel k} {v} : p ⊩ .rel R v ↔ Nonempty (⊢ᴷ .rel R v :: ∼p) := by
  constructor
  · rintro ⟨b⟩
    have ⟨d, hd⟩ := b.relEquiv
    exact ⟨d⟩
  · rintro ⟨d⟩
    let ⟨b, hb⟩ := main d
    exact ⟨Forces.relEquiv.symm ⟨b, hb⟩⟩

@[simp] lemma fal {p : ℙ} : p ⊩ ∀⁰ φ ↔ ∀ t, p ⊩ φ/[t] := by
  constructor
  · rintro ⟨b⟩ t
    exact ⟨b.allEquiv t⟩
  · rintro h
    exact ⟨Forces.allEquiv.symm fun t ↦ (h t).some⟩

@[simp] lemma and {p : ℙ} {φ ψ : Propositionᵢ L} : p ⊩ φ ⋏ ψ ↔ p ⊩ φ ∧ p ⊩ ψ := by
  constructor
  · rintro ⟨b⟩
    have ⟨bφ, bψ⟩ := b.andEquiv
    exact ⟨⟨bφ⟩, ⟨bψ⟩⟩
  · rintro ⟨⟨bφ⟩, ⟨bψ⟩⟩
    exact ⟨Forces.andEquiv.symm ⟨bφ, bψ⟩⟩

@[simp] lemma or {p : ℙ} {φ ψ : Propositionᵢ L} : p ⊩ φ ⋎ ψ ↔ p ⊩ φ ∨ p ⊩ ψ := by
  constructor
  · rintro ⟨b⟩
    have b' := b.orEquiv
    exact b'.rec (fun bφ ↦ .inl ⟨bφ⟩) (fun bψ ↦ .inr ⟨bψ⟩)
  · rintro (⟨⟨hφ⟩⟩ | ⟨⟨hψ⟩⟩)
    · exact ⟨Forces.orEquiv.symm <| .inl hφ⟩
    · exact ⟨Forces.orEquiv.symm <| .inr hψ⟩

lemma imply {p : ℙ} {φ ψ : Propositionᵢ L} : p ⊩ φ ➝ ψ ↔ (∀ q ≤ p, q ⊩ φ → q ⊩ ψ) := by
  constructor
  · rintro ⟨b⟩ q ⟨sqp⟩ ⟨bφ⟩
    exact ⟨b.implyEquiv _ sqp bφ⟩
  · rintro h
    refine ⟨Forces.implyEquiv.symm fun q sqp hφ ↦ (h q ⟨sqp⟩ ⟨hφ⟩).some⟩

@[simp] lemma exs {p : ℙ} : p ⊩ ∃⁰ φ ↔ ∃ t, p ⊩ φ/[t] := by
  constructor
  · rintro ⟨b⟩
    have ⟨t, f⟩ := b.exsEquiv
    exact ⟨t, ⟨f⟩⟩
  · rintro ⟨t, h⟩
    exact ⟨Forces.exsEquiv.symm ⟨t, h.some⟩⟩

lemma falsum {p : ℙ} : p ⊩ ⊥ ↔ Nonempty (⊢ᴷ ∼p) := by
  constructor
  · rintro ⟨b⟩
    have ⟨d, hd⟩ := b.falsumEquiv
    exact ⟨d⟩
  · rintro ⟨d⟩
    let ⟨b, hb⟩ := main d
    exact ⟨Forces.falsumEquiv.symm ⟨b, hb⟩⟩

lemma neg {p : ℙ} {φ : Propositionᵢ L} : p ⊩ ∼φ ↔ (∀ q ≤ p, q ⊩ φ → q ⊩ ⊥) := by
  simp [Semiformulaᵢ.neg_def, imply]

lemma monotone {p q : ℙ} (hqp : q ≤ p) {φ : Propositionᵢ L} (hφ : p ⊩ φ) : q ⊩ φ :=
  ⟨Forces.monotone hqp.some hφ.some⟩

instance : ForcingRelation.PreIntKripke ℙ (· ≥ ·) where
  verum _ := ⟨Forces.implyEquiv.symm fun _ _ d ↦ d⟩
  and _ := and
  or _ := or
  imply _ := imply
  monotone hφ _ hpq := hφ.monotone hpq

lemma efq {p : ℙ} (h : p ⊩ ⊥) (φ : Propositionᵢ L) : p ⊩ φ := by
  have : p ⊩ ⊥ ➝ φ := ⟨Forces.efq φ p⟩
  exact imply.mp this p (by simp) h

lemma sound_minimal {φ : Propositionᵢ L} : 𝗠𝗶𝗻¹ ⊢ φ → ℙ ∀⊩ φ := by
  rintro ⟨d⟩ p; exact ⟨Forces.sound d p⟩

lemma dn_neg_iff {φ : Proposition L} {p : ℙ} : p ⊩ (∼φ)ᴺ ↔ p ⊩ ∼(φᴺ) := by
  have := by simpa using (sound_minimal (Derivation.neg_doubleNegation φ) p)
  exact (this p (by simp)).symm

protected lemma refl (φ : Proposition L) : [φ] ⊩ φᴺ := ⟨Forces.refl φ⟩

lemma complete {φ : Proposition L} : ℙ ∀⊩ φᴺ ↔ 𝐋𝐊¹ ⊢ φ := by
  constructor
  · intro h
    have hn : [∼φ] ⊩ ∼(φᴺ) := by simpa [dn_neg_iff] using (IsForced.refl (∼φ))
    have hp : [∼φ] ⊩ φᴺ := h [∼φ]
    have : 𝐋𝐊¹ ⊢ φ := by simpa using falsum.mp <| neg.mp hn [∼φ] (by simp) hp
    exact this
  · intro b
    exact sound_minimal <| Provable.gödel_gentzen b

end IsForced

def hValue (φ : Propositionᵢ L) : LowerSet ℙ where
  carrier := { p | p ⊩ φ }
  lower' := fun _ _ hqp hp ↦ IsForced.monotone hqp hp

scoped prefix:max "♯" => hValue

@[simp] lemma mem_hValue {p : ℙ} {φ : Propositionᵢ L} : p ∈ ♯φ ↔ p ⊩ φ := by simp [hValue]

@[simp] lemma hValue_and_eq_inf {φ ψ : Propositionᵢ L} : ♯(φ ⋏ ψ) = (♯φ ⊓ ♯ψ) := by
  ext p; simp [hValue]

@[simp] lemma hValue_or_eq_sup {φ ψ : Propositionᵢ L} : ♯(φ ⋎ ψ) = (♯φ ⊔ ♯ψ) := by
  ext p; simp [hValue]

@[simp] lemma hValue_fal_eq_Inf {φ : Semipropositionᵢ L 1} : ♯(∀⁰ φ) = ⨅ t, ♯(φ/[t]) := by
  ext p; simp [hValue,]

@[simp] lemma hValue_exs_eq_Sup {φ : Semipropositionᵢ L 1} : ♯(∃⁰ φ) = ⨆ t, ♯(φ/[t]) := by
  ext p; simp [hValue,]

@[simp] lemma hValue_imply_eq_himp {φ ψ : Propositionᵢ L} : ♯(φ ➝ ψ) = (♯φ ⇨ ♯ψ) := by
  ext p; simp [IsForced.imply, LowerSet.mem_himp_iff]

lemma hValue_falsum : p ∈ ♯(⊥ : Propositionᵢ L) ↔ Nonempty (⊢ᴷ ∼p) := by
  simp [hValue, IsForced.falsum]

@[simp] lemma hValue_neg_eq_himp_bot (φ : Propositionᵢ L) : ♯(∼φ) = (♯φ ⇨ ♯⊥) := by
  simp [Semiformulaᵢ.neg_def]

@[simp] lemma hValue_falsum_le (φ : Propositionᵢ L) : ♯⊥ ≤ ♯φ := fun _ h ↦ IsForced.efq h φ

lemma eq_top_iff_provable {φ : Proposition L} : ♯φᴺ = ⊤ ↔ 𝐋𝐊¹ ⊢ φ := calc
  ♯φᴺ = ⊤ ↔ ⊤ ≤ ♯φᴺ := by simp only [top_le_iff]
  _       ↔ ℙ ∀⊩ φᴺ := by simp [SetLike.le_def]
  _       ↔ 𝐋𝐊¹ ⊢ φ := IsForced.complete

lemma lt_top_iff_provable {φ : Proposition L} : ♯φᴺ < ⊤ ↔ 𝐋𝐊¹ ⊬ φ := by
  simp [Entailment.Unprovable, ←eq_top_iff_provable, lt_top_iff_ne_top]


end Hauptsatz

alias hauptsatz := Hauptsatz.main

end LO.FirstOrder
