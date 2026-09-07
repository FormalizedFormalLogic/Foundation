module

public import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
public import Foundation.FirstOrder.Basic.Coding

/-!
# Hauptsatz of classical first-order logic

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/

@[expose] public section

namespace FFL.FirstOrder.Derivation

variable {L : Language}

inductive Positive (Ξ : Sequent L) : Sequent L → Type _
| or : Positive Ξ (Γ + ⦃φ, ψ⦄) → Positive Ξ (Γ + ⦃φ ⋎ ψ⦄)
| exs : Positive Ξ (Γ + ⦃φ/[t]⦄) → Positive Ξ (Γ + ⦃∃¹ φ⦄)
| contraction : Positive Ξ Δ → Δ ⊆ Γ → Positive Ξ Γ
| protected id : Positive Ξ Ξ

infix:45 " ⟶⁺ " => Positive

namespace Positive

variable {Ξ Γ Δ : Sequent L}

def ofSubset (ss : Ξ ⊆ Γ) : Ξ ⟶⁺ Γ := contraction .id ss

def trans {Ξ Γ Δ : Sequent L} : Ξ ⟶⁺ Γ → Γ ⟶⁺ Δ → Ξ ⟶⁺ Δ
  | b,    or d => or (b.trans d)
  | b,   exs d => exs (b.trans d)
  | b,  contraction d h => contraction (b.trans d) h
  | b,     .id => b

def cast {Ξ Γ Ξ' Γ' : Sequent L} (d : Ξ ⟶⁺ Γ)
    (hΞ : Ξ = Ξ' := by abel) (hΓ : Γ = Γ' := by abel) : Ξ' ⟶⁺ Γ' :=
  hΞ ▸ hΓ ▸ d

def addLeft (Δ : Sequent L) : {Γ : Sequent L} → Ξ ⟶⁺ Γ → Δ + Ξ ⟶⁺ Δ + Γ
  | _, or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
      cast (.or (Ξ := Δ + Ξ) (Γ := Δ + Γ) (φ := φ) (ψ := ψ)
        (cast (addLeft Δ d)))
  | _, exs (Γ := Γ) (φ := φ) (t := t) d =>
      cast (.exs (Ξ := Δ + Ξ) (Γ := Δ + Γ) (φ := φ) (t := t)
        (cast (addLeft Δ d)))
  | _, contraction d h => contraction (addLeft Δ d) <| by
      intro φ hφ
      simp only [Multiset.mem_add] at *
      tauto
  | _, .id => .id

def cons (φ) (d : Ξ ⟶⁺ Γ) : Ξ + ⦃φ⦄ ⟶⁺ Γ + ⦃φ⦄ :=
  cast (addLeft ⦃φ⦄ d)

def add {Γ Δ Ξ Θ : Sequent L} (d : Γ ⟶⁺ Δ) (b : Ξ ⟶⁺ Θ) : Γ + Ξ ⟶⁺ Δ + Θ :=
  (addLeft Γ b).trans (cast (addLeft Θ d))

def graft {Ξ Γ : Sequent L} (b : ⊢ᴸᴷ¹ Ξ) : Ξ ⟶⁺ Γ → ⊢ᴸᴷ¹ Γ
  |    or d => .or (d.graft b)
  |   exs d => .exs (d.graft b)
  |  contraction d h => .contraction (d.graft b) h
  |     .id => b

lemma graft_isCutFree_of_isCutFree {b : ⊢ᴸᴷ¹ Ξ} {d : Ξ ⟶⁺ Γ} (hb : Derivation.IsCutFree b) : Derivation.IsCutFree (d.graft b) := by
  induction d <;> simp [graft, *]

end Positive

namespace Canonical

open Semiformulaᵢ

structure StrongerThan (q p : Sequent L) where
  val : ∼p ⟶⁺ ∼q

scoped infix:60 " ≼ " => StrongerThan

scoped instance : Min (Sequent L) := ⟨fun p q ↦ p + q⟩

lemma inf_def (p q : Sequent L) : p ⊓ q = p + q := rfl

@[simp] lemma neg_inf_p_eq (p q : Sequent L) : ∼(p ⊓ q) = ∼p ⊓ ∼q := Multiset.map_add _ _ _

namespace StrongerThan

protected def refl (p : Sequent L) : p ≼ p := ⟨.id⟩

def trans {r q p : Sequent L} (srq : r ≼ q) (sqp : q ≼ p) : r ≼ p := ⟨sqp.val.trans srq.val⟩

def ofSubset {q p : Sequent L} (h : q ⊇ p) : q ≼ p := ⟨.ofSubset <| Multiset.map_subset_map h⟩

def and {p : Sequent L} (φ ψ : Proposition L) : p + ⦃φ ⋏ ψ⦄ ≼ p + ⦃φ, ψ⦄ := by
  let d : ∼p + ⦃∼φ, ∼ψ⦄ ⟶⁺ ∼p + ⦃∼φ ⋎ ∼ψ⦄ := .or .id
  exact ⟨d.cast (by simp) (by simp)⟩

def K_left {p : Sequent L} (φ ψ : Proposition L) : p + ⦃φ ⋏ ψ⦄ ≼ p + ⦃φ⦄ :=
  trans (and φ ψ) (ofSubset <| by
    intro θ hθ
    simp only [Multiset.mem_add] at *
    tauto)

def K_right {p : Sequent L} (φ ψ : Proposition L) : p + ⦃φ ⋏ ψ⦄ ≼ p + ⦃ψ⦄ :=
  trans (and φ ψ) (ofSubset <| by
    intro θ hθ
    simp only [Multiset.mem_add] at *
    tauto)

def all {p : Sequent L} (φ : Semiproposition L 1) (t) : p + ⦃∀¹ φ⦄ ≼ p + ⦃φ/[t]⦄ := by
  let d : ∼p + ⦃(∼φ)/[t]⦄ ⟶⁺ ∼p + ⦃∃¹ ∼φ⦄ := .exs .id
  exact ⟨d.cast (by simp) (by simp)⟩

def minLeLeft (p q : Sequent L) : p ⊓ q ≼ p := ofSubset (by intro φ hφ; simp_all [inf_def])

def minLeRight (p q : Sequent L) : p ⊓ q ≼ q := ofSubset (by intro φ hφ; simp_all [inf_def])

def leMinOfle (srp : r ≼ p) (srq : r ≼ q) : r ≼ p ⊓ q := ⟨
  let d : ∼p + ∼q ⟶⁺ ∼r := .contraction (srp.val.add srq.val) (by intro φ hφ; simp_all)
  neg_inf_p_eq _ _ ▸ d⟩

def leMinRightOfLe (s : q ≼ p) : q ≼ p ⊓ q := leMinOfle s (.refl q)

end StrongerThan

def Forces (p : Sequent L) : Propositionᵢ L → Type u
  |        ⊥ => { b : ⊢ᴸᴷ¹ ∼p // Derivation.IsCutFree b }
  | .rel R v => { b : ⊢ᴸᴷ¹ ∼p + ⦃.rel R v⦄ // Derivation.IsCutFree b }
  |    φ ⋏ ψ => Forces p φ × Forces p ψ
  |    φ ⋎ ψ => Forces p φ ⊕ Forces p ψ
  |    φ 🡒 ψ => (q : Sequent L) → q ≼ p → Forces q φ → Forces q ψ
  |     ∀¹ φ => (t : SyntacticTerm L) → Forces p (φ/[t])
  |     ∃¹ φ => (t : SyntacticTerm L) × Forces p (φ/[t])
  termination_by φ => φ.complexity


abbrev allForces (φ : Propositionᵢ L) := (p : Sequent L) → Forces p φ

namespace Forces

scoped infix:45 " ⊩ " => Forces

scoped prefix:45 "⊩ " => allForces


def falsumEquiv : p ⊩ ⊥ ≃ { b : ⊢ᴸᴷ¹ ∼p // Derivation.IsCutFree b} := by unfold Forces; exact .refl _

def relEquiv {k} {R : L.Rel k} {v} : p ⊩ .rel R v ≃ { b : ⊢ᴸᴷ¹ ∼p + ⦃.rel R v⦄ // Derivation.IsCutFree b } := by
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

def implyEquiv {φ ψ : Propositionᵢ L} : p ⊩ φ 🡒 ψ ≃ ((q : Sequent L) → q ≼ p → q ⊩ φ → q ⊩ ψ) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def allEquiv {φ} : p ⊩ ∀¹ φ ≃ ((t : SyntacticTerm L) → Forces p (φ/[t])) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def exsEquiv {φ} : p ⊩ ∃¹ φ ≃ ((t : SyntacticTerm L) × Forces p (φ/[t])) := by
  conv =>
    lhs
    unfold Forces
    exact .refl _

def cast {p : Sequent L} (f : p ⊩ φ) (s : φ = ψ) : p ⊩ ψ := s ▸ f

def monotone {q p : Sequent L} (s : q ≼ p) : {φ : Propositionᵢ L} → p ⊩ φ → q ⊩ φ
  | ⊥, b =>
    let ⟨d, hd⟩ := b.falsumEquiv
    falsumEquiv.symm ⟨s.val.graft d, Positive.graft_isCutFree_of_isCutFree hd⟩
  | .rel R v, b =>
    let ⟨d, hd⟩ := b.relEquiv
    relEquiv.symm ⟨s.val.cons (.rel R v) |>.graft d, Positive.graft_isCutFree_of_isCutFree hd⟩
  | φ ⋏ ψ, b => andEquiv.symm ⟨monotone s b.andEquiv.1, monotone s b.andEquiv.2⟩
  | φ ⋎ ψ, b => orEquiv.symm <| b.orEquiv.rec (fun b ↦ .inl <| b.monotone s) (fun b ↦ .inr <| b.monotone s)
  | φ 🡒 ψ, b => implyEquiv.symm fun r srq bφ ↦ b.implyEquiv r (srq.trans s) bφ
  | ∀¹ φ, b => allEquiv.symm fun t ↦ (b.allEquiv t).monotone s
  | ∃¹ φ, b =>
    let ⟨t, d⟩ : (t : SyntacticTerm L) × p ⊩ φ/[t] := b.exsEquiv
    exsEquiv.symm ⟨t, d.monotone s⟩
  termination_by φ => φ.complexity

def explosion {p : Sequent L} (b : p ⊩ ⊥) : (φ : Propositionᵢ L) → p ⊩ φ
  | ⊥ => b
  | .rel R v =>
    let ⟨d, hd⟩ := b.falsumEquiv
    let h : ∼p ⊆ ∼p + ⦃.rel R v⦄ := by intro φ hφ; simp_all
    relEquiv.symm ⟨.contraction d h, hd.contraction h⟩
  | φ ⋏ ψ => andEquiv.symm ⟨b.explosion φ, b.explosion ψ⟩
  | φ ⋎ ψ => orEquiv.symm <| .inl <| b.explosion φ
  | φ 🡒 ψ => implyEquiv.symm fun q sqp dφ ↦ (b.monotone sqp).explosion ψ
  | ∀¹ φ => allEquiv.symm fun t ↦ b.explosion (φ/[t])
  | ∃¹ φ => exsEquiv.symm ⟨default, b.explosion (φ/[default])⟩
  termination_by φ => φ.complexity

def efq (φ : Propositionᵢ L) : ⊩ ⊥ 🡒 φ := fun _ ↦ implyEquiv.symm fun _ _ d ↦ d.explosion φ

def implyOf {φ ψ : Propositionᵢ L} (b : (q : Sequent L) → q ⊩ φ → p ⊓ q ⊩ ψ) :
    p ⊩ φ 🡒 ψ := implyEquiv.symm fun q sqp fφ ↦
  let fψ : p ⊓ q ⊩ ψ := b q fφ
  fψ.monotone (StrongerThan.leMinRightOfLe sqp)

open LawfulSyntacticRewriting

def modusPonens {φ ψ : Propositionᵢ L} (f : p ⊩ φ 🡒 ψ) (g : p ⊩ φ) : p ⊩ ψ :=
  f.implyEquiv p (StrongerThan.refl p) g

abbrev ContextForces (p : Sequent L) (Γ : LJ.Sequent L) :=
  (φ : Propositionᵢ L) → φ ∈ Γ → p ⊩ φ

namespace ContextForces

variable {p q : Sequent L} {Γ Δ : LJ.Sequent L}

def ofSubset (b : ContextForces p Δ) (h : Γ ⊆ Δ) : ContextForces p Γ :=
  fun φ hφ ↦ b φ (h hφ)

def monotone (b : ContextForces p Γ) (s : q ≼ p) : ContextForces q Γ :=
  fun φ hφ ↦ (b φ hφ).monotone s

/-- Extend a forcing assignment by one formula (a routine semantic operation). -/
def cons [L.DecidableEq] (b : ContextForces p Γ) (hφ : p ⊩ φ) :
    ContextForces p (Γ + ⦃φ⦄) := fun ψ hψ ↦
  if h : φ = ψ then hφ.cast h else b ψ (by simp_all [eq_comm])

end ContextForces

def HeadForces (p : Sequent L) : LJ.Head L → Type u
  | none => p ⊩ ⊥
  | some φ => p ⊩ φ

def HeadForces.ofSubset {Ξ Λ : LJ.Head L} (h : Ξ ⊆ Λ) :
    HeadForces p Ξ → HeadForces p Λ := by
  intro b
  cases Ξ with
  | none => cases Λ with
    | none => exact b
    | some φ => exact b.explosion φ
  | some φ => cases Λ with
    | none => simp at h
    | some ψ =>
        have : φ = ψ := Option.some_subset_some.mp h
        subst ψ
        exact b

private lemma rewrite_shift_eq (t : SyntacticTerm L) (φ : Propositionᵢ L) :
    Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ Rewriting.shift φ = φ := by
  rw [← TransitiveRewriting.comp_app, Rew.rewrite_comp_shift_eq_id,
    ReflectiveRewriting.id_app]

/-- Soundness of LJ for the canonical Type-valued forcing interpretation.
- [Avi01, Section 3]
-/
def sound [L.DecidableEq] {Γ : LJ.Sequent L} {Ξ : LJ.Head L}
    (d : Γ ⊢ᴸᴶ¹ Ξ) (p : Sequent L) (b : ContextForces p Γ) : HeadForces p Ξ :=
  match d with
  | .identity R v => b (.rel R v) (by simp)
  | .cut (φ := φ) (Γ := Γ) (Δ := Δ) dφ d =>
      let bΓ := b.ofSubset (by intro ψ hψ; simp_all)
      let bΔ := b.ofSubset (by intro ψ hψ; simp_all)
      sound d p <| bΔ.cons (sound dφ p bΓ)
  | .contraction d hΓ hΞ =>
      HeadForces.ofSubset hΞ <| sound d p (b.ofSubset hΓ)
  | .verum => implyEquiv.symm fun _ _ h ↦ h
  | .falsum => b ⊥ (by simp)
  | .positiveImply d => implyEquiv.symm fun q sqp bφ ↦
      sound d q <| (b.monotone sqp).cons bφ
  | .negativeImply (φ := φ) (ψ := ψ) (Γ := Γ) (Δ := Δ) dφ d =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      let bΔ := b.ofSubset (by intro θ hθ; simp_all)
      let bi : p ⊩ φ 🡒 ψ := b _ (by simp)
      sound d p <| bΔ.cons (bi.modusPonens <| sound dφ p bΓ)
  | .positiveAnd dφ dψ =>
      andEquiv.symm ⟨sound dφ p b, sound dψ p b⟩
  | .negativeAnd (φ := φ) (ψ := ψ) (Γ := Γ) d =>
      let bΓ : ContextForces p Γ := b.ofSubset Multiset.subset_add_left
      let ⟨bφ, bψ⟩ := (b (φ ⋏ ψ) (by simp)).andEquiv
      sound d p <| ((bΓ.cons bφ).cons bψ).ofSubset (by intro θ hθ; simpa [add_assoc] using hθ)
  | .positiveOrLeft d => orEquiv.symm <| .inl <| sound d p b
  | .positiveOrRight d => orEquiv.symm <| .inr <| sound d p b
  | .negativeOr (φ := φ) (ψ := ψ) (Γ := Γ) dφ dψ =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      (b (φ ⋎ ψ) (by simp)).orEquiv.rec
        (fun bφ ↦ sound dφ p <| bΓ.cons bφ)
        (fun bψ ↦ sound dψ p <| bΓ.cons bψ)
  | .positiveForall (Γ := Γ) (φ := φ) d => allEquiv.symm fun t ↦
      let f : ℕ → SyntacticTerm L := t :>ₙ fun x ↦ &x
      let dt : Γ ⊢ᴸᴶ¹ some (φ/[t]) := (d.rewrite f).cast
        (by simp [f, Rewriting.shiftsM, Multiset.map_map, rewrite_shift_eq])
        (by simp [f, LJ.Head.rewrite, rewrite_free_eq_subst])
      sound dt p b
  | .negativeForall (φ := φ) (Γ := Γ) d =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      let bAll := (b (∀¹ φ) (by simp)).allEquiv _
      sound d p <| bΓ.cons bAll
  | .positiveExists (t := t) d => exsEquiv.symm ⟨t, sound d p b⟩
  | .negativeExists (Γ := Γ) (Ξ := Ξ) (φ := φ) d =>
      let ⟨t, bt⟩ := (b (∃¹ φ) (by simp)).exsEquiv
      let f : ℕ → SyntacticTerm L := t :>ₙ fun x ↦ &x
      let dt : Γ + ⦃φ/[t]⦄ ⊢ᴸᴶ¹ Ξ := (d.rewrite f).cast
        (by simp [f, Rewriting.shiftsM, Multiset.map_map, rewrite_shift_eq,
          rewrite_free_eq_subst])
        (by cases Ξ <;> simp [f, LJ.Head.shift, LJ.Head.rewrite, rewrite_shift_eq])
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      sound dt p <| bΓ.cons bt
  termination_by d.height
  decreasing_by
    all_goals simp [LJ.Derivation.height]
    all_goals try omega
    all_goals
      exact Nat.lt_succ_iff.mpr <| Nat.le_of_eq <|
        (LJ.Derivation.height_cast _ _ _).trans (LJ.Derivation.height_rewrite (t :>ₙ fun x ↦ &x) d)

def ljSound [L.DecidableEq] {φ : Propositionᵢ L} (d : 𝐋𝐉¹ ⊢! φ) : ⊩ φ :=
  fun p ↦ sound d p fun _ h ↦ by simp at h

def relRefl {k} (R : L.Rel k) (v : Fin k → SyntacticTerm L) : ⦃.rel R v⦄ ⊩ rel R v :=
  relEquiv.symm ⟨Derivation.cast <| Derivation.identity _ _, by simp⟩

protected def refl.or (ihφ : ⦃φ⦄ ⊩ φᴺ) (ihψ : ⦃ψ⦄ ⊩ ψᴺ) : ⦃φ ⋎ ψ⦄ ⊩ (φ ⋎ ψ)ᴺ :=
  implyOf fun q dq ↦
    let ⟨dφ, dψ⟩ : q ⊩ ∼φᴺ × q ⊩ ∼ψᴺ := dq.andEquiv
    let bφ : ⦃φ⦄ ⊓ q ⊩ ⊥ := dφ.implyEquiv (⦃φ⦄ ⊓ q) (.minLeRight _ _) (ihφ.monotone (.minLeLeft _ _))
    let bψ : ⦃ψ⦄ ⊓ q ⊩ ⊥ := dψ.implyEquiv (⦃ψ⦄ ⊓ q) (.minLeRight _ _) (ihψ.monotone (.minLeLeft _ _))
    let ⟨bbφ, hbbφ⟩ := bφ.falsumEquiv
    let ⟨bbψ, hbbψ⟩ := bψ.falsumEquiv
    let bbφ' : ⊢ᴸᴷ¹ ∼q + ⦃∼φ⦄ := Derivation.cast bbφ (by simp [inf_def]; abel)
    let bbψ' : ⊢ᴸᴷ¹ ∼q + ⦃∼ψ⦄ := Derivation.cast bbψ (by simp [inf_def]; abel)
    let band : ⊢ᴸᴷ¹ ∼q + ⦃∼φ ⋏ ∼ψ⦄ := Derivation.and bbφ' bbψ'
    falsumEquiv.symm ⟨Derivation.cast band (by simp [inf_def]; abel), by
      simpa [band, bbφ', bbψ'] using And.intro hbbφ hbbψ⟩

-- Transparency is lowered so that rewriting under the recursive forcing definition remains stable.
set_option backward.isDefEq.respectTransparency false in
protected def refl.exs (d : ∀ x, ⦃φ/[&x]⦄ ⊩ (φ/[&x])ᴺ) : ⦃∃¹ φ⦄ ⊩ (∃¹ φ)ᴺ :=
  implyOf fun q f ↦
    let x := Sequent.newVar (∼q + ⦃∀¹ ∼φ⦄)
    let ih : ⦃φ/[&x]⦄ ⊩ φᴺ/[&x] := cast (d x) (by simp [Semiformula.subst_doubleNegation])
    let b : ⦃φ/[&x]⦄ ⊓ q ⊩ ⊥ :=
      (f.allEquiv &x).implyEquiv (⦃φ/[&x]⦄ ⊓ q) (StrongerThan.minLeRight _ _)
        (ih.monotone (StrongerThan.minLeLeft _ _))
    let ⟨b, hb⟩ := b.falsumEquiv
    let hp : ¬(∼φ).FVar? x := by
      have : ¬(∀¹ ∼φ).FVar? x := Sequent.not_fvar?_newVar (by simp)
      simpa using this
    let hq : ∀ ψ ∈ ∼q, ¬ψ.FVar? x :=
      fun ψ hψ ↦ Sequent.not_fvar?_newVar (by simp [hψ])
    let b' : ⊢ᴸᴷ¹ ∼q + ⦃(∼φ)/[&x]⦄ :=
      Derivation.cast b (by simp [inf_def]; abel)
    let ba : ⊢ᴸᴷ¹ ∼q + ⦃∀¹ ∼φ⦄ :=
      Derivation.generalizeByNewVar hp hq b'
    falsumEquiv.symm ⟨Derivation.cast ba (by simp [inf_def]; abel), by
      simpa [ba, b'] using hb⟩

-- Transparency is lowered for the structural recursion through translated formulas.
set_option backward.isDefEq.respectTransparency false in
protected def refl : (φ : Proposition L) → ⦃φ⦄ ⊩ φᴺ
  |         ⊤ => implyEquiv.symm fun q sqp dφ ↦ dφ
  |         ⊥ => falsumEquiv.symm ⟨Derivation.verum, by simp⟩
  |  .rel R v => implyOf fun q dq ↦
    let b : ⦃.rel R v⦄ ⊓ q ⊩ rel R v := (relRefl R v).monotone (StrongerThan.minLeLeft _ _)
    dq.implyEquiv (⦃.rel R v⦄ ⊓ q) (StrongerThan.minLeRight _ _) b
  | .nrel R v => implyOf fun q dq ↦
    let ⟨d, hd⟩ := dq.relEquiv
    falsumEquiv.symm ⟨Derivation.cast d (by simp [inf_def]; abel), by simpa using hd⟩
  |     φ ⋏ ψ =>
    let ihφ : ⦃φ⦄ ⊩ φᴺ := Forces.refl φ
    let ihψ : ⦃ψ⦄ ⊩ ψᴺ := Forces.refl ψ
    andEquiv.symm ⟨by simpa using ihφ.monotone (.K_left (p := 0) φ ψ),
      by simpa using ihψ.monotone (.K_right (p := 0) φ ψ)⟩
  |     φ ⋎ ψ => refl.or (Forces.refl φ) (Forces.refl ψ)
  |      ∀¹ φ => allEquiv.symm fun t ↦
    let b : ⦃φ/[t]⦄ ⊩ φᴺ/[t] := by simpa [Semiformula.rew_doubleNegation] using Forces.refl (φ/[t])
    by simpa using b.monotone (StrongerThan.all (p := 0) φ t)
  |      ∃¹ φ => refl.exs fun x ↦ Forces.refl (φ/[&x])
  termination_by φ => φ.complexity

end Forces

def constructiveHauptsatz [L.DecidableEq] [L.Encodable] {Γ : Sequent L} (d : ⊢ᴸᴷ¹ Γ) :
    {d : ⊢ᴸᴷ¹ Γ // Derivation.IsCutFree d} := by
  have f : ((ψ : Propositionᵢ L) → ψ ∈ (∼Γ)ᴺ → Forces (∼Γ) ψ) → Forces (∼Γ) ⊥ :=
    Forces.sound d.gödelGentzen (∼Γ)
  have g : (ψ : Propositionᵢ L) → ψ ∈ (∼Γ)ᴺ → Forces (∼Γ) ψ := fun φ hφ ↦
    have φ₀ := Multiset.getPreimage hφ
    have h : Forces (∼Γ) (φ₀.val)ᴺ := (Forces.refl φ₀.val).monotone <|
      StrongerThan.ofSubset (by simpa using φ₀.property.1)
    h.cast (by simpa using φ₀.property.2)
  have ⟨b, hb⟩ := (f g).falsumEquiv
  exact ⟨Derivation.cast b (by simp), by simpa using hb⟩

noncomputable def hauptsatz {Γ : Sequent L} (d : ⊢ᴸᴷ¹ Γ) :
    {d : ⊢ᴸᴷ¹ Γ // Derivation.IsCutFree d} := by
  classical
  have f : ((ψ : Propositionᵢ L) → ψ ∈ (∼Γ)ᴺ → Forces (∼Γ) ψ) → Forces (∼Γ) ⊥ :=
    Forces.sound d.gödelGentzen (∼Γ)
  have : ∀ ψ ∈ (∼Γ)ᴺ, Nonempty (Forces (∼Γ) ψ) := fun φ hφ ↦ by
    have : ∃ φ₀ : Proposition L, ∼φ₀ ∈ Γ ∧ φ₀ᴺ = φ := by simpa [Sequent.doubleNegation] using hφ
    rcases this with ⟨φ₀, hφ₀⟩
    have h : Forces (∼Γ) (φ₀.val)ᴺ := (Forces.refl φ₀.val).monotone <|
      StrongerThan.ofSubset (by simpa using φ₀.property.1)
    exact ⟨h.cast (by simpa using φ₀.property.2)⟩
  have ⟨b, hb⟩ := (f fun φ hφ ↦ Classical.choice (this φ hφ)).falsumEquiv
  exact ⟨Derivation.cast b (by simp), by simpa using hb⟩

end Canonical
