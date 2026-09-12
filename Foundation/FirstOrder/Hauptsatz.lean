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
| refl : Ξ.Traversal → Positive Ξ Ξ
| weakening : Positive Ξ Γ → Positive Ξ (Γ + ⦃φ⦄)
| contraction : Positive Ξ (Γ + ⦃φ, φ⦄) → Positive Ξ (Γ + ⦃φ⦄)
| or : Positive Ξ (Γ + ⦃φ, ψ⦄) → Positive Ξ (Γ + ⦃φ ⋎ ψ⦄)
| exs : Positive Ξ (Γ + ⦃φ/[t]⦄) → Positive Ξ (Γ + ⦃∃¹ φ⦄)

infix:45 " ⟶⁺ " => Positive

namespace Positive

variable {Ξ Γ Δ : Sequent L}

/-- Recovers the traversal stored at the source of a positive derivation. -/
def sourceTraversal : {Γ : Sequent L} → Ξ ⟶⁺ Γ → Ξ.Traversal
  | _, .refl t => t
  | _, .weakening d | _, .contraction d | _, .or d | _, .exs d => d.sourceTraversal

/-- Enumerates the target of a positive derivation. -/
def traversal [L.DecidableEq] : {Γ : Sequent L} → Ξ ⟶⁺ Γ → Γ.Traversal
  | _, .refl t => t
  | _, .weakening (φ := φ) d => d.traversal.succ φ
  | _, .contraction (φ := φ) d => (d.traversal.cast (by abel)).remove (a := φ)
  | _, .or (φ := φ) (ψ := ψ) d =>
      ((d.traversal.cast (by abel)).remove (a := ψ)).remove (a := φ) |>.succ (φ ⋎ ψ)
  | _, .exs (φ := φ) d => d.traversal.remove.succ (∃¹ φ)

instance : Structural (Positive Ξ) where
  weakening d := d.weakening
  contraction d := d.contraction

def ofSubset [L.DecidableEq] (tΞ : Ξ.Traversal) (tΓ : Γ.Traversal)
    (ss : Ξ ⊆ Γ) : Ξ ⟶⁺ Γ :=
  Structural.ofSubset (F := Proposition L) (𝔇 := Positive Ξ)
    (Γ := Ξ) (Δ := Γ) tΞ tΓ (.refl tΞ) ss

def trans {Ξ Γ Δ : Sequent L} : Ξ ⟶⁺ Γ → Γ ⟶⁺ Δ → Ξ ⟶⁺ Δ
  | b,    or d => or (b.trans d)
  | b,   exs d => exs (b.trans d)
  | b, weakening d => weakening (b.trans d)
  | b, contraction d => contraction (b.trans d)
  | b, .refl _ => b

def cast {Ξ Γ Ξ' Γ' : Sequent L} (d : Ξ ⟶⁺ Γ)
    (hΞ : Ξ = Ξ' := by abel) (hΓ : Γ = Γ' := by abel) : Ξ' ⟶⁺ Γ' :=
  hΞ ▸ hΓ ▸ d

def addLeft [L.DecidableEq] (tΔ : Δ.Traversal) : {Γ : Sequent L} → Ξ ⟶⁺ Γ → Δ + Ξ ⟶⁺ Δ + Γ
  | _, or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
      cast (.or (Ξ := Δ + Ξ) (Γ := Δ + Γ) (φ := φ) (ψ := ψ)
        (cast (addLeft tΔ d)))
  | _, exs (Γ := Γ) (φ := φ) (t := t) d =>
      cast (.exs (Ξ := Δ + Ξ) (Γ := Δ + Γ) (φ := φ) (t := t)
        (cast (addLeft tΔ d)))
  | _, weakening (φ := φ) d => cast (.weakening (φ := φ) (addLeft tΔ d))
  | _, contraction (Γ := Γ) (φ := φ) d =>
      cast (.contraction (Γ := Δ + Γ) (φ := φ)
        (cast (addLeft tΔ d) (hΞ := rfl) (hΓ := by abel)))
  | _, .refl t => .refl (tΔ.add t)

def cons [L.DecidableEq] (φ) (d : Ξ ⟶⁺ Γ) : Ξ + ⦃φ⦄ ⟶⁺ Γ + ⦃φ⦄ :=
  cast (addLeft (.atom φ) d)

def add [L.DecidableEq] {Γ Δ Ξ Θ : Sequent L} (d : Γ ⟶⁺ Δ) (b : Ξ ⟶⁺ Θ) :
    Γ + Ξ ⟶⁺ Δ + Θ :=
  (addLeft d.sourceTraversal b).trans (cast (addLeft b.traversal d))

def graft {Ξ Γ : Sequent L} (b : ⊢ᴸᴷ¹ Ξ) : Ξ ⟶⁺ Γ → ⊢ᴸᴷ¹ Γ
  |    or d => .or (d.graft b)
  |   exs d => .exs (d.graft b)
  | weakening d => .weakening (d.graft b)
  | contraction d => .contraction (d.graft b)
  | .refl _ => b

lemma graft_isCutFree_of_isCutFree {b : ⊢ᴸᴷ¹ Ξ} {d : Ξ ⟶⁺ Γ} (hb : Derivation.IsCutFree b) : Derivation.IsCutFree (d.graft b) := by
  induction d <;> simp [graft, *]

end Positive

namespace Canonical

open Semiformulaᵢ

variable [L.DecidableEq]

structure StrongerThan (q p : Sequent L) where
  val : ∼p ⟶⁺ ∼q

scoped infix:60 " ≼ " => StrongerThan

scoped instance : Min (Sequent L) := ⟨fun p q ↦ p + q⟩

omit [L.DecidableEq] in
lemma inf_def (p q : Sequent L) : p ⊓ q = p + q := rfl

omit [L.DecidableEq] in
@[simp] lemma neg_inf_p_eq (p q : Sequent L) : ∼(p ⊓ q) = ∼p ⊓ ∼q := Multiset.map_add _ _ _

namespace StrongerThan

protected def refl (p : Sequent L) (t : (∼p).Traversal) : p ≼ p := ⟨.refl t⟩

def trans {r q p : Sequent L} (srq : r ≼ q) (sqp : q ≼ p) : r ≼ p := ⟨sqp.val.trans srq.val⟩

def ofSubset {q p : Sequent L} (tp : (∼p).Traversal) (tq : (∼q).Traversal)
    (h : q ⊇ p) : q ≼ p :=
  ⟨.ofSubset tp tq <| Multiset.map_subset_map h⟩

def and {p : Sequent L} (tp : (∼p).Traversal) (φ ψ : Proposition L) :
    p + ⦃φ ⋏ ψ⦄ ≼ p + ⦃φ, ψ⦄ := by
  let t := (tp.succ (∼φ)).succ (∼ψ)
  let d : ∼p + ⦃∼φ, ∼ψ⦄ ⟶⁺ ∼p + ⦃∼φ ⋎ ∼ψ⦄ :=
    .or (.refl (t.cast (by abel)))
  exact ⟨d.cast (by simp) (by simp)⟩

def K_left {p : Sequent L} (tp : (∼p).Traversal) (φ ψ : Proposition L) :
    p + ⦃φ ⋏ ψ⦄ ≼ p + ⦃φ⦄ :=
  trans (and tp φ ψ) (ofSubset ((tp.succ (∼φ)).cast (by simp))
    (((tp.succ (∼φ)).succ (∼ψ)).cast (by simp; abel)) <| by
    intro θ hθ
    simp only [Multiset.mem_add] at *
    tauto)

def K_right {p : Sequent L} (tp : (∼p).Traversal) (φ ψ : Proposition L) :
    p + ⦃φ ⋏ ψ⦄ ≼ p + ⦃ψ⦄ :=
  trans (and tp φ ψ) (ofSubset ((tp.succ (∼ψ)).cast (by simp))
    (((tp.succ (∼φ)).succ (∼ψ)).cast (by simp; abel)) <| by
    intro θ hθ
    simp only [Multiset.mem_add] at *
    tauto)

def all {p : Sequent L} (tp : (∼p).Traversal) (φ : Semiproposition L 1) (t) :
    p + ⦃∀¹ φ⦄ ≼ p + ⦃φ/[t]⦄ := by
  let d : ∼p + ⦃(∼φ)/[t]⦄ ⟶⁺ ∼p + ⦃∃¹ ∼φ⦄ := .exs (.refl (tp.succ _))
  exact ⟨d.cast (by simp) (by simp)⟩

def minLeLeft (p q : Sequent L) (tp : (∼p).Traversal) (tq : (∼q).Traversal) :
    p ⊓ q ≼ p :=
  ofSubset tp (by simpa [inf_def] using tp.add tq) (by intro φ hφ; simp_all [inf_def])

def minLeRight (p q : Sequent L) (tp : (∼p).Traversal) (tq : (∼q).Traversal) :
    p ⊓ q ≼ q :=
  ofSubset tq (by simpa [inf_def] using tp.add tq) (by intro φ hφ; simp_all [inf_def])

def leMinOfle {r p q : Sequent L} (srp : r ≼ p) (srq : r ≼ q) : r ≼ p ⊓ q := ⟨
  let d : ∼p + ∼q ⟶⁺ ∼r := Positive.cast
    (Structural.contractMany (F := Proposition L) (𝔇 := Positive (∼p + ∼q))
      (Δ := 0) srp.val.traversal (Positive.cast (srp.val.add srq.val)))
  neg_inf_p_eq _ _ ▸ d⟩

def leMinRightOfLe {p q : Sequent L} (s : q ≼ p) : q ≼ p ⊓ q :=
  leMinOfle s (.refl q s.val.traversal)

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


abbrev allForces (φ : Propositionᵢ L) :=
  (p : Sequent L) → (∼p).Traversal → Forces p φ

namespace Forces

variable {p q : Sequent L}

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
    relEquiv.symm ⟨d.weakening, hd.weakening⟩
  | φ ⋏ ψ => andEquiv.symm ⟨b.explosion φ, b.explosion ψ⟩
  | φ ⋎ ψ => orEquiv.symm <| .inl <| b.explosion φ
  | φ 🡒 ψ => implyEquiv.symm fun q sqp _ ↦ (b.monotone sqp).explosion ψ
  | ∀¹ φ => allEquiv.symm fun t ↦ b.explosion (φ/[t])
  | ∃¹ φ => exsEquiv.symm ⟨default, b.explosion (φ/[default])⟩
  termination_by φ => φ.complexity

def efq (φ : Propositionᵢ L) : ⊩ ⊥ 🡒 φ :=
  fun _ _ ↦ implyEquiv.symm fun _ _ d ↦ d.explosion φ

def implyOf {φ ψ : Propositionᵢ L}
    (b : (q : Sequent L) → (∼q).Traversal → q ⊩ φ → p ⊓ q ⊩ ψ) :
    p ⊩ φ 🡒 ψ := implyEquiv.symm fun q sqp fφ ↦
  let fψ : p ⊓ q ⊩ ψ := b q sqp.val.traversal fφ
  fψ.monotone (StrongerThan.leMinRightOfLe sqp)

open LawfulSyntacticRewriting

def modusPonens {φ ψ : Propositionᵢ L} (tp : (∼p).Traversal)
    (f : p ⊩ φ 🡒 ψ) (g : p ⊩ φ) : p ⊩ ψ :=
  f.implyEquiv p (StrongerThan.refl p tp) g

abbrev ContextForces (p : Sequent L) (Γ : LJ.Sequent L) :=
  (φ : Propositionᵢ L) → φ ∈ Γ → p ⊩ φ

namespace ContextForces

variable {p q : Sequent L} {Γ Δ : LJ.Sequent L}

def ofSubset (b : ContextForces p Δ) (h : Γ ⊆ Δ) : ContextForces p Γ :=
  fun φ hφ ↦ b φ (h hφ)

def monotone (b : ContextForces p Γ) (s : q ≼ p) : ContextForces q Γ :=
  fun φ hφ ↦ (b φ hφ).monotone s

/-- Extend a forcing assignment by one formula (a routine semantic operation). -/
def cons (b : ContextForces p Γ) (hφ : p ⊩ φ) :
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

omit [L.DecidableEq] in
private lemma rewrite_shift_eq (t : SyntacticTerm L) (φ : Propositionᵢ L) :
    Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ Rewriting.shift φ = φ := by
  rw [← TransitiveRewriting.comp_app, Rew.rewrite_comp_shift_eq_id,
    ReflectiveRewriting.id_app]

/-- Soundness of LJ for the canonical Type-valued forcing interpretation.
- [Avi01, Section 3]
-/
def sound {Γ : LJ.Sequent L} {Ξ : LJ.Head L}
    (d : Γ ⊢ᴸᴶ¹ Ξ) (p : Sequent L) (tp : (∼p).Traversal)
    (b : ContextForces p Γ) : HeadForces p Ξ :=
  match d with
  | .identity R v => b (.rel R v) (by simp)
  | .cut (φ := φ) (Γ := Γ) (Δ := Δ) dφ d =>
      let bΓ := b.ofSubset (by intro ψ hψ; simp_all)
      let bΔ := b.ofSubset (by intro ψ hψ; simp_all)
      sound d p tp <| bΔ.cons (sound dφ p tp bΓ)
  | .contraction d => sound d p tp fun ψ hψ ↦ b ψ (by simp_all)
  | .weakening d => sound d p tp (b.ofSubset Multiset.subset_add_left)
  | .weakeningRight d => (sound d p tp b).explosion _
  | .verum => implyEquiv.symm fun _ _ h ↦ h
  | .falsum => b ⊥ (by simp)
  | .positiveImply d => implyEquiv.symm fun q sqp bφ ↦
      sound d q sqp.val.traversal <| (b.monotone sqp).cons bφ
  | .negativeImply (φ := φ) (ψ := ψ) (Γ := Γ) (Δ := Δ) dφ d =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      let bΔ := b.ofSubset (by intro θ hθ; simp_all)
      let bi : p ⊩ φ 🡒 ψ := b _ (by simp)
      sound d p tp <| bΔ.cons (bi.modusPonens tp <| sound dφ p tp bΓ)
  | .positiveAnd dφ dψ =>
      andEquiv.symm ⟨sound dφ p tp b, sound dψ p tp b⟩
  | .negativeAnd (φ := φ) (ψ := ψ) (Γ := Γ) d =>
      let bΓ : ContextForces p Γ := b.ofSubset Multiset.subset_add_left
      let ⟨bφ, bψ⟩ := (b (φ ⋏ ψ) (by simp)).andEquiv
      sound d p tp <| ((bΓ.cons bφ).cons bψ).ofSubset
        (by intro θ hθ; simpa [add_assoc] using hθ)
  | .positiveOrLeft d => orEquiv.symm <| .inl <| sound d p tp b
  | .positiveOrRight d => orEquiv.symm <| .inr <| sound d p tp b
  | .negativeOr (φ := φ) (ψ := ψ) (Γ := Γ) dφ dψ =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      (b (φ ⋎ ψ) (by simp)).orEquiv.rec
        (fun bφ ↦ sound dφ p tp <| bΓ.cons bφ)
        (fun bψ ↦ sound dψ p tp <| bΓ.cons bψ)
  | .positiveForall (Γ := Γ) (φ := φ) d => allEquiv.symm fun t ↦
      let f : ℕ → SyntacticTerm L := t :>ₙ fun x ↦ &x
      let dt : Γ ⊢ᴸᴶ¹ some (φ/[t]) := (d.rewrite f).cast
        (by simp [f, Rewriting.shifts, Multiset.map_map, rewrite_shift_eq])
        (by simp [f, LJ.Head.rewrite, rewrite_free_eq_subst])
      sound dt p tp b
  | .negativeForall (φ := φ) (Γ := Γ) d =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      let bAll := (b (∀¹ φ) (by simp)).allEquiv _
      sound d p tp <| bΓ.cons bAll
  | .positiveExists (t := t) d => exsEquiv.symm ⟨t, sound d p tp b⟩
  | .negativeExists (Γ := Γ) (Ξ := Ξ) (φ := φ) d =>
      let ⟨t, bt⟩ := (b (∃¹ φ) (by simp)).exsEquiv
      let f : ℕ → SyntacticTerm L := t :>ₙ fun x ↦ &x
      let dt : Γ + ⦃φ/[t]⦄ ⊢ᴸᴶ¹ Ξ := (d.rewrite f).cast
        (by simp [f, Rewriting.shifts, Multiset.map_map, rewrite_shift_eq,
          rewrite_free_eq_subst])
        (by cases Ξ <;> simp [f, LJ.Head.shift, LJ.Head.rewrite, rewrite_shift_eq])
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      sound dt p tp <| bΓ.cons bt
  termination_by d.height
  decreasing_by
    all_goals simp [LJ.Derivation.height]
    all_goals try omega
    all_goals
      exact Nat.lt_succ_iff.mpr <| Nat.le_of_eq <|
        (LJ.Derivation.height_cast _ _ _).trans (LJ.Derivation.height_rewrite (t :>ₙ fun x ↦ &x) d)

def ljSound {φ : Propositionᵢ L} (d : 𝐋𝐉¹ ⊢! φ) : ⊩ φ :=
  fun p tp ↦ sound d p tp fun _ h ↦ by simp at h

def relRefl {k} (R : L.Rel k) (v : Fin k → SyntacticTerm L) : ⦃.rel R v⦄ ⊩ rel R v :=
  relEquiv.symm ⟨Derivation.cast <| Derivation.identity _ _, by simp⟩

protected def refl.or {φ ψ : Proposition L}
    (ihφ : ⦃φ⦄ ⊩ φᴺ) (ihψ : ⦃ψ⦄ ⊩ ψᴺ) : ⦃φ ⋎ ψ⦄ ⊩ (φ ⋎ ψ)ᴺ :=
  implyOf fun q tq dq ↦
    let ⟨dφ, dψ⟩ : q ⊩ ∼φᴺ × q ⊩ ∼ψᴺ := dq.andEquiv
    let tφ : (∼(⦃φ⦄ : Sequent L)).Traversal := .atom _
    let tψ : (∼(⦃ψ⦄ : Sequent L)).Traversal := .atom _
    let bφ : ⦃φ⦄ ⊓ q ⊩ ⊥ := dφ.implyEquiv (⦃φ⦄ ⊓ q)
      (.minLeRight _ _ tφ tq) (ihφ.monotone (.minLeLeft _ _ tφ tq))
    let bψ : ⦃ψ⦄ ⊓ q ⊩ ⊥ := dψ.implyEquiv (⦃ψ⦄ ⊓ q)
      (.minLeRight _ _ tψ tq) (ihψ.monotone (.minLeLeft _ _ tψ tq))
    let ⟨bbφ, hbbφ⟩ := bφ.falsumEquiv
    let ⟨bbψ, hbbψ⟩ := bψ.falsumEquiv
    let bbφ' : ⊢ᴸᴷ¹ ∼q + ⦃∼φ⦄ := Derivation.cast bbφ (by simp [inf_def]; abel)
    let bbψ' : ⊢ᴸᴷ¹ ∼q + ⦃∼ψ⦄ := Derivation.cast bbψ (by simp [inf_def]; abel)
    let band : ⊢ᴸᴷ¹ ∼q + ⦃∼φ ⋏ ∼ψ⦄ := Derivation.and bbφ' bbψ'
    falsumEquiv.symm ⟨Derivation.cast band (by simp [inf_def]; abel), by
      simpa [band, bbφ', bbψ'] using And.intro hbbφ hbbψ⟩

-- Transparency is lowered so that rewriting under the recursive forcing definition remains stable.
set_option backward.isDefEq.respectTransparency false in
protected def refl.exs {φ : Semiproposition L 1}
    (d : ∀ x, ⦃φ/[&x]⦄ ⊩ (φ/[&x])ᴺ) : ⦃∃¹ φ⦄ ⊩ (∃¹ φ)ᴺ :=
  implyOf fun q tq f ↦
    let x := Sequent.newVar (∼q + ⦃∀¹ ∼φ⦄)
    let ih : ⦃φ/[&x]⦄ ⊩ φᴺ/[&x] := cast (d x) (by simp [Semiformula.subst_doubleNegation])
    let b : ⦃φ/[&x]⦄ ⊓ q ⊩ ⊥ :=
      let tφ : (∼(⦃φ/[&x]⦄ : Sequent L)).Traversal := .atom _
      (f.allEquiv &x).implyEquiv (⦃φ/[&x]⦄ ⊓ q)
        (StrongerThan.minLeRight _ _ tφ tq)
        (ih.monotone (StrongerThan.minLeLeft _ _ tφ tq))
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
  |  .rel R v => implyOf fun q tq dq ↦
    let tr : (∼(⦃.rel R v⦄ : Sequent L)).Traversal := .atom _
    let b : ⦃.rel R v⦄ ⊓ q ⊩ rel R v :=
      (relRefl R v).monotone (StrongerThan.minLeLeft _ _ tr tq)
    dq.implyEquiv (⦃.rel R v⦄ ⊓ q) (StrongerThan.minLeRight _ _ tr tq) b
  | .nrel R v => implyOf fun q _ dq ↦
    let ⟨d, hd⟩ := dq.relEquiv
    falsumEquiv.symm ⟨Derivation.cast d (by simp [inf_def]; abel), by simpa using hd⟩
  |     φ ⋏ ψ =>
    let ihφ : ⦃φ⦄ ⊩ φᴺ := Forces.refl φ
    let ihψ : ⦃ψ⦄ ⊩ ψᴺ := Forces.refl ψ
    andEquiv.symm ⟨by simpa using ihφ.monotone (.K_left (p := 0) .zero φ ψ),
      by simpa using ihψ.monotone (.K_right (p := 0) .zero φ ψ)⟩
  |     φ ⋎ ψ => refl.or (Forces.refl φ) (Forces.refl ψ)
  |      ∀¹ φ => allEquiv.symm fun t ↦
    let b : ⦃φ/[t]⦄ ⊩ φᴺ/[t] := by simpa [Semiformula.rew_doubleNegation] using Forces.refl (φ/[t])
    by simpa using b.monotone (StrongerThan.all (p := 0) .zero φ t)
  |      ∃¹ φ => refl.exs fun x ↦ Forces.refl (φ/[&x])
  termination_by φ => φ.complexity

end Forces

def constructiveHauptsatz {Γ : Sequent L} (d : ⊢ᴸᴷ¹ Γ) :
    {d : ⊢ᴸᴷ¹ Γ // Derivation.IsCutFree d} := by
  let tΓ : (∼(∼Γ)).Traversal := d.traversal.cast (by simp)
  have f : ((ψ : Propositionᵢ L) → ψ ∈ (∼Γ)ᴺ → Forces (∼Γ) ψ) → Forces (∼Γ) ⊥ :=
    Forces.sound d.gödelGentzen (∼Γ) tΓ
  have g : (ψ : Propositionᵢ L) → ψ ∈ (∼Γ)ᴺ → Forces (∼Γ) ψ := fun φ hφ ↦
    let t : (∼Γ).Traversal := d.traversal.map (∼·)
    have φ₀ := t.getPreimage (f := fun θ : Proposition L ↦ θᴺ)
      (by simpa [Sequent.doubleNegation] using hφ)
    have h : Forces (∼Γ) (φ₀.val)ᴺ := (Forces.refl φ₀.val).monotone <|
      StrongerThan.ofSubset (.atom _) tΓ (by simpa using φ₀.property.1)
    h.cast φ₀.property.2
  have ⟨b, hb⟩ := (f g).falsumEquiv
  exact ⟨Derivation.cast b (by simp), by simpa using hb⟩

def hauptsatz {Γ : Sequent L} (d : ⊢ᴸᴷ¹ Γ) :
    {d : ⊢ᴸᴷ¹ Γ // Derivation.IsCutFree d} := constructiveHauptsatz d

end Canonical
