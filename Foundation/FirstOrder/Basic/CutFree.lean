module

public import Foundation.FirstOrder.Basic.Calculus

@[expose] public section
/-!
# Canonical model of classical first-order logic

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/

namespace LO.FirstOrder

variable {L : Language.{u}}

namespace Derivation

inductive IsCutFree : {Γ : Sequent L} → ⊢ᴷ Γ → Prop
| identity (r : L.Rel k) (v) : IsCutFree (identity r v)
| verum : IsCutFree verum
| or {d : ⊢ᴷ φ :: ψ :: Γ} : IsCutFree d → IsCutFree d.or
| and {dφ : ⊢ᴷ φ :: Γ} {dψ : ⊢ᴷ ψ :: Γ} : IsCutFree dφ → IsCutFree dψ → IsCutFree (dφ.and dψ)
| all {d : ⊢ᴷ Rewriting.free φ :: Γ⁺} : IsCutFree d → IsCutFree d.all
| exs (t) {d : ⊢ᴷ φ/[t] :: Γ} : IsCutFree d → IsCutFree d.exs
| wk  {d : ⊢ᴷ Δ} (ss : Δ ⊆ Γ) : IsCutFree d → IsCutFree (d.wk ss)

attribute [simp] IsCutFree.identity IsCutFree.verum

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

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma isCutFree_rewrite_iff_isCutFree {f : ℕ → SyntacticTerm L} {d : ⊢ᴷ Γ} :
    IsCutFree (rewrite f d) ↔ IsCutFree d := by
  induction d generalizing f <;> simp [rewrite, *]

@[simp] lemma isCutFree_map_iff_isCutFree {f : ℕ → ℕ} {d : ⊢ᴷ Γ} :
    IsCutFree (Derivation.map d f) ↔ IsCutFree d := isCutFree_rewrite_iff_isCutFree

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma IsCutFree.genelalizeByNewver_isCutFree {φ : Semiproposition L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : ⊢ᴷ φ/[&m] :: Δ) : IsCutFree (genelalizeByNewver hp hΔ d) ↔ IsCutFree d := by simp [genelalizeByNewver]

end Derivation
