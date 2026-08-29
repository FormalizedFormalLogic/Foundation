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

def IsCutFree : {Γ : Sequent L} → ⊢ᴸᴷ¹ Γ → Prop
  | _, .identity _ _ => True
  | _, .cut _ _ => False
  | _, .contraction d _ => IsCutFree d
  | _, .verum => True
  | _, .or d => IsCutFree d
  | _, .and dφ dψ => IsCutFree dφ ∧ IsCutFree dψ
  | _, .all d => IsCutFree d
  | _, .exs d => IsCutFree d

@[simp] lemma IsCutFree.identity (r : L.Rel k) (v) : IsCutFree (identity r v) := trivial

@[simp] lemma IsCutFree.verum : IsCutFree (verum : ⊢ᴸᴷ¹ (⦃⊤⦄ : Sequent L)) := trivial

lemma IsCutFree.or {d : ⊢ᴸᴷ¹ Γ + ⦃φ, ψ⦄} (h : IsCutFree d) : IsCutFree d.or := h

lemma IsCutFree.and {dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄} {dψ : ⊢ᴸᴷ¹ Γ + ⦃ψ⦄}
    (hφ : IsCutFree dφ) (hψ : IsCutFree dψ) : IsCutFree (dφ.and dψ) := ⟨hφ, hψ⟩

lemma IsCutFree.all {d : ⊢ᴸᴷ¹ Γ⁺ᵐ + ⦃Rewriting.free φ⦄} (h : IsCutFree d) : IsCutFree d.all := h

lemma IsCutFree.exs (t) {d : ⊢ᴸᴷ¹ Γ + ⦃φ/[t]⦄} (h : IsCutFree d) : IsCutFree d.exs := h

lemma IsCutFree.contraction {d : ⊢ᴸᴷ¹ Δ} (ss : Δ ⊆ Γ) (h : IsCutFree d) :
    IsCutFree (d.contraction ss) := h

variable {Γ Δ : Sequent L}

@[simp] lemma isCutFree_or_iff {d : ⊢ᴸᴷ¹ Γ + ⦃φ, ψ⦄} :
    IsCutFree d.or ↔ IsCutFree d := by rfl

@[simp] lemma isCutFree_and_iff {dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄} {dψ : ⊢ᴸᴷ¹ Γ + ⦃ψ⦄} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ := by rfl

@[simp] lemma isCutFree_all_iff {d : ⊢ᴸᴷ¹ Γ⁺ᵐ + ⦃Rewriting.free φ⦄} :
    IsCutFree d.all ↔ IsCutFree d := by rfl

@[simp] lemma isCutFree_exs_iff {d : ⊢ᴸᴷ¹ Γ + ⦃φ/[t]⦄} :
    IsCutFree d.exs ↔ IsCutFree d := by rfl

@[simp] lemma isCutFree_contraction_iff {d : ⊢ᴸᴷ¹ Δ} {ss : Δ ⊆ Γ} :
    IsCutFree (d.contraction ss) ↔ IsCutFree d := by rfl

@[simp] lemma IsCutFree.cast {d : ⊢ᴸᴷ¹ Γ} {e : Γ = Δ} :
    IsCutFree (.cast d e) ↔ IsCutFree d := by rcases e; rfl

@[simp] lemma IsCutFree.not_cut (dp : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (dn : ⊢ᴸᴷ¹ Δ + ⦃∼φ⦄) : ¬IsCutFree (dp.cut dn) := by
  simp [IsCutFree]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma isCutFree_rewrite_iff_isCutFree {f : ℕ → SyntacticTerm L} {d : ⊢ᴸᴷ¹ Γ} :
    IsCutFree (rewrite f d) ↔ IsCutFree d := by
  induction d generalizing f <;> simp [rewrite, *]

@[simp] lemma isCutFree_map_iff_isCutFree {f : ℕ → ℕ} {d : ⊢ᴸᴷ¹ Γ} :
    IsCutFree (Derivation.map d f) ↔ IsCutFree d := isCutFree_rewrite_iff_isCutFree

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma IsCutFree.generalizeByNewVar_isCutFree {φ : Semiproposition L 1} (hp : ¬φ.FVar? m)
    (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m) (d : ⊢ᴸᴷ¹ Δ + ⦃φ/[&m]⦄) :
    IsCutFree (generalizeByNewVar hp hΔ d) ↔ IsCutFree d := by simp [generalizeByNewVar]

end Derivation
