module

public import Foundation.FirstOrder.Intuitionistic.LJ

@[expose] public section
namespace LO.FirstOrder

namespace Semiformula

def doubleNegation {n} : Semiformula L ξ n → Semiformulaᵢ L ξ n
  |  rel r v => ∼∼(.rel r v)
  | nrel r v => ∼(.rel r v)
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.doubleNegation ⋏ ψ.doubleNegation
  |    φ ⋎ ψ => ∼(∼φ.doubleNegation ⋏ ∼ψ.doubleNegation)
  |     ∀¹ φ => ∀¹ φ.doubleNegation
  |     ∃¹ φ => ∼(∀¹ ∼φ.doubleNegation)

scoped[LO.FirstOrder] postfix:max "ᴺ" => Semiformula.doubleNegation

@[simp] lemma doubleNegation_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v)ᴺ = ∼∼(.rel r v) := rfl

@[simp] lemma doubleNegation_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v)ᴺ = ∼(.rel r v) := rfl

@[simp] lemma doubleNegation_verum : (⊤ : Semiformula L ξ n)ᴺ = ∼⊥ := rfl

@[simp] lemma doubleNegation_falsum : (⊥ : Semiformula L ξ n)ᴺ = ⊥ := rfl

@[simp] lemma doubleNegation_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ)ᴺ = φᴺ ⋏ ψᴺ := rfl

@[simp] lemma doubleNegation_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ)ᴺ = ∼(∼φᴺ ⋏ ∼ψᴺ) := rfl

@[simp] lemma doubleNegation_all (φ : Semiformula L ξ (n + 1)) : (∀¹ φ)ᴺ = ∀¹ φᴺ := rfl

@[simp] lemma doubleNegation_ex (φ : Semiformula L ξ (n + 1)) : (∃¹ φ)ᴺ = ∼(∀¹ ∼φᴺ) := rfl

lemma doubleNegation_imply (φ ψ : Semiformula L ξ n) : (φ 🡒 ψ)ᴺ = ∼(∼(∼φ)ᴺ ⋏ ∼ψᴺ) := by simp [imp_eq]

@[simp] lemma doubleNegation_isNegative (φ : Semiformula L ξ n) : φᴺ.IsNegative := by
  induction φ using rec' <;> simp [*]

@[simp] lemma doubleNegation_conj₂ (Γ : List (Semiformula L ξ n)) :
    (Γ.conj₂)ᴺ = (Γ.map Semiformula.doubleNegation).conj₂ :=
  match Γ with
  |          [] => by simp; rfl
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [doubleNegation_conj₂ (ψ :: Γ)]

lemma doubleNegation_fconj (s : Finset (Semiformula L ξ n)) :
    (s.conj)ᴺ = (s.toList.map Semiformula.doubleNegation).conj₂ := doubleNegation_conj₂ _

lemma rew_doubleNegation (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : ω ▹ φᴺ = (ω ▹ φ)ᴺ := by
  induction φ using rec' generalizing n₂ <;> simp [Semiformulaᵢ.rew_rel, *, Function.comp_def]

lemma subst_doubleNegation (φ : Semiformula L ξ n₁) (v : Fin n₁ → Semiterm L ξ n₂) :
    φᴺ ⇜ v = (φ ⇜ v)ᴺ := rew_doubleNegation _ _

lemma emb_doubleNegation (φ : Semisentence L n₁) :
    Rewriting.emb (φᴺ) = (Rewriting.emb φ : Semiformula L ξ n₁)ᴺ := rew_doubleNegation _ _

end Semiformula

namespace Sequent

def doubleNegation (Γ : Sequent L) : LJ.Sequent L :=
  Γ.map Semiformula.doubleNegation

scoped[LO.FirstOrder] postfix:max "ᴺ" => Sequent.doubleNegation

@[simp] lemma doubleNegation_nil : ([] : Sequent L)ᴺ = [] := rfl

@[simp] lemma doubleNegation_cons (φ : Proposition L) (Γ : Sequent L) :
    (φ :: Γ)ᴺ = φᴺ :: Γᴺ := rfl

@[simp] lemma doubleNegation_append (Γ Δ : Sequent L) : (Γ ++ Δ)ᴺ = Γᴺ ++ Δᴺ := by
  simp [doubleNegation]

lemma shift_doubleNegation (Γ : Sequent L) : (Γᴺ)⁺ = (Γ⁺)ᴺ := by
  simp [Sequent.doubleNegation, Rewriting.shifts, Semiformula.rew_doubleNegation, Function.comp_def]

end Sequent

def Theory.ToHilbTheory (T : Theory L) (Λ : Hilbertᵢ L) : HilbTheory L Λ where
  theory := Semiformula.doubleNegation '' T

@[simp] lemma Theory.ToHilbTheory_theory_def (T : Theory L) (Λ : Hilbertᵢ L) :
    (T.ToHilbTheory Λ).theory = Semiformula.doubleNegation '' T := rfl
