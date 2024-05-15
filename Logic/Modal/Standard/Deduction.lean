import Logic.Logic.HilbertStyle.Basic
import Logic.Logic.HilbertStyle.Supplemental
import Logic.Modal.Standard.System
import Logic.Modal.Standard.Formula

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α]

inductive Deduction (Λ : AxiomSet α) : (Formula α) → Type _
  | maxm {p}     : p ∈ Λ → Deduction Λ p
  | mdp {p q}    : Deduction Λ (p ⟶ q) → Deduction Λ p → Deduction Λ q
  | nec {p}      : Deduction Λ p → Deduction Λ (□p)
  | verum        : Deduction Λ ⊤
  | imply₁ p q   : Deduction Λ (p ⟶ q ⟶ p)
  | imply₂ p q r : Deduction Λ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ p q    : Deduction Λ (p ⋏ q ⟶ p)
  | conj₂ p q    : Deduction Λ (p ⋏ q ⟶ q)
  | conj₃ p q    : Deduction Λ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ p q    : Deduction Λ (p ⟶ p ⋎ q)
  | disj₂ p q    : Deduction Λ (q ⟶ p ⋎ q)
  | disj₃ p q r  : Deduction Λ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne p        : Deduction Λ (~~p ⟶ p)

instance : System (Formula α) (AxiomSet α) := ⟨Deduction⟩

open Deduction

instance : System.Classical (Λ : AxiomSet α) where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  conj₁ := conj₁
  conj₂ := conj₂
  conj₃ := conj₃
  disj₁ := disj₁
  disj₂ := disj₂
  disj₃ := disj₃
  dne := dne

instance : System.Necessitation (Λ : AxiomSet α) where
  nec := nec

variable {Λ₁ Λ₂ : AxiomSet α}

def maxm_subset (hs : Λ₁ ⊆ Λ₂) : (Λ₁ ⊢ p) → (Λ₂ ⊢ p)
  | maxm h => maxm (hs h)
  | mdp h₁ h₂    => mdp (maxm_subset hs h₁) (maxm_subset hs h₂)
  | nec h        => nec $ maxm_subset hs h
  | verum        => verum
  | imply₁ _ _   => imply₁ _ _
  | imply₂ _ _ _ => imply₂ _ _ _
  | conj₁ _ _    => conj₁ _ _
  | conj₂ _ _    => conj₂ _ _
  | conj₃ _ _    => conj₃ _ _
  | disj₁ _ _    => disj₁ _ _
  | disj₂ _ _    => disj₂ _ _
  | disj₃ _ _ _  => disj₃ _ _ _
  | dne _        => dne _

lemma maxm_subset! (hs : Λ₁ ⊆ Λ₂) (h : Λ₁ ⊢! p) : Λ₂ ⊢! p := ⟨maxm_subset hs h.some⟩

instance K_of_subset_K (hK : 𝐊 ⊆ Λ := by simp) : System.K (Λ : AxiomSet α) where
  K _ _ := maxm $ Set.mem_of_subset_of_mem hK (by simp);

instance : System.K (𝐊 : AxiomSet α) := K_of_subset_K (by rfl)


instance S4_of_subset_S4 (hS4 : 𝐒𝟒 ⊆ Λ := by simp) : System.S4 (Λ : AxiomSet α) where
  K _ _   := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);
  T _     := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);
  Four _  := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);

instance : System.S4 (𝐒𝟒 : AxiomSet α) := S4_of_subset_S4 (by rfl)

end LO.Modal.Standard
