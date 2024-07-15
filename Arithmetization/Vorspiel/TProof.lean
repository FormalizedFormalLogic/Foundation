import Arithmetization.Vorspiel.Vorspiel

namespace LO.FirstOrder

#check LO.FirstOrder.Derivation

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

inductive FDerivation : Finset (SyntacticFormula L) → Type _
| axL   {Δ} (p : SyntacticFormula L)       : p ∈ Δ → ~p ∈ Δ → FDerivation Δ
| verum {Δ}                                : ⊤ ∈ Δ → FDerivation Δ
| and   {Δ} {p q : SyntacticFormula L}     : p ⋏ q ∈ Δ → FDerivation (insert p Δ) → FDerivation (insert q Δ) → FDerivation Δ
| or    {Δ} {p q : SyntacticFormula L}     : p ⋎ q ∈ Δ → FDerivation (insert p (insert q Δ)) → FDerivation Δ
| all   {Δ} {p : SyntacticSemiformula L 1} : ∀' p ∈ Δ → FDerivation (insert (Rew.free.hom p) (Δ.image Rew.shift.hom)) → FDerivation Δ
| ex    {Δ} {p : SyntacticSemiformula L 1} : ∃' p ∈ Δ → (t : SyntacticTerm L) → FDerivation (insert (p/[t]) Δ) → FDerivation Δ
| wk    {Δ Γ} : FDerivation Δ → Δ ⊆ Γ → FDerivation Γ
| cut   {Δ p} : FDerivation (insert p Δ) → FDerivation (insert (~p) Δ) → FDerivation Δ

prefix: 45 " ⊢¹ᶠ " => FDerivation

lemma shifts_toFinset_eq_image_shift (Δ : Sequent L) :
    (shifts Δ).toFinset = Δ.toFinset.image Rew.shift.hom := by ext p; simp [shifts]

def Derivation.toFDerivation : {Γ : Sequent L} → ⊢¹ Γ → ⊢¹ᶠ Γ.toFinset
  | _, Derivation.axL Δ r v          => FDerivation.axL (Semiformula.rel r v) (by simp) (by simp)
  | _, Derivation.verum Δ            => FDerivation.verum (by simp)
  | _, @Derivation.and _ Δ p q dp dq =>
    FDerivation.and (p := p) (q := q) (by simp)
      (FDerivation.wk (Derivation.toFDerivation dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
      (FDerivation.wk (Derivation.toFDerivation dq) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.or _ Δ p q dpq    =>
    FDerivation.or (p := p) (q := q) (by simp)
      (FDerivation.wk (Derivation.toFDerivation dpq)
      (by simpa using Finset.insert_subset_insert _ <| Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.all _ Δ p dp      =>
    FDerivation.all (p := p) (by simp)
      (FDerivation.wk (Derivation.toFDerivation dp)
        (by simpa using Finset.insert_subset_insert _ (by simp [shifts_toFinset_eq_image_shift])))
  | _, @Derivation.ex _ Δ p t dp     =>
    FDerivation.ex (p := p) (by simp) t
      (FDerivation.wk (Derivation.toFDerivation dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, Derivation.wk d h             =>
    FDerivation.wk (Derivation.toFDerivation d) (List.toFinset_mono h)
  | _, @Derivation.cut _ Δ p d₁ d₂   =>
    FDerivation.cut (p := p)
      (FDerivation.wk (Derivation.toFDerivation d₁) (by simp))
      (FDerivation.wk (Derivation.toFDerivation d₂) (by simp))

end LO.FirstOrder
