import Logic.FirstOrder.Basic.Calculus

/-!

# Derivation2

Different characterizations of proof.

-/

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

variable [L.ConstantInhabited]

section derivation3

inductive Derivation2 (T : Theory L) : Finset (SyntacticFormula L) → Type _
| closed (Δ) (p : SyntacticFormula L)      : p ∈ Δ → ∼p ∈ Δ → Derivation2 T Δ
| root  {Δ} (p : SyntacticFormula L)       : p ∈ T → p ∈ Δ → Derivation2 T Δ
| verum {Δ}                                : ⊤ ∈ Δ → Derivation2 T Δ
| and   {Δ} {p q : SyntacticFormula L}     : p ⋏ q ∈ Δ → Derivation2 T (insert p Δ) → Derivation2 T (insert q Δ) → Derivation2 T Δ
| or    {Δ} {p q : SyntacticFormula L}     : p ⋎ q ∈ Δ → Derivation2 T (insert p (insert q Δ)) → Derivation2 T Δ
| all   {Δ} {p : SyntacticSemiformula L 1} : ∀' p ∈ Δ → Derivation2 T (insert (Rew.free.hom p) (Δ.image Rew.shift.hom)) → Derivation2 T Δ
| ex    {Δ} {p : SyntacticSemiformula L 1} : ∃' p ∈ Δ → (t : SyntacticTerm L) → Derivation2 T (insert (p/[t]) Δ) → Derivation2 T Δ
| wk    {Δ Γ} : Derivation2 T Δ → Δ ⊆ Γ → Derivation2 T Γ
| shift {Δ}   : Derivation2 T Δ → Derivation2 T (Δ.image Rew.shift.hom)
| cut   {Δ p} : Derivation2 T (insert p Δ) → Derivation2 T (insert (∼p) Δ) → Derivation2 T Δ

scoped infix:45 " ⊢₃ " => Derivation2

abbrev Derivable3 (T : Theory L) (Γ : Finset (SyntacticFormula L)) := Nonempty (T ⊢₃ Γ)

scoped infix:45 " ⊢₃! " => Derivable3

abbrev Derivable3SingleConseq (T : Theory L) (p : SyntacticFormula L) : Prop := T ⊢₃! {p}

scoped infix: 45 " ⊢₃.! " => Derivable3SingleConseq

variable {T : Theory L}

lemma shifts_toFinset_eq_image_shift (Δ : Sequent L) :
    (shifts Δ).toFinset = Δ.toFinset.image Rew.shift.hom := by ext p; simp [shifts]

def Derivation.toDerivation2 T : {Γ : Sequent L} → T ⟹ Γ → T ⊢₃ Γ.toFinset
  | _, Derivation.axL Δ R v            => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | _, Derivation.root (p := p) h      => Derivation2.root p h (by simp)
  | _, Derivation.verum Δ              => Derivation2.verum (by simp)
  | _, @Derivation.and _ _ Δ p q dp dq =>
    Derivation2.and (p := p) (q := q) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
      (Derivation2.wk (Derivation.toDerivation2 T dq) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.or _ _ Δ p q dpq    =>
    Derivation2.or (p := p) (q := q) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dpq)
      (by simpa using Finset.insert_subset_insert _ <| Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.all _ _ Δ p dp      =>
    Derivation2.all (p := p) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp)
        (by simpa using Finset.insert_subset_insert _ (by simp [shifts_toFinset_eq_image_shift])))
  | _, @Derivation.ex _ _ Δ p t dp     =>
    Derivation2.ex (p := p) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, Derivation.wk d h               =>
    Derivation2.wk (Derivation.toDerivation2 T d) (List.toFinset_mono h)
  | _, @Derivation.cut _ _ Δ p d₁ d₂   =>
    Derivation2.cut (p := p)
      (Derivation2.wk (Derivation.toDerivation2 T d₁) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 T d₂) (by simp))

noncomputable def Derivation2.toDerivation : {Γ : Finset (SyntacticFormula L)} → T ⊢₃ Γ → T ⟹ Γ.toList
  | _, Derivation2.closed Δ p hp hn              => Derivation.em (p := p) (by simp [hp]) (by simp [hn])
  | _, Derivation2.root p hp h                   => Tait.wk (Derivation.root hp) (by simp_all)
  | _, Derivation2.verum h                       => Tait.verum' (by simp [h])
  | _, Derivation2.and (p := p) (q := q) h dp dq =>
    Tait.and' (p := p) (q := q) (by simp [h])
      (Tait.wk dp.toDerivation <| by intro x; simp)
      (Tait.wk dq.toDerivation <| by intro x; simp)
  | _, Derivation2.or (p := p) (q := q) h dpq    =>
    Tait.or' (p := p) (q := q) (by simp [h]) (Tait.wk dpq.toDerivation <| by intro x; simp)
  | _, Derivation2.all (p := p) h d              =>
    Derivation.all' (p := p) (by simp [h]) (Tait.wk d.toDerivation <| by intro x; simp [shifts])
  | _, Derivation2.ex (p := p) h t d             =>
    Derivation.ex' (p := p) (by simp [h]) t (Tait.wk d.toDerivation <| by intro x; simp [shifts])
  | _, Derivation2.wk d h                        =>
    Tait.wk d.toDerivation (by intro x; simp; exact @h x)
  | _, Derivation2.shift d                       =>
    Tait.wk (Derivation.shift d.toDerivation) <| by intro x; simp [shifts]
  | _, Derivation2.cut (p := p) d dn             =>
    Tait.cut (p := p)
      (Tait.wk d.toDerivation <| by intro x; simp)
      (Tait.wk dn.toDerivation <| by intro x; simp)

lemma derivable_iff_derivable2 {Γ : List (SyntacticFormula L)} : T ⟹! Γ ↔ T ⊢₃! Γ.toFinset := by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using Derivation.toDerivation2 T d⟩
  · rintro ⟨d⟩; exact ⟨.wk d.toDerivation (by intro x; simp)⟩

def provable_iff_derivable2 {p} : T ⊢! p ↔ T ⊢₃.! p := derivable_iff_derivable2

end derivation3

end LO.FirstOrder
