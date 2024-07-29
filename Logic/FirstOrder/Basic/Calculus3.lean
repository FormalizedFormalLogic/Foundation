import Logic.FirstOrder.Basic.Calculus2

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

inductive Derivation3 (T : SyntacticTheory L) : Finset (SyntacticFormula L) → Type _
| closed (Δ) (p : SyntacticFormula L)      : p ∈ Δ → ~p ∈ Δ → Derivation3 T Δ
| root  {Δ} (p : SyntacticFormula L)       : p ∈ T → p ∈ Δ → Derivation3 T Δ
| verum {Δ}                                : ⊤ ∈ Δ → Derivation3 T Δ
| and   {Δ} {p q : SyntacticFormula L}     : p ⋏ q ∈ Δ → Derivation3 T (insert p Δ) → Derivation3 T (insert q Δ) → Derivation3 T Δ
| or    {Δ} {p q : SyntacticFormula L}     : p ⋎ q ∈ Δ → Derivation3 T (insert p (insert q Δ)) → Derivation3 T Δ
| all   {Δ} {p : SyntacticSemiformula L 1} : ∀' p ∈ Δ → Derivation3 T (insert (Rew.free.hom p) (Δ.image Rew.shift.hom)) → Derivation3 T Δ
| ex    {Δ} {p : SyntacticSemiformula L 1} : ∃' p ∈ Δ → (t : SyntacticTerm L) → Derivation3 T (insert (p/[t]) Δ) → Derivation3 T Δ
| wk    {Δ Γ} : Derivation3 T Δ → Δ ⊆ Γ → Derivation3 T Γ
| shift {Δ}   : Derivation3 T Δ → Derivation3 T (Δ.image Rew.shift.hom)
| cut   {Δ p} : Derivation3 T (insert p Δ) → Derivation3 T (insert (~p) Δ) → Derivation3 T Δ

scoped infix:45 " ⊢₃ " => Derivation3

abbrev Derivable3 (T : SyntacticTheory L) (Γ : Finset (SyntacticFormula L)) := Nonempty (T ⊢₃ Γ)

scoped infix:45 " ⊢₃! " => Derivable3

abbrev Derivable3SingleConseq (T : SyntacticTheory L) (p : SyntacticFormula L) : Prop := T ⊢₃! {p}

scoped infix: 45 " ⊢₃.! " => Derivable3SingleConseq

variable {T : SyntacticTheory L}

lemma shifts_toFinset_eq_image_shift (Δ : Sequent L) :
    (shifts Δ).toFinset = Δ.toFinset.image Rew.shift.hom := by ext p; simp [shifts]

def Derivation2.toDerivation3 T : {Γ : Sequent L} → T ⊢₂ Γ → T ⊢₃ Γ.toFinset
  | _, Derivation2.closed Δ p           => Derivation3.closed _ p (by simp) (by simp)
  | _, Derivation2.root Γ p h           => Derivation3.root p h (by simp)
  | _, Derivation2.verum Δ              => Derivation3.verum (by simp)
  | _, @Derivation2.and _ _ Δ p q dp dq =>
    Derivation3.and (p := p) (q := q) (by simp)
      (Derivation3.wk (Derivation2.toDerivation3 T dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
      (Derivation3.wk (Derivation2.toDerivation3 T dq) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation2.or _ _ Δ p q dpq    =>
    Derivation3.or (p := p) (q := q) (by simp)
      (Derivation3.wk (Derivation2.toDerivation3 T dpq)
      (by simpa using Finset.insert_subset_insert _ <| Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation2.all _ _ Δ p dp      =>
    Derivation3.all (p := p) (by simp)
      (Derivation3.wk (Derivation2.toDerivation3 T dp)
        (by simpa using Finset.insert_subset_insert _ (by simp [shifts_toFinset_eq_image_shift])))
  | _, @Derivation2.ex _ _ Δ p t dp     =>
    Derivation3.ex (p := p) (by simp) t
      (Derivation3.wk (Derivation2.toDerivation3 T dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, Derivation2.wk d h               =>
    Derivation3.wk (Derivation2.toDerivation3 T d) (List.toFinset_mono h)
  | _, @Derivation2.cut _ _ Δ p d₁ d₂   =>
    Derivation3.cut (p := p)
      (Derivation3.wk (Derivation2.toDerivation3 T d₁) (by simp))
      (Derivation3.wk (Derivation2.toDerivation3 T d₂) (by simp))

noncomputable def Derivation3.toDerivation2 : {Γ : Finset (SyntacticFormula L)} → T ⊢₃ Γ → T ⊢₂ Γ.toList
  | _, Derivation3.closed Δ p hp hn              => Derivation2.closed' _ p (by simp [hp]) (by simp [hn])
  | _, Derivation3.root Γ hp h                   => Derivation2.root' _ hp (by simp [h])
  | _, Derivation3.verum h                       => Derivation2.verum' (by simp [h])
  | _, Derivation3.and (p := p) (q := q) h dp dq =>
    Derivation2.and' (p := p) (q := q) (by simp [h])
      (Derivation2.wk dp.toDerivation2 <| by intro x; simp)
      (Derivation2.wk dq.toDerivation2 <| by intro x; simp)
  | _, Derivation3.or (p := p) (q := q) h dpq    =>
    Derivation2.or' (p := p) (q := q) (by simp [h]) (Derivation2.wk dpq.toDerivation2 <| by intro x; simp)
  | _, Derivation3.all (p := p) h d              =>
    Derivation2.all' (p := p) (by simp [h]) (Derivation2.wk d.toDerivation2 <| by intro x; simp [shifts])
  | _, Derivation3.ex (p := p) h t d             =>
    Derivation2.ex' (p := p) (by simp [h]) t (Derivation2.wk d.toDerivation2 <| by intro x; simp [shifts])
  | _, Derivation3.wk d h                        =>
    Derivation2.wk d.toDerivation2 (by intro x; simp; exact @h x)
  | _, Derivation3.shift d                       =>
    Derivation2.wk (Derivation2.shift d.toDerivation2) <| by intro x; simp [shifts]
  | _, Derivation3.cut (p := p) d dn             =>
    Derivation2.cut (p := p)
      (Derivation2.wk d.toDerivation2 <| by intro x; simp)
      (Derivation2.wk dn.toDerivation2 <| by intro x; simp)

lemma derivable2_iff_derivable3 {Γ : List (SyntacticFormula L)} : T ⊢₂! Γ ↔ T ⊢₃! Γ.toFinset := by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using Derivation2.toDerivation3 T d⟩
  · rintro ⟨d⟩; exact ⟨.wk d.toDerivation2 (by intro x; simp)⟩

def provable_iff_derivable3 {σ} : T.close ⊢! σ ↔ T ⊢₃.! Rew.embs.hom σ := by
  simp [provable_iff_derivable2, derivable2_iff_derivable3]

end LO.FirstOrder
