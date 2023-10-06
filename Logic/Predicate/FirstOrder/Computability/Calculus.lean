import Logic.Predicate.FirstOrder.Computability.Term
import Logic.Predicate.FirstOrder.Computability.Formula
import Logic.Predicate.FirstOrder.Hauptsatz

namespace LO

namespace FirstOrder

open Encodable
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
variable [(k : ℕ) → Primcodable (L.func k)] [(k : ℕ) → Primcodable (L.rel k)]
  [UniformlyPrimcodable L.func] [UniformlyPrimcodable L.rel] [Primcodable μ]

namespace Derivation

open DerivationCR

inductive Code (L : Language.{u})
  | axL : {k : ℕ} → (r : L.rel k) → (v : Fin k → SyntacticTerm L) → Code L
  | verum : Code L
  | and : SyntacticFormula L → SyntacticFormula L → Code L
  | or : SyntacticFormula L → SyntacticFormula L → Code L
  | all : SyntacticSubFormula L 1 → Code L
  | ex : SyntacticSubFormula L 1 → SyntacticTerm L → Code L
  | wk : List (SyntacticFormula L) → Code L

def Code.equiv (L : Language.{u}) :
    Code L ≃
    ((k : ℕ) × (L.rel k) × (Fin k → SyntacticTerm L)) ⊕
    Unit ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticSubFormula L 1) ⊕
    (SyntacticSubFormula L 1 × SyntacticTerm L) ⊕
    List (SyntacticFormula L) where
  toFun := fun c =>
    match c with
    | (Code.axL r v) => Sum.inl ⟨_, r, v⟩
    | Code.verum     => Sum.inr $ Sum.inl ()
    | (Code.and p q) => Sum.inr $ Sum.inr $ Sum.inl (p, q)
    | (Code.or p q)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, q)
    | (Code.all p)   => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl p
    | (Code.ex p t)  => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, t)
    | (Code.wk Δ)    => Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr Δ
  invFun := fun x =>
    match x with
    | (Sum.inl ⟨_, r, v⟩)                                                => Code.axL r v
    | (Sum.inr $ Sum.inl ())                                             => Code.verum
    | (Sum.inr $ Sum.inr $ Sum.inl (p, q))                               => Code.and p q
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, q))                     => Code.or p q
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl p)                => Code.all p
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inl (p, t)) => Code.ex p t
    | (Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr $ Sum.inr Δ)      => Code.wk Δ
  left_inv := fun c => by cases c <;> simp
  right_inv := fun x => by
    rcases x with (⟨_, _, _⟩ | ⟨⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ | ⟨_, _⟩ | _) <;> simp

instance : Primcodable (Code L) := Primcodable.ofEquiv _ (Code.equiv L)

abbrev ProofList (L : Language.{u}) := List (Code L × List (SyntacticFormula L))

namespace ProofList

def sequents : ProofList L → List (List (SyntacticFormula L)) := List.map Prod.snd

def isProper : ProofList L → Bool
  | []                     => true
  | (Code.axL r v, Γ) :: l => isProper l && SubFormula.rel r v ∈ Γ && SubFormula.nrel r v ∈ Γ
  | (Code.verum,   Γ) :: l => isProper l && ⊤ ∈ Γ
  | (Code.and p q, Γ) :: l => isProper l && p ⋏ q ∈ Γ && p :: Γ ∈ sequents l && q :: Γ ∈ sequents l
  | (Code.or p q,  Γ) :: l => isProper l && p ⋎ q ∈ Γ && p :: q :: Γ ∈ sequents l
  | (Code.all p,   Γ) :: l => isProper l && ∀' p ∈ Γ && Rew.freel p :: Γ.map Rew.shiftl ∈ sequents l
  | (Code.ex p t,  Γ) :: l => isProper l && ∃' p ∈ Γ && Rew.substsl ![t] p :: Γ ∈ sequents l
  | (Code.wk Δ,    Γ) :: l => isProper l && Δ ⊆ Γ && Δ ∈ sequents l

private def F (Γ : List (SyntacticFormula L)) (seq : List (List (SyntacticFormula L))) : Code L → Bool := fun c =>
  Sum.recOn (Code.equiv L c)
    (fun f => SubFormula.rel f.2.1 f.2.2 ∈ Γ && SubFormula.nrel f.2.1 f.2.2 ∈ Γ)
  <| fun c => c.casesOn (fun _ => ⊤ ∈ Γ)
  <| fun c => c.casesOn (fun p => p.1 ⋏ p.2 ∈ Γ && p.1 :: Γ ∈ seq && p.2 :: Γ ∈ seq)
  <| fun c => c.casesOn (fun p => p.1 ⋎ p.2 ∈ Γ && p.1 :: p.2 :: Γ ∈ seq)
  <| fun c => c.casesOn (fun p => ∀' p ∈ Γ && Rew.freel p :: Γ.map Rew.shiftl ∈ seq)
  <| fun c => c.casesOn (fun p => ∃' p.1 ∈ Γ && Rew.substsl ![p.2] p.1 :: Γ ∈ seq)
  <| fun Δ => Δ ⊆ Γ && Δ ∈ seq

section

open Primrec

instance : Primcodable
  ((((List (SyntacticFormula L) × List (List (SyntacticFormula L))) × Code L) ×
      (Unit ⊕
        SyntacticFormula L × SyntacticFormula L ⊕
          SyntacticFormula L × SyntacticFormula L ⊕
            SyntacticSubFormula L 1 ⊕ SyntacticSubFormula L 1 × SyntacticTerm L ⊕ List (SyntacticFormula L))) ×
    (SyntacticFormula L × SyntacticFormula L ⊕
      SyntacticFormula L × SyntacticFormula L ⊕
        SyntacticSubFormula L 1 ⊕ SyntacticSubFormula L 1 × SyntacticTerm L ⊕ List (SyntacticFormula L))) := Primcodable.prod

private lemma F_primrec : Primrec₂ (fun (p : List (SyntacticFormula L) × List (List (SyntacticFormula L))) => F p.1 p.2) :=
  to₂' <| sum_casesOn (of_equiv.comp snd)
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂ (SubFormula.rel_primrec.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂ (SubFormula.nrel_primrec.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    (by apply list_mem.comp₂ (Primrec₂.const ⊤) (fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      ((dom_bool₂ _).comp₂
        (by apply list_mem.comp₂
              (SubFormula.and_primrec.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
              (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
        (by apply list_mem.comp₂
              (list_cons.comp₂ (fst.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
              (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
      (by apply list_mem.comp₂
            (list_cons.comp₂ (snd.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
            (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂
            (SubFormula.or_primrec.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
            (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂
            (by apply list_cons.comp₂ (fst.comp₂ Primrec₂.right) $ list_cons.comp₂
                  (snd.comp₂ Primrec₂.right)
                  (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
            (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂
            (SubFormula.all_primrec.comp₂ Primrec₂.right)
            (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂
            (list_cons.comp₂
              (SubFormula.free_primrec.comp₂ Primrec₂.right)
              (to₂' <| by apply list_map
                            (fst.comp $ fst.comp $ fst.comp $ fst.comp $ fst.comp $ fst.comp $ fst)
                            (SubFormula.shift_primrec.comp₂ Primrec₂.right)))
            (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂
            (SubFormula.ex_primrec.comp₂ $ fst.comp₂ Primrec₂.right)
            (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂
            (by apply list_cons.comp₂
                  (by apply SubFormula.substs₁_primrec.comp₂ (snd.comp₂ Primrec₂.right) (fst.comp₂ Primrec₂.right))
                  (by apply fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
            (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| (dom_bool₂ _).comp₂
    (by apply list_subset.comp₂
          Primrec₂.right
          (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
    (by apply list_mem.comp₂
          Primrec₂.right
          (by apply snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))

lemma isProper_primrec : Primrec (isProper : ProofList L → Bool) := by
  have : Primrec₂ (fun _ p => p.2.2 && F p.1.2 (sequents p.2.1) p.1.1
    : ProofList L → (Code L × List (SyntacticFormula L)) × (List (Code L × List (SyntacticFormula L))) × Bool → Bool) :=
    (dom_bool₂ _).comp₂ (snd.comp₂ $ snd.comp₂ Primrec₂.right)
    (F_primrec.comp₂
        ((Primrec₂.pair.comp (snd.comp fst) (list_map (fst.comp snd) (snd.comp₂ Primrec₂.right))).comp₂ Primrec₂.right)
        (fst.comp₂ $ fst.comp₂ Primrec₂.right))
  have : Primrec (fun l => l.rec true (fun c l' ih => ih && F c.2 (sequents l') c.1) : ProofList L → Bool) :=
    list_rec Primrec.id (const true) this
  exact this.of_eq <| by
    intro l; induction' l with c l ih <;> simp[isProper]
    rw[ih]; rcases c with ⟨⟨⟩, Γ⟩ <;> simp[isProper, F, Code.equiv, Bool.and_assoc]

end

@[simp] lemma sequents_append {l₁ l₂ : ProofList L} : sequents (l₁ ++ l₂) = sequents l₁ ++ sequents l₂ := by simp[sequents]

lemma isProper_append {l₁ l₂ : ProofList L} (h₁ : isProper l₁) (h₂ : isProper l₂) : isProper (l₁ ++ l₂) := by
  induction' l₁ with c l₁ ih
  · simpa
  · simp
    rcases c with ⟨⟨⟩, Γ⟩ <;> simp[isProper] at h₁ ⊢
    case axL k r v => { exact ⟨⟨ih h₁.1.1, h₁.1.2⟩, h₁.2⟩ }
    case verum => { exact ⟨ih h₁.1, h₁.2⟩ }
    case and p q => { exact ⟨⟨⟨ih h₁.1.1.1, h₁.1.1.2⟩, Or.inl h₁.1.2⟩, Or.inl h₁.2⟩ }
    case or p q => { exact ⟨⟨ih h₁.1.1, h₁.1.2⟩, Or.inl h₁.2⟩ }
    case all => { exact ⟨⟨ih h₁.1.1, h₁.1.2⟩, Or.inl h₁.2⟩ }
    case ex => { exact ⟨⟨ih h₁.1.1, h₁.1.2⟩, Or.inl h₁.2⟩ }
    case wk => { exact ⟨⟨ih h₁.1.1, h₁.1.2⟩, Or.inl h₁.2⟩ }

lemma derivation_of_isProper : (l : ProofList L) → isProper l → ∀ Γ ∈ sequents l, Nonempty (⊢ᵀ Γ.toFinset)
  | [],                     _, Δ, hΔ => by simp[sequents] at hΔ
  | (Code.axL r v, Γ) :: l, H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨ih, h₁⟩, h₂⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · exact ⟨axL _ r v (by simpa using h₁) (by simpa using h₂)⟩
    · exact derivation_of_isProper l ih Δ (by simpa[sequents] using hΔ)
  | (Code.verum,   Γ) :: l, H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨ih, h⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · exact ⟨verum _ (by simp[h])⟩
    · exact derivation_of_isProper l ih _ (by simpa[sequents] using hΔ)
  | (Code.and p q, Γ) :: l, H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨⟨hl, H⟩, hp⟩, hq⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · have : Nonempty (⊢ᵀ List.toFinset (p :: Δ)) := derivation_of_isProper l hl _ hp
      rcases this with ⟨bp⟩
      have : Nonempty (⊢ᵀ List.toFinset (q :: Δ)) := derivation_of_isProper l hl _ hq
      rcases this with ⟨bq⟩
      have : ⊢ᵀ insert (p ⋏ q) Δ.toFinset := and Δ.toFinset p q (by simpa using bp) (by simpa using bq)
      exact ⟨this.cast (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.or p q, Γ) :: l,  H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, hpq⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl _ hpq with ⟨b⟩
      have : ⊢ᵀ insert (p ⋎ q) Δ.toFinset := DerivationCR.or Δ.toFinset p q (by simpa using b)
      exact ⟨this.cast (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.all p, Γ) :: l,   H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, hp⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl _ hp with ⟨b⟩
      have : ⊢ᵀ insert (∀' p) Δ.toFinset :=
        DerivationCR.all Δ.toFinset p (by simpa[shifts, List.toFinset_map, Finset.map_eq_image] using b)
      exact ⟨this.cast (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.ex p t, Γ) :: l,    H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, hp⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl _ hp with ⟨b⟩
      have : ⊢ᵀ insert (∃' p) Δ.toFinset := DerivationCR.ex Δ.toFinset t p (by simpa using b)
      exact ⟨this.cast (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.wk E,   Γ) :: l,    H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, h⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl E h with ⟨b⟩
      exact ⟨b.weakening (by intro x; simp; intro hx; exact H hx)⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)

noncomputable def ofDerivation : {Γ : Sequent L} → ⊢ᵀ Γ → ProofList L
  | _, DerivationCR.axL Γ r v _ _   => [(Code.axL r v, Γ.toList)]
  | _, DerivationCR.verum Γ _       => [(Code.verum, Γ.toList)]
  | _, DerivationCR.and Γ p q bp bq =>
    (Code.and p q, (insert (p ⋏ q) Γ).toList) ::
    (Code.wk (insert p Γ).toList, p :: (insert (p ⋏ q) Γ).toList) ::
    (Code.wk (insert q Γ).toList, q :: (insert (p ⋏ q) Γ).toList) :: (ofDerivation bp ++ ofDerivation bq)
  | _, DerivationCR.or Γ p q bpq    =>
    (Code.or p q, (insert (p ⋎ q) Γ).toList) ::
    (Code.wk (insert p $ insert q Γ).toList, p :: q :: (insert (p ⋎ q) Γ).toList) :: ofDerivation bpq
  | _, DerivationCR.all Γ p b       =>
    (Code.all p, (insert (∀' p) Γ).toList) ::
    (Code.wk (insert (Rew.freel p) $ shifts Γ).toList, Rew.freel p :: (insert (∀' p) Γ).toList.map Rew.shiftl) :: ofDerivation b
  | _, DerivationCR.ex Γ t p b      =>
    (Code.ex p t, (insert (∃' p) Γ).toList) ::
    (Code.wk (insert (Rew.substsl ![t] p) Γ).toList, Rew.substsl ![t] p :: (insert (∃' p) Γ).toList) :: ofDerivation b

lemma mem_ofDerivation {Γ : Sequent L} (b : ⊢ᵀ Γ) : Γ.toList ∈ sequents (ofDerivation b) := by
  cases b <;> simp[ofDerivation, sequents]
  { contradiction }

lemma iff_mem_sequents {l : ProofList L} : (∃ c, (c, Γ) ∈ l) ↔ Γ ∈ sequents l := by simp[sequents]

@[simp] lemma sequents_cons {l : ProofList L} : sequents ((c, Γ) :: l) = Γ :: sequents l := by simp[sequents]

lemma List.mem_cons_cons (l : List α) (a b : α) : l ⊆ a :: b :: l := by
  intro x hx; simp; exact Or.inr (Or.inr $ hx)

lemma Finset.mem_cons_cons [DecidableEq α] (s : Finset α) (a b : α) : s ⊆ insert a (insert b s) := by
  intro x hx; simp; exact Or.inr (Or.inr $ hx)

lemma Finset.toList_subset_toList {s₁ s₂ : Finset α} : s₁.toList ⊆ s₂.toList ↔ s₁ ⊆ s₂ := by
  simp[List.subset_def]; rfl

lemma isProper_ofDerivation : ∀ {Γ : Sequent L} (b : ⊢ᵀ Γ), isProper (ofDerivation b)
  | _, DerivationCR.axL Γ r v h₁ h₂ => by simp[ofDerivation, isProper, h₁, h₂]
  | _, DerivationCR.verum Γ h       => by simp[ofDerivation, isProper, h]
  | _, DerivationCR.and Γ p q bp bq => by
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact ⟨⟨isProper_append (isProper_ofDerivation bp) (isProper_ofDerivation bq), by simp[List.subset_def]; intro x hx; exact Or.inr (Or.inr hx)⟩,
      by simp[List.subset_def]; intro x hx; exact Or.inr (Or.inr hx)⟩
  | _, DerivationCR.or Γ p q bpq    => by
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact ⟨isProper_ofDerivation bpq, by simp[List.subset_def]; intro x hx; simp[hx]⟩
  | _, DerivationCR.all Γ p b       => by
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact ⟨isProper_ofDerivation b, by simp[List.subset_def, shifts_eq_image]; intro x hx; exact (Or.inr $ Or.inr $ ⟨x, hx, rfl⟩)⟩
  | _, DerivationCR.ex Γ t p b      => by
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact ⟨isProper_ofDerivation b, by simp[List.subset_def]; intro x hx; simp[hx]⟩
  
lemma derivable_iff_isProper {Γ : Sequent L} : Nonempty (⊢ᵀ Γ) ↔ ∃ l, isProper l ∧ Γ.toList ∈ sequents l :=
  ⟨by rintro ⟨b⟩; exact ⟨ofDerivation b, isProper_ofDerivation b, mem_ofDerivation b⟩,
   by rintro ⟨l, hl⟩; rcases derivation_of_isProper l hl.1 _ hl.2 with ⟨d⟩; exact ⟨d.cast (by simp)⟩⟩

lemma provable_iff {T : Theory L} [DecidablePred T] {σ : Sentence L} :
    Nonempty (T ⊢ σ) ↔ ∃ l, ∃ U : List (Sentence L), (U.map (~·)).all (T ·) ∧ (σ :: U).map Rew.embl ∈ sequents l ∧ isProper l := by
  exact ⟨by
    rintro ⟨U, hU, d⟩
    rcases derivable_iff_isProper.mp (iff_cut.mpr ⟨d⟩) with ⟨l, hl, hmem⟩
    let l' := (Code.wk ((insert σ U).image Rew.embl).toList, ((σ :: U.toList).map Rew.embl)) :: l
    have hl' : isProper l' := by simp[isProper, hl]; exact ⟨by simp[List.subset_def], by simp[Finset.insert_eq, hmem]⟩
    exact ⟨l', U.toList, by
      simp[List.subsetSet]; intro x hx
      have : ∃ y ∈ T, ~y = x := by simpa using hU hx
      rcases this with ⟨y, hy, rfl⟩; simpa[hy], by simp, hl'⟩,
  by rintro ⟨l, U, hU, hl, hproper⟩
     rcases derivation_of_isProper l hproper _ hl with ⟨d⟩
     exact ⟨{ 
       leftHand := U.toFinset
       hleftHand := by intro x; simp; intro hx; exact ⟨~x, by { simp at hU; exact ⟨hU x hx, by simp⟩ }⟩
       derivation := cutWeakeningCut (d.cast (by simp[List.toFinset_map, Finset.insert_eq])) }⟩⟩

end ProofList

end Derivation

open Derivation ProofList

def provFn (T : Theory L) [DecidablePred T] : ℕ → ℕ → ℕ := fun x e =>
  (decode x : Option (Sentence L)).casesOn 0
  <| fun σ => (decode e : Option (ProofList L × List (Sentence L))).casesOn 0
  <| fun A => bif (A.2.map (~·)).all (T ·) && (σ :: A.2).map Rew.embl ∈ sequents A.1 && isProper A.1 then 1 else 0

lemma provable_iff_provFn {T : Theory L} [DecidablePred T] {σ : Sentence L} :
    Nonempty (T ⊢ σ) ↔ ∃ e, provFn T (encode σ) e = 1 := by
  simp[provable_iff, provFn]
  constructor
  · rintro ⟨l, U, hU, hl, hproper⟩
    use encode (l, U)
    have : (U.map (~·)).all (T ·) := by simp; intro x hx; exact hU x hx
    simp[hU, hl, hproper, this]
  · simp; intro e
    rcases decode e.unpair.1 with (_ | ⟨l⟩) <;> simp
    rcases decode e.unpair.2 with (_ | ⟨U⟩) <;> simp
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, ite_eq_iff]; simp
    intro h₁ h₂ h₃
    exact ⟨l, U, h₁, h₂, h₃⟩

section

open Computable

lemma provFn_primrec {T : Theory L} [DecidablePred T] (hT : Computable (fun x => decide (T x))) :
    Computable₂ (provFn T) :=
  to₂' <| option_casesOn (Computable.decode.comp fst) (const 0)
  <| option_casesOn (Computable.decode.comp $ snd.comp fst) (const 0)
  <| to₂' <| Computable.cond
    (dom_bool₂.comp
      (dom_bool₂.comp
        (list_all (hT.comp Computable₂.right)
          (Primrec.to_comp $ Primrec.list_map (Primrec.snd.comp .snd) (SubFormula.neg_primrec.comp₂ .right)))
        (Primrec.to_comp $ by
          apply Primrec.list_mem.comp
                  (Primrec.list_map (Primrec.list_cons.comp (Primrec.snd.comp .fst) (Primrec.snd.comp .snd))
                    (SubFormula.emb_primrec.comp₂ .right))
                  (Primrec.list_map (Primrec.fst.comp .snd) (Primrec.snd.comp₂ .right))))
      (Primrec.to_comp $ isProper_primrec.comp $ Primrec.fst.comp .snd))
    (const 1) (const 0)

end

end FirstOrder

end LO
