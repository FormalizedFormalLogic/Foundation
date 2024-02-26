import Logic.FirstOrder.Computability.Term
import Logic.FirstOrder.Computability.Formula
import Logic.FirstOrder.Hauptsatz

namespace LO

namespace FirstOrder

open Encodable
variable {L : Language.{u}} [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]
variable [(k : ℕ) → Primcodable (L.Func k)] [(k : ℕ) → Primcodable (L.Rel k)]
  [UniformlyPrimcodable L.Func] [UniformlyPrimcodable L.Rel] [Primcodable μ]

namespace Derivation

inductive Code (L : Language.{u})
  | axL : {k : ℕ} → (r : L.Rel k) → (v : Fin k → SyntacticTerm L) → Code L
  | verum : Code L
  | and : SyntacticFormula L → SyntacticFormula L → Code L
  | or : SyntacticFormula L → SyntacticFormula L → Code L
  | all : SyntacticSemiformula L 1 → Code L
  | ex : SyntacticSemiformula L 1 → SyntacticTerm L → Code L
  | wk : List (SyntacticFormula L) → Code L

def Code.equiv (L : Language.{u}) :
    Code L ≃
    ((k : ℕ) × (L.Rel k) × (Fin k → SyntacticTerm L)) ⊕
    Unit ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticFormula L × SyntacticFormula L) ⊕
    (SyntacticSemiformula L 1) ⊕
    (SyntacticSemiformula L 1 × SyntacticTerm L) ⊕
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
  | (Code.axL r v, Γ) :: l => isProper l && Semiformula.rel r v ∈ Γ && Semiformula.nrel r v ∈ Γ
  | (Code.verum,   Γ) :: l => isProper l && ⊤ ∈ Γ
  | (Code.and p q, Γ) :: l => isProper l && p ⋏ q ∈ Γ && p :: Γ ∈ sequents l && q :: Γ ∈ sequents l
  | (Code.or p q,  Γ) :: l => isProper l && p ⋎ q ∈ Γ && p :: q :: Γ ∈ sequents l
  | (Code.all p,   Γ) :: l => isProper l && ∀' p ∈ Γ && Rew.free.hom p :: Γ.map Rew.shift.hom ∈ sequents l
  | (Code.ex p t,  Γ) :: l => isProper l && ∃' p ∈ Γ && p/[t] :: Γ ∈ sequents l
  | (Code.wk Δ,    Γ) :: l => isProper l && Δ ⊆ Γ && Δ ∈ sequents l

private def F (Γ : List (SyntacticFormula L)) (seq : List (List (SyntacticFormula L))) : Code L → Bool := fun c =>
  Sum.recOn (Code.equiv L c)
    (fun f => Semiformula.rel f.2.1 f.2.2 ∈ Γ && Semiformula.nrel f.2.1 f.2.2 ∈ Γ)
  <| fun c => c.casesOn (fun _ => ⊤ ∈ Γ)
  <| fun c => c.casesOn (fun p => p.1 ⋏ p.2 ∈ Γ && p.1 :: Γ ∈ seq && p.2 :: Γ ∈ seq)
  <| fun c => c.casesOn (fun p => p.1 ⋎ p.2 ∈ Γ && p.1 :: p.2 :: Γ ∈ seq)
  <| fun c => c.casesOn (fun p => ∀' p ∈ Γ && Rew.free.hom p :: Γ.map Rew.shift.hom ∈ seq)
  <| fun c => c.casesOn (fun p => ∃' p.1 ∈ Γ && (Rew.substs ![p.2]).hom p.1 :: Γ ∈ seq)
  <| fun Δ => Δ ⊆ Γ && Δ ∈ seq

section

open Primrec

instance : Primcodable
  ((((List (SyntacticFormula L) × List (List (SyntacticFormula L))) × Code L) ×
      (Unit ⊕
        SyntacticFormula L × SyntacticFormula L ⊕
          SyntacticFormula L × SyntacticFormula L ⊕
            SyntacticSemiformula L 1 ⊕ SyntacticSemiformula L 1 × SyntacticTerm L ⊕ List (SyntacticFormula L))) ×
    (SyntacticFormula L × SyntacticFormula L ⊕
      SyntacticFormula L × SyntacticFormula L ⊕
        SyntacticSemiformula L 1 ⊕ SyntacticSemiformula L 1 × SyntacticTerm L ⊕ List (SyntacticFormula L))) := Primcodable.prod

private lemma F_primrec : Primrec₂ (fun (p : List (SyntacticFormula L) × List (List (SyntacticFormula L))) => F p.1 p.2) :=
  to₂' <| sum_casesOn (of_equiv.comp snd)
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂ (Semiformula.rel_primrec.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂ (Semiformula.nrel_primrec.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    (by apply list_mem.comp₂ (Primrec₂.const ⊤) (fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      ((dom_bool₂ _).comp₂
        (by apply list_mem.comp₂
              (Semiformula.and_primrec.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
              (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
        (by apply (list_mem (α := List (SyntacticFormula L))).comp₂
              (list_cons.comp₂ (fst.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
              (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
      (by apply list_mem.comp₂
            (list_cons.comp₂ (snd.comp₂ Primrec₂.right) (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
            (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂
            (Semiformula.or_primrec.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
            (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂
            (by apply list_cons.comp₂ (fst.comp₂ Primrec₂.right) $ list_cons.comp₂
                  (snd.comp₂ Primrec₂.right)
                  (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
            (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂
            (Semiformula.all_primrec.comp₂ Primrec₂.right)
            (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂
            (list_cons.comp₂
              (Semiformula.free_primrec.comp₂ Primrec₂.right)
              (to₂' <| by apply list_map
                            (fst.comp $ fst.comp $ fst.comp $ fst.comp $ fst.comp $ fst.comp $ fst)
                            (Semiformula.shift_primrec.comp₂ Primrec₂.right)))
            (snd.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left)))
  <| to₂' <| sum_casesOn snd
    ((dom_bool₂ _).comp₂
      (by apply list_mem.comp₂
            (Semiformula.ex_primrec.comp₂ $ fst.comp₂ Primrec₂.right)
            (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left))
      (by apply list_mem.comp₂
            (by apply list_cons.comp₂
                  (by apply Semiformula.substs₁_primrec.comp₂ (snd.comp₂ Primrec₂.right) (fst.comp₂ Primrec₂.right))
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

open Derivation

lemma derivation_of_isProper : (l : ProofList L) → isProper l → ∀ Γ ∈ sequents l, Nonempty (⊢¹ Γ)
  | [],                     _, Δ, hΔ => by simp[sequents] at hΔ
  | (Code.axL r v, Γ) :: l, H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨ih, h₁⟩, h₂⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · exact ⟨axL' r v (by simpa using h₁) (by simpa using h₂)⟩
    · exact derivation_of_isProper l ih Δ (by simpa[sequents] using hΔ)
  | (Code.verum,   Γ) :: l, H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨ih, h⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · exact ⟨verum' (by simp[h])⟩
    · exact derivation_of_isProper l ih _ (by simpa[sequents] using hΔ)
  | (Code.and p q, Γ) :: l, H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨⟨hl, H⟩, hp⟩, hq⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · have : Nonempty (⊢¹ p :: Δ) := derivation_of_isProper l hl _ hp
      rcases this with ⟨bp⟩
      have : Nonempty (⊢¹ q :: Δ) := derivation_of_isProper l hl _ hq
      rcases this with ⟨bq⟩
      have : ⊢¹ p ⋏ q :: Δ := and (by simpa using bp) (by simpa using bq)
      exact ⟨this.weakening (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.or p q, Γ) :: l,  H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, hpq⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl _ hpq with ⟨b⟩
      have : ⊢¹ p ⋎ q :: Δ := Derivation.or (by simpa using b)
      exact ⟨this.weakening (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.all p, Γ) :: l,   H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, hp⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl _ hp with ⟨b⟩
      have : ⊢¹ (∀' p) :: Δ :=
        Derivation.all (by simpa[shifts, List.toFinset_map, Finset.map_eq_image] using b)
      exact ⟨this.weakening (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.ex p t, Γ) :: l,    H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, hp⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl _ hp with ⟨b⟩
      have : ⊢¹ (∃' p) :: Δ := Derivation.ex t (by simpa using b)
      exact ⟨this.weakening (by simp[H])⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)
  | (Code.wk E,   Γ) :: l,    H, Δ, hΔ => by
    simp[isProper] at H; rcases H with ⟨⟨hl, H⟩, h⟩
    simp[sequents] at hΔ; rcases hΔ with (rfl | hΔ)
    · rcases derivation_of_isProper l hl E h with ⟨b⟩
      exact ⟨b.weakening H⟩
    · exact derivation_of_isProper l hl _ (by simpa[sequents] using hΔ)

noncomputable def ofDerivation : {Γ : Sequent L} → { d : ⊢¹ Γ // CutFree d } → ProofList L
  | _, ⟨axL Γ r v, _⟩          => [(Code.axL r v, .rel r v :: .nrel r v :: Γ)]
  | _, ⟨verum Γ, _⟩            => [(Code.verum, ⊤ :: Γ)]
  | _, ⟨@and _ Γ p q bp bq, H⟩ =>
    have H : CutFree bp ∧ CutFree bq := by simpa [CutFree] using H
    (Code.and p q, p ⋏ q :: Γ) ::
    (Code.wk (p :: Γ), p :: p ⋏ q :: Γ) ::
    (Code.wk (q :: Γ), q :: p ⋏ q :: Γ) :: (ofDerivation ⟨bp, H.1⟩ ++ ofDerivation ⟨bq, H.2⟩)
  | _, ⟨@or _ Γ p q bpq, H⟩    =>
    (Code.or p q, p ⋎ q :: Γ) :: (Code.wk (p :: q :: Γ), p :: q :: (p ⋎ q :: Γ)) :: ofDerivation ⟨bpq, by simpa[CutFree] using H⟩
  | _, ⟨@all _ Γ p b, H⟩       =>
    (Code.all p, (∀' p) :: Γ) ::
    (Code.wk (Rew.free.hom p :: shifts Γ), Rew.free.hom p :: ((∀' p) :: Γ).map Rew.shift.hom) :: ofDerivation ⟨b, by simpa[CutFree] using H⟩
  | _, ⟨@ex _ Γ p t b, H⟩      =>
    (Code.ex p t, (∃' p) :: Γ) :: (Code.wk (p/[t] :: Γ), p/[t] :: (∃' p) :: Γ) :: ofDerivation ⟨b, by simpa[CutFree] using H⟩
  | _, ⟨@wk _ Γ Γ' b _, H⟩     =>
    (Code.wk Γ, Γ') :: ofDerivation ⟨b, by simpa[CutFree] using H⟩
  termination_by ofDerivation d => length d.val

lemma mem_ofDerivation {Γ : Sequent L} (b : { d : ⊢¹ Γ // CutFree d }) : Γ ∈ sequents (ofDerivation b) := by
  rcases b with ⟨b, hb⟩
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

lemma isProper_ofDerivation : ∀ {Γ : Sequent L} (b : { d : ⊢¹ Γ // CutFree d }), isProper (ofDerivation b)
  | _, ⟨@axL _ Γ _ r v, _⟩     => by simp[ofDerivation, isProper]
  | _, ⟨@verum _ Γ, _⟩         => by simp[ofDerivation, isProper]
  | _, ⟨@and _ Γ p q bp bq, H⟩ => by
    have H : CutFree bp ∧ CutFree bq := by simpa [CutFree] using H
    simp[ofDerivation]
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact isProper_append (isProper_ofDerivation ⟨bp, H.1⟩) (isProper_ofDerivation ⟨bq, H.2⟩)
  | _, ⟨@or _ Γ p q b, H⟩      => by
    simp[ofDerivation]
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact ⟨isProper_ofDerivation ⟨b, by simpa[CutFree] using H⟩, by simp[List.subset_def]; intro x hx; simp[hx]⟩
  | _, ⟨@all _ Γ p b, H⟩       => by
    simp[ofDerivation]
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact ⟨isProper_ofDerivation ⟨b, by simpa[CutFree] using H⟩, List.subset_cons_of_subset _ $ List.subset_cons_of_subset _ $ by simp[shifts]⟩
  | _, ⟨@ex _ Γ p t b, H⟩      => by
    simp[ofDerivation]
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation]
    exact isProper_ofDerivation ⟨b, by simpa[CutFree] using H⟩
  | _, ⟨@wk _ Γ Γ' b ss, H⟩    => by
    simp[ofDerivation]
    simp[isProper, sequents_cons, List.mem_cons_cons, mem_ofDerivation, ss]
    exact isProper_ofDerivation ⟨b, by simpa[CutFree] using H⟩
  termination_by isProper_ofDerivation d => length d.val

lemma derivable_iff_isProper {Γ : Sequent L} : Nonempty (⊢¹ Γ) ↔ ∃ l, isProper l ∧ Γ ∈ sequents l :=
  ⟨by rintro h
      rcases iff_cut.mpr h with ⟨b⟩
      exact ⟨ofDerivation b, isProper_ofDerivation b, mem_ofDerivation b⟩,
   by rintro ⟨l, hl⟩
      rcases derivation_of_isProper l hl.1 _ hl.2 with ⟨d⟩
      exact ⟨d⟩⟩

lemma provable_iff {T : Theory L} [DecidablePred T] {σ : Sentence L} :
    T ⊢! σ ↔ ∃ l, ∃ U : List (Sentence L), U.all (T ·) ∧ (σ :: U.map (~·)).map Rew.emb.hom ∈ sequents l ∧ isProper l := by
  exact ⟨by
    rintro ⟨U, hU, d⟩
    rcases derivable_iff_isProper.mp ⟨d⟩ with ⟨l, hl, hmem⟩
    let l' := (Code.wk ((U.map (~·) ++ [σ]).map Rew.emb.hom), ((σ :: U.map (~·)).map Rew.emb.hom)) :: l
    have hl' : isProper l' := by simpa[isProper, hl] using hmem
    exact ⟨l', U, by simpa[List.subsetSet] using hU, by simp, hl'⟩,
  by rintro ⟨l, U, hU, hl, hproper⟩
     rcases derivation_of_isProper l hproper _ hl with ⟨d⟩
     exact Gentzen.provable_iff.mpr ⟨U, by simpa using hU, ⟨Derivation.toOneSided (d.wk $ by simp)⟩⟩⟩

end ProofList

end Derivation

open Derivation ProofList

def isProofFn (T : Theory L) [DecidablePred T] : Sentence L → ℕ → Bool :=
  fun σ e => (decode e : Option (ProofList L × List (Sentence L))).casesOn false
  <| fun A => bif A.2.all (T ·) && (σ :: A.2.map (~·)).map Rew.emb.hom ∈ sequents A.1 && isProper A.1 then true else false

-- TODO: move to Vorspiel
def Bool.toOpt : Bool → Option Unit := fun b => bif b then some () else none

@[simp] lemma isSome_bool_to_opt (b) : Option.isSome (Bool.toOpt b) = b := by cases b <;> simp[Bool.toOpt]

@[simp] lemma to_opt_eq_some_iff (b) : Bool.toOpt b = some () ↔ b := by cases b <;> simp[Bool.toOpt]

def provableFn (T : Theory L) [DecidablePred T] : Sentence L →. Unit := fun x =>
  Nat.rfindOpt (fun e => Bool.toOpt (isProofFn T x e))

lemma provable_iff_isProofFn {T : Theory L} [DecidablePred T] {σ : Sentence L} :
    T ⊢! σ ↔ ∃ e, isProofFn T σ e := by
  simp[provable_iff, isProofFn]
  constructor
  · rintro ⟨l, U, hU, hl, hproper⟩
    use encode (l, U)
    have : U.all (T ·) := by simp; intro x hx; exact hU x hx
    simp[hU, hl, hproper, this]
  · simp; intro e
    rcases decode e.unpair.1 with (_ | ⟨l⟩) <;> simp
    rcases decode e.unpair.2 with (_ | ⟨U⟩) <;> simp
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, ite_eq_iff]; simp
    intro h₁ h₂ h₃
    exact ⟨l, U, h₁, h₂, h₃⟩

lemma provable_iff_provableFn {T : Theory L} [DecidablePred T] {σ : Sentence L} {u} :
    T ⊢! σ ↔ u ∈ provableFn T σ := by
  rcases u with ⟨⟩
  simp[provableFn, provable_iff_isProofFn, Nat.rfindOpt, @eq_comm _ true, @eq_comm _ false]
  constructor
  · intro h
    rcases Nat.least_number _ h with ⟨e, he, hm⟩
    exact ⟨e, ⟨he, fun h => by simpa using hm _ h⟩, he⟩
  · rintro ⟨e, ⟨he, _⟩, _⟩; exact ⟨e, he⟩

class Theory.Computable (T : Theory L) [DecidablePred T] where
  comp : Computable (fun x => decide (T x))

section

open Computable
variable (T : Theory L) [DecidablePred T] [Theory.Computable T]

lemma isProofFn_computable :
    Computable₂ (isProofFn T) :=
  to₂' <| option_casesOn (Computable.decode.comp snd) (const false)
  <| to₂' <| Computable.cond
    (dom_bool₂.comp
      (dom_bool₂.comp
        (list_all (Theory.Computable.comp.comp Computable₂.right)
          (Computable.snd.comp .snd))
        (Primrec.to_comp $ by
          apply Primrec.list_mem.comp
            (Primrec.list_map
              (Primrec.list_cons.comp (Primrec.fst.comp .fst)
                (Primrec.list_map (Primrec.snd.comp .snd) $ Semiformula.neg_primrec.comp₂ .right))
                <| Semiformula.emb_primrec.comp₂ .right)
            (Primrec.list_map (Primrec.fst.comp .snd) <| Primrec.snd.comp₂ .right)))
      (Primrec.to_comp $ isProper_primrec.comp $ Primrec.fst.comp .snd))
    (const true)
    (const false)

lemma provableFn_partrec :
    Partrec (provableFn T) := Partrec.rfindOpt (dom_bool.comp $ isProofFn_computable T)

lemma provable_RePred : RePred (T ⊢! ·) :=
  (provableFn_partrec T).of_eq <| by intro σ; ext; simp[←provable_iff_provableFn]

end

end FirstOrder

end LO
