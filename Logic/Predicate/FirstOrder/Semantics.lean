import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.Semantics

variable {L : Language} {μ μ₁ μ₂ μ₃ : Type _}

namespace FirstOrder

namespace SubFormula
variable {n n₁ n₂ n₃ : ℕ} (S : Structure₁ L) (e : Fin n → S) (Φ : μ → S)

def subval' (Φ : μ → S) : ∀ {n}, (Fin n → S) → SubFormula L μ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel p v  => S.rel p (fun i => SubTerm.val S e Φ (v i))
  | _, e, nrel p v => ¬S.rel p (fun i => SubTerm.val S e Φ (v i))
  | _, e, p ⋏ q    => p.subval' Φ e ∧ q.subval' Φ e
  | _, e, p ⋎ q    => p.subval' Φ e ∨ q.subval' Φ e
  | _, e, ∀' p     => ∀ x : S, (p.subval' Φ (x :> e))
  | _, e, ∃' p     => ∃ x : S, (p.subval' Φ (x :> e))

@[simp] lemma subval'_neg (p : SubFormula L μ n) :
    subval' S Φ e (¬'p) = ¬subval' S Φ e p :=
  by induction p using rec' <;> simp[*, subval', ←neg_eq, or_iff_not_imp_left]

def subval (e : Fin n → S) (Φ : μ → S) : SubFormula L μ n →L Prop where
  toFun := subval' S Φ e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp[subval']
  map_or' := by simp[subval']
  map_neg' := by simp[subval'_neg]
  map_imp' := by simp[imp_eq, subval'_neg, ←neg_eq, subval', imp_iff_not_or]

def val (Φ : μ → S) : Formula L μ →L Prop := subval S Fin.nil Φ

notation:50 S " ⊧₁[" e :80 "] "p :0 => val S e p

def models (S : Structure₁ L) (p : Formula L μ) : Prop := ∀ e, S ⊧₁[e] p


@[simp] lemma subval_rel {k} {r : L.rel k} {v} :
    subval S e Φ (rel r v) ↔ S.rel r (fun i => SubTerm.val S e Φ (v i)) := by simp[subval, subval']

@[simp] lemma subval_nrel {k} {r : L.rel k} {v} :
    subval S e Φ (nrel r v) ↔ ¬S.rel r (fun i => SubTerm.val S e Φ (v i)) := by simp[subval, subval']

@[simp] lemma subval_all {p : SubFormula L μ (n + 1)} :
    subval S e Φ (∀' p) ↔ ∀ x : S, subval S (x :> e) Φ p := by simp[subval, subval']

@[simp] lemma subval_ex {p : SubFormula L μ (n + 1)} :
    subval S e Φ (∃' p) ↔ ∃ x : S, subval S (x :> e) Φ p := by simp[subval, subval']

lemma subval_bind (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (e : Fin n₂ → S) (Φ : μ₂ → S) (p : SubFormula L μ₁ n₁) :
    subval S e Φ (bind fixed free p) = subval S (fun x => SubTerm.val S e Φ (fixed x)) (fun x => SubTerm.val S e Φ (free x)) p :=
  by
  induction p using rec' generalizing n₂ <;> simp[*, SubTerm.val_bind]
  · apply forall_congr'; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)
  · apply exists_congr; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)

lemma subval_map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (e : Fin n₂ → S) (Φ : μ₂ → S) (p : SubFormula L μ₁ n₁) :
    subval S e Φ (map fixed free p) = subval S (e ∘ fixed) (Φ ∘ free) p :=
  by simp[map, subval_bind, Function.comp]

lemma subval_subst (u : SubTerm L μ n) (p : SubFormula L μ (n + 1)) :
    subval S e Φ (subst u p) = subval S (e <: u.val S e Φ) Φ p :=
  by simp[subst, subval_bind]; apply of_eq; congr ; exact funext $ Fin.lastCases (by simp) (by simp)

section Syntactic
variable (Ψ : ℕ → S)

end Syntactic

end SubFormula

instance : HasDoubleTurnstile (Structure₁ L) (Formula L μ) := ⟨SubFormula.models⟩

instance : HasDoubleTurnstile (Theory L μ) (Formula L μ) :=
  ⟨fun T p => ∀ S : Structure₁ L, (∀ q ∈ T, S ⊧ q) → S ⊧ p⟩

lemma models_def {S : Structure₁ L} {p : Formula L μ} : S ⊧ p ↔ (∀ e, S ⊧₁[e] p) :=
  by simp[HasDoubleTurnstile.doubleTurnstile, SubFormula.models]

lemma semanticConsequence_def {T : Theory L μ} {p : Formula L μ} :
    T ⊧ p ↔ (∀ S : Structure₁ L, (∀ q ∈ T, S ⊧ q) → S ⊧ p) :=
  by simp[HasDoubleTurnstile.doubleTurnstile, SubFormula.models]

end FirstOrder
