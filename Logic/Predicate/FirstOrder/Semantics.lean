import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.Semantics

universe u u₁ u₂ v v₁ v₂ w w₁ w₂

variable {L : Language.{u}} {μ : Type v}

namespace FirstOrder

namespace SubFormula
variable {n : ℕ} {M : Type w} (s : Structure₁ L M)
  (e : Fin n → M) (e₂ : Fin n₂ → M) (ε : μ → M) (ε₂ : μ₂ → M)

def subval' (ε : μ → M) : ∀ {n}, (Fin n → M) → SubFormula L μ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel p v  => Structure₁.rel p (fun i => SubTerm.val s e ε (v i))
  | _, e, nrel p v => ¬Structure₁.rel p (fun i => SubTerm.val s e ε (v i))
  | _, e, p ⋏ q    => p.subval' ε e ∧ q.subval' ε e
  | _, e, p ⋎ q    => p.subval' ε e ∨ q.subval' ε e
  | _, e, ∀' p     => ∀ x : M, (p.subval' ε (x :> e))
  | _, e, ∃' p     => ∃ x : M, (p.subval' ε (x :> e))

@[simp] lemma subval'_neg (p : SubFormula L μ n) :
    subval' s ε e (¬'p) = ¬subval' s ε e p :=
  by induction p using rec' <;> simp[*, subval', ←neg_eq, or_iff_not_imp_left]

def subval : SubFormula L μ n →L Prop where
  toFun := subval' s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp[subval']
  map_or' := by simp[subval']
  map_neg' := by simp[subval'_neg]
  map_imp' := by simp[imp_eq, subval'_neg, ←neg_eq, subval', imp_iff_not_or]

@[reducible] def subval! (M : Type w) [s : Structure₁ L M] {n} (e : Fin n → M) (ε : μ → M) :
    SubFormula L μ n →L Prop := subval s e ε

def val (ε : μ → M) : Formula L μ →L Prop := subval s Fin.nil ε

@[reducible] def val! (M : Type w) [s : Structure₁ L M] (ε : μ → M) :
    Formula L μ →L Prop := val s ε

@[simp] lemma subval_rel {k} {r : L.rel k} {v} :
    subval s e ε (rel r v) ↔ s.rel r (fun i => SubTerm.val s e ε (v i)) := of_eq rfl

@[simp] lemma subval_nrel {k} {r : L.rel k} {v} :
    subval s e ε (nrel r v) ↔ ¬s.rel r (fun i => SubTerm.val s e ε (v i)) := of_eq rfl

@[simp] lemma subval_all {p : SubFormula L μ (n + 1)} :
    subval s e ε (∀' p) ↔ ∀ x : M, subval s (x :> e) ε p := of_eq rfl

@[simp] lemma subval_ex {p : SubFormula L μ (n + 1)} :
    subval s e ε (∃' p) ↔ ∃ x : M, subval s (x :> e) ε p := of_eq rfl

lemma subval_bind (fixed : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (p : SubFormula L μ₁ n₁) :
    subval s e₂ ε₂ (bind fixed free p) =
    subval s (SubTerm.val s e₂ ε₂ ∘ fixed) (SubTerm.val s e₂ ε₂ ∘ free) p := by
  induction p using rec' generalizing n₂ <;> simp[*, SubTerm.val_bind, Function.comp]
  · apply forall_congr'; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)
  · apply exists_congr; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)

lemma subval_map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (e : Fin n₂ → M) (ε : μ₂ → M) (p : SubFormula L μ₁ n₁) :
    subval s e ε (map fixed free p) = subval s (e ∘ fixed) (ε ∘ free) p :=
  by simp[map, subval_bind, Function.comp]

lemma subval_subst (u : SubTerm L μ n) (p : SubFormula L μ (n + 1)) :
    subval s e ε (subst u p) = subval s (e <: u.val s e ε) ε p :=
  by simp[subst, subval_bind]; apply of_eq; congr ; exact funext $ Fin.lastCases (by simp) (by simp)

section Syntactic
variable (Ψ : ℕ → M)

end Syntactic

end SubFormula

notation:50 M " ⊧₁[" e :80 "] "p :0 => SubFormula.val! M e p

def models (s : Structure₁ L M) (p : Formula L μ) : Prop := ∀ ε, SubFormula.val s ε p

instance : HasDoubleTurnstile (Structure₁ L M) (Formula L μ) := ⟨models⟩

@[reducible] def models! (M : Type w) [s : Structure₁ L M] (p : Formula L μ) : Prop := s ⊧ p

infix:50 " ⊧₁ " => models!

lemma models_def {s : Structure₁ L M} {p : Formula L μ} : s ⊧ p ↔ (∀ e, SubFormula.val s e p) :=
  by simp[HasDoubleTurnstile.doubleTurnstile, models]

def valid (p : Formula L μ) : Prop := ∀ {M : Type u} [Inhabited M] (s : Structure₁ L M), s ⊧ p

instance : HasDoubleTurnstile (Theory L μ) (Formula L μ) :=
  ⟨fun T p => ∀ {M : Type u} [Inhabited M] (s : Structure₁ L M), (∀ q ∈ T, s ⊧ q) → s ⊧ p⟩

lemma semanticConsequence_def {T : Theory L μ} {p : Formula L μ} :
    T ⊧ p ↔ (∀ {M : Type u} [Inhabited M] (s : Structure₁ L M), (∀ q ∈ T, s ⊧ q) → s ⊧ p) :=
  by simp[HasDoubleTurnstile.doubleTurnstile, models]

lemma semanticConsequence_def! {T : Theory L μ} {p : Formula L μ} :
    T ⊧ p ↔ (∀ (M : Type u) [Inhabited M] [Structure₁ L M], (∀ q ∈ T, M ⊧₁ q) → M ⊧₁ p) :=
  by simp[semanticConsequence_def]

lemma valid_def! {p : Formula L μ} :
    valid p ↔ ∀ (M : Type u) [Inhabited M] [Structure₁ L M], M ⊧₁ p := of_eq rfl

@[simp] lemma valid_top : valid (⊤ : Formula L μ) := by simp[valid, models_def]; simp[Top.top]

@[simp] lemma nvalid_bot : ¬valid (⊥ : Formula L μ) := by
  simp[valid]
  exact ⟨PUnit, instInhabitedPUnit, default, by simp[models_def]; simp[Bot.bot]⟩

namespace SubFormula
variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂} 

section 
variable {M : Type w} {s₂ : Structure₁ L₂ M} {n} {e : Fin n → M} {ε : μ → M}

lemma subval_onSubFormula₁ {p : SubFormula L₁ μ n} :
    subval s₂ e ε (Φ.onSubFormula₁ p) ↔ subval (Φ.onStructure₁ s₂) e ε p :=
  by induction p using rec' <;> simp[*, SubTerm.val_onSubTerm]

lemma models_onSubFormula₁ {p : Formula L₁ μ} :
    s₂ ⊧ Φ.onSubFormula₁ p ↔ Φ.onStructure₁ s₂ ⊧ p :=
  by simp[models_def, val, subval_onSubFormula₁]

lemma onSubFormula₁_models_onSubFormula₁ {T : Theory L₁ μ} {p : Formula L₁ μ} (h : T ⊧ p) :
    Φ.onSubFormula₁ '' T ⊧ Φ.onSubFormula₁ p := by
  intros M _ s hM
  have : Φ.onStructure₁ s ⊧ p := h (Φ.onStructure₁ s) (fun q hq => models_onSubFormula₁.mp $ hM _ (Set.mem_image_of_mem _ hq))
  exact models_onSubFormula₁.mpr this

end 

section
variable
  (injf : ∀ k, Function.Injective (Φ.onFunc : L₁.func k → L₂.func k))
  (injr : ∀ k, Function.Injective (Φ.onRel : L₁.rel k → L₂.rel k))
  {M : Type w} [Inhabited M] (s₁ : Structure₁ L₁ M)
  {n} (e : Fin n → M) (ε : μ → M)

lemma subval_extendStructure₁_onSubFormula₁ {p : SubFormula L₁ μ n} :
    subval (Φ.extendStructure₁ s₁) e ε (Φ.onSubFormula₁ p) ↔ subval s₁ e ε p := by
  induction p using rec' <;> simp[*, SubTerm.val_extendStructure₁_onSubTerm Φ e ε injf s₁]
  · case hrel k r v =>
    exact Structure₁.extendStructure₁_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))
  · case hnrel k r v =>
    simpa[not_iff_not] using
      Structure₁.extendStructure₁_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))

lemma models_extendStructure₁_onSubFormula₁ {p : Formula L₁ μ} :
    Φ.extendStructure₁ s₁ ⊧ Φ.onSubFormula₁ p ↔ s₁ ⊧ p := by
  simp[models_def, val, subval_extendStructure₁_onSubFormula₁ injf injr]

lemma onSubFormula₁_models_onSubFormula₁_iff {T : Theory L₁ μ} {p : Formula L₁ μ} :
    Φ.onSubFormula₁ '' T ⊧ Φ.onSubFormula₁ p ↔ T ⊧ p :=
  ⟨by intros h M _ s₁ hs₁
      exact (models_extendStructure₁_onSubFormula₁ injf injr s₁).mp $
        h (Φ.extendStructure₁ s₁) (by simpa[models_extendStructure₁_onSubFormula₁ injf injr] using hs₁),
   onSubFormula₁_models_onSubFormula₁⟩

end

end SubFormula

end FirstOrder
