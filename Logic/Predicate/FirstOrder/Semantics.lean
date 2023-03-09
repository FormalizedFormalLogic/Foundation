import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.Semantics

universe u u₁ u₂ v v₁ v₂ w w₁ w₂

variable {L : Language.{u}} {μ : Type v}

namespace FirstOrder

namespace SubFormula
variable {n : ℕ} {M : Type w} (s : Structure₁ L M)
  (e : Fin n → M) (e₂ : Fin n₂ → M) (ε : μ → M) (ε₂ : μ₂ → M)

def SubVal' (ε : μ → M) : ∀ {n}, (Fin n → M) → SubFormula L μ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel p v  => Structure₁.rel p (fun i => SubTerm.val s e ε (v i))
  | _, e, nrel p v => ¬Structure₁.rel p (fun i => SubTerm.val s e ε (v i))
  | _, e, p ⋏ q    => p.SubVal' ε e ∧ q.SubVal' ε e
  | _, e, p ⋎ q    => p.SubVal' ε e ∨ q.SubVal' ε e
  | _, e, ∀' p     => ∀ x : M, (p.SubVal' ε (x :> e))
  | _, e, ∃' p     => ∃ x : M, (p.SubVal' ε (x :> e))

@[simp] lemma SubVal'_neg (p : SubFormula L μ n) :
    SubVal' s ε e (~p) = ¬SubVal' s ε e p :=
  by induction p using rec' <;> simp[*, SubVal', ←neg_eq, or_iff_not_imp_left]

def SubVal : SubFormula L μ n →L Prop where
  toFun := SubVal' s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp[SubVal']
  map_or' := by simp[SubVal']
  map_neg' := by simp[SubVal'_neg]
  map_imp' := by simp[imp_eq, SubVal'_neg, ←neg_eq, SubVal', imp_iff_not_or]

abbrev SubVal! (M : Type w) [s : Structure₁ L M] {n} (e : Fin n → M) (ε : μ → M) :
    SubFormula L μ n →L Prop := SubVal s e ε

abbrev Val (ε : μ → M) : Formula L μ →L Prop := SubVal s ![] ε

abbrev Val! (M : Type w) [s : Structure₁ L M] (ε : μ → M) :
    Formula L μ →L Prop := Val s ε

lemma subVal_rel {k} {r : L.rel k} {v} :
    SubVal s e ε (rel r v) ↔ s.rel r (fun i => SubTerm.val s e ε (v i)) := of_eq rfl

@[simp] lemma subVal_rel₀ {r : L.rel 0} :
    SubVal s e ε (rel r ![]) ↔ s.rel r ![] := by simp[subVal_rel, Matrix.empty_eq]

@[simp] lemma subVal_rel₁ {r : L.rel 1} (t : SubTerm L μ n) :
    SubVal s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp[subVal_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma subVal_rel₂ {r : L.rel 2} (t₁ t₂ : SubTerm L μ n) :
    SubVal s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[subVal_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

lemma subVal_nrel {k} {r : L.rel k} {v} :
    SubVal s e ε (nrel r v) ↔ ¬s.rel r (fun i => SubTerm.val s e ε (v i)) := of_eq rfl

@[simp] lemma subVal_nrel₀ {r : L.rel 0} :
    SubVal s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp[subVal_nrel, Matrix.empty_eq]

@[simp] lemma subVal_nrel₁ {r : L.rel 1} (t : SubTerm L μ n) :
    SubVal s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp[subVal_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma subVal_nrel₂ {r : L.rel 2} (t₁ t₂ : SubTerm L μ n) :
    SubVal s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[subVal_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma subVal_all {p : SubFormula L μ (n + 1)} :
    SubVal s e ε (∀' p) ↔ ∀ x : M, SubVal s (x :> e) ε p := of_eq rfl

@[simp] lemma subVal_ex {p : SubFormula L μ (n + 1)} :
    SubVal s e ε (∃' p) ↔ ∃ x : M, SubVal s (x :> e) ε p := of_eq rfl

lemma subVal_bind (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (p : SubFormula L μ₁ n₁) :
    SubVal s e₂ ε₂ (bind bound free p) =
    SubVal s (SubTerm.val s e₂ ε₂ ∘ bound) (SubTerm.val s e₂ ε₂ ∘ free) p := by
  induction p using rec' generalizing n₂ <;> simp[*, SubTerm.val_bind, Function.comp,
    bind_rel, bind_nrel, subVal_rel, subVal_nrel]
  · apply forall_congr'; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)
  · apply exists_congr; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)

lemma subVal_map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (e : Fin n₂ → M) (ε : μ₂ → M) (p : SubFormula L μ₁ n₁) :
    SubVal s e ε (map bound free p) = SubVal s (e ∘ bound) (ε ∘ free) p :=
  by simp[map, subVal_bind, Function.comp]

lemma subVal_subst (u : SubTerm L μ n) (p : SubFormula L μ (n + 1)) :
    SubVal s e ε (subst u p) = SubVal s (e <: u.val s e ε) ε p :=
  by simp[subst, subVal_bind]; apply of_eq; congr ; exact funext $ Fin.lastCases (by simp) (by simp)

section Syntactic
variable (Ψ : ℕ → M)

end Syntactic

end SubFormula

notation:50 M " ⊧₁[" e :80 "] "p :0 => SubFormula.Val! M e p

def Models (s : Structure₁ L M) (p : Formula L μ) : Prop := ∀ ε, SubFormula.Val s ε p

instance : HasDoubleTurnstile (Structure₁ L M) (Formula L μ) := ⟨Models⟩

@[reducible] def models! (M : Type w) [s : Structure₁ L M] (p : Formula L μ) : Prop := s ⊧ p

infix:50 " ⊧₁ " => models!

def ModelsTheory (s : Structure₁ L M) (T : Theory L μ) : Prop := ∀ p ∈ T, s ⊧ p

instance : HasDoubleTurnstile (Structure₁ L M) (Theory L μ) := ⟨ModelsTheory⟩

lemma models_def {s : Structure₁ L M} {p : Formula L μ} : s ⊧ p ↔ (∀ e, SubFormula.Val s e p) :=
  by simp[HasDoubleTurnstile.doubleTurnstile, Models]

lemma models_sentence_def {s : Structure₁ L M} {σ : Sentence L} : s ⊧ σ ↔ SubFormula.Val s Empty.elim σ :=
  by simp[HasDoubleTurnstile.doubleTurnstile, Models, Empty.eq_elim]

def Valid (p : Formula L μ) : Prop := ∀ {M : Type u} [Inhabited M] (s : Structure₁ L M), s ⊧ p

instance : HasDoubleTurnstile (Theory L μ) (Formula L μ) :=
  ⟨fun T p => ∀ {M : Type u} [Inhabited M] (s : Structure₁ L M), (∀ q ∈ T, s ⊧ q) → s ⊧ p⟩

lemma semanticConsequence_def {T : Theory L μ} {p : Formula L μ} :
    T ⊧ p ↔ (∀ {M : Type u} [Inhabited M] (s : Structure₁ L M), (∀ q ∈ T, s ⊧ q) → s ⊧ p) :=
  by simp[HasDoubleTurnstile.doubleTurnstile, Models]

lemma semanticConsequence_def! {T : Theory L μ} {p : Formula L μ} :
    T ⊧ p ↔ (∀ (M : Type u) [Inhabited M] [Structure₁ L M], (∀ q ∈ T, M ⊧₁ q) → M ⊧₁ p) :=
  by simp[semanticConsequence_def]

lemma valid_def! {p : Formula L μ} :
    Valid p ↔ ∀ (M : Type u) [Inhabited M] [Structure₁ L M], M ⊧₁ p := of_eq rfl

@[simp] lemma Valid_top : Valid (⊤ : Formula L μ) := by simp[Valid, models_def]; simp[Top.top]

@[simp] lemma nValid_bot : ¬Valid (⊥ : Formula L μ) := by
  simp[Valid]
  exact ⟨PUnit, instInhabitedPUnit, default, by simp[models_def]; simp[Bot.bot]⟩

def SubFormula.Satisfiable (p : Formula L μ) : Prop :=
  ∃ (M : Type u) (_ : Inhabited M) (s : Structure₁ L M), s ⊧ p

def Satisfiable (T : Theory L μ) : Prop :=
  ∃ (M : Type u) (_ : Inhabited M) (s : Structure₁ L M), s ⊧ T

namespace SubFormula
variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂} 

section 
variable {M : Type w} {s₂ : Structure₁ L₂ M} {n} {e : Fin n → M} {ε : μ → M}

lemma subVal_onSubFormula₁ {p : SubFormula L₁ μ n} :
    SubVal s₂ e ε (Φ.onSubFormula₁ p) ↔ SubVal (Φ.onStructure₁ s₂) e ε p :=
  by induction p using rec' <;>
    simp[*, SubTerm.val_onSubTerm, Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel,
      subVal_rel, subVal_nrel]

lemma models_onSubFormula₁ {p : Formula L₁ μ} :
    s₂ ⊧ Φ.onSubFormula₁ p ↔ Φ.onStructure₁ s₂ ⊧ p :=
  by simp[models_def, Val, subVal_onSubFormula₁]

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

lemma subVal_extendStructure₁_onSubFormula₁ {p : SubFormula L₁ μ n} :
    SubVal (Φ.extendStructure₁ s₁) e ε (Φ.onSubFormula₁ p) ↔ SubVal s₁ e ε p := by
  induction p using rec' <;> simp[*, SubTerm.val_extendStructure₁_onSubTerm Φ e ε injf s₁,
    Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel, subVal_rel, subVal_nrel]
  · case hrel k r v =>
    exact Structure₁.extendStructure₁_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))
  · case hnrel k r v =>
    simpa[not_iff_not] using
      Structure₁.extendStructure₁_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))

lemma models_extendStructure₁_onSubFormula₁ {p : Formula L₁ μ} :
    Φ.extendStructure₁ s₁ ⊧ Φ.onSubFormula₁ p ↔ s₁ ⊧ p := by
  simp[models_def, Val, subVal_extendStructure₁_onSubFormula₁ injf injr]

lemma onSubFormula₁_models_onSubFormula₁_iff {T : Theory L₁ μ} {p : Formula L₁ μ} :
    Φ.onSubFormula₁ '' T ⊧ Φ.onSubFormula₁ p ↔ T ⊧ p :=
  ⟨by intros h M _ s₁ hs₁
      exact (models_extendStructure₁_onSubFormula₁ injf injr s₁).mp $
        h (Φ.extendStructure₁ s₁) (by simpa[models_extendStructure₁_onSubFormula₁ injf injr] using hs₁),
   onSubFormula₁_models_onSubFormula₁⟩

end

section Eq
open Language

variable {L : Language.{u}} [L.HasEq] {μ : Type v} (M : Type w) (s : Structure₁ L M) [Structure₁.Eq L M]
  {n} (e : Fin n → M) (ε : μ → M)

@[simp] lemma subVal_eq (t u : SubTerm L μ n) :
    SubVal s e ε (rel Language.HasEq.eq ![t, u]) ↔ t.val s e ε = u.val s e ε :=
  by simp

end Eq

end SubFormula

namespace Theory

end Theory

end FirstOrder

