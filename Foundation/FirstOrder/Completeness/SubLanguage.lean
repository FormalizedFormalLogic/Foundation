module

public import Foundation.FirstOrder.Basic

@[expose] public section
namespace LO

namespace FirstOrder

variable {L : Language.{u}} {L₁ : Language.{u}} {L₂ : Language.{u}}

namespace Language

def subLanguage (L : Language) (pfunc : ∀ k, L.Func k → Prop) (prel : ∀ k, L.Rel k → Prop) :
    Language where
  Func := fun k => Subtype (pfunc k)
  Rel  := fun k => Subtype (prel k)

section subLanguage

variable (L)

variable {pf : (k : ℕ) → L.Func k → Prop} {pr : (k : ℕ) → L.Rel k → Prop}

def ofSubLanguage : subLanguage L pf pr →ᵥ L where
  func := Subtype.val
  rel  := Subtype.val

@[simp] lemma ofSubLanguage_onFunc :
    L.ofSubLanguage.func φ = φ.val := rfl

@[simp] lemma ofSubLanguage_onRel :
    L.ofSubLanguage.rel φ = φ.val := rfl

end subLanguage

end Language

namespace Semiterm

open Language
variable [∀ k, DecidableEq (L.Func k)]

def lang : Semiterm L ξ n → Finset (Σ k, L.Func k)
  | #_       => ∅
  | &_       => ∅
  | func f v => insert ⟨_, f⟩ $ Finset.biUnion Finset.univ (fun i => lang (v i))

@[simp] lemma lang_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    ⟨k, f⟩ ∈ (func f v).lang := by simp [lang]

lemma lang_func_ss {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).lang ⊆ (func f v).lang := by
  intros x
  simp only [lang, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  intros h; exact Or.inr ⟨i, h⟩

def toSubLanguage' (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) : ∀ t : Semiterm L ξ n,
    (∀ k f, ⟨k, f⟩ ∈ t.lang → pf k f) → Semiterm (subLanguage L pf pr) ξ n
  | #x,                    _ => #x
  | &x,                    _ => &x
  | func (arity := k) f v, h => func ⟨f, h k f (by simp)⟩
      (fun i => toSubLanguage' pf pr (v i) (fun k' f' h' => h k' f' (lang_func_ss f v i h')))

@[simp] lemma lMap_toSubLanguage' (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop)
  (t : Semiterm L ξ n) (h : ∀ k f, ⟨k, f⟩ ∈ t.lang → pf k f) :
    (t.toSubLanguage' pf pr h).lMap L.ofSubLanguage = t :=
  by induction t <;> simp [*, toSubLanguage', lMap_func]

end Semiterm

namespace Semiformula

variable [L.DecidableEq]

noncomputable def langFunc {n} : Semiformula L ξ n → Finset (Σ k, L.Func k)
  | ⊤        => ∅
  | ⊥        => ∅
  | rel  _ v => Finset.biUnion Finset.univ (fun i => (v i).lang)
  | nrel _ v => Finset.biUnion Finset.univ (fun i => (v i).lang)
  | φ ⋏ ψ    => langFunc φ ∪ langFunc ψ
  | φ ⋎ ψ    => langFunc φ ∪ langFunc ψ
  | ∀' φ     => langFunc φ
  | ∃' φ     => langFunc φ

noncomputable def langRel {n} : Semiformula L ξ n → Finset (Σ k, L.Rel k)
  | ⊤        => ∅
  | ⊥        => ∅
  | rel  r _ => {⟨_, r⟩}
  | nrel r _ => {⟨_, r⟩}
  | φ ⋏ ψ    => langRel φ ∪ langRel ψ
  | φ ⋎ ψ    => langRel φ ∪ langRel ψ
  | ∀' φ     => langRel φ
  | ∃' φ     => langRel φ

lemma langFunc_rel_ss {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).lang ⊆ (rel r v).langFunc := by
  intros x
  simp only [langFunc, Finset.mem_biUnion, Finset.mem_univ, true_and]
  intros h; exact ⟨i, h⟩

def toSubLanguage' (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) {n} :
    (φ : Semiformula L ξ n) →
    (∀ k f, ⟨k, f⟩ ∈ φ.langFunc → pf k f) →
    (∀ k r, ⟨k, r⟩ ∈ φ.langRel → pr k r) →
    Semiformula (L.subLanguage pf pr) ξ n
  | ⊤,        _,  _  => ⊤
  | ⊥,        _,  _  => ⊥
  | rel r v,  hf, hr =>
      rel ⟨r, hr _ r (by simp [langRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (langFunc_rel_ss r v i h)))
  | nrel r v, hf, hr =>
      nrel ⟨r, hr _ r (by simp [langRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (langFunc_rel_ss r v i h)))
  | φ ⋏ ψ,    hf, hr =>
      toSubLanguage' pf pr φ (fun k f h => hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋏
      toSubLanguage' pf pr ψ (fun k f h => hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | φ ⋎ ψ,    hf, hr =>
      toSubLanguage' pf pr φ (fun k f h => hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋎
      toSubLanguage' pf pr ψ (fun k f h => hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | ∀' φ,     hf, hr => ∀' toSubLanguage' pf pr φ hf hr
  | ∃' φ,     hf, hr => ∃' toSubLanguage' pf pr φ hf hr

@[simp] lemma lMap_toSubLanguage'
  (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) {n} (φ : Semiformula L ξ n)
  (hf : ∀ k f, ⟨k, f⟩ ∈ φ.langFunc → pf k f) (hr : ∀ k r, ⟨k, r⟩ ∈ φ.langRel → pr k r) :
    lMap L.ofSubLanguage (φ.toSubLanguage' pf pr hf hr) = φ := by
  induction φ using rec' <;> simp [*, toSubLanguage', lMap_rel, lMap_nrel]

noncomputable def languageFuncIndexed (φ : Semiformula L ξ n) (k) : Finset (L.Func k) :=
  Finset.preimage (langFunc φ) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective)

noncomputable def languageRelIndexed (φ : Semiformula L ξ n) (k) : Finset (L.Rel k) :=
  Finset.preimage (langRel φ) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective)

abbrev languageFinset (Γ : Finset (Semiformula L ξ n)) : Language :=
  Language.subLanguage L (fun k f => ∃ φ ∈ Γ, ⟨k, f⟩ ∈ langFunc φ) (fun k r => ∃ φ ∈ Γ, ⟨k, r⟩ ∈ langRel φ)

noncomputable instance (Γ : Finset (Semiformula L ξ n)) (k) : Fintype ((languageFinset Γ).Func k) :=
  Fintype.subtype (Γ.biUnion (languageFuncIndexed · k)) (by simp [languageFuncIndexed])

noncomputable instance (Γ : Finset (Semiformula L ξ n)) (k) : Fintype ((languageFinset Γ).Rel k) :=
  Fintype.subtype (Γ.biUnion (languageRelIndexed · k)) (by simp [languageRelIndexed])

def toSubLanguageFinsetSelf {Γ : Finset (Semiformula L ξ n)} {φ} (h : φ ∈ Γ) : Semiformula (languageFinset Γ) ξ n :=
  φ.toSubLanguage' _ _ (fun _ _ hf => ⟨φ, h, hf⟩) (fun _ _ hr => ⟨φ, h, hr⟩)

@[simp] lemma lMap_toSubLanguageFinsetSelf {Γ : Finset (Semiformula L ξ n)} {φ} (h : φ ∈ Γ) :
    lMap L.ofSubLanguage (toSubLanguageFinsetSelf h) = φ :=
  lMap_toSubLanguage' _ _ _ _ _

end Semiformula

namespace Structure

instance subLanguageStructure {pf : ∀ k, L.Func k → Prop} {pr : ∀ k, L.Rel k → Prop}
  {M : Type w} (s : Structure L M) : Structure (Language.subLanguage L pf pr) M :=
  s.lMap (Language.ofSubLanguage L)

noncomputable def extendStructure (Φ : L₁ →ᵥ L₂) {M : Type w} [Nonempty M] (s : Structure L₁ M) : Structure L₂ M where
  func := fun {k} f₂ v => Classical.epsilon (fun y => ∃ f₁ : L₁.Func k, Φ.func f₁ = f₂ ∧ y = s.func f₁ v)
  rel  := fun {k} r₂ v => ∃ r₁ : L₁.Rel k, Φ.rel r₁ = r₂ ∧ s.rel r₁ v

namespace extendStructure

variable {M : Type u} [Nonempty M] (s₁ : Structure L₁ M)

protected lemma func
    (Φ : L₁ →ᵥ L₂)
    {k} (injf : Function.Injective (Φ.func : L₁.Func k → L₂.Func k)) (f₁ : L₁.Func k) (v : Fin k → M) :
    (s₁.extendStructure Φ).func (Φ.func f₁) v = s₁.func f₁ v := by
  have : ∃ y, ∃ f₁' : L₁.Func k, Φ.func f₁' = Φ.func f₁ ∧ y = s₁.func f₁' v := ⟨s₁.func f₁ v, f₁, rfl, rfl⟩
  rcases Classical.epsilon_spec this with ⟨f', f'eq, h⟩
  rcases injf f'eq with rfl; exact h

protected lemma rel
    (Φ : L₁ →ᵥ L₂)
    {k} (injr : Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    (r₁ : L₁.Rel k) (v : Fin k → M) :
    (s₁.extendStructure Φ).rel (Φ.rel r₁) v ↔ s₁.rel r₁ v := by
  refine ⟨by intros h; rcases h with ⟨r₁', e, h⟩; rcases injr e; exact h, by intros h; refine ⟨r₁, rfl, h⟩⟩

lemma val_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    {n} (e : Fin n → M) (ε : ξ → M)
    (t : Semiterm L₁ ξ n) :
    Semiterm.val (s₁.extendStructure Φ) e ε (t.lMap Φ) = Semiterm.val s₁ e ε t := by
  induction t
  case func k f v ih =>
    simp only [Semiterm.lMap_func, Semiterm.val_func, ih]
    exact extendStructure.func s₁ Φ (injf k) f fun i ↦ Semiterm.val s₁ e ε (v i)
  case _ => simp [*]
  case _ => simp [*]

open Semiformula

lemma eval_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    {n} (e : Fin n → M) (ε : ξ → M)
    {φ : Semiformula L₁ ξ n} :
    Eval (s₁.extendStructure Φ) e ε (lMap Φ φ) ↔ Eval s₁ e ε φ := by
  induction φ using Semiformula.rec'
  case hrel k r v =>
    simp only [Semiformula.lMap_rel, eval_rel, val_lMap s₁ Φ injf e ε]
    exact extendStructure.rel s₁ Φ (injr k) r (fun i => Semiterm.val s₁ e ε (v i))
  case hnrel k r v =>
    simp only [lMap_nrel, eval_nrel, val_lMap s₁ Φ injf e ε]
    simpa [not_iff_not] using
      extendStructure.rel s₁ Φ (injr k) r (fun i => Semiterm.val s₁ e ε (v i))
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]

lemma models_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    (φ : Sentence L₁) :
    (s₁.extendStructure Φ).toStruc ⊧ Semiformula.lMap Φ φ ↔ s₁.toStruc ⊧ φ := by
  simp [Semantics.Models, eval_lMap s₁ Φ injf injr]

end extendStructure

end Structure

section lMap

lemma lMap_models_lMap_iff
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    {T : Theory L₁} {φ : Sentence L₁} :
    Theory.lMap Φ T ⊨ Semiformula.lMap Φ φ ↔ T ⊨ φ := by
  constructor
  · intro h s₁ hs₁
    refine (Structure.extendStructure.models_lMap s₁.struc Φ injf injr φ).mp <| h ?_
    suffices ∀ σ ∈ T, (Structure.extendStructure Φ s₁.struc).toStruc ⊧ Semiformula.lMap Φ σ by
      simpa [Semantics.modelsSet_iff, Theory.lMap, Semantics.models]
    intro σ hσ
    exact (Structure.extendStructure.models_lMap s₁.struc Φ injf injr σ).mpr (hs₁.models _ hσ)
  · exact lMap_models_lMap

lemma satisfiable_lMap
    (Φ : L₁ →ᵥ L₂)
    (injf : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k))
    (injr : ∀ k, Function.Injective (Φ.rel : L₁.Rel k → L₂.Rel k))
    {T : Theory L₁} (s : Satisfiable T) :
    Satisfiable (Semiformula.lMap Φ '' T) := by
  rcases s with ⟨⟨M, i, s⟩, hM⟩
  exact ⟨⟨M, i, s.extendStructure Φ⟩, by
    simp only [Semantics.modelsSet_iff, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro φ hp
    exact (Structure.extendStructure.models_lMap s Φ injf injr φ).mpr (hM.models _ hp)⟩

end lMap

end FirstOrder

end LO
