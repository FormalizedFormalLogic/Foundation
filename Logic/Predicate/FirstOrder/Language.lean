import Logic.Predicate.FirstOrder.Formula

variable {L L₁ L₂ L₃ : Language} {μ : Type _}

namespace Language

namespace Hom
variable (Φ : Hom L₁ L₂) {n : ℕ}

open FirstOrder

def onSubFormula₁' (Φ : Hom L₁ L₂) : ∀ {n}, SubFormula L₁ μ n → SubFormula L₂ μ n
  | _, ⊤                   => ⊤ 
  | _, ⊥                   => ⊥ 
  | _, SubFormula.rel r v  => SubFormula.rel (Φ.onRel r) (fun i => Φ.onSubTerm (v i))
  | _, SubFormula.nrel r v => SubFormula.nrel (Φ.onRel r) (fun i => Φ.onSubTerm (v i))
  | _, p ⋏ q               => Φ.onSubFormula₁' p ⋏ Φ.onSubFormula₁' q
  | _, p ⋎ q               => Φ.onSubFormula₁' p ⋎ Φ.onSubFormula₁' q
  | _, ∀' p                => ∀' Φ.onSubFormula₁' p
  | _, ∃' p                => ∃' Φ.onSubFormula₁' p

lemma onSubFormula₁'_neg {n} (p : SubFormula L₁ μ n) :
    Φ.onSubFormula₁' (¬'p) = ¬' Φ.onSubFormula₁' p :=
  by induction p using SubFormula.rec' <;> simp[*, onSubFormula₁', ←SubFormula.neg_eq]

def onSubFormula₁ (Φ : Hom L₁ L₂) {n} : SubFormula L₁ μ n →L SubFormula L₂ μ n where
  toFun := Φ.onSubFormula₁'
  map_top' := by simp[onSubFormula₁']
  map_bot' := by simp[onSubFormula₁']
  map_and' := by simp[onSubFormula₁']
  map_or'  := by simp[onSubFormula₁']
  map_neg' := by simp[onSubFormula₁'_neg]
  map_imp' := by simp[SubFormula.imp_eq, onSubFormula₁'_neg, ←SubFormula.neg_eq, onSubFormula₁']

@[simp] lemma onSubFormula₁_rel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onSubFormula₁ (SubFormula.rel r v) = SubFormula.rel (Φ.onRel r) (fun i => Φ.onSubTerm (v i)) := rfl

@[simp] lemma onSubFormula₁_nrel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onSubFormula₁ (SubFormula.nrel r v) = SubFormula.nrel (Φ.onRel r) (fun i => Φ.onSubTerm (v i)) := rfl

@[simp] lemma onSubFormula₁_all (p : SubFormula L₁ μ (n + 1)) :
    Φ.onSubFormula₁ (∀' p) = ∀' Φ.onSubFormula₁ p := rfl

@[simp] lemma onSubFormula₁_ex (p : SubFormula L₁ μ (n + 1)) :
    Φ.onSubFormula₁ (∃' p) = ∃' Φ.onSubFormula₁ p := rfl

end Hom

end Language

namespace FirstOrder

namespace SubFormula
variable {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) {μ₁ μ₂ : Type _} {n₁ n₂ : ℕ}

lemma onSubFormula₁_bind (fixed : Fin n₁ → SubTerm L₁ μ₂ n₂) (free : μ₁ → SubTerm L₁ μ₂ n₂) (p) :
    Φ.onSubFormula₁ (bind fixed free p) =
    bind (fun x => Φ.onSubTerm (fixed x)) (fun x => Φ.onSubTerm (free x)) (Φ.onSubFormula₁ p) :=
  by
  induction p using rec' generalizing μ₂ n₂ <;>
  simp[*, SubTerm.onSubTerm_bind, Fin.comp_left_concat, Function.comp, SubTerm.onSubTerm_fixedSucc]

lemma onSubFormula₁_map (fixed : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (p) :
    Φ.onSubFormula₁ (map fixed free p) = map fixed free (Φ.onSubFormula₁ p) :=
  by simp[map, onSubFormula₁_bind]

lemma onSubFormula₁_subst (u) (p : SubFormula L₁ μ (n + 1)) :
    Φ.onSubFormula₁ (subst u p) = subst (Φ.onSubTerm u) (Φ.onSubFormula₁ p) :=
  by simp[subst, onSubFormula₁_bind, Fin.comp_right_concat, Function.comp]

lemma onSubFormula₁_shift (p : SyntacticSubFormula L₁ n) : Φ.onSubFormula₁ (shift p) = shift (Φ.onSubFormula₁ p) :=
  by simp[shift, onSubFormula₁_map]

lemma onSubFormula₁_free (p : SyntacticSubFormula L₁ (n + 1)) : Φ.onSubFormula₁ (free p) = free (Φ.onSubFormula₁ p) :=
  by simp[free, onSubFormula₁_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma onSubFormula₁_fix (p : SyntacticSubFormula L₁ n) : Φ.onSubFormula₁ (fix p) = fix (Φ.onSubFormula₁ p) :=
  by simp[fix, onSubFormula₁_bind]; congr; funext x; cases x <;> simp

end SubFormula

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace SubFormula

noncomputable def langf : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.func k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  _ v => Finset.bunionᵢ Finset.univ (fun i => SubTerm.langf (v i))
  | _, nrel _ v => Finset.bunionᵢ Finset.univ (fun i => SubTerm.langf (v i))
  | _, p ⋏ q    => langf p ∪ langf q 
  | _, p ⋎ q    => langf p ∪ langf q 
  | _, ∀' p     => langf p 
  | _, ∃' p     => langf p 

noncomputable def langr : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.rel k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  r _ => {⟨_, r⟩}
  | _, nrel r _ => {⟨_, r⟩}
  | _, p ⋏ q    => langr p ∪ langr q 
  | _, p ⋎ q    => langr p ∪ langr q 
  | _, ∀' p     => langr p 
  | _, ∃' p     => langr p 

def lang (p : SubFormula L μ n) : Language :=
  Language.subLanguage L (fun k f => ⟨k, f⟩ ∈ langf p) (fun k r => ⟨k, r⟩ ∈ langr p) 

variable [DecidableEq μ]

def hasDecEq : (p q : SubFormula L μ n) → Decidable (p = q)
  | ⊤,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | ⊥,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | rel r v,  q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h => by simp[h]; exact Fin.decFinfun _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | nrel r v, q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h => by simp[h]; exact Fin.decFinfun _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | p ⋏ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hand p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | p ⋎ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hor p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | ∀' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hall p' => simp; exact hasDecEq p p'
  | ∃' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hex p' => simp; exact hasDecEq p p'

instance : DecidableEq (SubFormula L μ n) := hasDecEq

end SubFormula

end FirstOrder

