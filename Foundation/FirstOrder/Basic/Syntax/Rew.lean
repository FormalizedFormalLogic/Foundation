import Foundation.Logic.Predicate.Rew
import Foundation.FirstOrder.Basic.Syntax.Formula

/-!
# Rewriting Entailment

term/formula morphisms such as Rewritings, substitutions, and embs are handled by the structure `LO.FirstOrder.Rew`.
- `LO.FirstOrder.Rew.rewrite f` is a Rewriting of the free variables occurring in the term by `f : ξ₁ → Semiterm L ξ₂ n`.
- `LO.FirstOrder.Rew.subst v` is a substitution of the bounded variables occurring in the term by `v : Fin n → Semiterm L ξ n'`.
- `LO.FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in the term by `#x ↦ #(Fin.succ x)`.
- `LO.FirstOrder.Rew.shift` is a transformation of the free variables occurring in the term by `&x ↦ &(x + 1)`.
- `LO.FirstOrder.Rew.emb` is a emb of the term with no free variables.

Rewritings `LO.FirstOrder.Rew` is naturally converted to formula Rewritings by `LO.FirstOrder.Rew.hom`.

-/

namespace Finset

lemma biUnion_eq_empty [DecidableEq β] {s : Finset α} {f : α → Finset β} :
    s.biUnion f = ∅ ↔ ∀ i ∈ s, f i = ∅ := by
  constructor
  · intro h a ha; ext b
    have := by simpa using congrFun (congrArg Membership.mem h) b
    simpa using this a ha
  · intro h; ext b
    suffices ∀ x ∈ s, b ∉ f x by simpa
    intro a ha; simpa using congrFun (congrArg Membership.mem (h a ha)) b

end Finset

namespace LO

namespace FirstOrder

namespace Semiformula

def rewAux ⦃n₁ n₂ : ℕ⦄ (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L ξ₁ n₁ → Semiformula L ξ₂ n₂
  | ⊤        => ⊤
  | ⊥        => ⊥
  | rel r v  => rel r (ω ∘ v)
  | nrel r v => nrel r (ω ∘ v)
  | φ ⋏ ψ    => rewAux ω φ ⋏ rewAux ω ψ
  | φ ⋎ ψ    => rewAux ω φ ⋎ rewAux ω ψ
  | ∀' φ     => ∀' rewAux ω.q φ
  | ∃' φ     => ∃' rewAux ω.q φ

lemma rewAux_neg (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    rewAux ω (∼φ) = ∼rewAux ω φ :=
  by induction φ using Semiformula.rec' generalizing n₂ <;> simp [*, rewAux]

lemma ext_rewAux' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (φ : Semiformula L ξ₁ n₁) : rewAux ω₁ φ = rewAux ω₂ φ:= by simp [h]

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L ξ₁ n₁ →ˡᶜ Semiformula L ξ₂ n₂ where
  toTr := rewAux ω
  map_top'   := by rfl
  map_bot'   := by rfl
  map_neg'   := rewAux_neg ω
  map_and'   := fun φ ψ ↦ rfl
  map_or'    := fun φ ψ ↦ rfl
  map_imply' := fun φ ψ ↦ by simp [imp_eq, rewAux_neg, rewAux, ←neg_eq]

instance : Rewriting L ξ (Semiformula L ξ) ζ (Semiformula L ζ) where
  app := rew
  app_all (_ _) := rfl
  app_ex (_ _) := rfl

abbrev subst (φ : Semiformula L ξ n) (v : Fin n → Semiterm L ξ m) : Semiformula L ξ m := Rewriting.subst φ v

@[coe] abbrev emb [IsEmpty o] (φ : Semiformula L o n) : Semiformula L ξ n := Rewriting.emb φ

abbrev free (φ : SyntacticSemiformula L (n + 1)) : SyntacticSemiformula L n := Rewriting.free φ

abbrev shift (φ : SyntacticSemiformula L n) : SyntacticSemiformula L n := Rewriting.shift φ

lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) : ω ▹ rel r v = rel r fun i ↦ ω (v i) := rfl

lemma rew_nrel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) : ω ▹ nrel r v = nrel r fun i ↦ ω (v i) := rfl

lemma rew_rel' (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ rel r v = rel r (ω ∘ v) := rfl

lemma nrel' (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ nrel r v = nrel r (ω ∘ v) := rfl

@[simp] lemma rew_rel0 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 0} {v : Fin 0 → Semiterm L ξ₁ n₁} :
    ω ▹ rel r v = rel r ![] := by simp [rew_rel, Matrix.empty_eq]

@[simp] lemma rew_rel1 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 1} {t : Semiterm L ξ₁ n₁} :
    ω ▹ rel r ![t] = rel r ![ω t] := by simp [rew_rel, Matrix.constant_eq_singleton]

@[simp] lemma rew_rel2 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 2} {t₁ t₂ : Semiterm L ξ₁ n₁} :
    ω ▹ rel r ![t₁, t₂] = rel r ![ω t₁, ω t₂] := by simp [rew_rel, Matrix.constant_eq_singleton, Matrix.comp_vecCons']

@[simp] lemma rew_rel3 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 3} {t₁ t₂ t₃ : Semiterm L ξ₁ n₁} :
    ω ▹ rel r ![t₁, t₂, t₃] = rel r ![ω t₁, ω t₂, ω t₃] := by
  simp [rew_rel, Matrix.constant_eq_singleton, Matrix.comp_vecCons']

@[simp] lemma rew_nrel0 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 0} {v : Fin 0 → Semiterm L ξ₁ n₁} :
    ω ▹ nrel r v = nrel r ![] := by simp [rew_nrel, Matrix.empty_eq]

@[simp] lemma rew_nrel1 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 1} {t : Semiterm L ξ₁ n₁} :
    ω ▹ nrel r ![t] = nrel r ![ω t] := by simp [rew_nrel, Matrix.constant_eq_singleton]

@[simp] lemma rew_nrel2 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 2} {t₁ t₂ : Semiterm L ξ₁ n₁} :
    ω ▹ nrel r ![t₁, t₂] = nrel r ![ω t₁, ω t₂] := by simp [rew_nrel, Matrix.constant_eq_singleton, Matrix.comp_vecCons']

@[simp] lemma rew_nrel3 (ω : Rew L ξ₁ n₁ ξ₂ n₂) {r : L.Rel 3} {t₁ t₂ t₃ : Semiterm L ξ₁ n₁} :
    ω ▹ nrel r ![t₁, t₂, t₃] = nrel r ![ω t₁, ω t₂, ω t₃] := by
  simp [rew_nrel, Matrix.constant_eq_singleton, Matrix.comp_vecCons']

private lemma map_inj {b : Fin n₁ → Fin n₂} {f : ξ₁ → ξ₂}
    (hb : Function.Injective b) (hf : Function.Injective f) :
    Function.Injective fun φ : Semiformula L ξ₁ n₁ ↦ @Rew.map L ξ₁ ξ₂ n₁ n₂ b f ▹ φ
  | rel r v => fun φ ↦
    match φ with
    | rel s w => by
      simp only [rew_rel, rel.injEq, and_imp]
      rintro rfl; simp only [heq_eq_eq, true_and]; rintro rfl h; simp only [true_and]
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
    | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | nrel r v => fun φ ↦
    match φ with
    | nrel s w => by
      simp only [rew_nrel, nrel.injEq, and_imp]
      rintro rfl; simp only [heq_eq_eq, true_and]; rintro rfl h; simp only [true_and]
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
     | rel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  |       ⊤ => by intro φ; cases φ using cases' <;> simp [rew_rel, rew_nrel]
  |       ⊥ => by intro φ; cases φ using cases' <;> simp [rew_rel, rew_nrel]
  | φ ⋏ ψ => fun χ ↦
    match χ with
    | _ ⋏ _ => by
      simp only [LogicalConnective.HomClass.map_and, and_inj, and_imp]
      intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋎ _ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | φ ⋎ ψ => fun χ ↦
    match χ with
    | _ ⋎ _ => by
      simp only [LogicalConnective.HomClass.map_or, or_inj, and_imp]
      intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | ∀' φ => fun ψ ↦
    match ψ with
    | ∀' _ => by
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, all_inj]
      exact fun h ↦ map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | ∃' φ => fun ψ ↦
    match ψ with
    | ∃' _ => by
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, ex_inj]
      exact fun h ↦ map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
    | rel _ _ | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀' _ => by simp [rew_rel, rew_nrel]

instance : ReflectiveRewriting L ξ (Semiformula L ξ) where
  id_app (φ) := by induction φ using rec' <;> simp [rew_rel, rew_nrel, *]

instance : TransitiveRewriting L ξ₁ (Semiformula L ξ₁) ξ₂ (Semiformula L ξ₂) ξ₃ (Semiformula L ξ₃) where
  comp_app {n₁ n₂ n₃ ω₁₂ ω₂₃ φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [rew_rel, rew_nrel, Rew.comp_app, Rew.q_comp, *]

instance : InjMapRewriting L ξ (Semiformula L ξ) ζ (Semiformula L ζ) where
  smul_map_injective := map_inj

instance : LawfulSyntacticRewriting L (SyntacticSemiformula L) where

@[simp] lemma complexity_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : (ω ▹ φ).complexity = φ.complexity := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*, rew_rel, rew_nrel]

section

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

@[simp] lemma eq_top_iff {φ : Semiformula L ξ₁ n₁} : ω ▹ φ = (⊤ : Semiformula L ξ₂ n₂) ↔ φ = ⊤ := by
  cases φ using Semiformula.rec' <;> simp [rew_rel, rew_nrel]

@[simp] lemma eq_bot_iff {φ : Semiformula L ξ₁ n₁} : ω ▹ φ = (⊥ : Semiformula L ξ₂ n₂) ↔ φ = ⊥ := by
  cases φ using Semiformula.rec' <;> simp [rew_rel, rew_nrel]

lemma eq_rel_iff {φ : Semiformula L ξ₁ n₁} {k} {r : L.Rel k} {v} :
    ω ▹ φ = Semiformula.rel r v ↔ ∃ v', ω ∘ v' = v ∧ φ = Semiformula.rel r v' := by
  match φ with
  | rel (arity := k') r' v' =>
    simp only [rew_rel, rel.injEq]
    by_cases hk : k' = k <;> simp [hk]; rcases hk with rfl; simp
    by_cases hr : r' = r <;> simp [hr, funext_iff]
  | nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀' _ | ∃' _ => simp [rew_nrel]

lemma eq_nrel_iff {φ : Semiformula L ξ₁ n₁} {k} {r : L.Rel k} {v} :
    ω ▹ φ = Semiformula.nrel r v ↔ ∃ v', ω ∘ v' = v ∧ φ = Semiformula.nrel r v' := by
  match φ with
  | nrel (arity := k') r' v' =>
    simp only [rew_nrel]
    by_cases hk : k' = k <;> simp [hk]; rcases hk with rfl; simp
    by_cases hr : r' = r <;> simp [hr, funext_iff]
  | rel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀' _ | ∃' _ => simp [rew_rel]

@[simp] lemma eq_and_iff {φ : Semiformula L ξ₁ n₁} {ψ₁ ψ₂ : Semiformula L ξ₂ n₂} :
    ω ▹ φ = ψ₁ ⋏ ψ₂ ↔ ∃ φ₁ φ₂ : Semiformula L ξ₁ n₁, ω ▹ φ₁ = ψ₁ ∧ ω ▹ φ₂ = ψ₂ ∧ φ = φ₁ ⋏ φ₂ := by
  cases φ using Semiformula.rec' <;> simp [rew_rel, rew_nrel]

@[simp] lemma eq_or_iff {φ : Semiformula L ξ₁ n₁} {ψ₁ ψ₂ : Semiformula L ξ₂ n₂} :
    ω ▹ φ = ψ₁ ⋎ ψ₂ ↔ ∃ φ₁ φ₂ : Semiformula L ξ₁ n₁, ω ▹ φ₁ = ψ₁ ∧ ω ▹ φ₂ = ψ₂ ∧ φ = φ₁ ⋎ φ₂ := by
  cases φ using Semiformula.rec' <;> simp [rew_rel, rew_nrel]

lemma eq_all_iff {φ : Semiformula L ξ₁ n₁} {ψ : Semiformula L ξ₂ (n₂ + 1)} :
    ω ▹ φ = ∀' ψ ↔ ∃ φ' : Semiformula L ξ₁ (n₁ + 1), ω.q ▹ φ' = ψ ∧ φ = ∀' φ' := by
  cases φ using Semiformula.rec' <;> simp [rew_rel, rew_nrel]

lemma eq_ex_iff {φ : Semiformula L ξ₁ n₁} {ψ : Semiformula L ξ₂ (n₂ + 1)} :
    ω ▹ φ = ∃' ψ ↔ ∃ φ' : Semiformula L ξ₁ (n₁ + 1), ω.q ▹ φ' = ψ ∧ φ = ∃' φ' := by
  cases φ using Semiformula.rec' <;> simp [rew_rel, rew_nrel]

@[simp] lemma eq_neg_iff {φ : Semiformula L ξ₁ n₁} {ψ₁ ψ₂ : Semiformula L ξ₂ n₂} :
    ω ▹ φ = ψ₁ ➝ ψ₂ ↔ ∃ φ₁ φ₂ : Semiformula L ξ₁ n₁, ω ▹ φ₁ = ψ₁ ∧ ω ▹ φ₂ = ψ₂ ∧ φ = φ₁ ➝ φ₂ := by
  simp only [imp_eq, eq_or_iff, exists_and_left]; constructor
  · rintro ⟨φ₁, hp₁, ψ₂, rfl, rfl⟩; exact ⟨∼φ₁, by simp [hp₁]⟩
  · rintro ⟨φ₁, rfl, φ₂, rfl, rfl⟩; exact ⟨∼φ₁, by simp, φ₂, by simp⟩

lemma eq_ball_iff {φ : Semiformula L ξ₁ n₁} {ψ₁ ψ₂ : Semiformula L ξ₂ (n₂ + 1)} :
    (ω ▹ φ = ∀[ψ₁] ψ₂) ↔ ∃ φ₁ φ₂ : Semiformula L ξ₁ (n₁ + 1), ω.q ▹ φ₁ = ψ₁ ∧ ω.q ▹ φ₂ = ψ₂ ∧ φ = ∀[φ₁] φ₂ := by
  simp only [ball, eq_all_iff, eq_neg_iff, exists_and_left]; constructor
  · rintro ⟨φ', ⟨φ₁, rfl, φ₂, rfl, rfl⟩, rfl⟩; exact ⟨φ₁, rfl, φ₂, rfl, rfl⟩
  · rintro ⟨φ₁, rfl, φ₂, rfl, rfl⟩; simp

lemma eq_bex_iff {φ : Semiformula L ξ₁ n₁} {ψ₁ ψ₂ : Semiformula L ξ₂ (n₂ + 1)} :
    (ω ▹ φ = ∃[ψ₁] ψ₂) ↔ ∃ φ₁ φ₂ : Semiformula L ξ₁ (n₁ + 1), ω.q ▹ φ₁ = ψ₁ ∧ ω.q ▹ φ₂ = ψ₂ ∧ φ = ∃[φ₁] φ₂ := by
  simp only [bex, eq_ex_iff, eq_and_iff, exists_and_left]; constructor
  · rintro ⟨φ', ⟨φ₁, rfl, φ₂, rfl, rfl⟩, rfl⟩; exact ⟨φ₁, rfl, φ₂, rfl, rfl⟩
  · rintro ⟨φ₁, rfl, φ₂, rfl, rfl⟩; simp

end

instance : Coe (Semisentence L n) (SyntacticSemiformula L n) := ⟨Rewriting.emb (ξ := ℕ)⟩

@[simp] lemma coe_inj (σ π : Semisentence L n) : (σ : SyntacticSemiformula L n) = π ↔ σ = π := Rewriting.emb_injective.eq_iff

lemma coe_rel [IsEmpty ο] {k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ο n) :
    (Rewriting.emb (rel R v) : Semiformula L ξ n) = (rel R fun i ↦ Rew.emb (v i)) := by rfl

lemma coe_nrel [IsEmpty ο] {k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ο n) :
    (Rewriting.emb (nrel R v) : Semiformula L ξ n) = (nrel R fun i ↦ Rew.emb (v i)) := by rfl

lemma coe_subst_eq_subst_coe (φ : Semisentence L k) (v : Fin k → ClosedSemiterm L n) :
    (↑(φ ⇜ v) : SyntacticSemiformula L n) = (↑φ : SyntacticSemiformula L k)⇜(fun i ↦ (↑(v i) : Semiterm L ℕ n)) :=
  Rewriting.emb_subst_eq_subst_emb φ v

lemma coe_subst_eq_subst_coe₁ (φ : Semisentence L 1) (t : ClosedSemiterm L n) :
    (↑(φ/[t]) : SyntacticSemiformula L n) = (↑φ : SyntacticSemiformula L 1)/[(↑t : Semiterm L ℕ n)] :=
  Rewriting.emb_subst_eq_subst_coe₁ φ t

@[elab_as_elim]
def formulaRec {C : SyntacticFormula L → Sort _}
  (verum  : C ⊤)
  (falsum : C ⊥)
  (rel    : ∀ {l : ℕ} (r : L.Rel l) (v : Fin l → SyntacticTerm L), C (rel r v))
  (nrel   : ∀ {l : ℕ} (r : L.Rel l) (v : Fin l → SyntacticTerm L), C (nrel r v))
  (and    : ∀ (φ ψ : SyntacticFormula L), C φ → C ψ → C (φ ⋏ ψ))
  (or     : ∀ (φ ψ : SyntacticFormula L), C φ → C ψ → C (φ ⋎ ψ))
  (all    : ∀ (φ : SyntacticSemiformula L 1), C (Rewriting.free φ) → C (∀' φ))
  (ex     : ∀ (φ : SyntacticSemiformula L 1), C (Rewriting.free φ) → C (∃' φ)) :
    ∀ (φ : SyntacticFormula L), C φ
  | ⊤         => verum
  | ⊥         => falsum
  | .rel r v  => rel r v
  | .nrel r v => nrel r v
  | φ ⋏ ψ     => and φ ψ (formulaRec verum falsum rel nrel and or all ex φ) (formulaRec verum falsum rel nrel and or all ex ψ)
  | φ ⋎ ψ     => or φ ψ  (formulaRec verum falsum rel nrel and or all ex φ) (formulaRec verum falsum rel nrel and or all ex ψ)
  | ∀' φ      => all φ   (formulaRec verum falsum rel nrel and or all ex (Rewriting.free φ))
  | ∃' φ      => ex φ    (formulaRec verum falsum rel nrel and or all ex (Rewriting.free φ))
  termination_by φ => φ.complexity

lemma fvar?_rew [DecidableEq ξ₁] [DecidableEq ξ₂]
    {φ : Semiformula L ξ₁ n₁} {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {x} (h : (ω ▹ φ).FVar? x) :
    (∃ i : Fin n₁, (ω #i).FVar? x) ∨ (∃ z : ξ₁, φ.FVar? z ∧ (ω &z).FVar? x) := by
  induction φ using rec' generalizing n₂
  case hverum => simp [FVar?] at h
  case hfalsum => simp [FVar?] at h
  case hrel n k r v =>
    have : ∃ i, (ω (v i)).FVar? x := by simpa [rew_rel, fvar?_rel] using h
    rcases this with ⟨i, hi⟩
    rcases Semiterm.fvar?_rew hi with (h | ⟨z, hi, hz⟩)
    · left; exact h
    · right; exact ⟨z, by simpa using ⟨i, hi⟩, hz⟩
  case hnrel n k r v =>
    have : ∃ i, (ω (v i)).FVar? x := by simpa [rew_nrel, fvar?_rel] using h
    rcases this with ⟨i, hi⟩
    rcases Semiterm.fvar?_rew hi with (h | ⟨z, hi, hz⟩)
    · left; exact h
    · right; exact ⟨z, by simpa using ⟨i, hi⟩, hz⟩
  case hand n φ ψ ihp ihq =>
    have : (ω ▹ φ).FVar? x ∨ (ω ▹ ψ).FVar? x := by simpa using h
    rcases this with (h | h)
    · rcases ihp h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
    · rcases ihq h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
  case hor n φ ψ ihp ihq =>
    have : (ω ▹ φ).FVar? x ∨ (ω ▹ ψ).FVar? x := by simpa using h
    rcases this with (h | h)
    · rcases ihp h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
    · rcases ihq h with (h | ⟨z, hi, hz⟩)
      · exact .inl h
      · exact .inr ⟨z, by simp [hi], hz⟩
  case hall n φ ihp =>
    have : (Rew.bind (#0 :> fun i ↦ Rew.bShift (ω #i)) (fun z ↦ Rew.bShift (ω &z)) ▹ φ).FVar? x := by simpa [Rew.q_bind] using h
    rcases ihp this with (⟨z, hz⟩ | ⟨z, hz⟩)
    · cases z using Fin.cases
      case zero => simp at hz
      case succ i =>
        have : (ω #i).FVar? x := by simpa using hz
        exact .inl ⟨i, this⟩
    · have : φ.FVar? z ∧ (ω &z).FVar? x := by simpa using hz
      exact .inr ⟨z, this⟩
  case hex n φ ihp =>
    have : (Rew.bind (#0 :> fun i ↦ Rew.bShift (ω #i)) (fun z ↦ Rew.bShift (ω &z)) ▹ φ).FVar? x := by simpa [Rew.q_bind] using h
    rcases ihp this with (⟨z, hz⟩ | ⟨z, hz⟩)
    · cases z using Fin.cases
      case zero => simp at hz
      case succ i =>
        have : (ω #i).FVar? x := by simpa using hz
        left; exact ⟨i, this⟩
    · have : φ.FVar? z ∧ (ω &z).FVar? x := by simpa using hz
      right; exact ⟨z, this⟩

@[simp] lemma freeVariables_emb [DecidableEq ξ] {ο : Type*} [IsEmpty ο] (φ : Semiformula L ο n) :
    (Rewriting.emb φ : Semiformula L ξ n).freeVariables = ∅ := by
  ext x
  suffices x ∉ (Rewriting.emb φ : Semiformula L ξ n).freeVariables by simpa using this
  intro hx
  rcases fvar?_rew hx with (⟨i, hi⟩ | ⟨z, _⟩)
  · simp at hi
  · exact IsEmpty.elim inferInstance z

lemma rew_eq_of_funEqOn [DecidableEq ξ₁] {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁}
  (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : Function.funEqOn φ.FVar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ ▹ φ = ω₂ ▹ φ := by
  induction φ using rec' generalizing n₂
  case hverum => simp
  case hfalsum => simp
  case hrel =>
    simp only [rew_rel, rel.injEq, heq_eq_eq, true_and]
    funext i
    exact Semiterm.rew_eq_of_funEqOn _ _ _ hb
      (hf.of_subset fun x hx ↦ fvar?_rel.mpr ⟨i, hx⟩)
  case hnrel =>
    simp only [rew_nrel, nrel.injEq, heq_eq_eq, true_and]
    funext i
    exact Semiterm.rew_eq_of_funEqOn _ _ _ hb
      (hf.of_subset fun x hx ↦ fvar?_nrel.mpr ⟨i, hx⟩)
  case hand ihp ihq =>
    simp only [LogicalConnective.HomClass.map_and, and_inj]
    exact ⟨ihp hb (hf.of_subset fun x hx ↦ by simp [hx]), ihq hb (hf.of_subset fun x hx ↦ by simp [hx])⟩
  case hor ihp ihq =>
    simp only [LogicalConnective.HomClass.map_or, or_inj]
    exact ⟨ihp hb (hf.of_subset fun x hx ↦ by simp [hx]), ihq hb (hf.of_subset fun x hx ↦ by simp [hx])⟩
  case hall ih =>
    simp only [Rewriting.app_all, all_inj]
    exact ih (fun x ↦ by cases x using Fin.cases <;> simp [hb]) (fun x hx ↦ by simpa using congr_arg _ (hf x hx))
  case hex ih =>
    simp only [Rewriting.app_ex, ex_inj]
    exact ih (fun x ↦ by cases x using Fin.cases <;> simp [hb]) (fun x hx ↦ by simpa using congr_arg _ (hf x hx))

lemma rew_eq_of_funEqOn₀ [DecidableEq ξ₁] {ω₁ ω₂ : Rew L ξ₁ 0 ξ₂ n₂} {φ : Semiformula L ξ₁ 0}
    (hf : Function.funEqOn (φ.FVar?) (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) : ω₁ ▹ φ = ω₂ ▹ φ :=
  rew_eq_of_funEqOn (fun x ↦ Fin.elim0 x) hf

lemma rew_eq_self_of [DecidableEq ξ] {ω : Rew L ξ n ξ n} {φ : Semiformula L ξ n}
  (hb : ∀ x, ω #x = #x) (hf : ∀ x, φ.FVar? x → ω &x = &x) :
    ω ▹ φ = φ := by
  suffices ω ▹ φ = Rew.id ▹ φ by rwa [ReflectiveRewriting.id_app] at this
  apply rew_eq_of_funEqOn
  · intro x; simpa using hb x
  · intro x hx; simp [hf x hx]

@[simp] lemma ex_ne_subst (φ : Semiformula L ξ 1) (t) : φ/[t] ≠ ∃' φ := ne_of_ne_complexity (by simp)

section univCl

@[simp] lemma fvSup_sentence (σ : Semisentence L n) : (Rewriting.emb σ).fvSup = 0 := by
    induction σ using rec' <;> simp [fvSup]

private lemma not_fvar?_fixitr_fvSup (φ : SyntacticFormula L) : ¬(Rew.fixitr 0 φ.fvSup ▹ φ).FVar? x := by
  rw [Rew.eq_bind (Rew.fixitr 0 φ.fvSup)]
  simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
  intro h
  rcases fvar?_rew h with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
  · simp at hz
  · have : z < φ.fvSup := lt_fvSup_of_fvar? hz
    simp [this] at hx

@[simp] lemma subst_comp_fixitr_eq_map (φ : SyntacticFormula L) (f : ℕ → SyntacticTerm L) :
    (Rew.fixitr 0 φ.fvSup ▹ φ)⇜(fun x ↦ f x) = Rew.rewrite f ▹ φ := by
  unfold Rewriting.subst; rw [← TransitiveRewriting.comp_app]
  apply rew_eq_of_funEqOn
  · simp
  · intro x hx
    simp [Rew.comp_app, Rew.fixitr_fvar, Semiformula.lt_fvSup_of_fvar? hx]

@[simp] lemma subst_comp_fixitr (φ : SyntacticFormula L) :
    (Rew.fixitr 0 φ.fvSup ▹ φ)⇜(fun x ↦ (&x : SyntacticTerm L)) = φ := by
  unfold Rewriting.subst; rw [← TransitiveRewriting.comp_app]
  apply rew_eq_self_of
  · simp
  · intro x hx
    simp [Rew.comp_app, Rew.fixitr_fvar, Semiformula.lt_fvSup_of_fvar? hx]

def univCl' (φ : SyntacticFormula L) : SyntacticFormula L := ∀* (@Rew.fixitr L 0 φ.fvSup ▹ φ)

@[simp] lemma rew_univCl' (φ : SyntacticFormula L) (ω : SyntacticRew L 0 0) :
    ω ▹ φ.univCl' = φ.univCl' := rew_eq_self_of (by simp) (by simp [univCl', not_fvar?_fixitr_fvSup])

lemma univCl'_eq_self_of (φ : SyntacticFormula L) (h : φ.freeVariables = ∅) : φ.univCl' = φ := by
  have : φ.fvSup = 0 := by simp [fvSup, h]
  simp only [univCl']; rw [this]; simp

@[simp] lemma senetnce_univCl'_eq_self (σ : Sentence L) :
    (σ : SyntacticFormula L).univCl' = σ := univCl'_eq_self_of _ (by simp)

@[simp] lemma fvarList_univCl' (φ : SyntacticFormula L) : φ.univCl'.freeVariables = ∅ := by
  ext x
  suffices x ∉ φ.univCl'.freeVariables by simpa
  simpa [univCl'] using not_fvar?_fixitr_fvSup φ

@[simp] lemma univCl'_univCl'_eq_univCl' (φ : SyntacticFormula L) :
    φ.univCl'.univCl' = φ.univCl' :=
  univCl'_eq_self_of φ.univCl' (by simp)

def toEmpty [DecidableEq ξ] {n : ℕ} : (φ : Semiformula L ξ n) → φ.freeVariables = ∅ → Semisentence L n
  | rel R v,  h => rel R fun i ↦ (v i).toEmpty <| by
    revert i; simpa [freeVariables_rel, Finset.biUnion_eq_empty] using h
  | nrel R v, h => nrel R fun i ↦ (v i).toEmpty <| by
    revert i; simpa [freeVariables_nrel, Finset.biUnion_eq_empty] using h
  | ⊤,        _ => ⊤
  | ⊥,        _ => ⊥
  | φ ⋏ ψ,    h =>
    φ.toEmpty (by simp [show φ.freeVariables = ∅ ∧ ψ.freeVariables = ∅ by simpa [Finset.union_eq_empty] using h]) ⋏
    ψ.toEmpty (by simp [show φ.freeVariables = ∅ ∧ ψ.freeVariables = ∅ by simpa [Finset.union_eq_empty] using h])
  | φ ⋎ ψ,    h =>
    φ.toEmpty (by simp [show φ.freeVariables = ∅ ∧ ψ.freeVariables = ∅ by simpa [Finset.union_eq_empty] using h]) ⋎
    ψ.toEmpty (by simp [show φ.freeVariables = ∅ ∧ ψ.freeVariables = ∅ by simpa [Finset.union_eq_empty] using h])
  | ∀' φ,     h => ∀' φ.toEmpty (by simpa using h)
  | ∃' φ,     h => ∃' φ.toEmpty (by simpa using h)

@[simp] lemma emb_toEmpty [DecidableEq ξ] (φ : Semiformula L ξ n) (hp : φ.freeVariables = ∅) : Rewriting.emb (φ.toEmpty hp) = φ := by
  induction φ using rec' <;> simp [toEmpty, rew_rel, rew_nrel, *]

@[simp] lemma toEmpty_emb [DecidableEq ξ] (φ : Semisentence L n) : (Rewriting.emb φ : Semiformula L ξ n).toEmpty (by simp) = φ := by
  induction φ using rec' <;> simp [toEmpty, rew_rel, rew_nrel, *]

@[simp] lemma toEmpty_verum [DecidableEq ξ] : (⊤ : Semiformula L ξ n).toEmpty (by simp) = ⊤ := rfl

@[simp] lemma toEmpty_falsum [DecidableEq ξ]: (⊥ : Semiformula L ξ n).toEmpty (by simp) = ⊥ := rfl

@[simp] lemma toEmpty_and [DecidableEq ξ] (φ ψ : Semiformula L ξ n) (h) :
    (φ ⋏ ψ).toEmpty h = φ.toEmpty (by simp [by simpa [Finset.union_eq_empty] using h]) ⋏ ψ.toEmpty (by simp [by simpa [Finset.union_eq_empty] using h]) := rfl

@[simp] lemma toEmpty_or [DecidableEq ξ] (φ ψ : Semiformula L ξ n) (h) :
    (φ ⋎ ψ).toEmpty h = φ.toEmpty (by simp [by simpa [Finset.union_eq_empty] using h]) ⋎ ψ.toEmpty (by simp [by simpa [Finset.union_eq_empty] using h]) := rfl

@[simp] lemma toEmpty_all [DecidableEq ξ] (φ : Semiformula L ξ (n + 1)) (h) : (∀' φ).toEmpty h = ∀' (φ.toEmpty (by simpa using h)) := rfl

@[simp] lemma toEmpty_ex [DecidableEq ξ] (φ : Semiformula L ξ (n + 1)) (h) : (∃' φ).toEmpty h = ∃' (φ.toEmpty (by simpa using h)) := rfl

/-- An universal closure of formula -/
def univCl (φ : SyntacticFormula L) : Sentence L := φ.univCl'.toEmpty (by simp)

@[simp] lemma coe_univCl_eq_univCl' (φ : SyntacticFormula L) : (φ.univCl : SyntacticFormula L) = φ.univCl' := by simp [univCl]

@[simp] lemma univCl_coe_sentence (σ : Sentence L) : univCl (↑σ : SyntacticFormula L) = σ := by
  unfold univCl
  refine (Semiformula.coe_inj _ _).mp ?_
  rw [emb_toEmpty]
  simp

def toEmpty' [DecidableEq ξ] {n : ℕ} (φ : Semiformula L ξ n) : Semisentence L n :=
  if h : φ.freeVariables = ∅ then φ.toEmpty h else ⊥

@[simp] lemma toEmpty'_coe [DecidableEq ξ] {n : ℕ} {φ : Semisentence L n} :
    (Rewriting.emb φ : Semiformula L ξ n).toEmpty' = φ := by
  simp [toEmpty']

end univCl

section lMap

variable {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}} {ξ : Type*} {Φ : L₁ →ᵥ L₂}

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (φ : Semiformula L₁ ξ₁ n₁) :
    lMap Φ (Rew.bind b e ▹ φ) = Rew.bind (Semiterm.lMap Φ ∘ b) (Semiterm.lMap Φ ∘ e) ▹ (lMap Φ φ) := by
  induction φ using rec' generalizing ξ₂ n₂ <;>
  simp [*, rew_rel, rew_nrel, lMap_rel, lMap_nrel, Semiterm.lMap_bind, Rew.q_bind, Matrix.comp_vecCons', Semiterm.lMap_bShift, Function.comp_def]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (φ : Semiformula L₁ ξ₁ n₁) :
    lMap Φ (Rew.map (L := L₁) b e ▹ φ) = Rew.map (L := L₂) b e ▹ lMap Φ φ := lMap_bind _ _ _

lemma lMap_rewrite (f : ξ₁ → Semiterm L₁ ξ₂ n) (φ : Semiformula L₁ ξ₁ n) :
    lMap Φ (Rew.rewrite f ▹ φ) = Rew.rewrite (Semiterm.lMap Φ ∘ f) ▹ lMap Φ φ := by
  simp [Rew.rewrite, lMap_bind, Function.comp_def]

lemma lMap_subst (w : Fin k → Semiterm L₁ ξ n) (φ : Semiformula L₁ ξ k) :
    lMap Φ (φ ⇜ w) = (lMap Φ φ)⇜(Semiterm.lMap Φ ∘ w) := lMap_bind _ _ _

lemma lMap_shift (φ : SyntacticSemiformula L₁ n) : lMap Φ (@Rew.shift L₁ n ▹ φ) = @Rew.shift L₂ n ▹ lMap Φ φ := lMap_bind _ _ _

lemma lMap_free (φ : SyntacticSemiformula L₁ (n + 1)) : lMap Φ (@Rew.free L₁ n ▹ φ) = @Rew.free L₂ n ▹ lMap Φ φ := by
  simp [Rew.free, lMap_bind, Function.comp_def, Matrix.comp_vecConsLast]

lemma lMap_fix (φ : SyntacticSemiformula L₁ n) : lMap Φ (@Rew.fix L₁ n ▹ φ) = @Rew.fix L₂ n ▹ lMap Φ φ := by
  simp only [Rew.fix, lMap_bind, Function.comp_def, Semiterm.lMap_bvar]
  congr; { funext x; cases x <;> simp }

lemma lMap_emb {ο : Type _} [IsEmpty ο] (φ : Semiformula L₁ ο n) :
    (lMap Φ (Rewriting.emb φ : Semiformula L₁ ξ n)) = Rewriting.emb (lMap Φ φ) := lMap_bind _ _ _

lemma lMap_toS (φ : Semiformula L₁ (Fin n) 0) :
    lMap Φ (@Rew.toS L₁ n ▹ φ) = @Rew.toS L₂ n ▹ lMap Φ φ := by
  rw [Rew.eq_bind Rew.toS, lMap_bind]
  simp [Function.comp_def, Matrix.empty_eq]; congr

lemma lMap_rewriteMap (φ : Semiformula L₁ ξ₁ n) (f : ξ₁ → ξ₂) :
    lMap Φ (Rew.rewriteMap (L := L₁) (n := n) f ▹ φ) = (Rew.rewriteMap (L := L₂) (n := n) f) ▹ (lMap Φ φ) := by
  simp [Rew.rewriteMap, lMap_rewrite, Function.comp_def]

end lMap

@[simp] lemma rew_open_iff {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} : (ω ▹ φ).Open ↔ φ.Open := by
  induction φ using Semiformula.rec' <;> simp [rew_rel, rew_nrel, *]

end Semiformula

end LO.FirstOrder
