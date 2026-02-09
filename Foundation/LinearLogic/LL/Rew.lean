module

public import Foundation.LinearLogic.LL.Formula

@[expose] public section

namespace LO.FirstOrder

namespace Semiformulaₗ

def rewAux (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformulaₗ L ξ₁ n₁ → Semiformulaₗ L ξ₂ n₂
  |  rel r v => rel r (ω ∘ v)
  | nrel r v => nrel r (ω ∘ v)
  |        1 => 1
  |        ⊥ => ⊥
  |    φ ⨂ ψ => rewAux ω φ ⨂ rewAux ω ψ
  |    φ ⅋ ψ => rewAux ω φ ⅋ rewAux ω ψ
  |        ⊤ => ⊤
  |        0 => 0
  |    φ ＆ ψ => rewAux ω φ ＆ rewAux ω ψ
  |    φ ⨁ ψ => rewAux ω φ ⨁ rewAux ω ψ
  |       ！φ => ！rewAux ω φ
  |       ？φ => ？rewAux ω φ
  |     ∀' φ => ∀' rewAux ω.q φ
  |     ∃' φ => ∃' rewAux ω.q φ

lemma rewAux_neg (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaₗ L ξ₁ n₁) :
    rewAux ω (∼φ) = ∼rewAux ω φ := by
  induction φ using rec' generalizing n₂ <;> simp [rewAux, *]

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformulaₗ L ξ₁ n₁ →ˡᶜ Semiformulaₗ L ξ₂ n₂ where
  toTr := rewAux ω
  map_top' := rfl
  map_bot' := rfl
  map_neg' := by simp [rewAux_neg]
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_imply' := fun _ _ ↦ by simp [imply_def', rewAux, rewAux_neg]

instance : Rewriting L ξ (Semiformulaₗ L ξ) ζ (Semiformulaₗ L ζ) where
  app := rew
  app_all (_ _) := rfl
  app_ex (_ _) := rfl

instance : Coe (Semisentenceₗ L n) (Semistatementₗ L n) := ⟨Rewriting.emb (ξ := ℕ)⟩

lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ rel r v = rel r fun i ↦ ω (v i) := rfl

lemma rew_rel' (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ rel r v = rel r (ω ∘ v) := rfl

lemma rew_nrel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ nrel r v = nrel r fun i ↦ ω (v i) := rfl

@[simp] lemma rew_one (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω ▹ (1 : Semiformulaₗ L ξ₁ n₁) = 1 := rfl

@[simp] lemma rew_falsum (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω ▹ (⊥ : Semiformulaₗ L ξ₁ n₁) = ⊥ := rfl

@[simp] lemma rew_tensor (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ ψ : Semiformulaₗ L ξ₁ n₁) :
    ω ▹ (φ ⨂ ψ) = (ω ▹ φ) ⨂ (ω ▹ ψ) := rfl

@[simp] lemma rew_par (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ ψ : Semiformulaₗ L ξ₁ n₁) :
    ω ▹ (φ ⅋ ψ) = (ω ▹ φ) ⅋ (ω ▹ ψ) := rfl

@[simp] lemma rew_verum (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω ▹ (⊤ : Semiformulaₗ L ξ₁ n₁) = ⊤ := rfl

@[simp] lemma rew_zero (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω ▹ (0 : Semiformulaₗ L ξ₁ n₁) = 0 := rfl

@[simp] lemma rew_with (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ ψ : Semiformulaₗ L ξ₁ n₁) :
    ω ▹ (φ ＆ ψ) = (ω ▹ φ) ＆ (ω ▹ ψ) := rfl

@[simp] lemma rew_plus (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ ψ : Semiformulaₗ L ξ₁ n₁) :
    ω ▹ (φ ⨁ ψ) = (ω ▹ φ) ⨁ (ω ▹ ψ) := rfl

@[simp] lemma rew_bang (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaₗ L ξ₁ n₁) :
    ω ▹ ！φ = ！(ω ▹ φ) := rfl

@[simp] lemma rew_quest (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaₗ L ξ₁ n₁) :
    ω ▹ ？φ = ？(ω ▹ φ) := rfl

private lemma map_inj {b : Fin n₁ → Fin n₂} {f : ξ₁ → ξ₂}
    (hb : Function.Injective b) (hf : Function.Injective f) :
    Function.Injective fun φ : Semiformulaₗ L ξ₁ n₁ ↦ @Rew.map L ξ₁ ξ₂ n₁ n₂ b f ▹ φ
  | rel r v => fun φ ↦
    match φ with
    | rel s w => by
      simp only [rew_rel, rel.injEq, and_imp]
      rintro rfl; simp only [heq_eq_eq, true_and]; rintro rfl h; simp only [true_and]
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
    | nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | nrel r v => fun φ ↦
    match φ with
    | nrel s w => by
      simp only [rew_nrel, nrel.injEq, and_imp]
      rintro rfl; simp only [heq_eq_eq, true_and]; rintro rfl h; simp only [true_and]
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
    | rel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | 1 => by intro φ; cases φ using cases' <;> simp [rew_rel, rew_nrel]
  | ⊥ => by intro φ; cases φ using cases' <;> simp [rew_rel, rew_nrel]
  | φ ⨂ ψ => fun χ ↦
    match χ with
    | _ ⨂ _ => by simpa using fun hp hq ↦ ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | φ ⅋ ψ => fun χ ↦
    match χ with
    | _ ⅋ _ => by simpa using fun hp hq ↦ ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⨂ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | ⊤ => by intro φ; cases φ using cases' <;> simp [rew_rel, rew_nrel]
  | 0 => by intro φ; cases φ using cases' <;> simp [rew_rel, rew_nrel]
  | φ ＆ ψ => fun χ ↦
    match χ with
    | _ ＆ _ => by simpa using fun hp hq ↦ ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ⨁ _ | ！_ | ？_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | φ ⨁ ψ => fun χ ↦
    match χ with
    | _ ⨁ _ => by simpa using fun hp hq ↦ ⟨map_inj hb hf hp, map_inj hb hf hq⟩
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | ！_ | ？_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | ！φ => fun ψ ↦
    match ψ with
    | ！_ => by simpa using fun hp ↦ map_inj hb hf hp
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ？_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | ？φ => fun ψ ↦
    match ψ with
    | ？_ => by simpa using fun hp ↦ map_inj hb hf hp
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ∀' _ | ∃' _ => by simp [rew_rel, rew_nrel]
  | ∀' φ => fun ψ ↦
    match ψ with
    | ∀' _ => by
      simp only [Rewriting.app_all, Rew.q_map, Nat.succ_eq_add_one, all_inj]
      exact fun h ↦ map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∃' _ => by simp [rew_rel, rew_nrel]
  | ∃' φ => fun ψ ↦
    match ψ with
    | ∃' _ => by
      simp only [Rewriting.app_ex, Rew.q_map, Nat.succ_eq_add_one, ex_inj]
      exact fun h ↦ map_inj (b := 0 :> Fin.succ ∘ b)
        (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
    | rel _ _ | nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀' _ => by simp [rew_rel, rew_nrel]

instance : ReflectiveRewriting L ξ (Semiformulaₗ L ξ) where
  id_app (φ) := by induction φ using rec' <;> simp [rew_rel, rew_nrel, *]

instance : TransitiveRewriting L ξ₁ (Semiformulaₗ L ξ₁) ξ₂ (Semiformulaₗ L ξ₂) ξ₃ (Semiformulaₗ L ξ₃) where
  comp_app {n₁ n₂ n₃ ω₁₂ ω₂₃ φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [rew_rel, rew_nrel, Rew.comp_app, Rew.q_comp, *]

instance : InjMapRewriting L ξ (Semiformulaₗ L ξ) ζ (Semiformulaₗ L ζ) where
  smul_map_injective := map_inj

instance : LawfulSyntacticRewriting L (Semistatementₗ L) where

@[simp] lemma complexity_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaₗ L ξ₁ n₁) : (ω ▹ φ).complexity = φ.complexity := by
  induction φ using rec' generalizing n₂ <;> simp [*, rew_rel, rew_nrel]

end Semiformulaₗ

end LO.FirstOrder
