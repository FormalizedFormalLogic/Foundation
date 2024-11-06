import Foundation.IntFO.Basic.Formula

namespace LO.FirstOrder

namespace Semiformulaᵢ

def rewAux ⦃n₁ n₂ : ℕ⦄ : Rew L ξ₁ n₁ ξ₂ n₂ → Semiformulaᵢ L ξ₁ n₁ → Semiformulaᵢ L ξ₂ n₂
  | _, ⊤        => ⊤
  | _, ⊥        => ⊥
  | ω, rel r v  => rel r (ω ∘ v)
  | ω, φ ⋏ ψ    => rewAux ω φ ⋏ rewAux ω ψ
  | ω, φ ⋎ ψ    => rewAux ω φ ⋎ rewAux ω ψ
  | ω, φ ➝ ψ    => rewAux ω φ ➝ rewAux ω ψ
  | ω, ∀' φ     => ∀' rewAux ω.q φ
  | ω, ∃' φ     => ∃' rewAux ω.q φ

def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformulaᵢ L ξ₁ n₁ →ˡᶜ Semiformulaᵢ L ξ₂ n₂ where
  toTr := rewAux ω
  map_top' := rfl
  map_bot' := rfl
  map_neg' := by simp [Semiformulaᵢ.neg_def, rewAux]
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_imply' := fun _ _ ↦ rfl

instance : Rewriting L (Semiformulaᵢ L) where
  app := rew
  app_all (_ _) := rfl
  app_ex (_ _) := rfl

lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω • rel r v = rel r fun i ↦ ω (v i) := rfl

lemma rew_rel' (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω • rel r v = rel r (ω ∘ v) := rfl

private lemma map_inj {n₁ n₂} {b : Fin n₁ → Fin n₂} {f : ξ₁ → ξ₂}
    (hb : Function.Injective b) (hf : Function.Injective f) : Function.Injective fun φ : Semiformulaᵢ L ξ₁ n₁ ↦ @Rew.map L ξ₁ ξ₂ n₁ n₂ b f • φ
  | ⊤,        φ => by cases φ using cases' <;> simp [rew_rel]
  | ⊥,        φ => by cases φ using cases' <;> simp [rew_rel]
  | rel r v,  φ => by
    cases φ using cases' <;> simp [rew_rel]
    case hRel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact Rew.map_inj hb hf (congr_fun h i)
  | φ ⋏ ψ,    χ => by
    cases χ using cases' <;> simp [rew_rel]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | φ ⋎ ψ,    χ => by
    cases χ using cases' <;> simp [rew_rel]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | φ ➝ ψ,    χ => by
    cases χ using cases' <;> simp [rew_rel]
    intro hp hq; exact ⟨map_inj hb hf hp, map_inj hb hf hq⟩
  | ∀' φ,     ψ => by
    cases ψ using cases' <;> simp [rew_rel, Rew.q_map]
    intro h; exact map_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h
  | ∃' φ,     ψ => by
    cases ψ using cases' <;> simp [rew_rel, Rew.q_map]
    intro h; exact map_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ ↦ (Fin.succ_ne_zero _).symm)) hf h

instance : LawfulRewriting L (Semiformulaᵢ L) where
  id_smul (φ) := by induction φ using rec' <;> simp [rew_rel, *]
  comp_smul {ξ₁ n₁ ξ₂ n₂ ξ₃ n₃ ω₁₂ ω₂₃ φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [rew_rel, Rew.comp_app, Rew.q_comp, *]
  smul_map_injective {n₁ n₂ ξ₁ ξ₂ b f hb hf} := map_inj hb hf

@[simp] lemma complexity_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaᵢ L ξ₁ n₁) : (ω • φ).complexity = φ.complexity := by
  induction φ using rec' generalizing n₂ <;> simp [*, rew_rel]

end Semiformulaᵢ

end LO.FirstOrder
