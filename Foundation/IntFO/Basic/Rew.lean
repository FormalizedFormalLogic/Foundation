import Foundation.IntFO.Basic.Formula

namespace LO.FirstOrder


namespace Rew

open Semiformulaᵢ

variable
  {L L₁ L₂ L₃ : Language} {ξ ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def loMapᵢ ⦃n₁ n₂ : ℕ⦄ : Rew L ξ₁ n₁ ξ₂ n₂ → Semiformulaᵢ L ξ₁ n₁ → Semiformulaᵢ L ξ₂ n₂
  | _, ⊤        => ⊤
  | _, ⊥        => ⊥
  | ω, rel r v  => rel r (ω ∘ v)
  | ω, φ ⋏ ψ    => ω.loMapᵢ φ ⋏ ω.loMapᵢ ψ
  | ω, φ ⋎ ψ    => ω.loMapᵢ φ ⋎ ω.loMapᵢ ψ
  | ω, φ ➝ ψ    => ω.loMapᵢ φ ➝ ω.loMapᵢ ψ
  | ω, ∀' φ     => ∀' ω.q.loMapᵢ φ
  | ω, ∃' φ     => ∃' ω.q.loMapᵢ φ

section

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

lemma ext_loMapᵢ' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (φ : Semiformulaᵢ L ξ₁ n₁) : ω₁.loMapᵢ φ = ω₂.loMapᵢ φ:= by simp[h]

def homᵢ (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformulaᵢ L ξ₁ n₁ →ˡᶜ Semiformulaᵢ L ξ₂ n₂ where
  toTr := loMapᵢ ω
  map_top' := rfl
  map_bot' := rfl
  map_neg' := by simp [Semiformulaᵢ.neg_def, loMapᵢ]
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_imply' := fun _ _ ↦ rfl

/-
instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiformula L ξ₁ n₁) (fun _ => Semiformula L ξ₂ n₂) where
  coe := fun ω => loMap ω
  coe_injective' := fun ω₁ ω₂ h => ext_loMap ω₁ ω₂ (congr_fun h)

instance : CoeFun (Rew L ξ₁ n₁ ξ₂ n₂) (fun _ => Semiformula L ξ₁ n₁ → Semiformula L ξ₂ n₂) := FunLike.hasCoeToFun

scoped[FirstOrder] notation:max ω "ᵀ" => (ω : Semiterm _ _ _ → Semiterm _ _ _)

scoped[FirstOrder] notation:max ω "ᴾ" => (ω : Semiformula _ _ _ → Semiformula _ _ _)

lemma neg' (φ : Semiformula L ξ₁ n₁) : ω (∼φ) = ∼ω φ := loMap_neg ω φ

lemma or' (φ ψ : Semiformula L ξ₁ n₁) : ω (φ ⋎ ψ) = ω φ ⋎ ω ψ := by rfl

instance : LogicalConnective.homClass (Rew L ξ₁ n₁ ξ₂ n₂) (Semiformula L ξ₁ n₁) (Semiformula L ξ₂ n₂) where
  map_top := fun ω => by rfl
  map_bot := fun ω => by rfl
  map_neg := loMap_neg
  map_and := fun ω φ ψ => by rfl
  map_or := fun ω φ ψ => by rfl
  map_imply := fun ω φ ψ => by simp[Semiformula.imp_eq, neg', or']

-/

lemma homᵢ_eq_loMapᵢ : ω.homᵢ = ω.loMapᵢ := rfl

protected lemma homᵢ_rel {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω.homᵢ (rel r v) = rel r (fun i ↦ ω (v i)) := rfl

lemma homᵢ_rel' {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω.homᵢ (rel r v) = rel r (ω ∘ v) := by rfl

@[simp] protected lemma homᵢ_all {φ : Semiformulaᵢ L ξ₁ (n₁ + 1)} :
    ω.homᵢ (∀' φ) = ∀' ω.q.homᵢ φ := by rfl

@[simp] protected lemma homᵢ_ex {φ : Semiformulaᵢ L ξ₁ (n₁ + 1)} :
    ω.homᵢ (∃' φ) = ∃' ω.q.homᵢ φ := by rfl

@[simp] protected lemma homᵢ_ball {φ ψ : Semiformulaᵢ L ξ₁ (n₁ + 1)} :
    ω.homᵢ (∀[φ] ψ) = ∀[ω.q.homᵢ φ] ω.q.homᵢ ψ := by simp [LogicalConnective.ball]

@[simp] protected lemma homᵢ_bex {φ ψ : Semiformulaᵢ L ξ₁ (n₁ + 1)} :
    ω.homᵢ (∃[φ] ψ) = ∃[ω.q.homᵢ φ] ω.q.homᵢ ψ := by simp [LogicalConnective.bex]

attribute [irreducible] homᵢ

@[simp] lemma complexity_homᵢ (φ : Semiformulaᵢ L ξ₁ n₁) : (ω.homᵢ φ).complexity = φ.complexity := by
  induction φ using Semiformulaᵢ.rec' generalizing n₂ <;> simp [*, Rew.homᵢ_rel]

end

@[simp] lemma homᵢ_id_eq : (Rew.id.homᵢ : Semiformulaᵢ L ξ n →ˡᶜ Semiformulaᵢ L ξ n) = LogicalConnective.Hom.id := by
  ext φ; induction φ using Semiformulaᵢ.rec' <;> simp [Rew.homᵢ_rel, *]

lemma homᵢ_comp_eq (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) : (ω₂.comp ω₁).homᵢ = ω₂.homᵢ.comp ω₁.homᵢ := by
  ext φ; simp; induction φ using Semiformulaᵢ.rec' generalizing n₂ n₃ <;> simp[Rew.homᵢ_rel, comp_app, q_comp, *]

lemma homᵢ_comp_app (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformulaᵢ L ξ₁ n₁) :
    (ω₂.comp ω₁).homᵢ φ = ω₂.homᵢ (ω₁.homᵢ φ) := by simp [homᵢ_comp_eq]

lemma eq_self_of_eq_idᵢ {ω : Rew L ξ n ξ n} (h : ω = Rew.id) {φ} : ω.homᵢ φ = φ := by rcases h; simp

lemma homᵢ_map_inj {n₁ n₂ ξ₁ ξ₂} {b : Fin n₁ → Fin n₂} {e : ξ₁ → ξ₂}
    (hb : Function.Injective b) (hf : Function.Injective e) : Function.Injective $ (map (L := L) b e).homᵢ
  | ⊤,        φ => by cases φ using cases' <;> simp [Rew.homᵢ_rel]
  | ⊥,        φ => by cases φ using cases' <;> simp [Rew.homᵢ_rel]
  | rel r v,  φ => by
    cases φ using cases' <;> simp [Rew.homᵢ_rel]
    case hRel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb hf (congr_fun h i)
  | φ ⋏ ψ,    χ => by
    cases χ using cases' <;> simp [Rew.homᵢ_rel]
    intro hp hq; exact ⟨homᵢ_map_inj hb hf hp, homᵢ_map_inj hb hf hq⟩
  | φ ⋎ ψ,    χ => by
    cases χ using cases' <;> simp [Rew.homᵢ_rel]
    intro hp hq; exact ⟨homᵢ_map_inj hb hf hp, homᵢ_map_inj hb hf hq⟩
  | φ ➝ ψ,    χ => by
    cases χ using cases' <;> simp [Rew.homᵢ_rel]
    intro hp hq; exact ⟨homᵢ_map_inj hb hf hp, homᵢ_map_inj hb hf hq⟩
  | ∀' φ,     ψ => by
    cases ψ using cases' <;> simp[Rew.homᵢ_rel, q_map]
    intro h; exact homᵢ_map_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ => (Fin.succ_ne_zero _).symm)) hf h
  | ∃' φ,     ψ => by
    cases ψ using cases' <;> simp[Rew.homᵢ_rel, q_map]
    intro h; exact homᵢ_map_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb) (fun _ => (Fin.succ_ne_zero _).symm)) hf h

lemma emb.homᵢ_injective {o} [e : IsEmpty o] : Function.Injective (emb.homᵢ : Semiformulaᵢ L o n → Semiformulaᵢ L ξ n) :=
  homᵢ_map_inj Function.injective_id (IsEmpty.elim e)

lemma shift.homᵢ_injective : Function.Injective (shift.homᵢ : SyntacticSemiformulaᵢ L n → SyntacticSemiformulaᵢ L n) :=
  homᵢ_map_inj Function.injective_id Nat.succ_injective

@[simp] lemma homᵢ_fix_free (φ : SyntacticSemiformulaᵢ L (n + 1)) :
    fix.homᵢ (free.homᵢ φ) = φ := by simp [←homᵢ_comp_app]

@[simp] lemma homᵢ_free_fix (φ : SyntacticSemiformulaᵢ L n) :
    free.homᵢ (fix.homᵢ φ) = φ := by simp [←homᵢ_comp_app]

@[simp] lemma homᵢ_substs_mbar_zero_comp_shift_eq_free (φ : SyntacticSemiformulaᵢ L 1) :
    (substs ![&0]).homᵢ (Rew.shift.homᵢ φ) = free.homᵢ φ := by simp [←homᵢ_comp_app, substs_mbar_zero_comp_shift_eq_free]

end Rew

scoped syntax (name := substsHomNotationI) term:max "/[" term,* "]ⁱ" : term

scoped macro_rules (kind := substsHomNotationI)
  | `($φ:term /[$terms:term,*]ⁱ) => `((Rew.substs ![$terms,*]).homᵢ $φ)

namespace Semiformulaᵢ

variable {L : Language} {ξ : Type*} {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

@[coe] abbrev embedding (σ : Semisentenceᵢ L n) : SyntacticSemiformulaᵢ L n := Rew.emb.homᵢ σ

instance : Coe (Semisentenceᵢ L n) (SyntacticSemiformulaᵢ L n) := ⟨embedding⟩

@[simp] lemma embedding_inj (σ π : Semisentenceᵢ L n) : (σ : SyntacticSemiformulaᵢ L n) = π ↔ σ = π := Rew.emb.homᵢ_injective.eq_iff

lemma coe_substs_eq_substs_coe (σ : Semisentenceᵢ L k) (v : Fin k → Semiterm L Empty n) :
    (((Rew.substs v).homᵢ σ) : SyntacticSemiformulaᵢ L n) =
    (Rew.substs (fun x ↦ Rew.emb (v x))).homᵢ (↑σ : SyntacticSemiformulaᵢ L k) := by
  simp only [embedding, ← Rew.homᵢ_comp_app]; congr 2
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

lemma coe_substs_eq_substs_coe₁ (σ : Semisentenceᵢ L 1) (t : Semiterm L Empty n) :
    (σ/[t]ⁱ : SyntacticSemiformulaᵢ L n) =
    (↑σ : SyntacticSemiformulaᵢ L 1)/[(↑t : Semiterm L ℕ n)]ⁱ := by
  simpa [Matrix.constant_eq_singleton] using coe_substs_eq_substs_coe σ ![t]

def shiftEmb : SyntacticSemiformulaᵢ L n ↪ SyntacticSemiformulaᵢ L n where
  toFun := Rew.shift.homᵢ
  inj' := Rew.shift.homᵢ_injective

lemma shiftEmb_eq_shift (φ : SyntacticSemiformulaᵢ L n) :
  shiftEmb φ = Rew.shift.homᵢ φ := rfl

end Semiformulaᵢ

end LO.FirstOrder
