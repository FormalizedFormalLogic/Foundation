import Foundation.FirstOrder.Internal.Formula.Typed
import Foundation.FirstOrder.Internal.Term.Coding
import Mathlib.Combinatorics.Colex

open Encodable LO FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath

namespace LO

class LCWQIsoGoedelQuote (α β : ℕ → Type*) [LCWQ α] [LCWQ β] where
  gq : ∀ n, GoedelQuote (α n) (β n)
  top : ⌜(⊤ : α n)⌝ = (⊤ : β n)
  bot : ⌜(⊥ : α n)⌝ = (⊥ : β n)
  and (φ ψ : α n) : (⌜φ ⋏ ψ⌝ : β n) = ⌜φ⌝ ⋏ ⌜ψ⌝
  or (φ ψ : α n) : (⌜φ ⋎ ψ⌝ : β n) = ⌜φ⌝ ⋎ ⌜ψ⌝
  imply (φ ψ : α n) : (⌜φ ➝ ψ⌝ : β n) = ⌜φ⌝ ➝ ⌜ψ⌝
  neg (φ : α n) : (⌜∼φ⌝ : β n) = ∼⌜φ⌝
  all (φ : α (n + 1)) : (⌜∀' φ⌝ : β n) = ∀' ⌜φ⌝
  ex (φ : α (n + 1)) : (⌜∃' φ⌝ : β n) = ∃' ⌜φ⌝

namespace LCWQIsoGoedelQuote

attribute [simp] top bot and or imply neg all ex

variable {α β : ℕ → Type*} [LCWQ α] [LCWQ β] [LCWQIsoGoedelQuote α β]

instance (n : ℕ) : GoedelQuote (α n) (β n) := gq n

@[simp] lemma iff (φ ψ : α n) : (⌜φ ⭤ ψ⌝ : β n) = ⌜φ⌝ ⭤ ⌜ψ⌝ := by simp [LogicalConnective.iff]

@[simp] lemma ball (φ : α (n + 1)) (ψ : α (n + 1)) :
    (⌜∀[φ] ψ⌝ : β n)  = ∀[⌜φ⌝] ⌜ψ⌝ := by simp [LO.ball]

@[simp] lemma bex (φ : α (n + 1)) (ψ : α (n + 1)) :
    (⌜∃[φ] ψ⌝ : β n)  = ∃[⌜φ⌝] ⌜ψ⌝ := by simp [LO.bex]

end LCWQIsoGoedelQuote

end LO

namespace LO

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FirstOrder.Semiformula

variable (V) {n : ℕ}

noncomputable def typedQuote {n} : SyntacticSemiformula L n → Metamath.Semiformula V L n
  |  rel R v => Metamath.Semiformula.rel R fun i ↦ ⌜v i⌝
  | nrel R v => Metamath.Semiformula.nrel R fun i ↦ ⌜v i⌝
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.typedQuote ⋏ ψ.typedQuote
  |    φ ⋎ ψ => φ.typedQuote ⋎ ψ.typedQuote
  |     ∀' φ => ∀' φ.typedQuote
  |     ∃' φ => ∃' φ.typedQuote

variable {V}

lemma typedQuote_neg {n} (φ : SyntacticSemiformula L n) : (∼φ).typedQuote V = ∼(φ.typedQuote V) := by
  match φ with
  |  rel R v => simp [typedQuote]
  | nrel R v => simp [typedQuote]
  |        ⊤ => simp [typedQuote]
  |        ⊥ => simp [typedQuote]
  |    φ ⋏ ψ => simp [typedQuote, typedQuote_neg φ, typedQuote_neg ψ]
  |    φ ⋎ ψ => simp [typedQuote, typedQuote_neg φ, typedQuote_neg ψ]
  |     ∀' φ => simp [typedQuote, typedQuote_neg φ]
  |     ∃' φ => simp [typedQuote, typedQuote_neg φ]

noncomputable instance : LCWQIsoGoedelQuote (SyntacticSemiformula L) (Metamath.Semiformula V L) where
  gq _ := ⟨typedQuote V⟩
  top := rfl
  bot := rfl
  and _ _ := rfl
  or _ _ := rfl
  neg _ := by simpa [typedQuote] using typedQuote_neg _
  imply _ _ := by simpa [Metamath.Semiformula.imp_def, imp_eq, typedQuote] using typedQuote_neg _
  all _ := rfl
  ex _ := rfl

@[simp] lemma typed_quote_rel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : Metamath.Semiformula V L n) = Metamath.Semiformula.rel R fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma typed_quote_nrel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : Metamath.Semiformula V L n) = Metamath.Semiformula.nrel R fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma typed_quote_shift (φ : SyntacticSemiformula L n) :
    (⌜Rewriting.shift φ⌝ : Metamath.Semiformula V L n) = Metamath.Semiformula.shift ⌜φ⌝ := by
  induction φ using Semiformula.rec'
  case hrel => simp [rew_rel, *]; rfl
  case hnrel => simp [rew_nrel, *]; rfl
  case hverum => simp
  case hfalsum => simp
  case hand => simp [*]
  case hor => simp [*]
  case hall φ ih => simp [*]
  case hex φ ih => simp [*]

@[simp] lemma typed_quote_substs {n m} (w : Fin n → SyntacticSemiterm L m) (φ : SyntacticSemiformula L n) :
    (⌜φ ⇜ w⌝ : Metamath.Semiformula V L m) = Metamath.Semiformula.substs (fun i ↦ ⌜w i⌝) ⌜φ⌝ := by
  induction φ using Semiformula.rec' generalizing m
  case hrel => simp [rew_rel, *]; rfl
  case hnrel => simp [rew_nrel, *]; rfl
  case hverum => simp
  case hfalsum => simp
  case hand => simp [*]
  case hor => simp [*]
  case hall φ ih =>
    simp [*, Rew.q_substs, Matrix.comp_vecCons']; rfl
  case hex φ ih =>
    simp [*, Rew.q_substs, Matrix.comp_vecCons']; rfl

@[simp] lemma free_quote (φ : SyntacticSemiformula L 1) :
    (⌜Rewriting.free φ⌝ : Metamath.Formula V L) = Metamath.Semiformula.free ⌜φ⌝ := by
  rw [← LawfulSyntacticRewriting.app_substs_fbar_zero_comp_shift_eq_free, typed_quote_substs, typed_quote_shift]
  simp [Metamath.Semiformula.free, Matrix.constant_eq_singleton]

open InternalArithmetic

@[simp] lemma typed_quote_eq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t = !!u” : SyntacticSemiformula ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≐ ⌜u⌝) := rfl

@[simp] lemma typed_quote_ne (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≠ !!u” : SyntacticSemiformula ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≉ ⌜u⌝) := rfl

@[simp] lemma typed_quote_lt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t < !!u” : SyntacticSemiformula ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ <' ⌜u⌝) := rfl

@[simp] lemma typed_quote_nlt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≮ !!u” : SyntacticSemiformula ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≮' ⌜u⌝) := rfl

lemma ne_iff_val_ne (φ ψ : Metamath.Semiformula V L n) : φ ≠ ψ ↔ φ.val ≠ ψ.val := Iff.ne Semiformula.ext_iff

lemma typed_quote_inj {n} {φ₁ φ₂ : SyntacticSemiformula L n} : (⌜φ₁⌝ : Metamath.Semiformula V L n) = ⌜φ₂⌝ → φ₁ = φ₂ :=
  match φ₁, φ₂ with
  | rel R₁ v₁, rel R₂ v₂ => by
    simp only [typed_quote_rel, Metamath.Semiformula.rel, Semiformula.mk.injEq, qqRel_inj,
      Nat.cast_inj, rel.injEq, and_imp]
    rintro rfl
    simp only [quote_rel_inj, heq_eq_eq, true_and]
    rintro rfl
    suffices ((fun i ↦ ⌜v₁ i⌝) = fun i ↦ ⌜v₂ i⌝) → v₁ = v₂ by
      simpa [←SemitermVec.val_inj]
    intro h
    ext i
    exact Semiterm.typed_quote_inj (congr_fun h i)
  | nrel R₁ v₁, nrel R₂ v₂ => by
    simp only [typed_quote_nrel, Metamath.Semiformula.nrel, Semiformula.mk.injEq, qqNRel_inj,
      Nat.cast_inj, nrel.injEq, and_imp]
    rintro rfl
    simp only [quote_rel_inj, heq_eq_eq, true_and]
    rintro rfl
    suffices ((fun i ↦ ⌜v₁ i⌝) = fun i ↦ ⌜v₂ i⌝) → v₁ = v₂ by
      simpa [←SemitermVec.val_inj]
    intro h
    ext i
    exact Semiterm.typed_quote_inj (congr_fun h i)
  |         ⊤,         ⊤ => by simp
  |         ⊥,         ⊥ => by simp
  |   φ₁ ⋏ ψ₁,   φ₂ ⋏ ψ₂ => by
    simp only [LCWQIsoGoedelQuote.and, Metamath.Semiformula.and_inj, and_inj, and_imp]
    intro hφ hψ
    refine ⟨typed_quote_inj hφ, typed_quote_inj hψ⟩
  |   φ₁ ⋎ ψ₁,   φ₂ ⋎ ψ₂ => by
    simp only [LCWQIsoGoedelQuote.or, Metamath.Semiformula.or_inj, or_inj, and_imp]
    intro hφ hψ
    refine ⟨typed_quote_inj hφ, typed_quote_inj hψ⟩
  |     ∀' φ₁,     ∀' φ₂ => by
    simp only [LCWQIsoGoedelQuote.all, Metamath.Semiformula.all_inj, all_inj]
    exact typed_quote_inj
  |     ∃' φ₁,     ∃' φ₂ => by
    simp only [LCWQIsoGoedelQuote.ex, Metamath.Semiformula.ex_inj, ex_inj]
    exact typed_quote_inj
  | rel _ _, nrel _ _ | rel _ _, ⊤ | rel _ _, ⊥ | rel _ _, _ ⋏ _ | rel _ _, _ ⋎ _ | rel _ _, ∀' _ | rel _ _, ∃' _
  | nrel _ _, rel _ _ | nrel _ _, ⊤ | nrel _ _, ⊥ | nrel _ _, _ ⋏ _ | nrel _ _, _ ⋎ _ | nrel _ _, ∀' _ | nrel _ _, ∃' _
  | ⊤, rel _ _ | ⊤, nrel _ _ | ⊤, ⊥ | ⊤, _ ⋏ _ | ⊤, _ ⋎ _ | ⊤, ∀' _ | ⊤, ∃' _
  | ⊥, rel _ _ | ⊥, nrel _ _ | ⊥, ⊤ | ⊥, _ ⋏ _ | ⊥, _ ⋎ _ | ⊥, ∀' _ | ⊥, ∃' _
  | _ ⋏ _, rel _ _ | _ ⋏ _, nrel _ _ | _ ⋏ _, ⊤ | _ ⋏ _, ⊥ | _ ⋏ _, _ ⋎ _ | _ ⋏ _, ∀' _ | _ ⋏ _, ∃' _
  | _ ⋎ _, rel _ _ | _ ⋎ _, nrel _ _ | _ ⋎ _, ⊤ | _ ⋎ _, ⊥ | _ ⋎ _, _ ⋏ _ | _ ⋎ _, ∀' _ | _ ⋎ _, ∃' _
  | ∀' _, rel _ _ | ∀' _, nrel _ _ | ∀' _, ⊤ | ∀' _, ⊥ | ∀' _, _ ⋏ _ | ∀' _, _ ⋎ _ | ∀' _, ∃' _
  | ∃' _, rel _ _ | ∃' _, nrel _ _ | ∃' _, ⊤ | ∃' _, ⊥ | ∃' _, _ ⋏ _ | ∃' _, _ ⋎ _ | ∃' _, ∀' _ => by
    simp [ne_iff_val_ne, qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]

@[simp] lemma typed_quote_inj_iff {φ₁ φ₂ : SyntacticSemiformula L n} :
    (⌜φ₁⌝ : Metamath.Semiformula V L n) = ⌜φ₂⌝ ↔ φ₁ = φ₂ := ⟨typed_quote_inj, by rintro rfl; rfl⟩

noncomputable instance : GoedelQuote (SyntacticSemiformula L n) V where
  quote φ := (⌜φ⌝ : Metamath.Semiformula V L n).val

def quote_def (φ : SyntacticSemiformula L n) : (⌜φ⌝ : V) = (⌜φ⌝ : Metamath.Semiformula V L n).val := rfl

@[simp] lemma quote_rel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : V) = ^rel ↑k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Metamath.Semiterm V L n)) := rfl

@[simp] lemma quote_nrel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : V) = ^nrel ↑k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Metamath.Semiterm V L n)) := rfl

@[simp] lemma quote_verum : (⌜(⊤ : SyntacticSemiformula L n)⌝ : V) = ^⊤ := rfl

@[simp] lemma quote_falsum : (⌜(⊥ : SyntacticSemiformula L n)⌝ : V) = ^⊥ := rfl

@[simp] lemma quote_and (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋏ ψ⌝ : V) = ⌜φ⌝ ^⋏ ⌜ψ⌝ := rfl

@[simp] lemma quote_or (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋎ ψ⌝ : V) = ⌜φ⌝ ^⋎ ⌜ψ⌝ := rfl

@[simp] lemma quote_all (φ : SyntacticSemiformula L (n + 1)) : (⌜∀' φ⌝ : V) = ^∀ ⌜φ⌝ := rfl

@[simp] lemma quote_ex (φ : SyntacticSemiformula L (n + 1)) : (⌜∃' φ⌝ : V) = ^∃ ⌜φ⌝ := rfl

lemma quote_shift (φ : SyntacticSemiformula L n) :
    (⌜Rewriting.shift φ⌝ : V) = Metamath.shift L ⌜φ⌝ := by simp [quote_def]

lemma quote_eq_encode (φ : SyntacticSemiformula L n) : (⌜φ⌝ : V) = ↑(encode φ) := by
  suffices (⌜φ⌝ : Metamath.Semiformula V L n).val = ↑(encode φ) from this
  induction φ using rec'
  case hrel => simp [encode_rel, qqRel, coe_pair_eq_pair_coe, Semiterm.quote_eq_encode']; rfl
  case hnrel => simp [encode_nrel, qqNRel, coe_pair_eq_pair_coe, Semiterm.quote_eq_encode']; rfl
  case hverum => simp [encode_verum, qqVerum, coe_pair_eq_pair_coe]
  case hfalsum => simp [encode_falsum, qqFalsum, coe_pair_eq_pair_coe]
  case hand => simp [encode_and, qqAnd, coe_pair_eq_pair_coe,  *]; simp [encode_eq_toNat]
  case hor => simp [encode_or, qqOr, coe_pair_eq_pair_coe,  *]; simp [encode_eq_toNat]
  case hall => simp [encode_all, qqAll, coe_pair_eq_pair_coe, *]; simp [encode_eq_toNat]
  case hex => simp [encode_ex, qqEx, coe_pair_eq_pair_coe, *]; simp [encode_eq_toNat]

lemma coe_quote_eq_quote (φ : SyntacticSemiformula L n) : (↑(⌜φ⌝ : ℕ) : V) = ⌜φ⌝ := by
  simp [quote_eq_encode]

@[simp] lemma quote_inj_iff {φ₁ φ₂ : SyntacticSemiformula L n} :
    (⌜φ₁⌝ : V) = ⌜φ₂⌝ ↔ φ₁ = φ₂ := by simp [quote_eq_encode]

noncomputable instance : LCWQIsoGoedelQuote (Semisentence L) (Metamath.Semiformula V L) where
  gq n := ⟨fun σ ↦ (⌜(Rewriting.embedding σ : SyntacticSemiformula L n)⌝)⟩
  top := by simp
  bot := by simp
  and _ _ := by simp
  or _ _ := by simp
  neg _ := by simp
  imply _ _ := by simp
  all _ := by simp
  ex _ := by simp

def empty_typed_quote_def (σ : Semisentence L n) :
    (⌜σ⌝ : Metamath.Semiformula V L n) = ⌜(Rewriting.embedding σ : SyntacticSemiformula L n)⌝ := rfl

@[simp] lemma empty_typed_quote_eq (t u : Semiterm ℒₒᵣ Empty n) :
    (⌜(“!!t = !!u” : Semisentence ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≐ ⌜u⌝) := rfl

@[simp] lemma empty_typed_quote_ne (t u : Semiterm ℒₒᵣ Empty n) :
    (⌜(“!!t ≠ !!u” : Semisentence ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≉ ⌜u⌝) := rfl

@[simp] lemma empty_typed_quote_lt (t u : Semiterm ℒₒᵣ Empty n) :
    (⌜(“!!t < !!u” : Semisentence ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ <' ⌜u⌝) := rfl

@[simp] lemma empty_typed_quote_nlt (t u : Semiterm ℒₒᵣ Empty n) :
    (⌜(“!!t ≮ !!u” : Semisentence ℒₒᵣ n)⌝ : Metamath.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≮' ⌜u⌝) := rfl

noncomputable instance : GoedelQuote (Semisentence L n) V where
  quote σ := ⌜(Rewriting.embedding σ : SyntacticSemiformula L n)⌝

lemma empty_quote_def (σ : Semisentence L n) : (⌜σ⌝ : V) = ⌜(Rewriting.embedding σ : SyntacticSemiformula L n)⌝ := rfl

def empty_quote_eq (σ : Semisentence L n) : (⌜σ⌝ : V) = (⌜σ⌝ : Metamath.Semiformula V L n).val := rfl

lemma empty_quote_eq_encode (σ : Semisentence L n) : (⌜σ⌝ : V) = ↑(encode σ) := by simp [empty_quote_def, quote_eq_encode]

lemma coe_empty_quote_eq_quote (σ : Semisentence L n) : (↑(⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  simp [empty_quote_eq_encode]

@[simp] lemma val_empty_quote {ξ n e ε} (σ : Semisentence L n) :
    Semiterm.valm V e ε (⌜σ⌝ : Semiterm ℒₒᵣ ξ m) = ⌜σ⌝ := by
  simp [goedelNumber'_def, empty_quote_eq_encode, numeral_eq_natCast]

@[simp] lemma coe_quote {ξ n} (φ : SyntacticSemiformula L n) : ↑(⌜φ⌝ : ℕ) = (⌜φ⌝ : Semiterm ℒₒᵣ ξ m) := by
  simp [goedelNumber'_def, quote_eq_encode]

@[simp] lemma coe_empty_quote {ξ n} (σ : Semisentence L n) : ↑(⌜σ⌝ : ℕ) = (⌜σ⌝ : Semiterm ℒₒᵣ ξ m) := by
  simp [goedelNumber'_def, empty_quote_eq_encode]

@[simp] lemma quote_quote_eq_numeral (φ : SyntacticSemiformula L n) :
    (⌜(⌜φ⌝ : Semiterm ℒₒᵣ ℕ m)⌝ : Metamath.Semiterm V ℒₒᵣ m) = InternalArithmetic.typedNumeral ⌜φ⌝ := by
  simp [←coe_quote, coe_quote_eq_quote]

@[simp] lemma empty_quote_quote_eq_numeral (σ : Semisentence L n) :
    (⌜(⌜σ⌝ : Semiterm ℒₒᵣ ℕ m)⌝ : Metamath.Semiterm V ℒₒᵣ m) = InternalArithmetic.typedNumeral ⌜σ⌝ := by
  simp [←coe_empty_quote, coe_empty_quote_eq_quote]

@[simp] lemma empty_quote_inj_iff {σ₁ σ₂ : Semisentence L n} :
    (⌜σ₁⌝ : V) = ⌜σ₂⌝ ↔ σ₁ = σ₂ := by simp [empty_quote_eq_encode]

end Semiformula

end FirstOrder

namespace ISigma1.Metamath

open Encodable FirstOrder

lemma IsSemiformula.sound {n φ : ℕ} (h : IsSemiformula L n φ) : ∃ F : FirstOrder.SyntacticSemiformula L n, ⌜F⌝ = φ := by
  induction φ using Nat.strongRec generalizing n
  case ind φ ih =>
    rcases IsSemiformula.case_iff.mp h with
      (⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
       ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, hp, rfl⟩ | ⟨φ, hp, rfl⟩)
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨FirstOrder.Semiformula.rel R v', ?_⟩
      suffices SemitermVec.val (fun i ↦ ⌜v' i⌝) = v by simpa [Semiformula.quote_rel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        (SemitermVec.val fun i ↦ ⌜v' i⌝).[i] = (SemitermVec.val fun i ↦ ⌜v' i⌝).[↑j] := rfl
        _                                    = ⌜v' j⌝ := by
          simpa [Semiterm.quote_def] using SemitermVec.val_nth_eq (fun i ↦ (⌜v' i⌝ : Metamath.Semiterm ℕ L n)) j
        _                                    = v.[i] := hv' j
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨FirstOrder.Semiformula.nrel R v', ?_⟩
      suffices SemitermVec.val (fun i ↦ ⌜v' i⌝) = v by simpa [Semiformula.quote_nrel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        (SemitermVec.val fun i ↦ ⌜v' i⌝).[i] = (SemitermVec.val fun i ↦ ⌜v' i⌝).[↑j] := rfl
        _                                    = ⌜v' j⌝ := by
          simpa [Semiterm.quote_def] using SemitermVec.val_nth_eq (fun i ↦ (⌜v' i⌝ : Metamath.Semiterm ℕ L n)) j
        _                                    = v.[i] := hv' j
    · exact ⟨⊤, by simp⟩
    · exact ⟨⊥, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋏ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋎ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∀' φ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∃' φ, by simp⟩

end ISigma1.Metamath

end LO
