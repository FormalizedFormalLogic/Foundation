module

public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Typed
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Coding

@[expose] public section
open Encodable FFL FirstOrder Arithmetic Bootstrapping

namespace FFL

class LCWQIsoGödelQuote (α β : ℕ → Type*) [LCWQ α] [LCWQ β] where
  gq : ∀ n, GödelQuote (α n) (β n)
  top {n} : ⌜(⊤ : α n)⌝ = (⊤ : β n)
  bot {n} : ⌜(⊥ : α n)⌝ = (⊥ : β n)
  and {n} (φ ψ : α n) : (⌜φ ⋏ ψ⌝ : β n) = ⌜φ⌝ ⋏ ⌜ψ⌝
  or {n} (φ ψ : α n) : (⌜φ ⋎ ψ⌝ : β n) = ⌜φ⌝ ⋎ ⌜ψ⌝
  imply {n} (φ ψ : α n) : (⌜φ 🡒 ψ⌝ : β n) = ⌜φ⌝ 🡒 ⌜ψ⌝
  neg {n} (φ : α n) : (⌜∼φ⌝ : β n) = ∼⌜φ⌝
  all {n} (φ : α (n + 1)) : (⌜∀¹ φ⌝ : β n) = ∀¹ ⌜φ⌝
  exs {n} (φ : α (n + 1)) : (⌜∃¹ φ⌝ : β n) = ∃¹ ⌜φ⌝

namespace LCWQIsoGödelQuote

attribute [simp] top bot and or imply neg all exs

variable {α β : ℕ → Type*} [LCWQ α] [LCWQ β] [LCWQIsoGödelQuote α β] {n : ℕ}

instance (n : ℕ) : GödelQuote (α n) (β n) := gq n

@[simp] lemma iff (φ ψ : α n) : (⌜φ 🡘 ψ⌝ : β n) = ⌜φ⌝ 🡘 ⌜ψ⌝ := by simp [LogicalConnective.iff]

@[simp] lemma ball (φ : α (n + 1)) (ψ : α (n + 1)) :
    (⌜∀¹[φ] ψ⌝ : β n)  = ∀¹[⌜φ⌝] ⌜ψ⌝ := by simp [FFL.FirstOrder.ball]

@[simp] lemma bexs (φ : α (n + 1)) (ψ : α (n + 1)) :
    (⌜∃¹[φ] ψ⌝ : β n)  = ∃¹[⌜φ⌝] ⌜ψ⌝ := by simp [FFL.FirstOrder.bexs]

end LCWQIsoGödelQuote

end FFL

namespace FFL

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FirstOrder.Semiformula

variable (V) {n : ℕ}

noncomputable def typedQuote {n} : Semiproposition L n → Bootstrapping.Semiformula V L n
  |  rel R v => Bootstrapping.Semiformula.rel R fun i ↦ ⌜v i⌝
  | nrel R v => Bootstrapping.Semiformula.nrel R fun i ↦ ⌜v i⌝
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.typedQuote ⋏ ψ.typedQuote
  |    φ ⋎ ψ => φ.typedQuote ⋎ ψ.typedQuote
  |     ∀¹ φ => ∀¹ φ.typedQuote
  |     ∃¹ φ => ∃¹ φ.typedQuote

variable {V}

lemma typedQuote_neg {n} (φ : Semiproposition L n) : (∼φ).typedQuote V = ∼(φ.typedQuote V) := by
  match φ with
  |  rel R v => simp [typedQuote]
  | nrel R v => simp [typedQuote]
  |        ⊤ => simp [typedQuote]
  |        ⊥ => simp [typedQuote]
  |    φ ⋏ ψ => simp [typedQuote, typedQuote_neg φ, typedQuote_neg ψ]
  |    φ ⋎ ψ => simp [typedQuote, typedQuote_neg φ, typedQuote_neg ψ]
  |     ∀¹ φ => simp [typedQuote, typedQuote_neg φ]
  |     ∃¹ φ => simp [typedQuote, typedQuote_neg φ]

noncomputable instance : LCWQIsoGödelQuote (Semiproposition L) (Bootstrapping.Semiformula V L) where
  gq _ := ⟨typedQuote V⟩
  top := rfl
  bot := rfl
  and _ _ := rfl
  or _ _ := rfl
  neg _ := by simpa [typedQuote] using! typedQuote_neg _
  imply _ _ := by
    simpa [Bootstrapping.Semiformula.imp_def, imp_eq, typedQuote] using! typedQuote_neg _
  all _ := rfl
  exs _ := rfl

@[simp] lemma typed_quote_rel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : Bootstrapping.Semiformula V L n) =
      Bootstrapping.Semiformula.rel R fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma typed_quote_nrel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : Bootstrapping.Semiformula V L n) =
      Bootstrapping.Semiformula.nrel R fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma typed_quote_shift (φ : Semiproposition L n) :
    (⌜Rewriting.shift φ⌝ : Bootstrapping.Semiformula V L n) =
      Bootstrapping.Semiformula.shift ⌜φ⌝ := by
  induction φ using Semiformula.rec'
  case hrel => simp [*]; rfl
  case hnrel => simp [*]; rfl
  case hverum => simp
  case hfalsum => simp
  case hand => simp [*]
  case hor => simp [*]
  case hall φ ih => simp [*]
  case hexs φ ih => simp [*]

@[simp] lemma typed_quote_substs {n m} (w : Fin n → SyntacticSemiterm L m)
    (φ : Semiproposition L n) :
    (⌜φ ⇜ w⌝ : Bootstrapping.Semiformula V L m) =
      Bootstrapping.Semiformula.subst (fun i ↦ ⌜w i⌝) ⌜φ⌝ := by
  induction φ using Semiformula.rec' generalizing m
  case hrel => simp [*]; rfl
  case hnrel => simp [*]; rfl
  case hverum => simp
  case hfalsum => simp
  case hand => simp [*]
  case hor => simp [*]
  case hall φ ih =>
    simp [*, Rew.q_subst, Matrix.comp_vecCons']; rfl
  case hexs φ ih =>
    simp [*, Rew.q_subst, Matrix.comp_vecCons']; rfl

@[simp] lemma free_quote (φ : Semiproposition L 1) :
    (⌜Rewriting.free φ⌝ : Bootstrapping.Formula V L) = Bootstrapping.Semiformula.free ⌜φ⌝ := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free, typed_quote_substs,
    typed_quote_shift]
  simp [Bootstrapping.Semiformula.free, Matrix.constant_eq_singleton]

open Bootstrapping.Arithmetic

@[simp] lemma typed_quote_eq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t = !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ ≐ ⌜u⌝) := rfl

@[simp] lemma typed_quote_ne (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≠ !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ ≉ ⌜u⌝) := rfl

@[simp] lemma typed_quote_lt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t < !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ <' ⌜u⌝) := rfl

@[simp] lemma typed_quote_nlt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≮ !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ ≮' ⌜u⌝) := rfl

lemma ne_iff_val_ne (φ ψ : Bootstrapping.Semiformula V L n) : φ ≠ ψ ↔ φ.val ≠ ψ.val :=
  Iff.ne Semiformula.ext_iff

lemma typed_quote_inj {n} {φ₁ φ₂ : Semiproposition L n} :
    (⌜φ₁⌝ : Bootstrapping.Semiformula V L n) = ⌜φ₂⌝ → φ₁ = φ₂ :=
  match φ₁, φ₂ with
  | rel R₁ v₁, rel R₂ v₂ => by
    simp only [typed_quote_rel, Bootstrapping.Semiformula.rel, Semiformula.mk.injEq, qqRel_inj,
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
    simp only [typed_quote_nrel, Bootstrapping.Semiformula.nrel, Semiformula.mk.injEq, qqNRel_inj,
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
    simp only [LCWQIsoGödelQuote.and, Bootstrapping.Semiformula.and_inj, and_inj, and_imp]
    intro hφ hψ
    refine ⟨typed_quote_inj hφ, typed_quote_inj hψ⟩
  |   φ₁ ⋎ ψ₁,   φ₂ ⋎ ψ₂ => by
    simp only [LCWQIsoGödelQuote.or, Bootstrapping.Semiformula.or_inj, or_inj, and_imp]
    intro hφ hψ
    refine ⟨typed_quote_inj hφ, typed_quote_inj hψ⟩
  |     ∀¹ φ₁,     ∀¹ φ₂ => by
    simp only [LCWQIsoGödelQuote.all, Bootstrapping.Semiformula.all_inj, all_inj]
    exact typed_quote_inj
  |     ∃¹ φ₁,     ∃¹ φ₂ => by
    simp only [LCWQIsoGödelQuote.exs, Bootstrapping.Semiformula.exs_inj, exs_inj]
    exact typed_quote_inj
  | rel _ _, nrel _ _ | rel _ _, ⊤ | rel _ _, ⊥ | rel _ _, _ ⋏ _ | rel _ _, _ ⋎ _
    | rel _ _, ∀¹ _ | rel _ _, ∃¹ _
  | nrel _ _, rel _ _ | nrel _ _, ⊤ | nrel _ _, ⊥ | nrel _ _, _ ⋏ _ | nrel _ _, _ ⋎ _
    | nrel _ _, ∀¹ _ | nrel _ _, ∃¹ _
  | ⊤, rel _ _ | ⊤, nrel _ _ | ⊤, ⊥ | ⊤, _ ⋏ _ | ⊤, _ ⋎ _ | ⊤, ∀¹ _ | ⊤, ∃¹ _
  | ⊥, rel _ _ | ⊥, nrel _ _ | ⊥, ⊤ | ⊥, _ ⋏ _ | ⊥, _ ⋎ _ | ⊥, ∀¹ _ | ⊥, ∃¹ _
  | _ ⋏ _, rel _ _ | _ ⋏ _, nrel _ _ | _ ⋏ _, ⊤ | _ ⋏ _, ⊥ | _ ⋏ _, _ ⋎ _
    | _ ⋏ _, ∀¹ _ | _ ⋏ _, ∃¹ _
  | _ ⋎ _, rel _ _ | _ ⋎ _, nrel _ _ | _ ⋎ _, ⊤ | _ ⋎ _, ⊥ | _ ⋎ _, _ ⋏ _
    | _ ⋎ _, ∀¹ _ | _ ⋎ _, ∃¹ _
  | ∀¹ _, rel _ _ | ∀¹ _, nrel _ _ | ∀¹ _, ⊤ | ∀¹ _, ⊥ | ∀¹ _, _ ⋏ _ | ∀¹ _, _ ⋎ _
    | ∀¹ _, ∃¹ _
  | ∃¹ _, rel _ _ | ∃¹ _, nrel _ _ | ∃¹ _, ⊤ | ∃¹ _, ⊥ | ∃¹ _, _ ⋏ _ | ∃¹ _, _ ⋎ _
    | ∃¹ _, ∀¹ _ => by
    simp [ne_iff_val_ne, qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

@[simp] lemma typed_quote_inj_iff {φ₁ φ₂ : Semiproposition L n} :
    (⌜φ₁⌝ : Bootstrapping.Semiformula V L n) = ⌜φ₂⌝ ↔ φ₁ = φ₂ :=
  ⟨typed_quote_inj, by rintro rfl; rfl⟩

noncomputable instance : GödelQuote (Semiproposition L n) V where
  quote φ := (⌜φ⌝ : Bootstrapping.Semiformula V L n).val

lemma quote_def (φ : Semiproposition L n) :
    (⌜φ⌝ : V) = (⌜φ⌝ : Bootstrapping.Semiformula V L n).val := rfl

@[simp] lemma quote_isSemiformula (φ : Semiproposition L n) : IsSemiformula L ↑n (⌜φ⌝ : V) := by
  simp [quote_def]

@[simp] lemma quote_isSemiformula₀ (φ : Proposition L) : IsSemiformula L 0 (⌜φ⌝ : V) := by
  simp [quote_def]

@[simp] lemma quote_isSemiformul₁ (φ : Semiproposition L 1) : IsSemiformula L 1 (⌜φ⌝ : V) := by
  simp [quote_def]

@[simp] lemma quote_rel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : V) = ^rel ↑k ⌜R⌝
      (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)) := rfl

@[simp] lemma quote_nrel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : V) = ^nrel ↑k ⌜R⌝
      (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)) := rfl

@[simp] lemma quote_verum : (⌜(⊤ : Semiproposition L n)⌝ : V) = ^⊤ := rfl

@[simp] lemma quote_falsum : (⌜(⊥ : Semiproposition L n)⌝ : V) = ^⊥ := rfl

@[simp] lemma quote_and (φ ψ : Semiproposition L n) : (⌜φ ⋏ ψ⌝ : V) = ⌜φ⌝ ^⋏ ⌜ψ⌝ := rfl

@[simp] lemma quote_or (φ ψ : Semiproposition L n) : (⌜φ ⋎ ψ⌝ : V) = ⌜φ⌝ ^⋎ ⌜ψ⌝ := rfl

@[simp] lemma quote_all (φ : Semiproposition L (n + 1)) : (⌜∀¹ φ⌝ : V) = ^∀ ⌜φ⌝ := rfl

@[simp] lemma quote_ex (φ : Semiproposition L (n + 1)) : (⌜∃¹ φ⌝ : V) = ^∃ ⌜φ⌝ := rfl

lemma quote_shift (φ : Semiproposition L n) :
    (⌜Rewriting.shift φ⌝ : V) = Bootstrapping.shift L ⌜φ⌝ := by simp [quote_def]

lemma quote_eq_encode (φ : Semiproposition L n) : (⌜φ⌝ : V) = ↑(encode φ) := by
  suffices (⌜φ⌝ : Bootstrapping.Semiformula V L n).val = ↑(encode φ) from this
  induction φ using rec'
  case hrel => simp [encode_rel, qqRel, coe_pair_eq_pair_coe, Semiterm.quote_eq_encode']; rfl
  case hnrel => simp [encode_nrel, qqNRel, coe_pair_eq_pair_coe, Semiterm.quote_eq_encode']; rfl
  case hverum => simp [encode_verum, qqVerum, coe_pair_eq_pair_coe]
  case hfalsum => simp [encode_falsum, qqFalsum, coe_pair_eq_pair_coe]
  case hand => simp [encode_and, qqAnd, coe_pair_eq_pair_coe,  *]; simp [encode_eq_toNat]
  case hor => simp [encode_or, qqOr, coe_pair_eq_pair_coe,  *]; simp [encode_eq_toNat]
  case hall => simp [encode_all, qqAll, coe_pair_eq_pair_coe, *]; simp [encode_eq_toNat]
  case hexs => simp [encode_ex, qqExs, coe_pair_eq_pair_coe, *]; simp [encode_eq_toNat]

lemma coe_quote_eq_quote (φ : Semiproposition L n) : (↑(⌜φ⌝ : ℕ) : V) = ⌜φ⌝ := by
  simp [quote_eq_encode]

lemma coe_quote_eq_quote' (φ : Semiproposition L n) :
    (↑(⌜φ⌝ : Bootstrapping.Semiformula ℕ L n).val : V) =
      (⌜φ⌝ : Bootstrapping.Semiformula V L n).val :=
  coe_quote_eq_quote φ

lemma quote_eq_encode_nat (φ : Semiproposition L n) : (⌜φ⌝ : ℕ) = encode φ := by
  simpa using quote_eq_encode (V := ℕ) φ

lemma primrec_quote_natCast [L.Primcodable] : Primrec (fun φ : Semiproposition L n ↦ (⌜φ⌝ : ℕ)) :=
  Primrec.encode.of_eq (fun φ ↦ (quote_eq_encode_nat φ).symm)

@[simp] lemma quote_inj_iff {φ₁ φ₂ : Semiproposition L n} :
    (⌜φ₁⌝ : V) = ⌜φ₂⌝ ↔ φ₁ = φ₂ := by simp [quote_eq_encode]

noncomputable instance : LCWQIsoGödelQuote (Semisentence L) (Bootstrapping.Semiformula V L) where
  gq n := ⟨fun σ ↦ (⌜(Rewriting.emb σ : Semiproposition L n)⌝)⟩
  top := by simp
  bot := by simp
  and _ _ := by simp
  or _ _ := by simp
  neg _ := by simp
  imply _ _ := by simp
  all _ := by simp
  exs _ := by simp

@[simp] lemma coe_quote {ξ n m} (φ : Semiproposition L n) :
    ↑(⌜φ⌝ : ℕ) = (⌜φ⌝ : ArithmeticSemiterm ξ m) := by
  simp [gödelNumber'_def, Semiformula.quote_eq_encode]

@[simp] lemma quote_quote_eq_numeral {m} (φ : Semiproposition L n) :
    (⌜(⌜φ⌝ : ArithmeticSemiterm ℕ m)⌝ : Bootstrapping.Semiterm V ℒₒᵣ m) =
      Bootstrapping.Arithmetic.typedNumeral ⌜φ⌝ := by
  simp [←coe_quote, coe_quote_eq_quote]

lemma quote_castLE (φ : Semiproposition L n) :
    ∀ {n' : ℕ} (h : n ≤ n'), (⌜(Rew.castLE h ▹ φ : Semiproposition L n')⌝ : V) = ⌜φ⌝ := by
  induction φ using rec' with
  | hverum => intro n' h; simp
  | hfalsum => intro n' h; simp
  | hrel r v =>
      intro n' h
      simp only [rew_rel, quote_rel, SemitermVec.val]
      congr 2; funext i; exact Semiterm.quote_castLE (v i) h
  | hnrel r v =>
      intro n' h
      simp only [rew_nrel, quote_nrel, SemitermVec.val]
      congr 2; funext i; exact Semiterm.quote_castLE (v i) h
  | hand φ ψ ihp ihq =>
      intro n' h; simp only [LogicalConnective.HomClass.map_and, quote_and, ihp h, ihq h]
  | hor φ ψ ihp ihq =>
      intro n' h; simp only [LogicalConnective.HomClass.map_or, quote_or, ihp h, ihq h]
  | hall φ ih =>
      intro n' h; rw [Rewriting.app_all, quote_all, Rew.q_castLE, ih, quote_all]
  | hexs φ ih =>
      intro n' h; rw [Rewriting.app_exs, quote_ex, Rew.q_castLE, ih, quote_ex]

omit [L.Encodable] [L.LORDefinable] in
lemma freeVariables_castLE (φ : Semiproposition L n) :
    ∀ {n' : ℕ} (h : n ≤ n'),
      (Rew.castLE h ▹ φ : Semiproposition L n').freeVariables = φ.freeVariables := by
  induction φ using rec' with
  | hverum => intro n' h; simp
  | hfalsum => intro n' h; simp
  | hrel r v =>
      intro n' h
      simp only [rew_rel, freeVariables_rel]
      apply Finset.biUnion_congr rfl; intro i _; exact Semiterm.freeVariables_castLE _ h
  | hnrel r v =>
      intro n' h
      simp only [rew_nrel, freeVariables_nrel]
      apply Finset.biUnion_congr rfl; intro i _; exact Semiterm.freeVariables_castLE _ h
  | hand φ ψ ihp ihq =>
      intro n' h; simp only [LogicalConnective.HomClass.map_and, freeVariables_and, ihp h, ihq h]
  | hor φ ψ ihp ihq =>
      intro n' h; simp only [LogicalConnective.HomClass.map_or, freeVariables_or, ihp h, ihq h]
  | hall φ ih =>
      intro n' h; simp only [Rewriting.app_all, freeVariables_all, Rew.q_castLE, ih]
  | hexs φ ih =>
      intro n' h; simp only [Rewriting.app_exs, freeVariables_exs, Rew.q_castLE, ih]

omit [L.Encodable] [L.LORDefinable] in
lemma fvar?_fvSup_pred (φ : Semiproposition L n) (h : 0 < φ.fvSup) : φ.FVar? (φ.fvSup - 1) := by
  by_cases he : φ.freeVariables = ∅
  · simp [fvSup, he] at h
  · obtain ⟨k, hk⟩ := Finset.max_of_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
    rw [show φ.fvSup = k + 1 from by simp [fvSup, hk]]
    simpa using Finset.mem_of_max hk

end Semiformula

namespace Sentence

variable {n : ℕ}

theorem typed_quote_def (σ : Semisentence L n) :
    (⌜σ⌝ : Bootstrapping.Semiformula V L n) =
      ⌜(Rewriting.emb σ : Semiproposition L n)⌝ := rfl

@[simp] lemma typed_quote_eq (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t = !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ ≐ ⌜u⌝) := rfl

@[simp] lemma typed_quote_ne (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≠ !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ ≉ ⌜u⌝) := rfl

@[simp] lemma typed_quote_lt (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t < !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ <' ⌜u⌝) := rfl

@[simp] lemma typed_quote_nlt (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≮ !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜t⌝ ≮' ⌜u⌝) := rfl

noncomputable instance : GödelQuote (Semisentence L n) V where
  quote σ := ⌜(Rewriting.emb σ : Semiproposition L n)⌝

lemma quote_def (σ : Semisentence L n) :
    (⌜σ⌝ : V) = ⌜(Rewriting.emb σ : Semiproposition L n)⌝ := rfl

theorem quote_eq (σ : Semisentence L n) :
    (⌜σ⌝ : V) = (⌜σ⌝ : Bootstrapping.Semiformula V L n).val := rfl

@[simp] lemma quote_isSemiformula (φ : Semisentence L n) : IsSemiformula L ↑n (⌜φ⌝ : V) := by
  simp [quote_def]

@[simp] lemma quote_isSemiformula₀ (φ : Sentence L) : IsSemiformula L 0 (⌜φ⌝ : V) := by
  simp [quote_def]

@[simp] lemma quote_isSemiformul₁ (φ : Semisentence L 1) : IsSemiformula L 1 (⌜φ⌝ : V) := by
  simp [quote_def]

lemma quote_eq_encode (σ : Semisentence L n) : (⌜σ⌝ : V) = ↑(encode σ) := by
  simp [quote_def, Semiformula.quote_eq_encode]

lemma coe_quote_eq_quote (σ : Semisentence L n) : (↑(⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  simp [quote_eq_encode]

lemma quote_eq_encode_nat (σ : Semisentence L n) : (⌜σ⌝ : ℕ) = encode σ := by
  simpa using quote_eq_encode (V := ℕ) σ

lemma primrec_quote_natCast [L.Primcodable] : Primrec (fun σ : Semisentence L n ↦ (⌜σ⌝ : ℕ)) :=
  Primrec.encode.of_eq (fun σ ↦ (quote_eq_encode_nat σ).symm)

@[simp] lemma val_quote {m ξ} {bv : Fin m → V} {fv : ξ → V} (σ : Semisentence L n) :
    (⌜σ⌝ : ArithmeticSemiterm ξ m).val bv fv = ⌜σ⌝ := by
  simp [gödelNumber'_def, quote_eq_encode, numeral_eq_natCast]

@[simp] lemma coe_quote {ξ m} (σ : Semisentence L n) :
    ↑(⌜σ⌝ : ℕ) = (⌜σ⌝ : ArithmeticSemiterm ξ m) := by
  simp [gödelNumber'_def, quote_eq_encode]

@[simp] lemma quote_quote_eq_numeral {m} (σ : Semisentence L n) :
    (⌜(⌜σ⌝ : ArithmeticSemiterm ℕ m)⌝ : Bootstrapping.Semiterm V ℒₒᵣ m) =
      Bootstrapping.Arithmetic.typedNumeral ⌜σ⌝ := by
  simp [←coe_quote, coe_quote_eq_quote]

@[simp] lemma quote_inj_iff {σ₁ σ₂ : Semisentence L n} :
    (⌜σ₁⌝ : V) = ⌜σ₂⌝ ↔ σ₁ = σ₂ := by
  simp [quote_eq_encode]

end Sentence

end FirstOrder

namespace FirstOrder.Arithmetic.Bootstrapping

open Encodable FirstOrder

lemma IsSemiformula.sound {n φ : ℕ} (h : IsSemiformula L n φ) :
    ∃ F : FirstOrder.Semiproposition L n, ⌜F⌝ = φ := by
  induction φ using Nat.strongRec generalizing n
  case ind φ ih =>
    rcases IsSemiformula.case_iff.mp h with
      (⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
       ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, hp, rfl⟩ | ⟨φ, hp, rfl⟩)
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] :=
          fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r :=
        isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨FirstOrder.Semiformula.rel R v', ?_⟩
      suffices SemitermVec.val (fun i ↦ ⌜v' i⌝) = v by
        simpa [Semiformula.quote_rel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        (SemitermVec.val fun i ↦ ⌜v' i⌝).[i] = (SemitermVec.val fun i ↦ ⌜v' i⌝).[↑j] := rfl
        _                                    = ⌜v' j⌝ := by
          simpa [Semiterm.quote_def] using
            SemitermVec.val_nth_eq (fun i ↦ (⌜v' i⌝ : Bootstrapping.Semiterm ℕ L n)) j
        _                                    = v.[i] := hv' j
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] :=
          fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r :=
        isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨FirstOrder.Semiformula.nrel R v', ?_⟩
      suffices SemitermVec.val (fun i ↦ ⌜v' i⌝) = v by
        simpa [Semiformula.quote_nrel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        (SemitermVec.val fun i ↦ ⌜v' i⌝).[i] = (SemitermVec.val fun i ↦ ⌜v' i⌝).[↑j] := rfl
        _                                    = ⌜v' j⌝ := by
          simpa [Semiterm.quote_def] using
            SemitermVec.val_nth_eq (fun i ↦ (⌜v' i⌝ : Bootstrapping.Semiterm ℕ L n)) j
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
      exact ⟨∀¹ φ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∃¹ φ, by simp⟩

lemma quote_allClosure {n : ℕ} (φ : Semiproposition L n) :
    (⌜(∀¹* φ : Semiproposition L 0)⌝ : V) = qqAlls (⌜φ⌝ : V) (n : V) := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [show (∀¹* φ : Semiproposition L 0) = ∀¹* (∀¹ φ) from rfl]
    simpa [Semiformula.quote_all, qqAlls_all] using ih (∀¹ φ)

lemma quote_univCl' (ψ : Semiproposition L 0) :
    (⌜Semiformula.univCl' ψ⌝ : V)
      = qqAlls (⌜(Rew.fixitr 0 ψ.fvSup ▹ ψ : Semiproposition L (0 + ψ.fvSup))⌝ : V)
          ((0 + ψ.fvSup : ℕ) : V) :=
  quote_allClosure _

lemma quote_subst_fvar_fixitr (φ : Semiproposition L 0) :
    (⌜(Rew.fixitr 0 φ.fvSup ▹ φ : Semiproposition L (0 + φ.fvSup))
        ⇜ (fun x : Fin (0 + φ.fvSup) ↦ (&↑x : SyntacticTerm L))⌝ : V) = ⌜φ⌝ := by
  rw [Semiformula.subst_comp_fixitr]

/-! ### Pinning `bv` of the `fixitr`-image -/

-- Only needs `GoedelQuote`/`Rewriting` structure on `L`, not `Encodable`/`LORDefinable`.
omit [L.Encodable] [L.LORDefinable] in
lemma not_fvar?_fixitr (χ : Semiproposition L 0) (x : ℕ) :
    ¬(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)).FVar? x := by
  rw [Rew.eq_bind (Rew.fixitr 0 χ.fvSup)]
  simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk, zero_add]
  intro hh
  rcases Semiformula.fvar?_rew hh with (⟨z, hz⟩ | ⟨z, hz, hx⟩)
  · simp at hz
  · have : z < χ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
    simp [this] at hx

lemma quote_shift_fixitr (χ : Semiproposition L 0) :
    Bootstrapping.shift (V := ℕ) L
        (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ := by
  have hshift : Rewriting.shift (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))
      = (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)) :=
    Semiformula.rew_eq_self_of (by simp) (fun x hx ↦ absurd hx (not_fvar?_fixitr χ x))
  rw [← Semiformula.quote_shift (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ), hshift]

lemma bv_quote_fixitr (χ : Semiproposition L 0) :
    bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ)
      = χ.fvSup := by
  have hβ := Semiformula.quote_isSemiformula (V := ℕ)
    (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))
  have hle := hβ.bv_le
  simp only [Nat.zero_add, natCast_nat] at hle
  set j := bv (V := ℕ) L (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup))⌝ : ℕ)
  -- `≤` on a model of arithmetic unfolds to `= ∨ <`.
  obtain h | hlt := (hle : j = χ.fvSup ∨ j < χ.fvSup)
  · exact h
  exfalso
  have hj : j ≤ 0 + χ.fvSup := by omega
  obtain ⟨γ, hγ⟩ := IsSemiformula.sound (hβ.isUFormula.isSemiformula : IsSemiformula L j _)
  have hcast : (Rew.castLE hj ▹ γ : Semiproposition L (0 + χ.fvSup))
      = (Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition L (0 + χ.fvSup)) :=
    (Semiformula.quote_inj_iff (V := ℕ)).mp <| by rw [Semiformula.quote_castLE, hγ]
  have hγfree : γ.freeVariables = ∅ := by
    rw [← Semiformula.freeVariables_castLE γ hj, hcast]
    exact Finset.eq_empty_of_forall_notMem fun x hx ↦ not_fvar?_fixitr χ x hx
  have hχ : γ ⇜ (fun i : Fin j ↦ (&↑i : SyntacticTerm L)) = χ := by
    have : (Rew.subst fun x : Fin (0 + χ.fvSup) ↦ (&↑x : SyntacticTerm L)).comp (Rew.castLE hj)
        = Rew.subst fun i : Fin j ↦ (&↑i : SyntacticTerm L) := by
      ext x <;> simp [Rew.comp_app]
    conv_rhs => rw [← Semiformula.subst_comp_fixitr χ, ← hcast]
    unfold Rewriting.subst
    rw [← TransitiveRewriting.comp_app, this]
  have hfv : (γ ⇜ fun i : Fin j ↦ (&↑i : SyntacticTerm L)).FVar? (χ.fvSup - 1) := by
    rw [hχ]; exact Semiformula.fvar?_fvSup_pred χ (by omega)
  unfold Rewriting.subst at hfv
  rcases Semiformula.fvar?_rew hfv with (⟨i, hi⟩ | ⟨z, hz, _⟩)
  · have : χ.fvSup - 1 = (i : ℕ) := by
      simpa [Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi
    have := i.isLt
    omega
  · simp [Semiformula.FVar?, hγfree] at hz

lemma subst_fvarVec_quote' {m : ℕ} (β : ArithmeticSemiproposition m) :
    Bootstrapping.subst ℒₒᵣ (fvarVec ((m : ℕ) : V)) (⌜β⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ)))⌝ : V) := by
  rw [fvarVec_val_eq]
  change ((⌜β⌝ : Bootstrapping.Semiformula V ℒₒᵣ m).subst _).val
    = (⌜β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm ℒₒᵣ))⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0).val
  simp [FirstOrder.Semiformula.typed_quote_substs, Semiterm.typed_quote_fvar]

end FirstOrder.Arithmetic.Bootstrapping

namespace FirstOrder.Arithmetic

open Bootstrapping

lemma quote_ball {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) (φ : ArithmeticSemiproposition (n + 1)) :
    (⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemiproposition n)⌝ : ℕ)
      = qqBall (termBShift ℒₒᵣ (⌜t⌝ : ℕ)) (⌜φ⌝ : ℕ) := by
  rw [Semiformula.ball_eq, Semiformula.imp_eq]
  simp only [Semiformula.Operator.lt_def, Semiformula.neg_rel, Semiformula.quote_all,
    Semiformula.quote_or, qqBall, qqAll_inj, qqOr_inj, and_true]
  simp [Semiformula.quote_nrel, Arithmetic.qqNLT, Arithmetic.ltIndex, Semiterm.quote_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

lemma termBShift_quote {n : ℕ} (s : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Rew.bShift s⌝ : ℕ) = termBShift ℒₒᵣ (⌜s⌝ : ℕ) := by
  simp [Semiterm.quote_def, Semiterm.typed_quote_bShift]

end FirstOrder.Arithmetic

end FFL
