import Logic.FirstOrder.Arith.Theory
import Logic.Logic.HilbertStyle.Gentzen
import Logic.Logic.HilbertStyle.Supplemental

namespace LO.FirstOrder

structure ProvabilityPredicate (L₀ L : Language) where
  prov : Semisentence L₀ 1

namespace ProvabilityPredicate

section

variable [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]

def pr (β : ProvabilityPredicate L₀ L) (σ : Sentence L) : Semisentence L₀ n := β.prov/[⸢σ⸣]

notation "⦍" β "⦎" σ:80 => pr β σ

class Conservative (β : ProvabilityPredicate L₀ L) (T₀ : Theory L₀) (T : outParam (Theory L)) where
  iff (σ : Sentence L) : T ⊢! σ ↔ T₀ ⊢! ⦍β⦎ σ

def consistency (β : ProvabilityPredicate L₀ L) : Sentence L₀ := ~⦍β⦎⊥
notation "Con⦍" β "⦎" => consistency β

end

section Conditions

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class HilbertBernays₁ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D1 {σ : Sentence L} : T ⊢! σ → T₀ ⊢! ⦍β⦎σ


class HilbertBernays₂ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D2 {σ τ : Sentence L} : T₀ ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ


class HilbertBernays₃ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D3 {σ : Sentence L} : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ

-- MEMO: たとえば`P(σ)`を「`σ`が`𝚺₁`文である」などを取れば，標準的な構成をすれば`⦍β⦎σ`は`𝚺₁`文なので直ちに`HilbertBernays₃`が得られる．
class FormalizedCompleteness (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) (P : Sentence L → Prop) where
  FC {σ : Sentence L} : P σ → T₀ ⊢! σ ⟶ ⦍β⦎σ

def HilbertBernays₃_of_FormalizedCompleteness {β : ProvabilityPredicate L L} {T₀ T}
  [β.FormalizedCompleteness T₀ T P] (hP : ∀ σ, P (⦍β⦎σ))
  : β.HilbertBernays₃ T₀ T := ⟨λ {σ} => FormalizedCompleteness.FC (hP σ)⟩

class HilbertBernays (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L))
  extends β.HilbertBernays₁ T₀ T, β.HilbertBernays₂ T₀ T, β.HilbertBernays₃ T₀ T

class Diagonalization (T : Theory L) where
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢! fixpoint θ ⟷ θ/[⸢fixpoint θ⸣]


class Loeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  LT {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ σ → T ⊢! σ

class FormalizedLoeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  FLT {σ : Sentence L} : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ


section

variable {T₀ T : Theory L}
variable [T₀ ≼ T] {σ τ : Sentence L}

def HilbertBernays₁.D1s [HilbertBernays₁ β T₀ T]: T ⊢! σ → T ⊢! ⦍β⦎σ := by
  intro h;
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₁.D1 h;

def HilbertBernays₂.D2s [HilbertBernays₂ β T₀ T] : T ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₂.D2;

def HilbertBernays₂.D2' [HilbertBernays β T₀ T] [System.ModusPonens T] : T₀ ⊢! ⦍β⦎(σ ⟶ τ) → T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎τ := by
  intro h;
  exact HilbertBernays₂.D2 ⨀ h;

def HilbertBernays₃.D3s [HilbertBernays₃ β T₀ T] : T ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₃.D3;

namespace HilbertBernays

open LO.System

variable [DecidableEq (Sentence L)]
         [HilbertBernays β T₀ T]

def prov_distribute_imply (h : T ⊢! σ ⟶ τ) : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎τ := HilbertBernays₂.D2' $ HilbertBernays₁.D1 h

def prov_distribute_iff (h : T ⊢! σ ⟷ τ) : T₀ ⊢! ⦍β⦎σ ⟷ ⦍β⦎τ := by
  apply iff_intro!;
  . exact prov_distribute_imply $ conj₁'! h;
  . exact prov_distribute_imply $ conj₂'! h;

def prov_distribute_and : T₀ ⊢! ⦍β⦎(σ ⋏ τ) ⟶ ⦍β⦎σ ⋏ ⦍β⦎τ := by
  have h₁ : T₀ ⊢! ⦍β⦎(σ ⋏ τ) ⟶ ⦍β⦎σ := HilbertBernays₂.D2' <| HilbertBernays₁.D1 conj₁!;
  have h₂ : T₀ ⊢! ⦍β⦎(σ ⋏ τ) ⟶ ⦍β⦎τ := HilbertBernays₂.D2' <| HilbertBernays₁.D1 conj₂!;
  exact implyRightAnd! h₁ h₂;

def prov_distribute_and! : T₀ ⊢! ⦍β⦎(σ ⋏ τ) → T₀ ⊢! ⦍β⦎σ ⋏ ⦍β⦎τ := λ h => prov_distribute_and ⨀ h

def prov_collect_and : T₀ ⊢! ⦍β⦎σ ⋏ ⦍β⦎τ ⟶ ⦍β⦎(σ ⋏ τ) := by
  have h₁ : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎(τ ⟶ σ ⋏ τ) := prov_distribute_imply $ conj₃!;
  have h₂ : T₀ ⊢! ⦍β⦎(τ ⟶ σ ⋏ τ) ⟶ ⦍β⦎τ ⟶ ⦍β⦎(σ ⋏ τ) := HilbertBernays₂.D2;
  apply andImplyIffImplyImply'!.mpr;
  exact imp_trans! h₁ h₂;

end HilbertBernays

end

end Conditions


section

variable [DecidableEq (Sentence L)]
         [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T₀ T : Theory L} [T₀ ≼ T] [Diagonalization T₀]
         {β : ProvabilityPredicate L L}
open LO.System LO.System.NegationEquiv
open HilbertBernays₁ HilbertBernays₂ HilbertBernays₃ HilbertBernays FormalizedCompleteness
open Diagonalization

abbrev goedel
  (T₀ T : Theory L) [Diagonalization T₀]
  (β : ProvabilityPredicate L L) [β.HilbertBernays₁ T₀ T] : Sentence L
  := fixpoint T₀ “x | ¬!β.prov x”
local notation "γ" => goedel T₀ T β


section

variable [β.HilbertBernays₁ T₀ T]

lemma goedel_spec : T₀ ⊢! γ ⟷ ~⦍β⦎γ := by
  convert (diag (T := T₀) “x | ¬!β.prov x”);
  simp [goedel, ←Rew.hom_comp_app, Rew.substs_comp_substs];
  rfl;

private lemma goedel_specAux₁ : T ⊢! γ ⟷ ~⦍β⦎γ := Subtheory.prf! (𝓢 := T₀) goedel_spec

private lemma goedel_specAux₂ : T ⊢! ~γ ⟶ ⦍β⦎γ := contra₂'! $ conj₂'! goedel_specAux₁

-- MEMO: 特にGödel文`γ`で健全性が成り立つという仮定．実際には標準的な構成をすれば`⦍β⦎γ`は`𝚷₁`文であるから`𝚷₁`健全性を示せば良い．
class GoedelSound (β : ProvabilityPredicate L L) (T₀ T) [Diagonalization T₀] [β.HilbertBernays₁ T₀ T] where
  γ_sound : T ⊢! ⦍β⦎(goedel T₀ T β) → T ⊢! (goedel T₀ T β)


-- MEMO: 特にGödel文の否定`~γ`で形式化された完全性が成り立つという仮定．`~⦍β⦎γ`は`𝚺₁`文であるから形式化された`𝚺₁`完全性を示せば良い．
class NotGoedelFormalizedCompleted (β : ProvabilityPredicate L L) (T₀ T) [Diagonalization T₀] [β.HilbertBernays₁ T₀ T] (P : outParam (Sentence L → Prop)) extends FormalizedCompleteness β T₀ T P where
  P_nγ : P (~(goedel T₀ T β))

lemma NotGoedelFormalizedCompleted.γ_fcomplete [β.NotGoedelFormalizedCompleted T₀ T P] : T₀ ⊢! ~γ ⟶ ⦍β⦎(~γ) := by
  exact FC (T := T) (P := P) (NotGoedelFormalizedCompleted.P_nγ);

end


open GoedelSound NotGoedelFormalizedCompleted


section First

variable [β.HilbertBernays₁ T₀ T]

theorem unprovable_goedel [System.Consistent T] : T ⊬! γ := by
  intro h;
  have h₁ : T ⊢! ⦍β⦎γ := D1s (T₀ := T₀) h;
  have h₂ : T ⊢! ~⦍β⦎γ := (conj₁'! goedel_specAux₁) ⨀ h;
  have : T ⊢! ⊥ := (neg_equiv'!.mp h₂) ⨀ h₁;

  have := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr this;
  contradiction;

theorem unrefutable_goedel [System.Consistent T] [β.GoedelSound T₀ T] : T ⊬! ~γ := by
  intro h₂;
  have h₁ : T ⊢! γ := γ_sound $ goedel_specAux₂ ⨀ h₂;
  have : T ⊢! ⊥ := (neg_equiv'!.mp h₂) ⨀ h₁;

  have := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr this;
  contradiction;

theorem goedel_independent [System.Consistent T] [β.GoedelSound T₀ T] : System.Undecidable T γ := by
  suffices T ⊬! γ ∧ T ⊬! ~γ by simpa [System.Undecidable, not_or] using this;
  constructor;
  . apply unprovable_goedel;
  . apply unrefutable_goedel;

theorem first_incompleteness [System.Consistent T] [β.GoedelSound T₀ T]
  : ¬System.Complete T := System.incomplete_iff_exists_undecidable.mpr ⟨γ, goedel_independent⟩

end First


section Second

lemma formalized_consistent_of_existance_unprovable [β.HilbertBernays T₀ T] : T₀ ⊢! ~⦍β⦎σ ⟶ Con⦍β⦎ := contra₀'! $ D2 ⨀ (D1 efq!)

private lemma consistency_lemma_1 [T₀ ≼ U] [β.HilbertBernays T₀ U] : (U ⊢! Con⦍β⦎ ⟶ ~⦍β⦎σ) ↔ (U ⊢! ⦍β⦎σ ⟶ ⦍β⦎(~σ)) := by
  constructor;
  . intro H;
    exact contra₃'! $ imp_trans! (Subtheory.prf! (𝓢 := T₀) formalized_consistent_of_existance_unprovable) H;
  . intro H;
    apply contra₀'!;
    have : T₀ ⊢! ⦍β⦎σ ⋏ ⦍β⦎(~σ) ⟶ ⦍β⦎⊥ := imp_trans! prov_collect_and $ prov_distribute_imply no_both!;
    have : U ⊢! ⦍β⦎σ ⟶ ⦍β⦎(~σ) ⟶ ⦍β⦎⊥ := Subtheory.prf! $ andImplyIffImplyImply'!.mp $ this;
    exact this ⨀₁ H;

variable [Diagonalization T] [β.HilbertBernays T₀ T]

/-- Formalized First theorem of unprovability -/
lemma formalized_unprovable_goedel [β.NotGoedelFormalizedCompleted T₀ T P] : T ⊢! Con⦍β⦎ ⟶ ~⦍β⦎γ := by
  have h₁ : T ⊢! ⦍β⦎γ ⟶ ~γ := contra₁'! $ conj₁'! $ goedel_specAux₁;
  have h₂ : T ⊢! ~γ ⟶ ⦍β⦎(~γ) := Subtheory.prf! (𝓢 := T₀) $ γ_fcomplete;
  exact consistency_lemma_1 (T₀ := T₀) |>.mpr $ imp_trans! h₁ h₂;

lemma iff_goedel_consistency [β.NotGoedelFormalizedCompleted T₀ T P] : T ⊢! γ ⟷ Con⦍β⦎
  := iff_trans! goedel_specAux₁ $ iff_intro! (Subtheory.prf! (𝓢 := T₀) formalized_consistent_of_existance_unprovable) (formalized_unprovable_goedel)

theorem unprovable_consistency [β.NotGoedelFormalizedCompleted T₀ T P] [System.Consistent T] : T ⊬! Con⦍β⦎
  := unprovable_iff! iff_goedel_consistency |>.mp $ unprovable_goedel (T₀ := T₀)

theorem unrefutable_consistency [β.NotGoedelFormalizedCompleted T₀ T P] [System.Consistent T] [β.GoedelSound T₀ T] : T ⊬! ~Con⦍β⦎
  := unprovable_iff! (neg_iff'! $ iff_goedel_consistency) |>.mp $ unrefutable_goedel (T₀ := T₀)

end Second


def kreisel
  (T₀ T : Theory L) [Diagonalization T₀]
  (β : ProvabilityPredicate L L) [β.HilbertBernays T₀ T]
  (σ : Sentence L) : Sentence L := fixpoint T₀ “x | !β.prov x → !σ”

local notation "κ(" σ ")" => kreisel T₀ T β σ

section

variable [β.HilbertBernays T₀ T]

lemma kreisel_spec (σ : Sentence L) : T₀ ⊢! κ(σ) ⟷ (⦍β⦎(κ(σ)) ⟶ σ) := by
  convert (diag (T := T₀) “x | !β.prov x → !σ”);
  simp [kreisel, ←Rew.hom_comp_app, Rew.substs_comp_substs];
  rfl;

lemma kreisel_specAux₁ (σ : Sentence L) : T₀ ⊢! ⦍β⦎κ(σ) ⟶ ⦍β⦎σ := (imp_trans! (D2 ⨀ (D1 (Subtheory.prf! $ conj₁'! (kreisel_spec σ)))) D2) ⨀₁ D3

lemma kreisel_specAux₂ (σ : Sentence L) : T₀ ⊢! (⦍β⦎κ(σ) ⟶ σ) ⟶ κ(σ) := conj₂'! (kreisel_spec σ)

end


section LoebTheorem

variable [β.HilbertBernays T₀ T]

theorem loeb_theorm (H : T ⊢! ⦍β⦎σ ⟶ σ) : T ⊢! σ := by
  have d₁ : T ⊢! ⦍β⦎κ(σ) ⟶ σ := imp_trans! (Subtheory.prf! (kreisel_specAux₁ σ)) H;
  have d₂ : T ⊢! ⦍β⦎κ(σ)      := Subtheory.prf! (𝓢 := T₀) (D1 $ Subtheory.prf! (kreisel_specAux₂ σ) ⨀ d₁);
  exact d₁ ⨀ d₂;

instance : Loeb β T₀ T := ⟨loeb_theorm (T₀ := T₀) (T := T)⟩

theorem formalized_loeb_theorem : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ := by
  have hκ₁ : T₀ ⊢! ⦍β⦎(κ(σ)) ⟶ ⦍β⦎σ := kreisel_specAux₁ σ;
  have : T₀ ⊢! (⦍β⦎σ ⟶ σ) ⟶ (⦍β⦎κ(σ) ⟶ σ) := imply_left_replace! hκ₁;
  have : T ⊢! (⦍β⦎σ ⟶ σ) ⟶ κ(σ) := Subtheory.prf! (𝓢 := T₀) $ imp_trans! this (kreisel_specAux₂ σ);
  exact imp_trans! (D2 ⨀ (D1 this)) hκ₁;

instance : FormalizedLoeb β T₀ T := ⟨formalized_loeb_theorem (T₀ := T₀) (T := T)⟩

end LoebTheorem


section

-- another proof of the 2nd incompleteness theorem via Löb
lemma unprovable_consistency_via_loeb
  [β.Loeb T₀ T]
  : System.Consistent T → T ⊬! Con⦍β⦎ := by
  contrapose;
  intro hC; simp at hC;
  have : T ⊢! ⊥ := Loeb.LT T₀ $ neg_equiv'!.mp hC;
  apply System.not_consistent_iff_inconsistent.mpr;
  apply System.inconsistent_of_provable this;

/-- Formalized Second theorem of unprovability -/
lemma formalized_unprovable_consistency
  [β.HilbertBernays T₀ T] [β.NotGoedelFormalizedCompleted T₀ T P]
  [System.Consistent T] [β.GoedelSound T₀ T]
  : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎) := by
  by_contra hC;
  have : T ⊢! ~Con⦍β⦎ := Loeb.LT T₀ $ contra₁'! hC;
  have : T ⊬! ~Con⦍β⦎ := unrefutable_consistency (T₀ := T₀);
  contradiction;

/-- Formalized First theorem of unrefutability -/
lemma formalized_unrefutable_goedel
  [β.HilbertBernays T₀ T] [β.NotGoedelFormalizedCompleted T₀ T P]
  [System.Consistent T] [β.GoedelSound T₀ T]
  : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~γ) := by
  by_contra hC;
  have : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎)  := formalized_unprovable_consistency (T₀ := T₀);
  have : T ⊢! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎) := imp_trans! hC $ Subtheory.prf! $ conj₁'! $ neg_iff'! $ prov_distribute_iff (T₀ := T₀) $ neg_iff'! $ iff_goedel_consistency;
  contradiction;

end

end

end ProvabilityPredicate

end LO.FirstOrder
