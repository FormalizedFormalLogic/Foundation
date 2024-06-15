import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.HilbertStyle

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α]

structure DeductionParameterRules where
  nec : Bool
  loeb : Bool
  henkin : Bool

namespace DeductionParameterRules

instance : LE DeductionParameterRules where
  le R₁ R₂ :=
    R₁.nec ≤ R₂.nec ∧
    R₁.loeb ≤ R₂.loeb ∧
    R₁.henkin ≤ R₂.henkin


variable {R₁ R₂ : DeductionParameterRules} (h : R₁ ≤ R₂ := by simpa)

@[simp] lemma nec_le (hNec : R₁.nec = true) : R₂.nec = true := by apply h.1; assumption;
@[simp] lemma loeb_le (hLoeb : R₁.loeb = true) : R₂.loeb = true := by apply h.2.1; assumption;
@[simp] lemma henkin_le (hHenkin : R₁.henkin = true) : R₂.henkin = true := by apply h.2.2; assumption;

end DeductionParameterRules

/--
  Parameter for deduction system.
-/
structure DeductionParameter (α) where
  axiomSet : AxiomSet α
  rules : DeductionParameterRules
notation "Ax(" 𝓓 ")" => DeductionParameter.axiomSet 𝓓

namespace DeductionParameter

variable (𝓓 𝓓₁ 𝓓₂ : DeductionParameter α)

class HasNec where
  has_nec : 𝓓.rules.nec = true := by rfl

class HasLoebRule where
  has_loeb : 𝓓.rules.loeb = true := by rfl

class HasHenkinRule where
  has_henkin : 𝓓.rules.henkin = true := by rfl

class HasNecOnly extends HasNec 𝓓 where
  not_has_loeb : 𝓓.rules.loeb = false := by rfl
  not_has_henkin : 𝓓.rules.henkin = false := by rfl

class IncludeK where
  include_K : 𝗞 ⊆ Ax(𝓓) := by intro; aesop;

/--
  Deduction system of `L` is normal modal 𝓓ogic.
-/
class Normal extends HasNecOnly 𝓓, IncludeK 𝓓 where

variable {𝓓}

@[simp] lemma normal_has_nec [𝓓.Normal] : 𝓓.rules.nec = true := HasNec.has_nec
@[simp] lemma notmal_not_has_loeb [𝓓.Normal] : 𝓓.rules.loeb = false := HasNecOnly.not_has_loeb
@[simp] lemma notmal_not_has_henkin [𝓓.Normal] : 𝓓.rules.henkin = false := HasNecOnly.not_has_henkin

@[simp] -- TODO: more simple proof
lemma normal_rule [𝓓.Normal] : 𝓓.rules = ⟨true, false, false⟩ := by
  nth_rw 1 [←(normal_has_nec (𝓓 := 𝓓))];
  nth_rw 1 [←(notmal_not_has_loeb (𝓓 := 𝓓))];
  nth_rw 1 [←(notmal_not_has_henkin (𝓓 := 𝓓))];

@[simp] lemma normal_rules [𝓓₁.Normal] [𝓓₂.Normal] : 𝓓₁.rules = 𝓓₂.rules := by simp;

def union (𝓓₁ 𝓓₂ : DeductionParameter α) (_ : 𝓓₁.rules = 𝓓₂.rules := by first | assumption | simp) : DeductionParameter α where
  axiomSet := 𝓓₁.axiomSet ∪ 𝓓₂.axiomSet
  rules := 𝓓₁.rules
notation:50 𝓓₁ " ⊔ " 𝓓₂ => DeductionParameter.union 𝓓₁ 𝓓₂

variable {𝓓₁ 𝓓₂}

lemma union_left_rules (h : 𝓓₁.rules = 𝓓₂.rules) : (𝓓₁ ⊔ 𝓓₂).rules = 𝓓₁.rules := by cases 𝓓₁; rfl

lemma union_right_rules (h : 𝓓₁.rules = 𝓓₂.rules) : (𝓓₁ ⊔ 𝓓₂).rules = 𝓓₂.rules := by cases 𝓓₂; exact h;

lemma union_left_rules_normal [𝓓₁.Normal] [𝓓₂.Normal] : (𝓓₁ ⊔ 𝓓₂).rules = 𝓓₁.rules := by apply union_left_rules;

lemma union_right_rules_normal [𝓓₁.Normal] [𝓓₂.Normal] : (𝓓₁ ⊔ 𝓓₂).rules = 𝓓₂.rules := by apply union_right_rules;

end DeductionParameter


inductive Deduction (𝓓 : DeductionParameter α) : (Formula α) → Type _
  | maxm {p}     : p ∈ Ax(𝓓) → Deduction 𝓓 p
  | mdp {p q}    : Deduction 𝓓 (p ⟶ q) → Deduction 𝓓 p → Deduction 𝓓 q
  | nec {p}      : (𝓓.rules.nec = true) → Deduction 𝓓 p → Deduction 𝓓 (□p)
  | loeb {p}     : (𝓓.rules.loeb = true) → Deduction 𝓓 (□p ⟶ p) → Deduction 𝓓 p
  | henkin {p}   : (𝓓.rules.henkin = true) → Deduction 𝓓 (□p ⟷ p) → Deduction 𝓓 p
  | verum        : Deduction 𝓓 ⊤
  | imply₁ p q   : Deduction 𝓓 (p ⟶ q ⟶ p)
  | imply₂ p q r : Deduction 𝓓 ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | and₁ p q     : Deduction 𝓓 (p ⋏ q ⟶ p)
  | and₂ p q     : Deduction 𝓓 (p ⋏ q ⟶ q)
  | and₃ p q     : Deduction 𝓓 (p ⟶ q ⟶ p ⋏ q)
  | or₁ p q      : Deduction 𝓓 (p ⟶ p ⋎ q)
  | or₂ p q      : Deduction 𝓓 (q ⟶ p ⋎ q)
  | or₃ p q r    : Deduction 𝓓 ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne p        : Deduction 𝓓 (~~p ⟶ p)

namespace Deduction

open DeductionParameter

instance : System (Formula α) (DeductionParameter α) := ⟨Deduction⟩

variable {𝓓 𝓓₁ 𝓓₂ : DeductionParameter α}

instance : System.Classical 𝓓 where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  and₁ := and₁
  and₂ := and₂
  and₃ := and₃
  or₁ := or₁
  or₂ := or₂
  or₃ := or₃
  dne := dne

def maxm_subset
  (hRules : 𝓓₁.rules ≤ 𝓓₂.rules)
  (hAx : Ax(𝓓₁) ⊆ Ax(𝓓₂)) : (𝓓₁ ⊢ p) → (𝓓₂ ⊢ p)
  | maxm h => maxm (hAx h)
  | mdp ih₁ ih₂  => mdp (maxm_subset hRules hAx ih₁) (maxm_subset hRules hAx ih₂)
  | nec b h      => nec (by apply hRules.1; assumption) $ maxm_subset hRules hAx h
  | loeb b h     => loeb (by apply hRules.2.1; assumption) $ maxm_subset hRules hAx h
  | henkin b h   => henkin (by apply hRules.2.2; assumption) $ maxm_subset hRules hAx h
  | verum        => verum
  | imply₁ _ _   => imply₁ _ _
  | imply₂ _ _ _ => imply₂ _ _ _
  | and₁ _ _    => and₁ _ _
  | and₂ _ _    => and₂ _ _
  | and₃ _ _    => and₃ _ _
  | or₁ _ _    => or₁ _ _
  | or₂ _ _    => or₂ _ _
  | or₃ _ _ _  => or₃ _ _ _
  | dne _        => dne _

lemma maxm_subset! (hRules : 𝓓₁.rules ≤ 𝓓₂.rules) (hAx : Ax(𝓓₁) ⊆ Ax(𝓓₂)) (h : 𝓓₁ ⊢! p) : 𝓓₂ ⊢! p := ⟨maxm_subset hRules hAx h.some⟩

@[simp]
lemma reducible_of_subset (hNec : 𝓓₁.rules ≤ 𝓓₂.rules) (hAx : Ax(𝓓₁) ⊆ Ax(𝓓₂) := by intro; aesop) : 𝓓₁ ≤ₛ 𝓓₂ := by
  intro p hp;
  apply maxm_subset! hNec hAx hp;

instance [HasNec 𝓓] : System.Necessitation 𝓓 where
  nec := nec HasNec.has_nec

instance [HasLoebRule 𝓓] : System.LoebRule 𝓓 where
  loeb := loeb HasLoebRule.has_loeb

instance [HasHenkinRule 𝓓] : System.HenkinRule 𝓓 where
  henkin := henkin HasHenkinRule.has_henkin

instance [IncludeK 𝓓] : System.HasAxiomK 𝓓 where
  K _ _ := maxm $ Set.mem_of_subset_of_mem (IncludeK.include_K) (by simp);

instance [Normal 𝓓] : System.K 𝓓 where

noncomputable def inducition!
  {motive  : (p : Formula α) → 𝓓 ⊢! p → Sort*}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p ⟨maxm h⟩)
  (hMdp    : ∀ {p q}, {hpq : 𝓓 ⊢! p ⟶ q} → {hp : 𝓓 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q ⟨mdp hpq.some hp.some⟩)
  (hNec    : (hasNec : 𝓓.rules.nec) → ∀ {p}, {hp : 𝓓 ⊢! p} → motive p hp → motive (□p) ⟨(nec hasNec hp.some)⟩)
  (hLoeb   : (hasLoeb : 𝓓.rules.loeb) → ∀ {p}, {hp : 𝓓 ⊢! □p ⟶ p} → motive (□p ⟶ p) hp → motive p ⟨loeb hasLoeb hp.some⟩)
  (hHenkin : (hasHenkin : 𝓓.rules.henkin) → ∀ {p}, {hp : 𝓓 ⊢! □p ⟷ p} → motive (□p ⟷ p) hp → motive p ⟨henkin hasHenkin hp.some⟩)
  (hVerum  : motive ⊤ ⟨verum⟩)
  (hImply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ ⟨imply₁ p q⟩)
  (hImply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ ⟨imply₂ p q r⟩)
  (hConj₁  : ∀ {p q}, motive (p ⋏ q ⟶ p) $ ⟨and₁ p q⟩)
  (hConj₂  : ∀ {p q}, motive (p ⋏ q ⟶ q) $ ⟨and₂ p q⟩)
  (hConj₃  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ ⟨and₃ p q⟩)
  (hDisj₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ ⟨or₁ p q⟩)
  (hDisj₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ ⟨or₂ p q⟩)
  (hDisj₃  : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ ⟨or₃ p q r⟩)
  (hDne    : ∀ {p}, motive (~~p ⟶ p) $ ⟨dne p⟩)
  : ∀ {p}, (d : 𝓓 ⊢! p) → motive p d := by
  intro p d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec has hp ihp => exact hNec has (ihp ⟨hp⟩)
  | loeb has hp ihp => exact hLoeb has (ihp ⟨hp⟩)
  | henkin has hp ihp => exact hHenkin has (ihp ⟨hp⟩)
  | _ => aesop

noncomputable def inducition_with_nec [HasNecOnly 𝓓]
  {motive  : (p : Formula α) → 𝓓 ⊢ p → Sort*}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p (maxm h))
  (hMdp    : ∀ {p q}, (hpq : 𝓓 ⊢ p ⟶ q) → (hp : 𝓓 ⊢ p) → motive (p ⟶ q) hpq → motive p hp → motive q (mdp hpq hp))
  (hNec    : ∀ {p}, (hp : 𝓓 ⊢ p) → motive p hp → motive (□p) (nec HasNec.has_nec hp))
  (hVerum  : motive ⊤ verum)
  (hImply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ imply₁ p q)
  (hImply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ imply₂ p q r)
  (hConj₁  : ∀ {p q}, motive (p ⋏ q ⟶ p) $ and₁ p q)
  (hConj₂  : ∀ {p q}, motive (p ⋏ q ⟶ q) $ and₂ p q)
  (hConj₃  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ and₃ p q)
  (hDisj₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ or₁ p q)
  (hDisj₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ or₂ p q)
  (hDisj₃  : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ or₃ p q r)
  (hDne    : ∀ {p}, motive (~~p ⟶ p) $ dne p)
  : ∀ {p}, (d : 𝓓 ⊢ p) → motive p d := by
  intro p d;
  induction d with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp hpq hp ihpq ihp
  | nec _ hp ihp => exact hNec hp ihp
  | loeb => have : 𝓓.rules.loeb = false := HasNecOnly.not_has_loeb; simp_all;
  | henkin => have : 𝓓.rules.henkin = false := HasNecOnly.not_has_henkin; simp_all;
  | _ => aesop

noncomputable def inducition_with_nec! [HasNecOnly 𝓓]
  {motive  : (p : Formula α) → 𝓓 ⊢! p → Sort*}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p ⟨maxm h⟩)
  (hMdp    : ∀ {p q}, {hpq : 𝓓 ⊢! p ⟶ q} → {hp : 𝓓 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (hNec    : ∀ {p}, {hp : 𝓓 ⊢! p} → motive p hp → motive (□p) ⟨(nec HasNec.has_nec hp.some)⟩)
  (hVerum  : motive ⊤ ⟨verum⟩)
  (hImply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ ⟨imply₁ p q⟩)
  (hImply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ ⟨imply₂ p q r⟩)
  (hConj₁  : ∀ {p q}, motive (p ⋏ q ⟶ p) $ ⟨and₁ p q⟩)
  (hConj₂  : ∀ {p q}, motive (p ⋏ q ⟶ q) $ ⟨and₂ p q⟩)
  (hConj₃  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ ⟨and₃ p q⟩)
  (hDisj₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ ⟨or₁ p q⟩)
  (hDisj₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ ⟨or₂ p q⟩)
  (hDisj₃  : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ ⟨or₃ p q r⟩)
  (hDne    : ∀ {p}, motive (~~p ⟶ p) $ ⟨dne p⟩)
  : ∀ {p}, (d : 𝓓 ⊢! p) → motive p d := by
  intro p d;
  induction d using Deduction.inducition! with
  | hMaxm h => exact hMaxm h
  | hMdp ihpq ihp => exact hMdp ihpq ihp
  | hNec _ ihp => exact hNec ihp
  | hLoeb => have : 𝓓.rules.loeb = false := HasNecOnly.not_has_loeb; simp_all;
  | hHenkin => have : 𝓓.rules.henkin = false := HasNecOnly.not_has_henkin; simp_all;
  | _ => aesop

/-
instance : System.K (𝐊 : AxiomSet α) := K_of_subset_K (by rfl)

instance : System.K (𝐊 ∪ Λ : AxiomSet α) := K_of_subset_K

instance S4_of_subset_S4 (hS4 : 𝐒𝟒 ⊆ Λ := by simp) : System.S4 (Λ : AxiomSet α) where
  K _ _   := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);
  T _     := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);
  Four _  := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);

instance : System.S4 (𝐒𝟒 : AxiomSet α) := S4_of_subset_S4 (by rfl)
-/

end Deduction


namespace DeductionParameter

open DeductionParameter

private abbrev NecOnly (Ax : AxiomSet α) : DeductionParameter α where
  axiomSet := Ax
  rules := ⟨true, false, false⟩

protected abbrev K : DeductionParameter α := NecOnly 𝗞
notation "𝐊" => DeductionParameter.K
instance : Normal (α := α) 𝐊 where


protected abbrev KT : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧)
notation "𝐊𝐓" => DeductionParameter.KT
instance : Normal (α := α) 𝐊𝐓 where


protected abbrev KD : DeductionParameter α := NecOnly (𝗞 ∪ 𝗗)
notation "𝐊𝐃" => DeductionParameter.KD
instance : Normal (α := α) 𝐊𝐃 where


protected abbrev K4 : DeductionParameter α := NecOnly (𝗞 ∪ 𝟰)
notation "𝐊𝟒" => DeductionParameter.K4
instance : Normal (α := α) 𝐊𝟒 where
instance : System.K4 (𝐊𝟒 : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K5 : DeductionParameter α := NecOnly (𝗞 ∪ 𝟱)
notation "𝐊𝟓" => DeductionParameter.K5
instance : Normal (α := α) 𝐊𝟓 where


protected abbrev S4 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰)
notation "𝐒𝟒" => DeductionParameter.S4
instance : Normal (α := α) 𝐒𝟒 where
instance : System.S4 (𝐒𝟒 : DeductionParameter α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev S5 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟱)
notation "𝐒𝟓" => DeductionParameter.S5
instance : Normal (α := α) 𝐒𝟓 where


protected abbrev KT4B : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ 𝗕)
notation "𝐊𝐓𝟒𝐁" => DeductionParameter.KT4B
instance : Normal (α := α) 𝐊𝐓𝟒𝐁 where


protected abbrev S4Dot2 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ .𝟮)
notation "𝐒𝟒.𝟐" => DeductionParameter.S4Dot2
instance : Normal (α := α) 𝐒𝟒.𝟐 where


protected abbrev S4Dot3 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ .𝟯)
notation "𝐒𝟒.𝟑" => DeductionParameter.S4Dot3
instance : Normal (α := α) 𝐒𝟒.𝟑 where


protected abbrev S4Grz : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ 𝗚𝗿𝘇)
notation "𝐒𝟒𝐆𝐫𝐳" => DeductionParameter.S4Grz
instance : Normal (α := α) 𝐒𝟒𝐆𝐫𝐳 where


protected abbrev Triv : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝗧𝗰)
notation "𝐓𝐫𝐢𝐯" => DeductionParameter.Triv
instance : Normal (α := α) 𝐓𝐫𝐢𝐯 where
instance : System.Triv (𝐓𝐫𝐢𝐯 : DeductionParameter α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Tc _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Ver : DeductionParameter α := NecOnly (𝗞 ∪ 𝗩𝗲𝗿)
notation "𝐕𝐞𝐫" => DeductionParameter.Ver
instance : Normal (α := α) 𝐕𝐞𝐫 where
instance : System.Ver (𝐕𝐞𝐫 : DeductionParameter α) where
  Ver _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev GL : DeductionParameter α := NecOnly (𝗞 ∪ 𝗟)
notation "𝐆𝐋" => DeductionParameter.GL
instance : Normal (α := α) 𝐆𝐋 where
instance : System.GL (𝐆𝐋 : DeductionParameter α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K4H : DeductionParameter α := NecOnly (𝗞 ∪ 𝟰 ∪ 𝗛)
notation "𝐊𝟒𝐇" => DeductionParameter.K4H
instance : Normal (α := α) 𝐊𝟒𝐇 where
instance : System.K4H (𝐊𝟒𝐇 : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  H _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K4Loeb : DeductionParameter α where
  axiomSet := 𝗞 ∪ 𝟰
  rules := ⟨true, true, false⟩
notation "𝐊𝟒(𝐋)" => DeductionParameter.K4Loeb
instance : IncludeK (α := α) 𝐊𝟒(𝐋) where
instance : HasNec (α := α) 𝐊𝟒(𝐋) where
instance : HasLoebRule (α := α) 𝐊𝟒(𝐋) where
instance : System.K4Loeb (𝐊𝟒(𝐋) : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K4Henkin : DeductionParameter α where
  axiomSet := 𝗞 ∪ 𝟰
  rules := ⟨true, false, true⟩
notation "𝐊𝟒(𝐇)" => DeductionParameter.K4Henkin
instance : IncludeK (α := α) 𝐊𝟒(𝐇) where
instance : HasNec (α := α) 𝐊𝟒(𝐇) where
instance : HasHenkinRule (α := α) 𝐊𝟒(𝐇) where
instance : System.K4Henkin (𝐊𝟒(𝐇) : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


/-- Logic of Pure Necessitation -/
protected abbrev N : DeductionParameter α := NecOnly ∅
notation "𝐍" => DeductionParameter.N

end DeductionParameter

open System

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply verum!
    | apply imply₁!
    | apply imply₁!
    | apply imply₂!
    | apply and₁!
    | apply and₂!
    | apply and₃!
    | apply or₁!
    | apply or₂!
    | apply or₃!
  )

macro_rules | `(tactic| trivial) => `(tactic | apply dne!)

section Reducible

lemma normal_reducible
  {𝓓₁ 𝓓₂ : DeductionParameter α} [𝓓₁.Normal] [𝓓₂.Normal]
  (hMaxm : ∀ {p : Formula α}, p ∈ Ax(𝓓₁) → 𝓓₂ ⊢! p) : (𝓓₁ : DeductionParameter α) ≤ₛ 𝓓₂ := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition_with_nec! with
  | hMaxm hp => exact hMaxm hp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | _ => trivial;

lemma normal_reducible_subset {𝓓₁ 𝓓₂ : DeductionParameter α} [𝓓₁.Normal] [𝓓₂.Normal]
  (hSubset : Ax(𝓓₁) ⊆ Ax(𝓓₂)) : (𝓓₁ : DeductionParameter α) ≤ₛ 𝓓₂ := by
  apply normal_reducible;
  intro p hp;
  exact ⟨Deduction.maxm $ hSubset hp⟩;

lemma reducible_K_KT : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐓 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_K_KD : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐃 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_KT_S4 : (𝐊𝐓 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_K4_S4 : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by apply normal_reducible_subset; intro; aesop;

lemma reducible_S4_S4Dot2 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟐 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_S4_S4Dot3 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟑 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_S4_S4Grz : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒𝐆𝐫𝐳 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_K_GL : (𝐊 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_K4_Triv : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐓𝐫𝐢𝐯 := by
  apply normal_reducible;
  intro p hp;
  rcases hp with (hK | hFour)
  . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
  . obtain ⟨_, _, e⟩ := hFour; subst_vars; exact axiomFour!;

lemma reducible_K4_GL : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by
  apply normal_reducible;
  intro p hp;
  rcases hp with (hK | hFour)
  . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
  . obtain ⟨_, _, e⟩ := hFour; subst_vars; exact axiomFour!;

-- Macintyre & Simmons (1973)
-- 𝐆𝐋 =ₛ 𝐊𝟒(𝐋) =ₛ 𝐊𝟒(𝐇) =ₛ 𝐊𝟒𝐇
section GL

lemma reducible_GL_K4Loeb : (𝐆𝐋 : DeductionParameter α) ≤ₛ 𝐊𝟒(𝐋) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hL)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hL; subst_vars; exact axiomL!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec _ ihp => exact nec! ihp;
  | hLoeb _ ihp => exact loeb! ihp;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | _ => trivial;

lemma reducible_K4Loeb_K4Henkin : (𝐊𝟒(𝐋) : DeductionParameter α) ≤ₛ 𝐊𝟒(𝐇) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec _ ihp => exact nec! ihp;
  | hLoeb _ ihp => exact loeb! ihp;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | _ => trivial;

lemma reducible_K4Henkin_K4H : (𝐊𝟒(𝐇) : DeductionParameter α) ≤ₛ 𝐊𝟒𝐇 := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec _ ihp => exact nec! ihp;
  | hHenkin _ ihp => exact henkin! ihp;
  | hLoeb => simp_all only [Bool.false_eq_true];
  | _ => trivial;

lemma reducible_K4Henkin_GL : (𝐊𝟒𝐇 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by
  apply normal_reducible;
  intro p hp;
  rcases hp with (hK | hFour) | hH
  . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
  . obtain ⟨_, _, e⟩ := hFour; subst_vars; exact axiomFour!;
  . obtain ⟨_, _, e⟩ := hH; subst_vars; exact axiomH!;

lemma equivalent_GL_K4Loeb : (𝐆𝐋 : DeductionParameter α) =ₛ 𝐊𝟒(𝐋) := by
  apply Equiv.antisymm_iff.mpr;
  constructor;
  . exact reducible_GL_K4Loeb;
  . exact Reducible.trans (reducible_K4Loeb_K4Henkin) $ Reducible.trans reducible_K4Henkin_K4H reducible_K4Henkin_GL

end GL

end Reducible

-- Toolkit for completeness
section

variable {α : Type*} [DecidableEq α] [Inhabited α]

open System

def Theory.Consistent (𝓓 : DeductionParameter α) (T : Theory α) := ∀ {Γ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → 𝓓 ⊬! Γ.conj' ⟶ ⊥
notation:max "(" 𝓓 ")-Consistent " T:90 => Theory.Consistent 𝓓 T

namespace Theory

variable {𝓓 : DeductionParameter α} {T : Theory α}

lemma self_Consistent [h : System.Consistent 𝓓] : (𝓓)-Consistent Ax(𝓓) := by
  intro Γ hΓ;
  obtain ⟨q, hq⟩ := h.exists_unprovable;
  by_contra hC;
  have : 𝓓 ⊢! q := imp_trans''! hC efq! ⨀ (iff_provable_list_conj.mpr $ λ _ h => ⟨Deduction.maxm $ hΓ _ h⟩);
  contradiction;

lemma def_not_Consistent : ¬(𝓓)-Consistent T ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ 𝓓 ⊢! Γ.conj' ⟶ ⊥ := by simp [Consistent];

lemma union_Consistent : (𝓓)-Consistent (T₁ ∪ T₂) → (𝓓)-Consistent T₁ ∧ (𝓓)-Consistent T₂ := by
  simp only [Consistent];
  intro h;
  constructor;
  . intro Γ hΓ; exact h (by intro p hp; simp; left; exact hΓ p hp);
  . intro Γ hΓ; exact h (by intro p hp; simp; right; exact hΓ p hp);

lemma union_not_Consistent : ¬(𝓓)-Consistent T₁ ∨ ¬(𝓓)-Consistent T₂ → ¬(𝓓)-Consistent (T₁ ∪ T₂) := by
  contrapose;
  push_neg;
  exact union_Consistent;

lemma iff_insert_Consistent : (𝓓)-Consistent (insert p T) ↔ ∀ {Γ : List (Formula α)}, (∀ q ∈ Γ, q ∈ T) → 𝓓 ⊬! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    by_contra hC;
    have : 𝓓 ⊬! p ⋏ List.conj' Γ ⟶ ⊥ := implyLeft_cons_conj'!.not.mp $ @h (p :: Γ) (by
      rintro q hq;
      simp at hq;
      cases hq with
      | inl h => subst h; simp;
      | inr h => simp; right; exact hΓ q h;
    );
    contradiction;
  . intro h Γ hΓ;
    have := @h (Γ.remove p) (by
      intro q hq;
      have := by simpa using hΓ q $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have := imp_trans''! and_comm! $ imply_left_remove_conj'! (p := p) hC;
    contradiction;

lemma iff_insert_Inconsistent : ¬(𝓓)-Consistent (insert p T) ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ 𝓓 ⊢! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . contrapose; push_neg; apply iff_insert_Consistent.mpr;
  . contrapose; push_neg; apply iff_insert_Consistent.mp;

lemma provable_iff_insert_neg_not_Consistent : T *⊢[𝓓]! p ↔ ¬(𝓓)-Consistent (insert (~p) T) := by
  constructor;
  . intro h;
    apply iff_insert_Inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact imp_trans''! hΓ₂ dni!;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_Inconsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . exact imp_trans''! (imp_swap'! $ and_imply_iff_imply_imply'!.mp hΓ₂) dne!;

lemma unprovable_iff_insert_neg_Consistent : T *⊬[𝓓]! p ↔ (𝓓)-Consistent (insert (~p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Consistent.mpr;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Consistent.mp;

lemma neg_provable_iff_insert_not_Consistent : T *⊢[𝓓]! ~p ↔ ¬(𝓓)-Consistent (insert (p) T) := by
  constructor;
  . intro h;
    apply iff_insert_Inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . assumption;
    . apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact hΓ₂;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_Inconsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . exact imp_swap'! $ and_imply_iff_imply_imply'!.mp hΓ₂;

lemma neg_unprovable_iff_insert_Consistent : T *⊬[𝓓]! ~p ↔ (𝓓)-Consistent (insert (p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Consistent.mpr;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Consistent.mp;

variable (hConsis : (𝓓)-Consistent T)

lemma unprovable_either : ¬(T *⊢[𝓓]! p ∧ T *⊢[𝓓]! ~p) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[𝓓]! ⊥ := hC₂ ⨀ hC₁;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp this;
  have : 𝓓 ⊬! List.conj' Γ ⟶ ⊥ := hConsis hΓ₁;
  have : 𝓓 ⊢! List.conj' Γ ⟶ ⊥ := FiniteContext.toₛ! hΓ₂;
  contradiction;

lemma not_provable_falsum : T *⊬[𝓓]! ⊥ := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp $ hC;
  have : 𝓓 ⊬! List.conj' Γ ⟶ ⊥ := hConsis hΓ₁;
  have : 𝓓 ⊢! List.conj' Γ ⟶ ⊥ := hΓ₂;
  contradiction;

lemma not_mem_falsum_of_Consistent : ⊥ ∉ T := by
  by_contra hC;
  have : 𝓓 ⊬! ⊥ ⟶ ⊥ := hConsis (Γ := [⊥]) (by simpa);
  have : 𝓓 ⊢! ⊥ ⟶ ⊥ := efq!;
  contradiction;

lemma either_consistent (p) : (𝓓)-Consistent (insert p T) ∨ (𝓓)-Consistent (insert (~p) T) := by
  by_contra hC; push_neg at hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_Inconsistent.mp hC.1;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_Inconsistent.mp hC.2;

  replace hΓ₂ := neg_equiv'!.mp hΓ₂;
  replace hΔ₂ := neg_equiv'!.mp hΔ₂;
  have : 𝓓 ⊢! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := demorgan₁'! $ or₃'''! (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΓ₂) or₁!) (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΔ₂) or₂!) lem!;
  have : 𝓓 ⊬! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := unprovable_imp_trans''! imply_left_concat_conj'! (hConsis (by
    simp;
    intro q hq;
    rcases hq with hΓ | hΔ
    . exact hΓ₁ _ hΓ;
    . exact hΔ₁ _ hΔ;
  ));
  contradiction;

lemma exists_maximal_Consistent_theory
  : ∃ Z, (𝓓)-Consistent Z ∧ T ⊆ Z ∧ ∀ U, (𝓓)-Consistent U → Z ⊆ U → U = Z
  := zorn_subset_nonempty { T : Theory α | (𝓓)-Consistent T } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [Consistent, Set.mem_setOf_eq, Set.mem_sUnion];
    constructor;
    . intro Γ;
      by_contra hC;
      obtain ⟨hΓs, hΓd⟩ := by simpa using hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro p hp; simp_all);
      simp [List.coe_toFinset] at hUs;
      have : (𝓓)-Consistent U := hc hUc;
      have : ¬(𝓓)-Consistent U := by
        simp only [Consistent, not_forall, not_not, exists_prop];
        existsi Γ;
        constructor;
        . intro p hp; exact hUs hp;
        . assumption;
      contradiction;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T hConsis
protected alias lindenbaum := exists_maximal_Consistent_theory

open Classical in
lemma intro_union_Consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ T₁) → (∀ p ∈ Γ₂, p ∈ T₂) → 𝓓 ⊬! Γ₁.conj' ⋏ Γ₂.conj' ⟶ ⊥) : (𝓓)-Consistent (T₁ ∪ T₂) := by
  intro Δ hΔ;
  simp at hΔ;
  let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  have : 𝓓 ⊬! Δ₁.conj' ⋏ Δ₂.conj' ⟶ ⊥ := @h Δ₁ Δ₂ (by intro _ h; simpa using List.of_mem_filter h) (by intro _ h; simpa using List.of_mem_filter h);
  exact unprovable_imp_trans''! (by
    apply FiniteContext.deduct'!;
    apply iff_provable_list_conj.mpr;
    intro q hq;
    cases (hΔ q hq);
    . exact iff_provable_list_conj.mp (and₁'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
    . exact iff_provable_list_conj.mp (and₂'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
  ) this;

end Theory

structure MaximalConsistentTheory (𝓓 : DeductionParameter α) where
  theory : Theory α
  consistent : (𝓓)-Consistent theory
  maximal : ∀ {U}, theory ⊂ U → ¬(𝓓)-Consistent U

notation "(" 𝓓 ")-MCT" => MaximalConsistentTheory 𝓓

namespace MaximalConsistentTheory

open Theory

variable {𝓓 : DeductionParameter α}
variable {Ω Ω₁ Ω₂ : (𝓓)-MCT}
variable {p : Formula α}

lemma exists_maximal_Lconsistented_theory (consisT : (𝓓)-Consistent T) : ∃ Ω : (𝓓)-MCT, (T ⊆ Ω.theory) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := Theory.lindenbaum consisT;
  existsi ⟨
    Ω,
    hΩ₁,
    by
      rintro U ⟨hU₁, hU₂⟩;
      by_contra hC;
      have : U = Ω := hΩ₃ U hC hU₁;
      subst_vars;
      simp at hU₂,
  ⟩;
  exact hΩ₂;

alias lindenbaum := exists_maximal_Lconsistented_theory

noncomputable instance [System.Consistent 𝓓] : Inhabited (𝓓)-MCT := ⟨lindenbaum self_Consistent |>.choose⟩

lemma either_mem (Ω : (𝓓)-MCT) (p) : p ∈ Ω.theory ∨ ~p ∈ Ω.theory := by
  by_contra hC; push_neg at hC;
  cases either_consistent Ω.consistent p with
  | inl h => have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

lemma maximal' {p : Formula α} (hp : p ∉ Ω.theory) : ¬(𝓓)-Consistent (insert p Ω.theory) := Ω.maximal (Set.ssubset_insert hp)

lemma membership_iff : (p ∈ Ω.theory) ↔ (Ω.theory *⊢[𝓓]! p) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~p ∉ Ω.theory by apply or_iff_not_imp_right.mp $ (either_mem Ω p); assumption;
    by_contra hC;
    have hnp : Ω.theory *⊢[𝓓]! ~p := Context.by_axm! hC;
    have := hnp ⨀ hp;
    have := not_provable_falsum Ω.consistent;
    contradiction;

lemma subset_axiomset : Ax(𝓓) ⊆ Ω.theory := by
  intro p hp;
  apply membership_iff.mpr;
  apply Context.of!;
  exact ⟨Deduction.maxm (by aesop)⟩

@[simp] lemma not_mem_falsum : ⊥ ∉ Ω.theory := not_mem_falsum_of_Consistent Ω.consistent

@[simp] lemma mem_verum : ⊤ ∈ Ω.theory := by apply membership_iff.mpr; apply verum!;

@[simp]
lemma unprovable_falsum : Ω.theory *⊬[𝓓]! ⊥ := by apply membership_iff.not.mp; simp

lemma iff_mem_neg : (~p ∈ Ω.theory) ↔ (p ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.theory *⊢[𝓓]! ⊥ := hnp ⨀ hp;
    have : Ω.theory *⊬[𝓓]! ⊥ := unprovable_falsum;
    contradiction;
  . intro hp;
    have := provable_iff_insert_neg_not_Consistent.not.mp $ membership_iff.not.mp hp;
    have := (not_imp_not.mpr $ Ω.maximal (U := insert (~p) Ω.theory)) this;
    simp [Set.ssubset_def] at this;
    apply this;
    simp;

lemma iff_mem_negneg : (~~p ∈ Ω.theory) ↔ (p ∈ Ω.theory) := by
  simp [membership_iff];
  constructor;
  . intro h; exact dne'! h;
  . intro h; exact dni'! h;

@[simp]
lemma iff_mem_imp : ((p ⟶ q) ∈ Ω.theory) ↔ (p ∈ Ω.theory) → (q ∈ Ω.theory) := by
  constructor;
  . intro hpq hp;
    replace dpq := membership_iff.mp hpq;
    replace dp  := membership_iff.mp hp;
    apply membership_iff.mpr;
    exact dpq ⨀ dp;
  . intro h;
    replace h : p ∉ Ω.theory ∨ q ∈ Ω.theory := or_iff_not_imp_left.mpr (by simpa using h);
    cases h with
    | inl h =>
      apply membership_iff.mpr;
      exact efq_of_neg! $ membership_iff.mp $ iff_mem_neg.mpr h;
    | inr h =>
      apply membership_iff.mpr;
      exact imply₁! ⨀ (membership_iff.mp h)

@[simp]
lemma iff_mem_and : ((p ⋏ q) ∈ Ω.theory) ↔ (p ∈ Ω.theory) ∧ (q ∈ Ω.theory) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    constructor;
    . apply membership_iff.mpr; exact and₁'! hpq;
    . apply membership_iff.mpr; exact and₂'! hpq;
  . rintro ⟨hp, hq⟩;
    apply membership_iff.mpr;
    exact and₃'! (membership_iff.mp hp) (membership_iff.mp hq);

@[simp]
lemma iff_mem_or : ((p ⋎ q) ∈ Ω.theory) ↔ (p ∈ Ω.theory) ∨ (q ∈ Ω.theory) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    by_contra hC; simp [not_or] at hC;
    have ⟨hp, hq⟩ := hC;
    replace hp := membership_iff.mp $ iff_mem_neg.mpr hp;
    replace hq := membership_iff.mp $ iff_mem_neg.mpr hq;
    have : Ω.theory *⊢[𝓓]! ⊥ := or₃'''! hp hq hpq;
    have : Ω.theory *⊬[𝓓]! ⊥ := unprovable_falsum;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact or₁'! (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact or₂'! (membership_iff.mp hq);

lemma iff_congr : (Ω.theory *⊢[𝓓]! (p ⟷ q)) → ((p ∈ Ω.theory) ↔ (q ∈ Ω.theory)) := by
  intro hpq;
  constructor;
  . intro hp; exact iff_mem_imp.mp (membership_iff.mpr $ and₁'! hpq) hp;
  . intro hq; exact iff_mem_imp.mp (membership_iff.mpr $ and₂'! hpq) hq;

lemma mem_dn_iff : (p ∈ Ω.theory) ↔ (~~p ∈ Ω.theory) := iff_congr $ dn!

lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.theory = Ω₂.theory := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases Ω₁; cases Ω₂; simp_all;

lemma intro_equality {h : ∀ p, p ∈ Ω₁.theory → p ∈ Ω₂.theory} : Ω₁ = Ω₂ := by
  exact equality_def.mpr $ Set.eq_of_subset_of_subset
    (by intro p hp; exact h p hp)
    (by
      intro p;
      contrapose;
      intro hp;
      apply iff_mem_neg.mp;
      apply h;
      apply iff_mem_neg.mpr hp;
    )

lemma neg_imp (h : q ∈ Ω₂.theory → p ∈ Ω₁.theory) : (~p ∈ Ω₁.theory) → (~q ∈ Ω₂.theory) := by
  contrapose;
  intro hq;
  apply iff_mem_neg.mp;
  apply mem_dn_iff.mp;
  apply h;
  exact mem_dn_iff.mpr $ iff_mem_neg.mpr hq;

lemma neg_iff (h : p ∈ Ω₁.theory ↔ q ∈ Ω₂.theory) : (~p ∈ Ω₁.theory) ↔ (~q ∈ Ω₂.theory) := ⟨neg_imp $ h.mpr, neg_imp $ h.mp⟩

-- These lemmata require 𝓓 normality
section Normal

variable [𝓓.Normal]

lemma iff_mem_multibox : (□^[n]p ∈ Ω.theory) ↔ (∀ {Ω' : (𝓓)-MCT}, (□''⁻¹^[n]Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := by
  constructor;
  . intro hp Ω' hΩ'; apply hΩ'; simpa;
  . contrapose;
    push_neg;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (𝓓 := 𝓓) (T := insert (~p) (□''⁻¹^[n]Ω.theory)) (by
      apply unprovable_iff_insert_neg_Consistent.mp;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : 𝓓 ⊢! □^[n]Γ.conj' ⟶ □^[n]p := imply_multibox_distribute'! hΓ₂;
      have : 𝓓 ⊬! □^[n]Γ.conj' ⟶ □^[n]p := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : 𝓓 ⊬! (□'^[n]Γ : List (Formula α)).conj' ⟶ □^[n]p := FiniteContext.provable_iff.not.mp $ this (□'^[n]Γ) (by
          intro q hq;
          obtain ⟨r, hr₁, hr₂⟩ := by simpa using hq;
          subst hr₂;
          simpa using hΓ₁ r hr₁;
        );
        revert this;
        contrapose;
        simp [neg_neg];
        exact imp_trans''! collect_multibox_conj'!;
      contradiction;
    );
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by simp_all) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]
lemma iff_mem_box : (□p ∈ Ω.theory) ↔ (∀ {Ω' : (𝓓)-MCT}, (□''⁻¹Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := iff_mem_multibox (n := 1)

lemma multibox_dn_iff : (□^[n](~~p) ∈ Ω.theory) ↔ (□^[n]p ∈ Ω.theory) := by
  simp only [iff_mem_multibox];
  constructor;
  . intro h Ω hΩ; exact iff_mem_negneg.mp $ h hΩ;
  . intro h Ω hΩ; exact iff_mem_negneg.mpr $ h hΩ;

lemma box_dn_iff : (□~~p ∈ Ω.theory) ↔ (□p ∈ Ω.theory) := multibox_dn_iff (n := 1)

lemma mem_multibox_dual : □^[n]p ∈ Ω.theory ↔ ~(◇^[n](~p)) ∈ Ω.theory := by
  simp [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multibox_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multibox_duality!);
lemma mem_box_dual : □p ∈ Ω.theory ↔ (~(◇(~p)) ∈ Ω.theory) := mem_multibox_dual (n := 1)

-- lemma multidia_dn_iff : (◇^[n](~~p) ∈ Ω.theory) ↔ (◇^[n]p ∈ Ω.theory) := by sorry

lemma dia_dn_iff : (◇~~p ∈ Ω.theory) ↔ (◇p) ∈ Ω.theory := neg_iff box_dn_iff -- TODO: multidia_dn_iff (n := 1)

lemma mem_multidia_dual : ◇^[n]p ∈ Ω.theory ↔ ~(□^[n](~p)) ∈ Ω.theory := by
  simp [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multidia_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multidia_duality!);
lemma mem_dia_dual : ◇p ∈ Ω.theory ↔ (~(□(~p)) ∈ Ω.theory) := mem_multidia_dual (n := 1)

lemma multibox_multidia : (∀ {p : Formula α}, (□^[n]p ∈ Ω₁.theory → p ∈ Ω₂.theory)) ↔ (∀ {p : Formula α}, (p ∈ Ω₂.theory → ◇^[n]p ∈ Ω₁.theory)) := by
  constructor;
  . intro H p;
    contrapose;
    intro h;
    apply iff_mem_neg.mp;
    apply H;
    apply mem_dn_iff.mpr;
    apply (neg_iff $ mem_multidia_dual).mp;
    exact iff_mem_neg.mpr h;
  . intro H p;
    contrapose;
    intro h;
    apply iff_mem_neg.mp;
    apply (neg_iff $ mem_multibox_dual).mpr;
    apply iff_mem_negneg.mpr;
    apply H;
    exact iff_mem_neg.mpr h;

variable {Γ : List (Formula α)}

lemma iff_mem_conj' : (Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, p ∈ Ω.theory) := by simp [membership_iff, iff_provable_list_conj];

lemma iff_mem_multibox_conj' : (□^[n]Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, □^[n]p ∈ Ω.theory) := by
  simp only [iff_mem_multibox, iff_mem_conj'];
  constructor;
  . intro h p hp Ω' hΩ';
    exact (h hΩ') p hp;
  . intro h Ω' hΩ' p hp;
    exact @h p hp Ω' hΩ';

lemma iff_mem_box_conj' : (□Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, □p ∈ Ω.theory) := iff_mem_multibox_conj' (n := 1)

end Normal

end MaximalConsistentTheory

end

end LO.Modal.Standard
