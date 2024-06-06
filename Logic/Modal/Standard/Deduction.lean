import Logic.Logic.HilbertStyle.Basic
import Logic.Logic.HilbertStyle.Supplemental
import Logic.Modal.Standard.System
import Logic.Modal.Standard.Formula

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α]

/--
  Parameter for deduction system.
-/
structure DeductionParameter (α) where
  axiomSet : AxiomSet α
  nec : Bool
notation "Ax(" L ")" => DeductionParameter.axiomSet L

namespace DeductionParameter

variable (L L₁ L₂ : DeductionParameter α)

class HasNec where
  has_nec : L.nec = true := by rfl

class IncludeK where
  include_K : 𝗞 ⊆ Ax(L) := by intro; aesop;

/--
  Deduction system of `L` is normal modal Logic.
-/
class Normal extends HasNec L, IncludeK L

end DeductionParameter


inductive Deduction (L : DeductionParameter α) : (Formula α) → Type _
  | maxm {p}     : p ∈ Ax(L) → Deduction L p
  | mdp {p q}    : Deduction L (p ⟶ q) → Deduction L p → Deduction L q
  | nec {p}      : (L.nec = true) → Deduction L p → Deduction L (□p)
  | verum        : Deduction L ⊤
  | imply₁ p q   : Deduction L (p ⟶ q ⟶ p)
  | imply₂ p q r : Deduction L ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ p q    : Deduction L (p ⋏ q ⟶ p)
  | conj₂ p q    : Deduction L (p ⋏ q ⟶ q)
  | conj₃ p q    : Deduction L (p ⟶ q ⟶ p ⋏ q)
  | disj₁ p q    : Deduction L (p ⟶ p ⋎ q)
  | disj₂ p q    : Deduction L (q ⟶ p ⋎ q)
  | disj₃ p q r  : Deduction L ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne p        : Deduction L (~~p ⟶ p)

namespace Deduction

open DeductionParameter

instance : System (Formula α) (DeductionParameter α) := ⟨Deduction⟩

variable {L L₁ L₂ : DeductionParameter α}

instance : System.Classical L where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  conj₁ := conj₁
  conj₂ := conj₂
  conj₃ := conj₃
  disj₁ := disj₁
  disj₂ := disj₂
  disj₃ := disj₃
  dne := dne

def maxm_subset (hNec : L₁.nec ≤ L₂.nec) (hAx : Ax(L₁) ⊆ Ax(L₂)) : (L₁ ⊢ p) → (L₂ ⊢ p)
  | maxm h => maxm (hAx h)
  | mdp ih₁ ih₂  => mdp (maxm_subset hNec hAx ih₁) (maxm_subset hNec hAx ih₂)
  | nec p h      => nec (by aesop) $ maxm_subset hNec hAx h
  | verum        => verum
  | imply₁ _ _   => imply₁ _ _
  | imply₂ _ _ _ => imply₂ _ _ _
  | conj₁ _ _    => conj₁ _ _
  | conj₂ _ _    => conj₂ _ _
  | conj₃ _ _    => conj₃ _ _
  | disj₁ _ _    => disj₁ _ _
  | disj₂ _ _    => disj₂ _ _
  | disj₃ _ _ _  => disj₃ _ _ _
  | dne _        => dne _

lemma maxm_subset! (hNec : L₁.nec ≤ L₂.nec) (hAx : Ax(L₁) ⊆ Ax(L₂)) (h : L₁ ⊢! p) : L₂ ⊢! p := ⟨maxm_subset hNec hAx h.some⟩

@[simp]
lemma reducible_of_subset (hNec : L₁.nec ≤ L₂.nec) (hAx : Ax(L₁) ⊆ Ax(L₂) := by intro; aesop) : L₁ ≤ₛ L₂ := by
  intro p hp;
  apply maxm_subset! hNec hAx hp;

instance [HasNec L] : System.Necessitation L where
  nec := nec HasNec.has_nec

instance [IncludeK L] : System.HasAxiomK L where
  K _ _ := maxm $ Set.mem_of_subset_of_mem (IncludeK.include_K) (by simp);

instance [Normal L] : System.K L where

lemma inducition_with_nec [HasNec L]
  {motive  : (p : Formula α) → Deduction L p → Sort*}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(L)) → motive p (maxm h))
  (hMdp    : ∀ {p q}, (hpq : L ⊢ p ⟶ q) → (hp : L ⊢ p) → motive (p ⟶ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (hNec    : ∀ {p}, (hp : L ⊢ p) → motive p hp → motive (□p) (nec HasNec.has_nec hp))
  (hVerum  : motive ⊤ verum)
  (hImply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ imply₁ p q)
  (hImply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ imply₂ p q r)
  (hConj₁  : ∀ {p q}, motive (p ⋏ q ⟶ p) $ conj₁ p q)
  (hConj₂  : ∀ {p q}, motive (p ⋏ q ⟶ q) $ conj₂ p q)
  (hConj₃  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ conj₃ p q)
  (hDisj₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ disj₁ p q)
  (hDisj₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ disj₂ p q)
  (hDisj₃  : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ disj₃ p q r)
  (hDne    : ∀ {p}, motive (~~p ⟶ p) $ dne p)
  : ∀ {p}, (d : L ⊢ p) → motive p d := by
  intro p d;
  induction d with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp hpq hp ihpq ihp
  | nec _ hp ihp => exact hNec hp ihp
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
  nec := true

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


protected abbrev GL : DeductionParameter α := NecOnly (𝗞 ∪ 𝗟)
notation "𝐆𝐋" => DeductionParameter.GL
instance : Normal (α := α) 𝐆𝐋 where


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


protected abbrev Ver : DeductionParameter α := NecOnly (𝗞 ∪ 𝗩𝗲𝗿)
notation "𝐕𝐞𝐫" => DeductionParameter.Ver
instance : Normal (α := α) 𝐕𝐞𝐫 where


/-- Logic of Pure Necessitation -/
protected abbrev N : DeductionParameter α := NecOnly ∅
notation "𝐍" => DeductionParameter.N

end DeductionParameter

@[simp] lemma reducible_K_KT : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐓 := by simp

@[simp] lemma reducible_K_KD : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐃 := by simp

@[simp] lemma reducible_KT_S4 : (𝐊𝐓 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by simp

@[simp] lemma reducible_S4_S4Dot2 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟐 := by simp

@[simp] lemma reducible_S4_S4Dot3 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟑 := by simp

@[simp] lemma reducible_S4_S4Grz : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒𝐆𝐫𝐳 := by simp

@[simp] lemma reducible_K_GL : (𝐊 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by simp

end LO.Modal.Standard
