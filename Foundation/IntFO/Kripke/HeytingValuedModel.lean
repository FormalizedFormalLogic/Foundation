import Foundation.IntFO.Kripke.Basic

namespace LO.FirstOrder.RelationalKripkeModel

variable {L : Language} [L.Relational] (𝓚 : RelationalKripkeModel L)

/-- Downword closed sets of Kripke model -/
structure DownwardClosed where
  val : Set 𝓚
  downward_closed' : ∀ {w v}, w ≤ v → v ∈ val → w ∈ val

variable {𝓚}

namespace DownwardClosed

lemma ext' {X Y : 𝓚.DownwardClosed} (h : ∀ w, w ∈ X.val ↔ w ∈ Y.val) : X = Y := by
  rcases X with ⟨X, _⟩
  rcases Y with ⟨Y, _⟩
  have : X = Y := by ext w; simp [h]
  rcases this
  rfl

instance : SetLike 𝓚.DownwardClosed 𝓚 where
  coe s := s.val
  coe_injective' X Y h := by
    apply ext'
    simp_all

@[simp] lemma mem_val {w : 𝓚} : w ∈ DownwardClosed.mk s h ↔ w ∈ s := by rfl

@[ext] lemma ext {X Y : 𝓚.DownwardClosed} (h : ∀ w, w ∈ X ↔ w ∈ Y) : X = Y := ext' h

lemma downward_closed {w v : 𝓚} {X : 𝓚.DownwardClosed} (h : w ≤ v) :
    v ∈ X → w ∈ X := X.downward_closed' h

def closure (s : Set 𝓚) : 𝓚.DownwardClosed where
  val := {w | ∃ v ∈ s, w ≤ v}
  downward_closed' {w v} h H := by
    have : ∃ x ∈ s, v ≤ x := by simpa using H
    rcases this with ⟨x, hx, hvx⟩
    suffices ∃ x ∈ s, w ≤ x by simpa
    exact ⟨x, hx, le_trans h hvx⟩

@[simp] lemma mem_closure_iff {w} {S : Set 𝓚} : w ∈ closure S ↔ ∃ v ∈ S, w ≤ v := by simp [closure]

instance : PartialOrder 𝓚.DownwardClosed where
  le_antisymm X Y hXY hYX := by
    ext w
    exact ⟨@hXY w, @hYX w⟩

def iSup (X : ι → 𝓚.DownwardClosed) : 𝓚.DownwardClosed where
  val := ⋃ i, X i
  downward_closed' {w v} h hv := by
    suffices ∃ i, w ∈ X i by simpa
    rcases show ∃ i, v ∈ X i by simpa using hv with ⟨i, hi⟩
    exact ⟨i, (X i).downward_closed h hi⟩

instance : SupSet 𝓚.DownwardClosed := ⟨fun 𝓧 ↦ iSup fun X : 𝓧 ↦ X⟩

lemma sSup_def (𝓧 : Set 𝓚.DownwardClosed) : sSup 𝓧 = iSup fun X : 𝓧 ↦ X := rfl

lemma iSup_def (X : ι → 𝓚.DownwardClosed) : ⨆ i, X i = iSup X := calc
  _ = sSup (Set.range X) := rfl
  _ = _ := by simp [sSup_def, iSup]

@[simp] lemma mem_sSup_iff {𝓧 : Set 𝓚.DownwardClosed} :
  w ∈ sSup 𝓧 ↔ ∃ X ∈ 𝓧, w ∈ X := by simp [sSup_def, iSup]

@[simp] lemma mem_iSup_iff {X : ι → 𝓚.DownwardClosed} :
  w ∈ ⨆ i, X i ↔ ∃ i, w ∈ X i := by simp [iSup_def, iSup]

def iInf (X : ι → 𝓚.DownwardClosed) : 𝓚.DownwardClosed where
  val := ⋂ i, X i
  downward_closed' {w v} h hv := by
    suffices ∀ i, w ∈ X i by simpa
    intro i
    have : ∀ i, v ∈ X i := by simpa using hv
    exact (X i).downward_closed h (this i)

instance : InfSet 𝓚.DownwardClosed := ⟨fun 𝓧 ↦ iInf fun X : 𝓧 ↦ X⟩

lemma sInf_def (𝓧 : Set 𝓚.DownwardClosed) : sInf 𝓧 = iInf fun X : 𝓧 ↦ X := rfl

lemma iInf_def (X : ι → 𝓚.DownwardClosed) : ⨅ i, X i = iInf X := calc
  _ = sInf (Set.range X) := rfl
  _ = _ := by simp [sInf_def, iInf]

@[simp] lemma mem_sInf_iff {𝓧 : Set 𝓚.DownwardClosed} :
  w ∈ sInf 𝓧 ↔ ∀ X ∈ 𝓧, w ∈ X := by simp [sInf_def, iInf]

@[simp] lemma mem_iInf_iff {X : ι → 𝓚.DownwardClosed} :
  w ∈ ⨅ i, X i ↔ ∀ i, w ∈ X i := by simp [iInf_def, iInf]

instance : Lattice 𝓚.DownwardClosed where
  sup X Y := sSup {X, Y}
  inf X Y := sInf {X, Y}
  le_sup_left X Y w hw := by simp [hw]
  le_sup_right X Y w hw := by simp [hw]
  sup_le X Y Z hXY hYZ w hw := by
    rcases show w ∈ X ∨ w ∈ Y by simpa using hw with (hw | hw)
    · exact hXY hw
    · exact hYZ hw
  inf_le_left X Y w hw := by
    rcases show w ∈ X ∧ w ∈ Y by simpa using hw with ⟨hw, _⟩
    exact hw
  inf_le_right X Y w hw := by
    rcases show w ∈ X ∧ w ∈ Y by simpa using hw with ⟨_, hw⟩
    exact hw
  le_inf X Y Z hXY hXZ w hw := by
    simp [hXY hw, hXZ hw]

@[simp] lemma mem_sup {w : 𝓚} {X Y : 𝓚.DownwardClosed} :
    w ∈ X ⊔ Y ↔ w ∈ X ∨ w ∈ Y := calc
  _ ↔ w ∈ sSup {X, Y} := by rfl
  _ ↔ _ := by simp

@[simp] lemma mem_inf {w : 𝓚} {X Y : 𝓚.DownwardClosed} :
    w ∈ X ⊓ Y ↔ w ∈ X ∧ w ∈ Y := calc
  _ ↔ w ∈ sInf {X, Y} := by rfl
  _ ↔ _ := by simp

def univ : 𝓚.DownwardClosed where
  val := Set.univ
  downward_closed' w v := by simp

def empty : 𝓚.DownwardClosed where
  val := ∅
  downward_closed' _ _ := by simp_all

def himp (X Y : 𝓚.DownwardClosed) : 𝓚.DownwardClosed where
  val := {w | ∀ v ≤ w, v ∈ X → v ∈ Y}
  downward_closed' {w v} h hv := by
    suffices ∀ x ≤ w, x ∈ X → x ∈ Y by simpa
    intro x hxw hxX
    have : ∀ x ≤ v, x ∈ X → x ∈ Y := by simpa using hv
    exact this x (le_trans hxw h) hxX

instance : HeytingAlgebra 𝓚.DownwardClosed where
  top := univ
  le_top X w := by simp [univ]
  bot := empty
  bot_le X w := by simp [empty]
  himp := himp
  le_himp_iff X Y Z := by
    constructor
    · intro hXYZ w hw
      rcases show w ∈ X ∧ w ∈ Y by simpa using hw with ⟨hwX, hwY⟩
      have : ∀ v ≤ w, v ∈ Y → v ∈ Z := hXYZ hwX
      exact this w (by rfl) hwY
    · intro h w hwX
      suffices ∀ v ≤ w, v ∈ Y → v ∈ Z by simpa [himp]
      intro v hvw hvY
      exact h (show v ∈ X ⊓ Y by simp [X.downward_closed hvw hwX, hvY])
  compl X := X.himp empty
  himp_bot X := rfl

@[simp] lemma mem_top (w : 𝓚) : w ∈ (⊤ : 𝓚.DownwardClosed) := by trivial

@[simp] lemma not_mem_top (w : 𝓚) : w ∉ (⊥ : 𝓚.DownwardClosed) := by rintro ⟨⟩

lemma mem_himp_iff {X Y : 𝓚.DownwardClosed} : w ∈ X ⇨ Y ↔ ∀ v ≤ w, v ∈ X → v ∈ Y := calc
  _ ↔ w ∈ X.himp Y := by rfl
  _ ↔ _ := by simp [himp]

lemma mem_compl_iff {X : 𝓚.DownwardClosed} : w ∈ Xᶜ ↔ ∀ v ≤ w, v ∉ X := calc
  _ ↔ w ∈ X.himp empty := by rfl
  _ ↔ _ := by simp [himp, empty]

def value (φ : Sentenceᵢ L) : 𝓚.DownwardClosed where
  val := {w | w ⊩ φ}
  downward_closed' h := Forces.monotone' h

scoped notation "‖" φ "‖" => value φ

@[simp] lemma mem_value_iff {w : 𝓚} {φ : Sentenceᵢ L} : w ∈ ‖φ‖ ↔ w ⊩ φ := by simp [value]

@[simp] lemma value_verum : (‖⊤‖ : 𝓚.DownwardClosed) = ⊤ := by ext; simp

@[simp] lemma value_falsum : (‖⊥‖ : 𝓚.DownwardClosed) = ⊥ := by ext; simp

@[simp] lemma value_and (φ ψ : Sentenceᵢ L) : (‖φ ⋏ ψ‖ : 𝓚.DownwardClosed) = ‖φ‖ ⊓ ‖ψ‖ := by ext; simp

@[simp] lemma value_or (φ ψ : Sentenceᵢ L) : (‖φ ⋎ ψ‖ : 𝓚.DownwardClosed) = ‖φ‖ ⊔ ‖ψ‖ := by ext; simp

@[simp] lemma value_imply (φ ψ : Sentenceᵢ L) : (‖φ ➝ ψ‖ : 𝓚.DownwardClosed) = ‖φ‖ ⇨ ‖ψ‖ := by
  ext; simp [ForcingRelation.Kripke.implies, mem_himp_iff]

@[simp] lemma value_not (φ : Sentenceᵢ L) : (‖∼φ‖ : 𝓚.DownwardClosed) = ‖φ‖ᶜ := by
  ext; simp [ForcingRelation.Kripke.not, mem_compl_iff]

end DownwardClosed

end LO.FirstOrder.RelationalKripkeModel
