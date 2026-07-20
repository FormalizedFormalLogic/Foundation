module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Traces of finite permutations
-/

@[expose] public section

namespace Equiv.Perm

lemma partition_parts_card_eq_cycleFactorsFinset_card_add_fixed
    {γ : Type*} [DecidableEq γ] [Fintype γ] (σ : Perm γ) :
    σ.partition.parts.card = σ.cycleFactorsFinset.card + Fintype.card {x : γ // σ x = x} := by
  rw [parts_partition, Multiset.card_add, Multiset.card_replicate, cycleType_def]
  simp only [Multiset.card_map]
  congr 1
  calc
    Fintype.card γ - σ.support.card =
        Fintype.card {x : γ // ¬x ∈ σ.support} := by
      rw [Fintype.card_subtype_compl (fun x : γ ↦ x ∈ σ.support)]
      have hs :
          Fintype.card {x : γ // x ∈ σ.support} = σ.support.card :=
        Fintype.card_of_subtype σ.support (fun x : γ ↦ Iff.rfl)
      rw [hs]
    _ = Fintype.card {x : γ // σ x = x} := by
      refine Fintype.card_congr (Equiv.subtypeEquivRight ?_).symm
      intro x
      simp [mem_support]

lemma fintype_card_eq_fintype_card_subtype_add_fintype_card_subtype_not
    {γ : Type*} [Fintype γ] {P : γ → Prop} [DecidablePred P] :
    Fintype.card γ = Fintype.card {x : γ // P x} + Fintype.card {x : γ // ¬P x} := by
  have hle : Fintype.card {x : γ // P x} ≤ Fintype.card γ :=
    Fintype.card_subtype_le P
  rw [Fintype.card_subtype_compl P]
  omega

namespace FirstReturn

section

variable {γ : Type*} [DecidableEq γ] [Fintype γ] {P : γ → Prop} [DecidablePred P]

omit [DecidableEq γ] [DecidablePred P] in
lemma exists_return
    (f : Perm γ) (x : {x // P x}) : ∃ n, 0 < n ∧ P ((f ^ n) x) := by
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  simpa using x.2

/-- The least positive time at which the orbit of `x` returns to the subset `P`. -/
def time
    (f : Perm γ) (x : {x // P x}) : ℕ :=
  Nat.find (exists_return f x)

omit [DecidableEq γ] in
lemma time_spec
    (f : Perm γ) (x : {x // P x}) :
    0 < time f x ∧ P ((f ^ time f x) x) := by
  unfold time
  exact Nat.find_spec (exists_return f x)

omit [DecidableEq γ] in
lemma time_le_of_return
    {f : Perm γ} {x : {x // P x}} {n : ℕ}
    (h : 0 < n ∧ P ((f ^ n) x)) : time f x ≤ n := by
  unfold time
  exact Nat.find_min' (exists_return f x) h

omit [DecidableEq γ] in
lemma not_return_of_lt_time
    {f : Perm γ} {x : {x // P x}} {n : ℕ}
    (h : n < time f x) : ¬(0 < n ∧ P ((f ^ n) x)) := by
  unfold time at h
  exact Nat.find_min (exists_return f x) h

/-- The first-return map of a finite permutation to a decidable subset. -/
def map
    (f : Perm γ) (x : {x // P x}) : {x // P x} :=
  ⟨(f ^ time f x) x, (time_spec f x).2⟩

end

end FirstReturn

section trace

open FirstReturn

variable {γ : Type*} [DecidableEq γ] [Fintype γ] (f : Perm γ)
    {P : γ → Prop} [DecidablePred P]

/-- The first-return permutation of a finite permutation outside a decidable subset. -/
def trace
    (f : Perm γ) (P : γ → Prop) [DecidablePred P] : Perm {x // ¬P x} := by
  have map_inv_apply (g : Perm γ) (x : {x // ¬P x}) :
      map g⁻¹ (map g x) = x := by
    let n := time g x
    let y := map g x
    let m := time g⁻¹ y
    let z := map g⁻¹ y
    have hn : 0 < n := (time_spec g x).1
    have hgn : (g ^ n) (x : γ) = y := rfl
    have hym : (g⁻¹ ^ m) (y : γ) = z := rfl
    have hback : (g⁻¹ ^ n) (y : γ) = x := by
      rw [← hgn]
      calc
        (g⁻¹ ^ n) ((g ^ n) (x : γ)) = (g ^ n)⁻¹ ((g ^ n) x) := by rw [inv_pow]
        _ = x := by rw [inv_def]; exact (g ^ n).symm_apply_apply x
    have hmn : m ≤ n := time_le_of_return ⟨hn, by rw [hback]; exact x.2⟩
    have hmn' : m = n := by
      apply le_antisymm hmn
      by_contra h
      have hmnlt : m < n := by omega
      have hpow : g⁻¹ ^ m * g ^ n = g ^ (n - m) := by
        rw [pow_sub g hmn, inv_pow]
        exact (Commute.pow_pow_self g m n).inv_left.eq
      have hearly : (g ^ (n - m)) (x : γ) = z := by
        rw [← hpow, mul_apply, hgn, hym]
      exact not_return_of_lt_time (Nat.sub_lt hn (time_spec g⁻¹ y).1)
        ⟨Nat.sub_pos_of_lt hmnlt, by rw [hearly]; exact z.2⟩
    rw [hmn'] at hym
    exact Subtype.ext (hym.symm.trans hback)
  exact {
    toFun := map f
    invFun := map f⁻¹
    left_inv := map_inv_apply f
    right_inv := fun x ↦ by simpa using map_inv_apply f⁻¹ x }

omit [DecidableEq γ] in
@[simp] lemma trace_inv
    : f⁻¹.trace P = (f.trace P)⁻¹ := rfl

omit [DecidableEq γ] in
lemma exists_f_pow_trace_pow
    (n : ℕ) (x : {x // ¬P x}) :
    ∃ k : ℕ, (f ^ k) x = ((f.trace P ^ n) x : {x // ¬P x}) := by
  induction n generalizing x with
  | zero =>
      exact ⟨0, rfl⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih x
      let y := ((f.trace P) ^ n) x
      refine ⟨time f y + k, ?_⟩
      rw [pow_add, mul_apply, hk]
      rw [show n + 1 = 1 + n by omega, pow_add, mul_apply]
      rfl

omit [DecidableEq γ] in
lemma trace_sameCycle_of_f_pow
    : ∀ n : ℕ, ∀ x y : {x // ¬P x},
      (f ^ n) x = y → (f.trace P).SameCycle x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x y hn
      rcases n with _ | n
      · exact (Subtype.ext hn).sameCycle (f.trace P)
      · let N := n + 1
        let r := time f x
        let z := f.trace P x
        have hpos : 0 < N := Nat.succ_pos n
        have hrpos : 0 < r := by
          change 0 < time f x
          exact (time_spec f x).1
        have hrle : r ≤ N := by
          change time f x ≤ N
          exact time_le_of_return ⟨hpos, by rw [hn]; exact y.2⟩
        by_cases hrN : r = N
        · have hz : z = y := by
            have hspec : (f ^ r) (x : γ) = z := rfl
            have hn' : (f ^ r) (x : γ) = y := by
              rw [hrN]
              exact hn
            exact Subtype.ext (hspec.symm.trans hn')
          refine ⟨(1 : ℤ), ?_⟩
          simpa [hz]
        · have hrlt : r < N := lt_of_le_of_ne hrle hrN
          have hrest : (f ^ (N - r)) (z : γ) = y := by
            have hpow : f ^ (N - r) * f ^ r = f ^ N := pow_sub_mul_pow f hrle
            rw [← hn, ← hpow, mul_apply]
            rfl
          exact SameCycle.trans ⟨(1 : ℤ), by change f.trace P x = z; rfl⟩ <|
            ih (N - r) (Nat.sub_lt hpos hrpos) z y hrest

omit [DecidableEq γ] in
lemma trace_sameCycle_iff_f_sameCycle
    (x y : {x // ¬P x}) :
    (f.trace P).SameCycle x y ↔ f.SameCycle (x : γ) y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    obtain ⟨k, hk⟩ := exists_f_pow_trace_pow f n x
    exact ⟨k, by simpa [hn] using hk⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact trace_sameCycle_of_f_pow f n x y hn

end trace

section permCongr

variable {α β : Type*}

lemma sameCycle_permCongr (e : α ≃ β) (σ : Perm α) (x y : α) :
    (e.permCongr σ).SameCycle (e x) (e y) ↔ σ.SameCycle x y := by
  constructor
  · rintro ⟨i, hi⟩
    change (e.permCongrHom σ ^ i) (e x) = e y at hi
    rw [← map_zpow e.permCongrHom σ i] at hi
    refine ⟨i, e.injective ?_⟩
    simpa using hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change (e.permCongrHom σ ^ i) (e x) = e y
    rw [← map_zpow e.permCongrHom σ i]
    simp [hi]

end permCongr

variable {γ : Type*} [DecidableEq γ] [Fintype γ]

abbrev Orbit (σ : Perm γ) := Quotient (SameCycle.setoid σ)

instance (σ : Perm γ) : Fintype (σ.Orbit) :=
  have : DecidableRel σ.SameCycle := inferInstance
  Quotient.fintype _

namespace Orbit

def permCongr {α β : Type*} (e : α ≃ β) (σ : Perm α) :
    σ.Orbit ≃ (e.permCongr σ).Orbit where
  toFun :=
    Quotient.map e fun {a b} h ↦
      (sameCycle_permCongr e σ _ _).mpr h
  invFun :=
    Quotient.map e.symm fun {a b} h ↦ by
      change (e.permCongr σ).SameCycle a b at h
      have h' :
          (e.permCongr σ).SameCycle (e (e.symm a)) (e (e.symm b)) := by
        simpa using h
      exact (sameCycle_permCongr e σ (e.symm a) (e.symm b)).mp h'
  left_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
        change (⟦e.symm (e x)⟧ : σ.Orbit) = ⟦x⟧
        simp
  right_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
        change (⟦e (e.symm x)⟧ : (e.permCongr σ).Orbit) = ⟦x⟧
        simp

abbrev Meets
    (f : Perm γ) (P : γ → Prop) (q : f.Orbit) : Prop :=
  ∃ x : {x // P x}, q = ⟦(x : γ)⟧

abbrev Meeting (f : Perm γ) (P : γ → Prop) :=
  {q : f.Orbit // Meets f P q}

abbrev Avoiding (f : Perm γ) (P : γ → Prop) :=
  {q : f.Orbit // ¬Meets f P q}

abbrev Closed (f : Perm γ) (P : γ → Prop) :=
  Avoiding f (¬P ·)

instance instDecidablePredMeets (f : Perm γ) (P : γ → Prop) [DecidablePred P] :
    DecidablePred (Meets f P) := by
  intro q
  exact Quotient.recOnSubsingleton q fun a ↦
    decidable_of_iff (∃ x : γ, P x ∧ f.SameCycle a x) <| by
      constructor
      · rintro ⟨x, hxP, hcycle⟩
        exact ⟨⟨x, hxP⟩, Quotient.sound hcycle⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, x.2, Quotient.eq.mp hx⟩

theorem partition_parts_card_eq_fintype_card (σ : Perm γ) :
    σ.partition.parts.card = Fintype.card σ.Orbit := by
  let toPart : γ → σ.cycleFactorsFinset ⊕ {x : γ // σ x = x} := fun x ↦
    if hx : x ∈ σ.support then
      Sum.inl ⟨σ.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr hx⟩
    else
      Sum.inr ⟨x, by simpa [mem_support] using hx⟩
  have htoPart : ∀ x y, σ.SameCycle x y → toPart x = toPart y := by
    intro x y hxy
    unfold toPart
    by_cases hx : x ∈ σ.support
    · have hy : y ∈ σ.support := hxy.mem_support_iff.mp hx
      simp [hx, hy, hxy.cycleOf_eq]
    · have hy : ¬y ∈ σ.support := by
        intro hy
        exact hx (hxy.mem_support_iff.mpr hy)
      have hfix : σ x = x := by simpa [mem_support] using hx
      have hxy' : x = y := hxy.eq_of_left hfix
      simp [hy, hxy']
  let toPartQuot : σ.Orbit →
      σ.cycleFactorsFinset ⊕ {x : γ // σ x = x} :=
    Quotient.lift toPart htoPart
  have hbij : Function.Bijective toPartQuot := by
    constructor
    · intro q r hqr
      induction q using Quotient.inductionOn' with
      | h x =>
          induction r using Quotient.inductionOn' with
          | h y =>
              apply Quotient.sound
              change toPart x = toPart y at hqr
              unfold toPart at hqr
              by_cases hx : x ∈ σ.support
              · by_cases hy : y ∈ σ.support
                · rw [dif_pos hx, dif_pos hy] at hqr
                  have hcycle :
                      σ.cycleOf x = σ.cycleOf y :=
                    congrArg Subtype.val (Sum.inl.inj hqr)
                  exact (sameCycle_iff_cycleOf_eq_of_mem_support hx hy).mpr hcycle
                · rw [dif_pos hx, dif_neg hy] at hqr
                  cases hqr
              · by_cases hy : y ∈ σ.support
                · rw [dif_neg hx, dif_pos hy] at hqr
                  cases hqr
                · rw [dif_neg hx, dif_neg hy] at hqr
                  exact (congrArg Subtype.val (Sum.inr.inj hqr)).sameCycle σ
    · intro s
      rcases s with c | x
      · obtain ⟨y, hy⟩ :=
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1).exists_mem
        refine ⟨⟦y⟧, ?_⟩
        change toPart y = Sum.inl c
        have hσy : y ∈ σ.support := mem_cycleFactorsFinset_support_le c.2 hy
        unfold toPart
        rw [dif_pos hσy]
        exact congrArg Sum.inl (Subtype.ext ((cycle_is_cycleOf hy c.2).symm))
      · refine ⟨⟦(x : γ)⟧, ?_⟩
        change toPart (x : γ) = Sum.inr x
        have hx : ¬(x : γ) ∈ σ.support := by simpa [mem_support] using x.2
        unfold toPart
        rw [dif_neg hx]
  rw [partition_parts_card_eq_cycleFactorsFinset_card_add_fixed σ]
  calc
    σ.cycleFactorsFinset.card + Fintype.card {x : γ // σ x = x}
        = Fintype.card (σ.cycleFactorsFinset ⊕ {x : γ // σ x = x}) := by
      simp [Fintype.card_sum]
    _ = Fintype.card σ.Orbit := by
      exact (Fintype.card_of_bijective hbij).symm

theorem partition_parts_card_permCongr {α β : Type*}
    [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]
    (e : α ≃ β) (σ : Perm α) :
    (e.permCongr σ).partition.parts.card = σ.partition.parts.card := by
  calc
    (e.permCongr σ).partition.parts.card
        = Fintype.card (e.permCongr σ).Orbit := partition_parts_card_eq_fintype_card _
    _ = Fintype.card σ.Orbit := by
      exact (Fintype.card_congr (permCongr e σ)).symm
    _ = σ.partition.parts.card := (partition_parts_card_eq_fintype_card σ).symm

omit [DecidableEq γ] in
noncomputable def meetingEquivTrace {P : γ → Prop} [DecidablePred P] (f : Perm γ) :
    Meeting f (¬P ·) ≃ (f.trace P).Orbit := by
  let toMeeting : (f.trace P).Orbit → Meeting f (¬P ·) :=
    Quotient.lift
      (fun x : {x // ¬P x} ↦
        (⟨⟦(x : γ)⟧, ⟨x, rfl⟩⟩ : Meeting f (¬P ·)))
      (fun x y hxy ↦ by
        change (f.trace P).SameCycle x y at hxy
        exact Subtype.ext (Quotient.sound ((trace_sameCycle_iff_f_sameCycle f x y).mp hxy)))
  have hbij : Function.Bijective toMeeting := by
    constructor
    · intro q r hqr
      induction q using Quotient.inductionOn' with
      | h x =>
          induction r using Quotient.inductionOn' with
          | h y =>
              exact Quotient.sound <|
                (trace_sameCycle_iff_f_sameCycle f x y).mpr
                  (Quotient.eq.mp (congrArg Subtype.val hqr))
    · intro q
      obtain ⟨q, x, hx⟩ := q
      refine ⟨⟦x⟧, ?_⟩
      exact Subtype.ext hx.symm
  exact (Equiv.ofBijective toMeeting hbij).symm

end Orbit

variable {P : γ → Prop} [DecidablePred P]

def closedCycles
    (f : Perm γ) (P : γ → Prop) [DecidablePred P] : ℕ :=
  Fintype.card (Orbit.Closed f P)

theorem partition_card_eq_trace_partition_card_add_closedCycles (f : Perm γ) :
    f.partition.parts.card = (f.trace P).partition.parts.card + f.closedCycles P := by
  calc
    f.partition.parts.card
      = Fintype.card f.Orbit := Orbit.partition_parts_card_eq_fintype_card f
    _ = Fintype.card {q : f.Orbit // Orbit.Meets f (¬P ·) q} +
          Fintype.card {q : f.Orbit // ¬Orbit.Meets f (¬P ·) q} :=
      fintype_card_eq_fintype_card_subtype_add_fintype_card_subtype_not
    _ = Fintype.card (f.trace P).Orbit + f.closedCycles P := by
      rw [Fintype.card_congr (Orbit.meetingEquivTrace f)]
      simp [closedCycles, Orbit.Closed, Orbit.Avoiding]
    _ = (f.trace P).partition.parts.card + f.closedCycles P := by
      exact congrArg (fun n ↦ n + f.closedCycles P)
        (Orbit.partition_parts_card_eq_fintype_card (f.trace P)).symm

end Equiv.Perm
