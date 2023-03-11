import Logic.Predicate.FirstOrder.Semantics

universe u v

section

variable {L : Language.{u}} {μ : Type v} {n : ℕ} {I : Type u}
  (A : I → Type u) [(ι : I) → Inhabited (A ι)] [s : (ι : I) → Structure₁ L (A ι)] (𝓤 : Ultrafilter I)

namespace Structure₁

structure Uprod (𝓤 : Ultrafilter I) where
  val : (i : I) → A i

instance : Structure₁ L (Uprod A 𝓤) where
  func := fun f v => ⟨fun ι => func f (fun i => (v i).val ι)⟩
  rel  := fun r v => {ι | rel r (fun i => (v i).val ι)} ∈ 𝓤

instance [Inhabited I] [(ι : I) → Inhabited (A ι)] : Inhabited (Uprod A 𝓤) := ⟨⟨default⟩⟩

@[simp] lemma func_Uprod {k} (f : L.func k) (v : Fin k → Uprod A 𝓤) :
    func f v = ⟨fun ι => func f (fun i => (v i).val ι)⟩ := rfl

@[simp] lemma rel_Uprod {k} (r : L.rel k) (v : Fin k → Uprod A 𝓤) :
    rel r v ↔ {ι | rel r (fun i => (v i).val ι)} ∈ 𝓤 := of_eq rfl

end Structure₁

namespace SubTerm
open Structure₁
variable (e : Fin n → Uprod A 𝓤) (ε : μ → Uprod A 𝓤)

lemma val_Uprod (t : SubTerm L μ n) :
    t.val! (Uprod A 𝓤) e ε = ⟨fun ι => t.val! (A ι) (fun i => (e i).val ι) (fun i => (ε i).val ι)⟩ :=
  by induction t <;> simp[*, val_func]

end SubTerm

namespace FirstOrder
open Structure₁
variable {A} {𝓤}

namespace SubFormula
variable {e : Fin n → Uprod A 𝓤} {ε : μ → Uprod A 𝓤}

lemma val_vecCons_val_eq {z : Uprod A 𝓤} {ι : I} :
    (z.val ι :> fun i => (e i).val ι) = (fun i => ((z :> e) i).val ι) :=
  by simp[Matrix.comp_vecCons (Uprod.val · ι), Function.comp]

lemma eval_Uprod {p : SubFormula L μ n} :
    Eval! (Uprod A 𝓤) e ε p ↔ {ι | Eval! (A ι) (fun i => (e i).val ι) (fun i => (ε i).val ι) p} ∈ 𝓤 := by
  induction p using rec' <;>
  simp[*, Prop.top_eq_true, Prop.bot_eq_false, eval_rel, eval_nrel, SubTerm.val_Uprod]
  case hverum => exact Filter.univ_mem
  case hnrel k r v =>
    exact Ultrafilter.compl_mem_iff_not_mem.symm
  case hand =>
    exact Filter.inter_mem_iff.symm
  case hor p q ihp ihq =>
    exact Ultrafilter.union_mem_iff.symm
  case hall p _ =>
    constructor
    · intro h
      let z : Uprod A 𝓤 := ⟨fun ι =>
        Classical.epsilon (fun z => ¬Eval! (A ι) (z :> fun i => (e i).val ι) (fun i => (ε i).val ι) p)⟩
      exact Filter.mem_of_superset (h z) (by 
        intro ι hι a
        have : Eval! (A ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          by rw [val_vecCons_val_eq]; exact hι
        by_contra hc
        have : ¬Eval! (A ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          Classical.epsilon_spec (p := fun z => ¬(Eval! (A ι) (z :> fun i => (e i).val ι) _ p)) ⟨a, hc⟩
        contradiction)
    · intro h x
      exact Filter.mem_of_superset h (by intro ι h; simpa [val_vecCons_val_eq] using h (x.val ι))
  case hex p _ =>
    constructor
    · rintro ⟨x, hx⟩
      exact Filter.mem_of_superset hx (by intro ι h; use x.val ι; simpa[val_vecCons_val_eq] using h)
    · intro h
      let z : Uprod A 𝓤 := ⟨fun ι =>
        Classical.epsilon (fun z => Eval! (A ι) (z :> fun i => (e i).val ι) (fun i => (ε i).val ι) p)⟩
      use z
      exact Filter.mem_of_superset h (by
        intro ι; rintro ⟨x, hx⟩
        have : Eval! (A ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          Classical.epsilon_spec (p := fun z => Eval! (A ι) (z :> fun i => (e i).val ι) _ p) ⟨x, hx⟩
        rw[val_vecCons_val_eq] at this; exact this)

lemma realize_Uprod {p : Formula L μ} :
    Realize! (Uprod A 𝓤) ε p ↔ {ι | Realize! (A ι) (fun i => (ε i).val ι) p} ∈ 𝓤 :=
  by simp[Realize!, Realize, eval_Uprod, Matrix.empty_eq]

end SubFormula

lemma model_Uprod {σ : Sentence L} :
    (Uprod A 𝓤) ⊧ σ ↔ {ι | (A ι) ⊧ σ} ∈ 𝓤 :=
  by simp[models_def, SubFormula.realize_Uprod, Empty.eq_elim]

variable (A)

def SubFormula.domain (σ : Sentence L) := {ι | (A ι) ⊧ σ}

end FirstOrder

end

section

namespace FirstOrder

variable {L : Language.{u}} {T : CTheory L}

abbrev FinSubTheory (T : CTheory L) := {t : Finset (Sentence L) // ↑t ⊆ T}

variable (A : FinSubTheory T → Type u) [s : (ι : FinSubTheory T) → Structure₁ L (A ι)]

instance : Inhabited (FinSubTheory T) := ⟨∅, by simp⟩

attribute [instance] Classical.propDecidable in
lemma ultrafilter_exists (H : ∀ (ι : FinSubTheory T), (A ι) ⊧* (ι.val : CTheory L)) :
    ∃ 𝓤 : Ultrafilter (FinSubTheory T), Set.image (SubFormula.domain A) T ⊆ 𝓤.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (by
    simp[Finset.subset_image_iff, SubFormula.domain]
    intro t ht
    use t; use ht
    intro σ hσ
    exact H ⟨t, ht⟩ hσ)

theorem compactness :
  Semantics.Satisfiableₛ T ↔ ∀ ι : FinSubTheory T, Semantics.Satisfiableₛ (ι.val : CTheory L) :=
  ⟨by rintro h ⟨t, ht⟩; exact Semantics.satisfiableₛ_of_subset h ht,
   by intro h
      have : ∀ ι : FinSubTheory T, ∃ (M : Type u) (_ : Inhabited M) (_ : Structure₁ L M), M ⊧* (ι.val : CTheory L) := 
        by intro ι; exact satisfiableₛ_iff.mp (h ι)
      choose A si s hA using this
      have : ∃ 𝓤 : Ultrafilter (FinSubTheory T), Set.image (SubFormula.domain A) T ⊆ 𝓤.sets := ultrafilter_exists A hA
      rcases this with ⟨𝓤, h𝓤⟩
      have : Structure₁.Uprod A 𝓤 ⊧* T := by intro σ hσ; exact model_Uprod.mpr (h𝓤 $ Set.mem_image_of_mem (SubFormula.domain A) hσ)
      exact Semantics.satisfiableₛ_intro (Structure₁.Uprod A 𝓤) this⟩

end FirstOrder

end

