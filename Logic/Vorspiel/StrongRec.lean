import Logic.Vorspiel.Computability

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

open Encodable
variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

namespace Primrec

lemma nat_rec'' {f : α → ℕ} {g : α → β} {h : α → ℕ → β → β}
  (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ (fun a (p : ℕ × β) => h a p.1 p.2)) :
  Primrec (fun a => @Nat.rec _ (g a) (h a) (f a)) := nat_rec' hf hg hh

lemma list_bind {f : α → List β} {g : α → β → List σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).bind (g a)) := list_join.comp (list_map hf hg)

lemma option_toList : Primrec (Option.toList : Option α → List α) := by
  have : Primrec (fun a => [a] : α → List α) := list_cons.comp Primrec.id (const [])
  exact (option_casesOn Primrec.id (const []) (this.comp₂ Primrec₂.right)).of_eq
    (fun o => by rcases o <;> simp)

lemma iterate {f : α → α} (hf : Primrec f) : Primrec₂ (f^[·] ·) := by
  have : Primrec₂ (fun s a => s.rec a (fun _ => f) : ℕ → α → α) :=
    to₂' (nat_rec' fst snd (hf.comp₂ (snd.comp₂ Primrec₂.right)))
  exact this.of_eq (fun s a => by
    induction' s with s ih <;> simp[*]; { exact Eq.symm (Function.iterate_succ_apply' f s a) })

lemma list_take : Primrec₂ (List.take : ℕ → List α → List α) := by
  have : Primrec₂ (fun s a => s.rec [] (fun n as => as ++ (a.get? n).toList) : ℕ → List α → List α) :=
    to₂' (nat_rec' fst (const [])
      (list_append.comp₂ (snd.comp₂ Primrec₂.right)
        (option_toList.comp₂ $ list_get?.comp₂ (snd.comp₂ Primrec₂.left) (fst.comp₂ Primrec₂.right))))
  exact this.of_eq (fun n as => by induction' n with n ih <;> simp[List.take_succ, *])

private def iterateL (f : α → ℕ → β) (h : α → α) (a : α) (m k : ℕ) : List β :=
  (List.range k).map (f (h^[m - k.pred] a))

private def F (g : α × ℕ → List σ → Option σ) (h : α → α) (a : α) (m : ℕ) : ℕ → List σ := fun k =>
  k.rec [] (fun k ih => (List.range k).bind (fun k' => (g (h^[m - k] a, k') (ih.take k')).toList) ++ (g (h^[m - k] a, k) ih).toList)

private lemma F_primrec {g : α × ℕ → List σ → Option σ} {h : α → α} (hg : Primrec₂ g) (hh : Primrec h) :
  Primrec₂ (fun a p => F g h a p.1 p.2 : α → ℕ × ℕ → List σ) :=
  to₂' <| nat_rec'' (snd.comp snd) (const [])
    (list_append.comp₂
      (to₂' <| list_bind (list_range.comp $ fst.comp snd) (option_toList.comp₂ $ hg.comp₂
        (Primrec₂.pair.comp₂
          ((iterate hh).comp₂
            (nat_sub.comp₂ (fst.comp₂ $ snd.comp₂ $ fst.comp₂ Primrec₂.left) (fst.comp₂ $ snd.comp₂ Primrec₂.left))
            (fst.comp₂ $ fst.comp₂ Primrec₂.left))
          Primrec₂.right) (list_take.comp₂ Primrec₂.right (snd.comp₂ $ snd.comp₂ Primrec₂.left))))
      (option_toList.comp₂ $ hg.comp₂
        (Primrec₂.pair.comp₂
          ((iterate hh).comp₂
            (nat_sub.comp₂ (fst.comp₂ $ snd.comp₂ Primrec₂.left) (fst.comp₂ Primrec₂.right))
            (fst.comp₂ Primrec₂.left))
          (fst.comp₂ Primrec₂.right))
        (snd.comp₂ $ Primrec₂.right)))

private lemma F_eq_iterateL {f : α → ℕ → σ} {g : α × ℕ → List σ → Option σ} {h : α → α}
  (H : ∀ a k, g (a, k) ((List.range k).map (f (h a))) = some (f a k)) (a) {m k} (hm : k ≤ m + 1) :
    F g h a m k = iterateL f h a m k := by
  have F_succ : ∀ a m k,
    F g h a m (k + 1) =
    (List.range k).bind (fun k' => (g (h^[m - k] a, k') ((F g h a m k).take k')).toList) ++
      (g (h^[m - k] a, k) $ F g h a m k).toList := by intro a m k; simp[F]
  simp[iterateL]
  induction' k with k ih generalizing a m
  · simp[F]
  · simp[F_succ, List.range_succ]
    have ih' : F g h a m k = (List.range k).map (f $ h^[m - k.pred] a) := ih a (Nat.le_of_lt hm)    
    have heq : k ≠ 0 → h (h^[m - k] a) = h^[m - k.pred] a := fun hk => by
      rw[←Function.iterate_succ_apply' h, Nat.sub_pred (Nat.lt_succ.mp hm) hk]
    apply congr_arg₂
    · have : ∀ k' < k, g (h^[m - k] a, k') ((F g h a m k).take k') = some (f (h^[m - k] a) k')
      { intro k' hk'
        have H' : g (h^[m - k] a, k') ((List.range k').map (f (h^[m - k.pred] a))) = some (f (h^[m - k] a) k') :=
          by simpa[heq (ne_zero_of_lt hk')] using H (h^[m - k] a) k'
        rw[←H', ih', List.take_map_range, Nat.min_eq_right (le_of_lt hk')] }
      exact List.bind_toList_some this
    · simp; rw[ih']
      by_cases hk : k = 0
      · simpa[hk] using H (h^[m] a) 0
      · simpa only [heq hk] using H (h^[m - k] a) k

lemma nat_one_side_strong_rec (f : α → ℕ → σ) {g : α × ℕ → List σ → Option σ} {h : α → α}
  (hg : Primrec₂ g) (hh : Primrec h)
  (H : ∀ a k, g (a, k) ((List.range k).map (f (h a))) = some (f a k)) : Primrec₂ f := 
  have : Primrec₂ (fun a m => (F g h a m (m + 1)).get? m) :=
    list_get?.comp₂
      ((F_primrec hg hh).comp₂ Primrec₂.left ((Primrec₂.pair.comp Primrec.id succ).comp₂ Primrec₂.right))
      Primrec₂.right
  Primrec₂.option_some_iff.1 <| this.of_eq <| fun a m => by
    simp[F_eq_iterateL H a (le_refl $ m + 1), iterateL, List.get?_range (Nat.lt.base m)]

end Primrec
