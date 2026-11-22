import Erdos708.Chain.Arithmetic
import Mathlib.Algebra.BigOperators.Fin

/-!
Certificate lemma with shared prime-power atoms and ranked private pieces
(Lemma 5 of the write-up, in the "shared atoms" form).  Uses H. Chen's
`window_multiples_lower`, `initial_multiples`, `fiber_product_dvd` (CC0).
-/

namespace E708F
open Finset BigOperators Erdos708Chain Erdos708Chain.Proofs

lemma ranked_assignment {ι : Type*} [Fintype ι] (q : ι → ℕ) (x m L : ℕ) (U : Finset ℕ)
    (hU : U.card ≤ L)
    (hq : ∀ i, 0 < q i ∧ L + (univ.filter (fun k => m / q k ≤ m / q i)).card ≤ m / q i) :
    ∃ f : ι → ℕ, Function.Injective f ∧
      ∀ i, f i ∈ Icc (x+1) (x+m) ∧ f i ∉ U ∧ q i ∣ f i := by
  classical
  let t : ι → Finset ℕ := fun i => ((Icc (x+1) (x+m)).filter (q i ∣ ·)) \ U
  obtain ⟨f, hf, ht⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp (by
    intro v
    by_cases hv : v.Nonempty
    · obtain ⟨i, hi, hmax⟩ := v.exists_max_image (fun k => m / q k) hv
      have hsub : v ⊆ univ.filter (fun k => m / q k ≤ m / q i) := by
        intro k hk; simp [hmax k hk]
      have hc : m / q i ≤ ((Icc (x+1) (x+m)).filter (q i ∣ ·)).card :=
        window_multiples_lower x m (q i)
      have hdiff := card_le_card_sdiff_add_card
        (s := (Icc (x+1) (x+m)).filter (q i ∣ ·)) (t := U)
      have h1 := card_le_card hsub
      have h2 := (hq i).2
      have hti : v.card ≤ (t i).card := by dsimp [t]; omega
      exact hti.trans (card_le_card (by intro b hb; exact mem_biUnion.mpr ⟨i, hi, hb⟩))
    · simp [not_nonempty_iff_eq_empty.mp hv])
  exact ⟨f, hf, fun i => by
    have h := mem_sdiff.mp (ht i)
    exact ⟨(mem_filter.mp h.1).1, h.2, (mem_filter.mp h.1).2⟩⟩

lemma shared_assignment {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ m)
    (P E own : ι → ℕ) (hP : ∀ i, (P i).Prime) (hown : ∀ i, own i ∈ A ∧ P i ^ E i ∣ own i)
    (hinj : ∀ i j, own i = own j → P i = P j → i = j) (x : ℕ) :
    ∃ f : ι → ℕ, (∀ i, f i ∈ Icc (x+1) (x+m) ∧ P i ^ E i ∣ f i) ∧
      ∀ i j, i ≠ j → f i = f j → P i ≠ P j := by
  classical
  have key : ∀ p : ℕ, ∃ g : {i // P i = p} → ℕ, Function.Injective g ∧
      ∀ i, g i ∈ Icc (x+1) (x+m) ∧ P i.1 ^ E i.1 ∣ g i := by
    intro p
    let t : {i // P i = p} → Finset ℕ := fun i => (Icc (x+1) (x+m)).filter (P i.1 ^ E i.1 ∣ ·)
    obtain ⟨g, hg, hmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp (by
      intro s
      by_cases hs : s.Nonempty
      · obtain ⟨i, hi, hmin⟩ := s.exists_min_image (fun k => E k.1) hs
        have himg : s.image (fun k => own k.1) ⊆ A.filter (P i.1 ^ E i.1 ∣ ·) := by
          intro b hb
          obtain ⟨k, hk, rfl⟩ := mem_image.mp hb
          refine mem_filter.mpr ⟨(hown k.1).1, ?_⟩
          have : P i.1 ^ E i.1 ∣ P k.1 ^ E k.1 := by
            rw [i.2, k.2]; exact pow_dvd_pow p (hmin k hk)
          exact this.trans (hown k.1).2
        have hinjs : Set.InjOn (fun k : {i // P i = p} => own k.1) s := by
          intro k _ k' _ h
          exact Subtype.ext (hinj _ _ h (k.2.trans k'.2.symm))
        have hAf : (A.filter (P i.1 ^ E i.1 ∣ ·)).card ≤ m / P i.1 ^ E i.1 := by
          rw [← initial_multiples m (P i.1 ^ E i.1)]
          apply card_le_card
          intro b hb
          have := hA b (mem_filter.mp hb).1
          simp only [mem_filter, mem_Icc] at hb ⊢
          exact ⟨⟨this.1, this.2⟩, hb.2⟩
        calc s.card = (s.image (fun k => own k.1)).card := (card_image_of_injOn hinjs).symm
          _ ≤ (A.filter (P i.1 ^ E i.1 ∣ ·)).card := card_le_card himg
          _ ≤ m / P i.1 ^ E i.1 := hAf
          _ ≤ (t i).card := window_multiples_lower x m _
          _ ≤ (s.biUnion t).card := card_le_card (fun b hb => mem_biUnion.mpr ⟨i, hi, hb⟩)
      · simp [not_nonempty_iff_eq_empty.mp hs])
    exact ⟨g, hg, fun i => mem_filter.mp (hmem i)⟩
  choose g hg hgm using key
  have hcast : ∀ p p' (h : p = p') (j : ι) (hj : P j = p),
      g p ⟨j, hj⟩ = g p' ⟨j, hj.trans h⟩ := by
    intro p p' h j hj; subst h; rfl
  refine ⟨fun i => g (P i) ⟨i, rfl⟩, fun i => hgm (P i) ⟨i, rfl⟩, ?_⟩
  intro i j hne heq hp
  apply hne
  have h2 : g (P i) ⟨j, hp.symm⟩ = g (P i) ⟨i, rfl⟩ := by
    rw [hcast (P i) (P j) hp j hp.symm]; exact heq.symm
  have := hg (P i) h2
  exact (congrArg Subtype.val this).symm

/-- Main certificate lemma (shared atoms + ranked private pieces). -/
theorem cert_good (D : Problem) (sh : ℕ → List (ℕ × ℕ)) (pv : ℕ → List ℕ) (L : ℕ)
    (hsh : ∀ a ∈ D.A, ∀ pe ∈ sh a, pe.1.Prime ∧ pe.1 ^ pe.2 ∣ a)
    (hnd : ∀ a ∈ D.A, ((sh a).map Prod.fst).Nodup)
    (hL : ∑ a ∈ D.A, (sh a).length ≤ L)
    (hpv : ∀ a ∈ D.A, ∀ d ∈ pv a, 0 < d ∧
       L + ∑ a' ∈ D.A, ((pv a').map (fun d' => if D.m / d' ≤ D.m / d then 1 else 0)).sum
         ≤ D.m / d)
    (hdiv : ∀ a ∈ D.A, a ∣ ((sh a).map (fun pe => pe.1 ^ pe.2)).prod * (pv a).prod) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ L + ∑ a ∈ D.A, (pv a).length := by
  classical
  let ιS := Σ a : D.A, Fin (sh a.1).length
  let ιP := Σ a : D.A, Fin (pv a.1).length
  let pe : ιS → ℕ × ℕ := fun i => (sh i.1.1)[i.2.1]
  have pe_mem : ∀ i : ιS, pe i ∈ sh i.1.1 := fun i => List.getElem_mem _
  obtain ⟨f, hfm, hfc⟩ := shared_assignment D.m D.A
    (fun a ha => ⟨by have := D.two_le a ha; omega, le_max' _ _ ha⟩)
    (fun i => (pe i).1) (fun i => (pe i).2) (fun i => i.1.1)
    (fun i => (hsh _ i.1.2 _ (pe_mem i)).1) (fun i => ⟨i.1.2, (hsh _ i.1.2 _ (pe_mem i)).2⟩)
    (by
      rintro ⟨a, k⟩ ⟨a', k'⟩ hown hp
      have haa : a = a' := Subtype.ext hown
      subst haa
      have hk : k = k' := by
        have hnd' := hnd a.1 a.2
        apply Fin.ext
        have h1 : ((sh a.1).map Prod.fst)[k.1]'(by simp) =
            ((sh a.1).map Prod.fst)[k'.1]'(by simp) := by
          simp only [List.getElem_map]; exact hp
        exact (hnd'.getElem_inj_iff).mp h1
      subst hk; rfl)
    D.x
  have hcardS : Fintype.card ιS = ∑ a ∈ D.A, (sh a).length := by
    simp only [ιS, Fintype.card_sigma, Fintype.card_fin]
    exact sum_coe_sort D.A (fun a => (sh a).length)
  have hcardP : Fintype.card ιP = ∑ a ∈ D.A, (pv a).length := by
    simp only [ιP, Fintype.card_sigma, Fintype.card_fin]
    exact sum_coe_sort D.A (fun a => (pv a).length)
  let U := (univ : Finset ιS).image f
  have hUc : U.card ≤ L := by
    show ((univ : Finset ιS).image f).card ≤ L
    have h1 := card_image_le (s := (univ : Finset ιS)) (f := f)
    rw [card_univ] at h1
    have h2 := hcardS
    have h3 := hL
    omega
  let dq : ιP → ℕ := fun i => (pv i.1.1)[i.2.1]
  have dq_mem : ∀ i, dq i ∈ pv i.1.1 := fun i => List.getElem_mem _
  have hcnt : ∀ i : ιP, (univ.filter (fun k : ιP => D.m / dq k ≤ D.m / dq i)).card =
      ∑ a' ∈ D.A, ((pv a').map (fun d' => if D.m / d' ≤ D.m / dq i then 1 else 0)).sum := by
    intro i
    rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma, ← sum_coe_sort D.A]
    apply sum_congr rfl
    intro a _
    exact Fin.sum_univ_fun_getElem (pv a.1) (fun d' => if D.m / d' ≤ D.m / dq i then 1 else 0)
  obtain ⟨g, hg, hgm⟩ := ranked_assignment dq D.x D.m L U hUc (by
    intro i
    have h := hpv i.1.1 i.1.2 (dq i) (dq_mem i)
    rw [hcnt i]; exact h)
  let V := (univ : Finset ιP).image g
  have hVc : V.card ≤ ∑ a ∈ D.A, (pv a).length := by
    have := card_image_le (s := (univ : Finset ιP)) (f := g)
    rw [card_univ, hcardP] at this
    exact this
  have hdisj : Disjoint U V := by
    apply disjoint_left.mpr
    intro b hbU hbV
    obtain ⟨i, _, rfl⟩ := mem_image.mp hbV
    exact (hgm i).2.1 hbU
  let qS : ιS → ℕ := fun i => (pe i).1 ^ (pe i).2
  have hUdiv : (∏ i ∈ (univ : Finset ιS), qS i) ∣ ∏ b ∈ U, b :=
    fiber_product_dvd univ qS f (fun i _ => (hfm i).2) (by
      intro i _ j _ hne heq
      exact Nat.coprime_pow_primes _ _ (hsh _ i.1.2 _ (pe_mem i)).1
        (hsh _ j.1.2 _ (pe_mem j)).1 (hfc i j hne heq))
  have hVdiv : (∏ i : ιP, dq i) ∣ ∏ b ∈ V, b := by
    change (∏ i : ιP, dq i) ∣ ∏ b ∈ univ.image g, b
    rw [prod_image (fun x _ y _ h => hg h)]
    exact prod_dvd_prod_of_dvd _ _ (fun i _ => (hgm i).2.2)
  have hqS : (∏ i ∈ (univ : Finset ιS), qS i) =
      ∏ a ∈ D.A, ((sh a).map (fun pe => pe.1 ^ pe.2)).prod := by
    rw [Fintype.prod_sigma, ← prod_coe_sort D.A]
    apply prod_congr rfl
    intro a _
    exact Fin.prod_univ_fun_getElem (sh a.1) (fun pe => pe.1 ^ pe.2)
  have hdq : (∏ i : ιP, dq i) = ∏ a ∈ D.A, (pv a).prod := by
    rw [Fintype.prod_sigma, ← prod_coe_sort D.A]
    apply prod_congr rfl
    intro a _
    exact Fin.prod_univ_getElem (pv a.1)
  refine ⟨U ∪ V, ⟨?_, ?_⟩, ?_⟩
  · intro b hb
    show b ∈ Icc (D.x + 1) (D.x + D.m)
    rcases mem_union.mp hb with hb | hb
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      exact (hfm i).1
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      exact (hgm i).1
  · rw [prod_union hdisj]
    have h1 : D.product ∣ ∏ a ∈ D.A, (((sh a).map (fun pe => pe.1 ^ pe.2)).prod * (pv a).prod) :=
      prod_dvd_prod_of_dvd _ _ (fun a ha => hdiv a ha)
    rw [prod_mul_distrib, ← hqS, ← hdq] at h1
    exact h1.trans (Nat.mul_dvd_mul hUdiv hVdiv)
  · have h := card_union_le U V
    omega

end E708F
