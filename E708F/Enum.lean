import E708F.Comp
import Mathlib.Data.Finset.Sort

namespace E708F
open Finset BigOperators Erdos708Chain Erdos708Chain.Proofs

lemma enum4_sound {H m : ℕ} {c pm : ℕ → ℕ} {full : List ℕ → Bool}
    (h : enum4 H m c pm full = true) (hpm : ∀ a d, 2 ≤ a → a < d → d ≤ m → c a ≤ pm d)
    (d1 d2 d3 : ℕ) (h1 : 2 ≤ d1) (h12 : d1 < d2) (h23 : d2 < d3) (h3 : d3 < m) :
    c m + c d3 + c d2 + c d1 ≤ H ∨ full [d1, d2, d3, m] = true := by
  simp only [enum4, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h d3 ⟨by omega, by omega⟩ with h | h
  · left
    have := hpm d2 d3 (by omega) h23 (by omega)
    have := hpm d1 d3 h1 (by omega) (by omega)
    omega
  rcases h d2 ⟨by omega, by omega⟩ with h | h
  · left
    have := hpm d1 d2 h1 h12 (by omega)
    omega
  rcases h d1 ⟨by omega, by omega⟩ with h | h
  · left; omega
  · right; exact h

lemma enum5_sound {H m : ℕ} {c pm : ℕ → ℕ} {full : List ℕ → Bool}
    (h : enum5 H m c pm full = true) (hpm : ∀ a d, 2 ≤ a → a < d → d ≤ m → c a ≤ pm d)
    (d1 d2 d3 d4 : ℕ) (h1 : 2 ≤ d1) (h12 : d1 < d2) (h23 : d2 < d3) (h34 : d3 < d4)
    (h4 : d4 < m) :
    c m + c d4 + c d3 + c d2 + c d1 ≤ H ∨ full [d1, d2, d3, d4, m] = true := by
  simp only [enum5, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h d4 ⟨by omega, by omega⟩ with h | h
  · left
    have := hpm d3 d4 (by omega) h34 (by omega)
    have := hpm d2 d4 (by omega) (by omega) (by omega)
    have := hpm d1 d4 h1 (by omega) (by omega)
    omega
  rcases h d3 ⟨by omega, by omega⟩ with h | h
  · left
    have := hpm d2 d3 (by omega) h23 (by omega)
    have := hpm d1 d3 h1 (by omega) (by omega)
    omega
  rcases h d2 ⟨by omega, by omega⟩ with h | h
  · left
    have := hpm d1 d2 h1 h12 (by omega)
    omega
  rcases h d1 ⟨by omega, by omega⟩ with h | h
  · left; omega
  · right; exact h

lemma tabOK_sound {H m : ℕ} {c pm : ℕ → ℕ} (h : tabOK H m c pm = true) :
    (∀ a ≤ m, c a = bestLen H m a) ∧ (∀ a d, 2 ≤ a → a < d → d ≤ m → c a ≤ pm d) := by
  simp only [tabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_range'_1,
    beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨fun a ha => h.1 a (by omega), pm_le c pm m ?_⟩
  intro d hd hdm
  exact h.2 d ⟨hd, by omega⟩

/-- From the cost table: a tuple whose cost sum is ≤ H is good. -/
lemma tuple_cost_good (D : Problem) (H : ℕ) (hH : H < 100) (l : List ℕ) (hl : l.Nodup)
    (hA : D.A = l.toFinset)
    (hs : (l.map (bestLen H D.m)).sum ≤ H) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ H := by
  classical
  have hmemA : ∀ a ∈ D.A, a ∈ l := by intro a ha; rw [hA] at ha; exact List.mem_toFinset.mp ha
  have hle : ∀ a ∈ l, bestLen H D.m a ≤ H := by
    intro a ha
    exact (List.le_sum_of_mem (List.mem_map_of_mem ha)).trans hs
  apply cost_good D H (fun a => (bestOpt H D.m a).getD ([], []))
  · intro a ha
    obtain ⟨o, ho, hv, hsm, _⟩ := bestLen_spec H D.m a (by have := hle a (hmemA a ha); omega)
    rw [ho]; exact ⟨hv, hsm⟩
  · have : ∀ a ∈ D.A, ((bestOpt H D.m a).getD ([], [])).1.length +
        ((bestOpt H D.m a).getD ([], [])).2.length = bestLen H D.m a := by
      intro a ha
      obtain ⟨o, ho, _, _, hlen⟩ := bestLen_spec H D.m a (by have := hle a (hmemA a ha); omega)
      rw [ho, ← hlen]; rfl
    rw [sum_congr rfl this, hA, List.sum_toFinset _ hl]
    exact hs

/-- sorted list of a 4-element problem -/
lemma sort4 (D : Problem) (hn : D.n = 4) : ∃ d1 d2 d3, 2 ≤ d1 ∧ d1 < d2 ∧ d2 < d3 ∧ d3 < D.m ∧
    D.A = [d1, d2, d3, D.m].toFinset ∧ [d1, d2, d3, D.m].Nodup := by
  classical
  have hlen : (D.A.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort]; exact hn
  have hsrt := Finset.pairwise_sort D.A (· ≤ ·)
  have hnd := Finset.sort_nodup D.A (· ≤ ·)
  have hto := Finset.sort_toFinset D.A (· ≤ ·)
  have hmem : ∀ a, a ∈ D.A.sort (· ≤ ·) ↔ a ∈ D.A := fun a => Finset.mem_sort _
  generalize D.A.sort (· ≤ ·) = l at hlen hsrt hnd hto hmem
  match l, hlen with
  | [a, b, c, d], _ =>
    simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, false_or, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true] at hsrt
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
      List.not_mem_nil, List.nodup_nil, and_true, not_false_eq_true] at hnd
    have hmD : D.m ∈ D.A := max'_mem _ _
    have hdm : d ≤ D.m := le_max' _ _ ((hmem d).mp (by simp))
    have ha2 : 2 ≤ a := D.two_le a ((hmem a).mp (by simp))
    have hmm := (hmem D.m).mpr hmD
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmm
    have hdm' : d = D.m := by omega
    subst hdm'
    refine ⟨a, b, c, ha2, by omega, by omega, by omega, hto.symm, ?_⟩
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
      List.not_mem_nil, List.nodup_nil, and_true, not_false_eq_true]
    omega

lemma sort5 (D : Problem) (hn : D.n = 5) : ∃ d1 d2 d3 d4, 2 ≤ d1 ∧ d1 < d2 ∧ d2 < d3 ∧
    d3 < d4 ∧ d4 < D.m ∧
    D.A = [d1, d2, d3, d4, D.m].toFinset ∧ [d1, d2, d3, d4, D.m].Nodup := by
  classical
  have hlen : (D.A.sort (· ≤ ·)).length = 5 := by rw [Finset.length_sort]; exact hn
  have hsrt := Finset.pairwise_sort D.A (· ≤ ·)
  have hnd := Finset.sort_nodup D.A (· ≤ ·)
  have hto := Finset.sort_toFinset D.A (· ≤ ·)
  have hmem : ∀ a, a ∈ D.A.sort (· ≤ ·) ↔ a ∈ D.A := fun a => Finset.mem_sort _
  generalize D.A.sort (· ≤ ·) = l at hlen hsrt hnd hto hmem
  match l, hlen with
  | [a, b, c, d, e], _ =>
    simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp,
      forall_eq, List.not_mem_nil, false_or, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true] at hsrt
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
      List.not_mem_nil, List.nodup_nil, and_true, not_false_eq_true] at hnd
    have hmD : D.m ∈ D.A := max'_mem _ _
    have hdm : e ≤ D.m := le_max' _ _ ((hmem e).mp (by simp))
    have ha2 : 2 ≤ a := D.two_le a ((hmem a).mp (by simp))
    have hmm := (hmem D.m).mpr hmD
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmm
    have hdm' : e = D.m := by omega
    subst hdm'
    refine ⟨a, b, c, d, ha2, by omega, by omega, by omega, by omega, hto.symm, ?_⟩
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
      List.not_mem_nil, List.nodup_nil, and_true, not_false_eq_true]
    omega

lemma mOK4_sound (D : Problem) (hn : D.n = 4) (h : mOK4 D.m = true) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 8 := by
  obtain ⟨d1, d2, d3, h1, h12, h23, h3, hA, hnd⟩ := sort4 D hn
  simp only [mOK4, Bool.and_eq_true] at h
  obtain ⟨ht, he⟩ := h
  obtain ⟨hc, hpm⟩ := tabOK_sound ht
  rcases enum4_sound he hpm d1 d2 d3 h1 h12 h23 h3 with hs | hf
  · apply tuple_cost_good D 8 (by norm_num) _ hnd hA
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [← hc d1 (by omega), ← hc d2 (by omega), ← hc d3 (by omega), ← hc D.m le_rfl]
    omega
  · exact fullOK_sound 8 D.m _ hf D hA rfl

lemma mOK5_sound (D : Problem) (hn : D.n = 5) (h : mOK5 D.m = true) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 10 := by
  obtain ⟨d1, d2, d3, d4, h1, h12, h23, h34, h4, hA, hnd⟩ := sort5 D hn
  simp only [mOK5, Bool.and_eq_true] at h
  obtain ⟨ht, he⟩ := h
  obtain ⟨hc, hpm⟩ := tabOK_sound ht
  rcases enum5_sound he hpm d1 d2 d3 d4 h1 h12 h23 h34 h4 with hs | hf
  · apply tuple_cost_good D 10 (by norm_num) _ hnd hA
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [← hc d1 (by omega), ← hc d2 (by omega), ← hc d3 (by omega), ← hc d4 (by omega),
      ← hc D.m le_rfl]
    omega
  · exact fullOK_sound 10 D.m _ hf D hA rfl

/-- short intervals: the whole window. -/
lemma short_case (D : Problem) (k : ℕ) (hk : D.m ≤ k) : ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ k :=
  ⟨D.interval, whole_interval D, by
    show (Icc (D.x+1) (D.x+D.m)).card ≤ k
    rw [Nat.card_Icc]; omega⟩

end E708F
