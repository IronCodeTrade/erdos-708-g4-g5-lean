import E708F.Enum
import Erdos708.Chain.Proofs.LongInterval
import E708C.K5.C000
import E708C.K5.C001
import E708C.K5.C002
import E708C.K5.C003
import E708C.K5.C004
import E708C.K5.C005
import E708C.K5.C006
import E708C.K5.C007
import E708C.K5.C008
import E708C.K5.C009
import E708C.K5.C010
import E708C.K5.C011
import E708C.K5.C012
import E708C.K5.C013
import E708C.K5.C014
import E708C.K5.C015
import E708C.K5.C016
import E708C.K5.C017
import E708C.K5.C018
import E708C.K5.C019
import E708C.K5.C020
import E708C.K5.C021
import E708C.K5.C022
import E708C.K5.C023
import E708C.K5.C024
import E708C.K5.C025
import E708C.K5.C026
import E708C.K5.C027
import E708C.K5.C028
import E708C.K5.C029
import E708C.K5.C030
import E708C.K5.C031
import E708C.K5.C032
import E708C.K5.C033
import E708C.K5.C034
import E708C.K5.C035
import E708C.K5.C036
import E708C.K5.C037
import E708C.K5.C038
import E708C.K5.C039
import E708C.K5.C040
import E708C.K5.C041
import E708C.K5.C042
import E708C.K5.C043
import E708C.K5.C044
import E708C.K5.C045
import E708C.K5.C046
import E708C.K5.C047

namespace E708F
open Finset BigOperators Erdos708Chain Erdos708Chain.Proofs

lemma enum5r_sound {H m : ℕ} {c pm : ℕ → ℕ} {full : List ℕ → Bool} {lo hi : ℕ}
    (h : enum5r H m c pm full lo hi = true)
    (hpm : ∀ a d, 2 ≤ a → a < d → d ≤ m → c a ≤ pm d)
    (d1 d2 d3 d4 : ℕ) (h1 : 2 ≤ d1) (h12 : d1 < d2) (h23 : d2 < d3) (h34 : d3 < d4)
    (h4 : d4 < m) (hlo : lo ≤ d4) (hhi : d4 < hi) :
    c m + c d4 + c d3 + c d2 + c d1 ≤ H ∨ full [d1, d2, d3, d4, m] = true := by
  simp only [enum5r, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h d4 ⟨hlo, by omega⟩ with h | h
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

theorem allChunks : ∀ k, k < 48 → chunkOK k = true
  | 0, _ => chunk000
  | 1, _ => chunk001
  | 2, _ => chunk002
  | 3, _ => chunk003
  | 4, _ => chunk004
  | 5, _ => chunk005
  | 6, _ => chunk006
  | 7, _ => chunk007
  | 8, _ => chunk008
  | 9, _ => chunk009
  | 10, _ => chunk010
  | 11, _ => chunk011
  | 12, _ => chunk012
  | 13, _ => chunk013
  | 14, _ => chunk014
  | 15, _ => chunk015
  | 16, _ => chunk016
  | 17, _ => chunk017
  | 18, _ => chunk018
  | 19, _ => chunk019
  | 20, _ => chunk020
  | 21, _ => chunk021
  | 22, _ => chunk022
  | 23, _ => chunk023
  | 24, _ => chunk024
  | 25, _ => chunk025
  | 26, _ => chunk026
  | 27, _ => chunk027
  | 28, _ => chunk028
  | 29, _ => chunk029
  | 30, _ => chunk030
  | 31, _ => chunk031
  | 32, _ => chunk032
  | 33, _ => chunk033
  | 34, _ => chunk034
  | 35, _ => chunk035
  | 36, _ => chunk036
  | 37, _ => chunk037
  | 38, _ => chunk038
  | 39, _ => chunk039
  | 40, _ => chunk040
  | 41, _ => chunk041
  | 42, _ => chunk042
  | 43, _ => chunk043
  | 44, _ => chunk044
  | 45, _ => chunk045
  | 46, _ => chunk046
  | 47, _ => chunk047
  | k+48, h => absurd h (by omega)

lemma unit_ok (i : ℕ) (hi : i < 48 * chunkS) : unitOK i = true := by
  have hS : 0 < chunkS := by decide
  have hk : i / chunkS < 48 := by
    rw [Nat.div_lt_iff_lt_mul hS]; rw [Nat.mul_comm] at hi; exact hi
  have h := allChunks (i / chunkS) hk
  simp only [chunkOK, List.all_eq_true, List.mem_range'_1] at h
  apply h i
  have := Nat.div_add_mod i chunkS
  have := Nat.mod_lt i hS
  constructor
  · rw [Nat.mul_comm]; omega
  · rw [Nat.mul_comm]; omega

theorem cov48 : covOK 48 = true := by native_decide

lemma cover_unit (m d4 : ℕ) (hm1 : 11 ≤ m) (hm2 : m < 1000) (hd1 : 5 ≤ d4) (hd2 : d4 < m) :
    ∃ lo hi, lo ≤ d4 ∧ d4 < hi ∧ mOK5r m lo hi = true := by
  have h := cov48
  simp only [covOK, List.all_eq_true, List.mem_range'_1, List.any_eq_true,
    List.mem_filterMap, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨u, ⟨i, hi, hu⟩, hlo, hhi⟩ := h m ⟨hm1, by omega⟩ d4 ⟨hd1, by omega⟩
  have hU := unit_ok i hi
  simp only [unitOK] at hU
  split at hu
  · rename_i hm
    simp only [Option.some.injEq] at hu
    subst hu
    simp only [beq_iff_eq] at hm
    refine ⟨_, _, hlo, hhi, ?_⟩
    rw [← hm]; exact hU
  · cases hu

lemma g5_mid (D : Problem) (hn : D.n = 5) (hm1 : 11 ≤ D.m) (hm2 : D.m < 1000) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 10 := by
  obtain ⟨d1, d2, d3, d4, h1, h12, h23, h34, h4, hA, hnd⟩ := sort5 D hn
  obtain ⟨lo, hi, hlo, hhi, h⟩ := cover_unit D.m d4 hm1 hm2 (by omega) h4
  simp only [mOK5r, Bool.and_eq_true] at h
  obtain ⟨ht, he⟩ := h
  obtain ⟨hc, hpm⟩ := tabOK_sound ht
  rcases enum5r_sound he hpm d1 d2 d3 d4 h1 h12 h23 h34 h4 hlo hhi with hs | hf
  · apply tuple_cost_good D 10 (by norm_num) _ hnd hA
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [← hc d1 (by omega), ← hc d2 (by omega), ← hc d3 (by omega), ← hc d4 (by omega),
      ← hc D.m le_rfl]
    omega
  · exact fullOK_sound 10 D.m _ hf D hA rfl

theorem g5 (D : Problem) (hn : D.n = 5) : ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 10 := by
  by_cases h1 : D.m ≤ 10
  · exact short_case D 10 h1
  by_cases h2 : 1000 ≤ D.m
  · obtain ⟨B, hB, hc⟩ := long_interval D (by rw [hn]; omega)
    exact ⟨B, hB, by rw [hn] at hc; exact hc⟩
  · exact g5_mid D hn (by omega) (by omega)

/-- Erdős #708, n = 5, stated with Mathlib notions only: g(5) ≤ 10. -/
theorem g5_le_10 : ∀ (A : Finset ℕ) (M : ℕ), A.card = 5 → M ∈ A → (∀ a ∈ A, a ≤ M) →
    (∀ a ∈ A, 2 ≤ a) → ∀ x : ℕ,
    ∃ B ⊆ Finset.Icc (x + 1) (x + M), B.card ≤ 10 ∧ (∏ a ∈ A, a) ∣ ∏ b ∈ B, b := by
  intro A M hc hM hle h2 x
  let D : Problem := ⟨A, ⟨M, hM⟩, h2, x⟩
  have hDm : D.m = M := le_antisymm (max'_le _ _ _ hle) (le_max' _ _ hM)
  obtain ⟨B, ⟨hBI, hBd⟩, hBc⟩ := g5 D hc
  refine ⟨B, ?_, hBc, hBd⟩
  have : D.interval = Icc (x+1) (x+M) := by
    show Icc (D.x + 1) (D.x + D.m) = _; rw [hDm]
  rw [← this]; exact hBI

end E708F
