import E708F.Enum
import Erdos708.Chain.Proofs.LongInterval

namespace E708F
open Finset BigOperators Erdos708Chain Erdos708Chain.Proofs

/-- the finite range 9 ≤ m ≤ 511, evaluated by compiled code -/
theorem allOK4 : (List.range' 9 503).all mOK4 = true := by native_decide

theorem g4 (D : Problem) (hn : D.n = 4) : ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 8 := by
  by_cases h1 : D.m ≤ 8
  · exact short_case D 8 h1
  by_cases h2 : 512 ≤ D.m
  · obtain ⟨B, hB, hc⟩ := long_interval D (by rw [hn]; omega)
    exact ⟨B, hB, by rw [hn] at hc; exact hc⟩
  · exact mOK4_sound D hn
      (List.all_eq_true.mp allOK4 D.m (List.mem_range'_1.mpr ⟨by omega, by omega⟩))

/-- Erdős #708, n = 4, stated with Mathlib notions only: g(4) ≤ 8. -/
theorem g4_le_8 : ∀ (A : Finset ℕ) (M : ℕ), A.card = 4 → M ∈ A → (∀ a ∈ A, a ≤ M) →
    (∀ a ∈ A, 2 ≤ a) → ∀ x : ℕ,
    ∃ B ⊆ Finset.Icc (x + 1) (x + M), B.card ≤ 8 ∧ (∏ a ∈ A, a) ∣ ∏ b ∈ B, b := by
  intro A M hc hM hle h2 x
  let D : Problem := ⟨A, ⟨M, hM⟩, h2, x⟩
  have hDm : D.m = M := le_antisymm (max'_le _ _ _ hle) (le_max' _ _ hM)
  obtain ⟨B, ⟨hBI, hBd⟩, hBc⟩ := g4 D hc
  refine ⟨B, ?_, hBc, hBd⟩
  have : D.interval = Icc (x+1) (x+M) := by
    show Icc (D.x + 1) (D.x + D.m) = _; rw [hDm]
  rw [← this]; exact hBI

end E708F
