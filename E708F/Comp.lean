import E708F.Core
import E708C.Defs

/-! Computable checkers and their soundness. -/

namespace E708F
open Finset BigOperators Erdos708Chain Erdos708Chain.Proofs

lemma isPrimeB_sound {p : ℕ} (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range'_1, bne_iff_ne, ne_eq] at h
  refine Nat.prime_def_lt'.mpr ⟨h.1, fun k hk hkp hd => ?_⟩
  exact h.2 k ⟨hk, by omega⟩ (Nat.mod_eq_zero_of_dvd hd)

theorem primeTab_ok : ((List.range 1001).all fun p => !pT p || isPrimeB p) = true := by
  native_decide

lemma pT_sound {p : ℕ} (h : pT p = true) : p.Prime := by
  have hp : p < 1001 := by simp only [pT, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  have := List.all_eq_true.mp primeTab_ok p (List.mem_range.mpr hp)
  simp only [h, Bool.not_true, Bool.false_or] at this
  exact isPrimeB_sound this

lemma validOpt_sound {a : ℕ} {o : Opt} (h : validOpt a o = true) :
    (∀ pe ∈ o.1, pe.1.Prime ∧ pe.1 ^ pe.2 ∣ a) ∧ (o.1.map Prod.fst).Nodup ∧
    (∀ d ∈ o.2, 0 < d) ∧ a ∣ (o.1.map (fun pe => pe.1 ^ pe.2)).prod * o.2.prod := by
  simp only [validOpt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun pe hpe => ⟨pT_sound (h1 pe hpe).1, Nat.dvd_of_mod_eq_zero (h1 pe hpe).2⟩, h2, h3,
    Nat.dvd_of_mod_eq_zero h4⟩

lemma sum_ite_le (l : List ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (l.map fun d => if p d then 1 else 0).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    split <;> omega

/-- G1: the cost-sum lemma. -/
theorem cost_good (D : Problem) (H : ℕ) (o : ℕ → Opt)
    (hv : ∀ a ∈ D.A, validOpt a (o a) = true ∧ ∀ d ∈ (o a).2, H * d ≤ D.m)
    (hs : ∑ a ∈ D.A, ((o a).1.length + (o a).2.length) ≤ H) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ H := by
  obtain ⟨B, hB, hc⟩ := cert_good D (fun a => (o a).1) (fun a => (o a).2)
    (∑ a ∈ D.A, (o a).1.length)
    (fun a ha => (validOpt_sound (hv a ha).1).1)
    (fun a ha => (validOpt_sound (hv a ha).1).2.1) le_rfl
    (by
      intro a ha d hd
      have hd0 := (validOpt_sound (hv a ha).1).2.2.1 d hd
      refine ⟨hd0, ?_⟩
      have h1 : ∑ a' ∈ D.A, ((o a').2.map (fun d' => if D.m / d' ≤ D.m / d then 1 else 0)).sum
          ≤ ∑ a' ∈ D.A, (o a').2.length := sum_le_sum (fun a' _ => sum_ite_le _ _)
      have h2 : H ≤ D.m / d := (Nat.le_div_iff_mul_le hd0).mpr (by
        have := (hv a ha).2 d hd; linarith)
      rw [sum_add_distrib] at hs
      omega)
    (fun a ha => (validOpt_sound (hv a ha).1).2.2.2)
  refine ⟨B, hB, ?_⟩
  rw [sum_add_distrib] at hs
  omega

/-! ### options of an integer -/

lemma foldl_bestStep (a H m : ℕ) (l : List Opt) : ∀ (init : Option Opt) (o : Opt),
    l.foldl (bestStep a H m) init = some o → init = some o ∨
      (validOpt a o = true ∧ ∀ d ∈ o.2, H * d ≤ m) := by
  induction l with
  | nil => intro init o h; exact Or.inl h
  | cons x l ih =>
    intro init o h
    rcases ih _ o h with h1 | h1
    · simp only [bestStep] at h1
      split at h1
      · rename_i hx
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hx
        split at h1
        · right; cases h1; exact hx
        · split at h1
          · right; cases h1; exact hx
          · left; exact h1
      · left; exact h1
    · right; exact h1

lemma bestLen_spec (H m a : ℕ) (h : bestLen H m a < 100) :
    ∃ o, bestOpt H m a = some o ∧ validOpt a o = true ∧ (∀ d ∈ o.2, H * d ≤ m) ∧
      optLen o = bestLen H m a := by
  unfold bestLen at h ⊢
  split at h
  · rename_i o ho
    rcases foldl_bestStep a H m (optsOf a) none o ho with h1 | h1
    · cases h1
    · exact ⟨o, ho, h1.1, h1.2, rfl⟩
  · omega

/-! ### tuple certificates -/

theorem checkTup_sound (H m : ℕ) (l : List ℕ) (cert : List Opt) (h : checkTup H m l cert = true)
    (D : Problem) (hA : D.A = l.toFinset) (hm : D.m = m) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ H := by
  classical
  simp only [checkTup, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hnd, hall⟩, htot⟩ := h
  have hsum : ∀ f : ℕ → ℕ, ∑ a ∈ D.A, f a = (l.map f).sum := by
    intro f; rw [hA]; exact List.sum_toFinset f hnd
  have hmemA : ∀ a ∈ D.A, a ∈ l := by intro a ha; rw [hA] at ha; exact List.mem_toFinset.mp ha
  obtain ⟨B, hB, hc⟩ := cert_good D (fun a => (optOf l cert a).1) (fun a => (optOf l cert a).2)
    (shL l cert)
    (fun a ha => (validOpt_sound (hall a (hmemA a ha)).1).1)
    (fun a ha => (validOpt_sound (hall a (hmemA a ha)).1).2.1)
    (by rw [hsum]; rfl)
    (by
      intro a ha d hd
      refine ⟨(validOpt_sound (hall a (hmemA a ha)).1).2.2.1 d hd, ?_⟩
      have := (hall a (hmemA a ha)).2 d hd
      rw [hsum, hm]
      exact this)
    (fun a ha => (validOpt_sound (hall a (hmemA a ha)).1).2.2.2)
  refine ⟨B, hB, ?_⟩
  rw [hsum] at hc
  omega

/-! ### search (unverified; its output is re-checked by `checkTup`) -/

theorem fullOK_sound (H m : ℕ) (l : List ℕ) (h : fullOK H m l = true)
    (D : Problem) (hA : D.A = l.toFinset) (hm : D.m = m) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ H := by
  unfold fullOK at h
  split at h
  · exact checkTup_sound H m l _ h D hA hm
  · cases h

/-! ### prefix maxima -/

lemma pm_le (c pm : ℕ → ℕ) (m : ℕ)
    (h : ∀ d, 2 ≤ d → d < m → c d ≤ pm (d+1) ∧ pm d ≤ pm (d+1)) :
    ∀ a d, 2 ≤ a → a < d → d ≤ m → c a ≤ pm d := by
  intro a d ha had hdm
  induction d with
  | zero => omega
  | succ d ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp had with h1 | h1
    · exact (ih h1 (by omega)).trans (h d (by omega) (by omega)).2
    · subst h1; exact (h a ha (by omega)).1

end E708F
