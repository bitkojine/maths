import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Filter

namespace Ivanisvili

/-- Boolean choices encode the two real signs. -/
noncomputable def sign (b : Bool) : ℝ := if b then 1 else -1

/-- Only the entries with row index smaller than column index are used. -/
abbrev Signing (n : ℕ) := Fin n → Fin n → Bool

abbrev Spins (n : ℕ) := Fin n → Bool

noncomputable def score {n : ℕ} (a : Signing n) (x : Spins n) : ℝ :=
  ∑ j : Fin n, ∑ i : Fin n, if i < j then sign (a i j) * sign (x i) * sign (x j) else 0

noncomputable def worst {n : ℕ} (a : Signing n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x : Spins n => |score a x|)

noncomputable def minimum (n : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : Signing n => worst a)

noncomputable def normalized (n : ℕ) : ℝ :=
  minimum n / (n : ℝ) ^ (3 / 2 : ℝ)

/-- The proposition asked by Ivanisvili. A solution proves this or its negation. -/
def LimitExists : Prop := ∃ L : ℝ, Tendsto normalized atTop (nhds L)

private def restrict {n : ℕ} (a : Signing (n + 1)) : Signing n :=
  fun i j => a i.castSucc j.castSucc

private theorem score_snoc {n : ℕ} (a : Signing (n + 1)) (x : Spins n) (b : Bool) :
    score a (Fin.snoc x b) =
      score (restrict a) x +
        (∑ i : Fin n, sign (a i.castSucc (Fin.last n)) * sign (x i)) * sign b := by
  simp only [score, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, not_lt.mpr (Fin.le_last _),
    lt_irrefl, if_true, if_false, add_zero, Finset.sum_mul, restrict]

/-- Deleting the last vertex cannot increase the maximum absolute score. -/
theorem worst_restrict {n : ℕ} (a : Signing (n + 1)) :
    worst (restrict a) ≤ worst a := by
  apply Finset.sup'_le
  intro x _
  have bound (b : Bool) : |score a (Fin.snoc x b)| ≤ worst a :=
    Finset.le_sup' (fun y : Spins (n + 1) => |score a y|) (Finset.mem_univ _)
  have pos := bound true
  have neg := bound false
  rw [score_snoc] at pos neg
  simp only [sign, if_true, Bool.false_eq_true, if_false, mul_one, mul_neg]
    at pos neg
  obtain ⟨posLower, posUpper⟩ := abs_le.mp pos
  obtain ⟨negLower, negUpper⟩ := abs_le.mp neg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The unnormalized min–max value is nondecreasing. -/
theorem minimum_monotone : Monotone minimum := by
  apply monotone_nat_of_le_succ
  intro n
  apply Finset.le_inf'
  intro a _
  exact le_trans
    (Finset.inf'_le (fun b : Signing n => worst b) (Finset.mem_univ (restrict a)))
    (worst_restrict a)

private theorem normalized_rescale (m n : ℕ) (hm : 0 < m) :
    normalized m * ((m : ℝ) / (n : ℝ)) ^ (3 / 2 : ℝ) =
      minimum m / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [normalized, Real.div_rpow hm'.le (Nat.cast_nonneg n), ← mul_div_assoc,
    div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hm' _))]

/-- Convergent normalized values at asymptotically adjacent bracketing sizes
imply convergence of the full sequence. -/
theorem tendsto_normalized_of_brackets (lo hi : ℕ → ℕ) {L : ℝ}
    (hbracket : ∀ᶠ n in atTop, 0 < lo n ∧ lo n ≤ n ∧ n ≤ hi n)
    (hlo : Tendsto (fun n => normalized (lo n)) atTop (nhds L))
    (hhi : Tendsto (fun n => normalized (hi n)) atTop (nhds L))
    (hloRatio : Tendsto (fun n => (lo n : ℝ) / (n : ℝ)) atTop (nhds 1))
    (hhiRatio : Tendsto (fun n => (hi n : ℝ) / (n : ℝ)) atTop (nhds 1)) :
    Tendsto normalized atTop (nhds L) := by
  have hloPow := hloRatio.rpow_const (p := (3 / 2 : ℝ)) (Or.inl one_ne_zero)
  have hhiPow := hhiRatio.rpow_const (p := (3 / 2 : ℝ)) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at hloPow hhiPow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [mul_one] using hlo.mul hloPow)
    (by simpa only [mul_one] using hhi.mul hhiPow) ?_ ?_
  · filter_upwards [hbracket] with n h
    rw [normalized_rescale (lo n) n h.1]
    exact div_le_div_of_nonneg_right (minimum_monotone h.2.1)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · filter_upwards [hbracket] with n h
    have hhi_pos : 0 < hi n := h.1.trans_le (h.2.1.trans h.2.2)
    rw [normalized_rescale (hi n) n hhi_pos]
    exact div_le_div_of_nonneg_right (minimum_monotone h.2.2)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end Ivanisvili
