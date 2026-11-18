import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

end Ivanisvili
