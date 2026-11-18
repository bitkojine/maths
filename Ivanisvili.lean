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

private theorem abs_sign (b : Bool) : |sign b| = 1 := by
  cases b <;> simp [sign]

/-- Adding one vertex costs at most the number of new edges. -/
theorem minimum_succ_le (n : ℕ) : minimum (n + 1) ≤ minimum n + n := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.univ) Finset.univ_nonempty (fun a : Signing n => worst a)
  change minimum n = worst a at ha
  let extended : Signing (n + 1) := Fin.snoc (fun i => Fin.snoc (a i) true) (fun _ => true)
  have hrestrict : restrict extended = a := by
    funext i j
    simp [restrict, extended]
  calc
    minimum (n + 1) ≤ worst extended :=
      Finset.inf'_le (fun a : Signing (n + 1) => worst a) (Finset.mem_univ extended)
    _ ≤ minimum n + n := by
      apply Finset.sup'_le
      intro x _
      let term (i : Fin n) := sign (extended i.castSucc (Fin.last n)) * sign (Fin.init x i)
      have habs : |∑ i : Fin n, term i| ≤ (n : ℝ) := by
        calc
          |∑ i : Fin n, term i| ≤ ∑ i : Fin n, |term i| := Finset.abs_sum_le_sum_abs _ _
          _ = n := by simp [term, abs_mul, abs_sign]
      have hscore : |score a (Fin.init x)| ≤ worst a :=
        Finset.le_sup' (fun y : Spins n => |score a y|) (Finset.mem_univ _)
      rw [← Fin.snoc_init_self x, score_snoc, hrestrict, ha]
      calc
        _ ≤ |score a (Fin.init x)| +
              |(∑ i : Fin n, term i) * sign (x (Fin.last n))| := abs_add_le _ _
        _ ≤ worst a + n := by
          rw [abs_mul, abs_sign, mul_one]
          exact add_le_add hscore habs

theorem minimum_nonneg (n : ℕ) : 0 ≤ minimum n := by
  apply Finset.le_inf'
  intro a _
  let x : Spins n := fun _ => true
  exact (abs_nonneg (score a x)).trans
    (Finset.le_sup' (fun y : Spins n => |score a y|) (Finset.mem_univ x))

/-- One-step upward variation of the normalized values. -/
theorem normalized_succ_le (n : ℕ) (hn : 0 < n) :
    normalized (n + 1) ≤ normalized n + (n : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
  have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.cast_le.mpr (Nat.le_succ n)) (by norm_num)
  unfold normalized
  calc
    _ ≤ (minimum n + n) / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_right (minimum_succ_le n) ((le_of_lt hpos).trans hpow)
    _ ≤ _ := by
      rw [add_div]
      exact add_le_add_right (div_le_div_of_nonneg_left (minimum_nonneg n) hpos hpow) _

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

/-- An increasing subsequence whose successive size ratios approach one
determines the limit whenever its normalized values converge. -/
theorem tendsto_normalized_of_subsequence (u : ℕ → ℕ) (hu : StrictMono u) {L : ℝ}
    (hvalue : Tendsto (fun k => normalized (u k)) atTop (nhds L))
    (hratio : Tendsto (fun k => (u (k + 1) : ℝ) / (u k : ℝ)) atTop (nhds 1)) :
    Tendsto normalized atTop (nhds L) := by
  have hfind (n : ℕ) : ∃ k : ℕ, n < u (k + 1) :=
    ⟨n, n.lt_succ_self.trans_le (hu.id_le (n + 1))⟩
  let index (n : ℕ) := Nat.find (hfind n)
  have hupper (n : ℕ) : n < u (index n + 1) := Nat.find_spec (hfind n)
  have hlower (n : ℕ) (hn : u 0 ≤ n) : u (index n) ≤ n := by
    cases h : index n with
    | zero => simpa only [h] using hn
    | succ k =>
      have hk : k < index n := by rw [h]; exact k.lt_succ_self
      exact not_lt.mp (Nat.find_min (hfind n) hk)
  have hindex : Tendsto index atTop atTop := by
    refine tendsto_atTop.2 (fun k => ?_)
    filter_upwards [eventually_ge_atTop (u k)] with n hn
    by_contra! hk
    exact (not_lt_of_ge (hu.monotone (Nat.succ_le_of_lt hk) |>.trans hn)) (hupper n)
  let lo (n : ℕ) := u (index n)
  let hi (n : ℕ) := u (index n + 1)
  have hbracket : ∀ᶠ n in atTop, 0 < lo n ∧ lo n ≤ n ∧ n ≤ hi n := by
    filter_upwards [eventually_ge_atTop (u 0), tendsto_atTop.1 hindex 1] with n hn hk
    exact ⟨Nat.zero_lt_one.trans_le (hk.trans (hu.id_le _)), hlower n hn, (hupper n).le⟩
  have hright : Tendsto (fun n => (hi n : ℝ) / (lo n : ℝ)) atTop (nhds 1) :=
    hratio.comp hindex
  have hleft : Tendsto (fun n => (lo n : ℝ) / (hi n : ℝ)) atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hright.inv₀ one_ne_zero
  refine tendsto_normalized_of_brackets lo hi hbracket (hvalue.comp hindex)
    (hvalue.comp ((tendsto_add_atTop_nat 1).comp hindex)) ?_ ?_
  · refine hleft.squeeze' tendsto_const_nhds ?_ ?_
    · filter_upwards [hbracket] with n h
      have hn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (h.1.trans_le h.2.1)
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn (Nat.cast_le.mpr h.2.2)
    · filter_upwards [hbracket] with n h
      exact (div_le_one (Nat.cast_pos.mpr (h.1.trans_le h.2.1))).2 (Nat.cast_le.mpr h.2.1)
  · refine tendsto_const_nhds.squeeze' hright ?_ ?_
    · filter_upwards [hbracket] with n h
      exact (one_le_div (Nat.cast_pos.mpr (h.1.trans_le h.2.1))).2 (Nat.cast_le.mpr h.2.2)
    · filter_upwards [hbracket] with n h
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Nat.cast_pos.mpr h.1)
        (Nat.cast_le.mpr h.2.1)

end Ivanisvili
