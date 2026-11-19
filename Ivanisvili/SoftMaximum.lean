import Ivanisvili

open scoped BigOperators
open Filter

namespace Ivanisvili

/-- A smooth approximation to the normalized maximum of a fixed signing. -/
noncomputable def softWorst (β : ℝ) {n : ℕ} (a : Signing n) : ℝ :=
  Real.log (∑ x : Spins n,
    Real.exp ((β * (n : ℝ)) * (|score a x| / (n : ℝ) ^ (3 / 2 : ℝ)))) /
    (β * (n : ℝ))

/-- Minimize the smooth approximation over all signings. -/
noncomputable def softMinimum (β : ℝ) (n : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : Signing n => softWorst β a)

private theorem softWorst_bounds (β : ℝ) (hβ : 0 < β) {n : ℕ} (hn : 0 < n)
    (a : Signing n) :
    worst a / (n : ℝ) ^ (3 / 2 : ℝ) ≤ softWorst β a ∧
      softWorst β a ≤ worst a / (n : ℝ) ^ (3 / 2 : ℝ) + Real.log 2 / β := by
  let t := β * (n : ℝ)
  let d := (n : ℝ) ^ (3 / 2 : ℝ)
  let e (x : Spins n) := Real.exp (t * (|score a x| / d))
  have ht : 0 < t := mul_pos hβ (Nat.cast_pos.mpr hn)
  have hd : 0 < d := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ) Finset.univ_nonempty (fun x : Spins n => |score a x|)
  change worst a = |score a x| at hmax
  have hlo : Real.exp (t * (worst a / d)) ≤ ∑ y, e y := by
    rw [hmax]
    exact Finset.single_le_sum (f := e) (fun _ _ => (Real.exp_pos _).le) hx
  have hhi : (∑ y, e y) ≤ (2 : ℝ)^n * Real.exp (t * (worst a / d)) := by
    calc
      _ ≤ ∑ _ : Spins n, Real.exp (t * (worst a / d)) := by
        apply Finset.sum_le_sum
        intro y hy
        change Real.exp (t * (|score a y| / d)) ≤ Real.exp (t * (worst a / d))
        have hymax : |score a y| ≤ worst a :=
          Finset.le_sup' (fun z : Spins n => |score a z|) hy
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hymax hd.le) ht.le)
      _ = _ := by simp [Fintype.card_fun]
  have hsumpos : 0 < ∑ y, e y := (Real.exp_pos _).trans_le hlo
  constructor
  · change worst a / d ≤ Real.log (∑ y, e y) / t
    apply (le_div_iff₀ ht).2
    simpa only [Real.log_exp, mul_comm] using Real.log_le_log (Real.exp_pos _) hlo
  · change Real.log (∑ y, e y) / t ≤ worst a / d + Real.log 2 / β
    apply (div_le_iff₀ ht).2
    have h := Real.log_le_log hsumpos hhi
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h
    convert h using 1
    dsimp [t]
    field_simp [hβ.ne']
    ring

/-- At every positive size the smooth minimum is within `log 2 / β` of the
normalized min–max value. The error is uniform in the size. -/
theorem softMinimum_bounds (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 0 < n) :
    normalized n ≤ softMinimum β n ∧ softMinimum β n ≤ normalized n + Real.log 2 / β := by
  constructor
  · apply Finset.le_inf'
    intro a ha
    have h : minimum n ≤ worst a := Finset.inf'_le (fun a : Signing n => worst a) ha
    exact (div_le_div_of_nonneg_right h (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
      (softWorst_bounds β hβ hn a).1
  · obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf'
      (s := Finset.univ) Finset.univ_nonempty (fun a : Signing n => worst a)
    change minimum n = worst a at hmin
    unfold normalized
    rw [hmin]
    exact (Finset.inf'_le (fun a : Signing n => softWorst β a) ha).trans
      (softWorst_bounds β hβ hn a).2

/-- Convergence of the soft values for arbitrarily large fixed parameters
suffices for the original zero-temperature limit. -/
theorem limitExists_of_soft_limits
    (h : ∀ B : ℝ, ∃ β ≥ B, ∃ L : ℝ, Tendsto (softMinimum β) atTop (nhds L)) :
    LimitExists := by
  apply cauchySeq_tendsto_of_complete
  refine Metric.cauchySeq_iff.2 (fun ε hε => ?_)
  obtain ⟨β, hβbound, L, hL⟩ := h (max 1 (4 * Real.log 2 / ε))
  have hβ : 0 < β := zero_lt_one.trans_le ((le_max_left _ _).trans hβbound)
  have herror : Real.log 2 / β ≤ ε / 4 := by
    apply (div_le_iff₀ hβ).2
    have hmul := (div_le_iff₀ hε).1 ((le_max_right _ _).trans hβbound)
    linarith
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.1 hL.cauchySeq) (ε / 2) (by positivity)
  refine ⟨max N 1, fun m hm n hn => ?_⟩
  have hstep := hN m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn)
  have hm' : 0 < m := (le_max_right N 1).trans hm
  have hn' : 0 < n := (le_max_right N 1).trans hn
  obtain ⟨hml, hmu⟩ := softMinimum_bounds β hβ m hm'
  obtain ⟨hnl, hnu⟩ := softMinimum_bounds β hβ n hn'
  rw [Real.dist_eq] at hstep ⊢
  obtain ⟨hlo, hhi⟩ := abs_lt.1 hstep
  exact abs_lt.2 ⟨by linarith, by linarith⟩

end Ivanisvili
