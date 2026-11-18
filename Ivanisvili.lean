import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

private theorem minimum_le_sq (n : ℕ) : minimum n ≤ (n : ℝ) ^ (2 : ℕ) := by
  induction n with
  | zero => simp [minimum, worst, score]
  | succ n ih =>
    push_cast
    linarith [minimum_succ_le n, ih, Nat.cast_nonneg (α := ℝ) n]

/-- Both upward and downward one-step changes vanish at infinity. -/
theorem tendsto_abs_normalized_step :
    Tendsto (fun n => |normalized (n + 1) - normalized n|) atTop (nhds 0) := by
  have upper (n : ℕ) (hn : 0 < n) :
      |normalized (n + 1) - normalized n| ≤ 2 * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnext : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr n.succ_pos
    have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr n.le_succ
    have hpow : (n : ℝ) ^ (3 / 2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hpos.le hle (by norm_num)
    have hr : (n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [show (-(1 / 2) : ℝ) = 1 - 3 / 2 by norm_num, Real.rpow_sub hpos, Real.rpow_one]
    have hnonneg : 0 ≤ normalized n :=
      div_nonneg (minimum_nonneg n) (Real.rpow_nonneg hpos.le _)
    let r : ℝ := (n : ℝ) / ((n + 1 : ℕ) : ℝ)
    have hrpos : 0 < r := div_pos hpos hnext
    have hrle : r ≤ 1 := (div_le_one hnext).2 hle
    have hrpow : r ^ (2 : ℕ) ≤ r ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hrpos hrle (by norm_num)
    have hdown : normalized n * r ^ (2 : ℕ) ≤ normalized (n + 1) := by
      calc
        _ ≤ normalized n * r ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hrpow hnonneg
        _ = minimum n / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := normalized_rescale n (n + 1) hn
        _ ≤ _ := div_le_div_of_nonneg_right (minimum_monotone n.le_succ)
          (Real.rpow_nonneg hnext.le _)
    have hgap : 1 - r ^ (2 : ℕ) ≤ 2 / (n : ℝ) := by
      calc
        _ = (1 - r) * (1 + r) := by ring
        _ ≤ (1 - r) * 2 := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hrle)
        _ = 2 / ((n + 1 : ℕ) : ℝ) := by
          dsimp [r]
          push_cast
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hpos hle
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hd : normalized n - normalized (n + 1) ≤ 2 * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
        calc
          _ ≤ normalized n * (1 - r ^ (2 : ℕ)) := by linarith
          _ ≤ normalized n * (2 / (n : ℝ)) := mul_le_mul_of_nonneg_left hgap hnonneg
          _ ≤ ((n : ℝ) ^ (2 : ℕ) / (n : ℝ) ^ (3 / 2 : ℝ)) * (2 / (n : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right (minimum_le_sq n) (Real.rpow_nonneg hpos.le _))
              (div_nonneg (by norm_num) hpos.le)
          _ = _ := by
            rw [← hr]
            field_simp [hpos.ne', (Real.rpow_pos_of_pos hpos (3 / 2 : ℝ)).ne']
            ring
      linarith
    · have hstep := normalized_succ_le n hn
      have hsmall := div_le_div_of_nonneg_left hpos.le (Real.rpow_pos_of_pos hpos _) hpow
      rw [hr] at hsmall
      linarith [Real.rpow_nonneg hpos.le (-(1 / 2) : ℝ)]
  have hlim : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (-(1 / 2) : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop |>.const_mul (2 : ℝ)
  exact tendsto_const_nhds.squeeze' hlim
    (Eventually.of_forall (fun _ => abs_nonneg _))
    (by filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn; exact upper n hn)

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

private theorem cluster_of_crossings (f : ℕ → ℝ) (c : ℝ)
    (hstep : Tendsto (fun n => |f (n + 1) - f n|) atTop (nhds 0))
    (hbelow : ∃ᶠ n in atTop, f n < c)
    (habove : ∃ᶠ n in atTop, c < f n) :
    MapClusterPt c atTop f := by
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  intro ε hε
  obtain ⟨Nstep, hNstep⟩ := eventually_atTop.1 (hstep.eventually (Iio_mem_nhds hε))
  refine frequently_atTop.2 (fun N => ?_)
  obtain ⟨n, hn, hfn⟩ := frequently_atTop.1 hbelow (max N Nstep)
  have hnN := (le_max_left N Nstep).trans hn
  have hnstep := (le_max_right N Nstep).trans hn
  have hex : ∃ m, n ≤ m ∧ c ≤ f m := by
    obtain ⟨m, hm, hfm⟩ := frequently_atTop.1 habove n
    exact ⟨m, hm, hfm.le⟩
  let m := Nat.find hex
  have hm : n ≤ m ∧ c ≤ f m := Nat.find_spec hex
  have hnm : n < m :=
    lt_of_le_of_ne hm.1 (fun h => (not_le_of_gt hfn) (by simpa only [← h] using hm.2))
  have hprev : m - 1 < m := by omega
  have hsucc : m - 1 + 1 = m := by omega
  have hnprev : n ≤ m - 1 := by omega
  have hbefore : f (m - 1) < c := by
    have hnot := Nat.find_min hex hprev
    exact lt_of_not_ge (fun h => hnot ⟨hnprev, h⟩)
  have hsmall := hNstep (m - 1) (hnstep.trans hnprev)
  change |f (m - 1 + 1) - f (m - 1)| < ε at hsmall
  rw [hsucc] at hsmall
  refine ⟨m, hnN.trans hm.1, ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hm.2)]
  linarith [le_abs_self (f m - f (m - 1))]

/-- Every intermediate value between two cluster points is a cluster point. -/
theorem normalized_cluster_points_ordConnected :
    Set.OrdConnected {c | MapClusterPt c atTop normalized} := by
  constructor
  intro a ha b hb c hc
  change MapClusterPt a atTop normalized at ha
  change MapClusterPt b atTop normalized at hb
  change MapClusterPt c atTop normalized
  obtain ⟨hac, hcb⟩ := hc
  rcases hac.eq_or_lt with rfl | hac
  · exact ha
  rcases hcb.eq_or_lt with rfl | hcb
  · exact hb
  exact cluster_of_crossings normalized c tendsto_abs_normalized_step
    (mapClusterPt_iff_frequently.mp ha _ (Iio_mem_nhds hac))
    (mapClusterPt_iff_frequently.mp hb _ (Ioi_mem_nhds hcb))

/-- Between any two subsequential limits, each real value is a subsequential limit. -/
theorem exists_subsequence_of_between_limits {u v : ℕ → ℕ} (hu : StrictMono u)
    (hv : StrictMono v) {a b c : ℝ}
    (ha : Tendsto (normalized ∘ u) atTop (nhds a))
    (hb : Tendsto (normalized ∘ v) atTop (nhds b)) (hac : a ≤ c) (hcb : c ≤ b) :
    ∃ w : ℕ → ℕ, StrictMono w ∧ Tendsto (normalized ∘ w) atTop (nhds c) := by
  have hA := MapClusterPt.of_comp hu.tendsto_atTop ha.mapClusterPt
  have hB := MapClusterPt.of_comp hv.tendsto_atTop hb.mapClusterPt
  have hC : MapClusterPt c atTop normalized :=
    normalized_cluster_points_ordConnected.out' hA hB ⟨hac, hcb⟩
  exact TopologicalSpace.FirstCountableTopology.tendsto_subseq hC

end Ivanisvili
