import Ivanisvili

open scoped BigOperators
open Filter

namespace Ivanisvili

private def split (k : ℕ) : Fin (2^k) ⊕ Fin (2^k) ≃ Fin (2^(k+1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))

private def sylvester : (k : ℕ) → Signing (2^k)
  | 0 => fun _ _ => true
  | k + 1 => fun i j =>
    match (split k).symm i, (split k).symm j with
    | .inl u, .inl v | .inl u, .inr v | .inr u, .inl v => sylvester k u v
    | .inr u, .inr v => !(sylvester k u v)

private theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> simp [sign]

private theorem sylvester_symm (k : ℕ) (i j : Fin (2^k)) :
    sylvester k i j = sylvester k j i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sylvester]
    cases (split k).symm i <;> cases (split k).symm j <;> simp [ih]

private theorem sum_split (k : ℕ) (f : Fin (2^(k+1)) → ℝ) :
    (∑ i, f i) =
      (∑ i, f (split k (.inl i))) + (∑ i, f (split k (.inr i))) := by
  rw [← (split k).sum_comp f, Fintype.sum_sum_type]

private noncomputable def transform (k : ℕ) (x : Fin (2^k) → ℝ) (i : Fin (2^k)) : ℝ :=
  ∑ j, sign (sylvester k i j) * x j

private theorem transform_left (k : ℕ) (x : Fin (2^(k+1)) → ℝ) (i : Fin (2^k)) :
    transform (k + 1) x (split k (.inl i)) =
      transform k (fun j => x (split k (.inl j)) + x (split k (.inr j))) i := by
  unfold transform
  rw [sum_split]
  simp [sylvester, mul_add, Finset.sum_add_distrib]

private theorem transform_right (k : ℕ) (x : Fin (2^(k+1)) → ℝ) (i : Fin (2^k)) :
    transform (k + 1) x (split k (.inr i)) =
      transform k (fun j => x (split k (.inl j)) - x (split k (.inr j))) i := by
  unfold transform
  rw [sum_split]
  simp [sylvester, sign_not, mul_add, Finset.sum_add_distrib, sub_eq_add_neg]

private theorem transform_energy (k : ℕ) (x : Fin (2^k) → ℝ) :
    (∑ i, transform k x i ^ 2) = (2^k : ℝ) * ∑ i, x i ^ 2 := by
  induction k with
  | zero => simp [transform, sylvester, sign, Fin.sum_univ_succ]
  | succ k ih =>
    rw [sum_split k (fun i => transform (k+1) x i ^ 2)]
    simp only [transform_left, transform_right, ih]
    rw [← mul_add, ← Finset.sum_add_distrib, sum_split k (fun i => x i ^ 2)]
    calc
      _ = (2^k : ℝ) * ∑ i : Fin (2^k),
          (2 * (x (split k (.inl i)) ^ 2 + x (split k (.inr i)) ^ 2)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, pow_succ, mul_assoc]

private theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

private theorem trace_zero (k : ℕ) (hk : 0 < k) :
    (∑ j, sign (sylvester k j j)) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    rw [sum_split]
    simp [sylvester, sign_not]

private theorem double_score (k : ℕ) (x : Spins (2^k)) :
    2 * score (sylvester k) x =
      (∑ j, sign (x j) * transform k (fun i => sign (x i)) j) -
        ∑ j, sign (sylvester k j j) := by
  let t (i j : Fin (2^k)) := sign (sylvester k i j) * sign (x i) * sign (x j)
  have ht (i j : Fin (2^k)) : t i j = t j i := by
    dsimp [t]
    rw [sylvester_symm k i j]
    ring
  have htri : (∑ j, ∑ i, if j < i then t i j else 0) = score (sylvester k) x := by
    rw [Finset.sum_comm]
    unfold score
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [ht j i]
  have hdiag : (∑ j, ∑ i, if i = j then t i j else 0) = ∑ j, sign (sylvester k j j) := by
    apply Finset.sum_congr rfl
    intro j _
    simp [t, mul_assoc, ← pow_two, sign_sq]
  have htotal : (∑ j, ∑ i, t i j) =
      (∑ j, sign (x j) * transform k (fun i => sign (x i)) j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [transform, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [t]
    rw [sylvester_symm k i j]
    ring
  have hpart (i j : Fin (2^k)) :
      t i j = (if i < j then t i j else 0) + (if j < i then t i j else 0) +
        (if i = j then t i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · simp
    · simp [h, h.ne', not_lt_of_ge h.le]
  have hsum : (∑ j, ∑ i, t i j) =
      score (sylvester k) x + score (sylvester k) x + (∑ j, sign (sylvester k j j)) := by
    conv_lhs =>
      arg 2
      ext j
      arg 2
      ext i
      rw [hpart i j]
    simp only [Finset.sum_add_distrib, htri, hdiag]
    rfl
  rw [htotal] at hsum
  linarith

/-- The Sylvester signing has zero trace and gives the spectral bound at powers of two. -/
theorem minimum_power_two_le (k : ℕ) (hk : 0 < k) :
    minimum (2^k) ≤ (2^k : ℝ) * Real.sqrt (2^k) / 2 := by
  refine (Finset.inf'_le (fun a : Signing (2^k) => worst a)
    (Finset.mem_univ (sylvester k))).trans ?_
  apply Finset.sup'_le
  intro x _
  let v (j : Fin (2^k)) := sign (x j)
  have hv : (∑ j, v j ^ 2) = (2^k : ℝ) := by simp [v, sign_sq]
  have htransform : (∑ j, transform k v j ^ 2) = (2^k : ℝ) ^ 2 := by
    rw [transform_energy, hv, pow_two]
  have hfull : |∑ j, v j * transform k v j| ≤ (2^k : ℝ) * Real.sqrt (2^k) := by
    calc
      _ ≤ ∑ j, |v j| * |transform k v j| := by
        simpa only [abs_mul] using
          (Finset.abs_sum_le_sum_abs (fun j => v j * transform k v j) Finset.univ)
      _ ≤ _ := by
        have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun j => |v j|) (fun j => |transform k v j|)
        simp only [sq_abs, hv, htransform, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2^k)] at hh
        simpa only [mul_comm] using hh
  have h := double_score k x
  rw [trace_zero k hk, sub_zero] at h
  change 2 * score (sylvester k) x = (∑ j, v j * transform k v j) at h
  rw [← h, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hfull
  linarith

private theorem exists_dyadic_bracket (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, n ≤ 2^k ∧ 2^k ≤ 2*n := by
  have hex : ∃ k : ℕ, n ≤ 2^k := ⟨n, Nat.lt_two_pow_self.le⟩
  let k := Nat.find hex
  have hnk : n ≤ 2^k := Nat.find_spec hex
  refine ⟨k, hnk, ?_⟩
  cases hk : k with
  | zero => simp only [pow_zero]; omega
  | succ j =>
    have hj : j < Nat.find hex := by change j < k; omega
    have hsmall : 2^j < n := lt_of_not_ge (Nat.find_min hex hj)
    rw [pow_succ]
    omega

/-- The original normalized sequence is bounded in a fixed compact interval. -/
theorem normalized_mem_Icc (n : ℕ) : normalized n ∈ Set.Icc (0 : ℝ) (Real.sqrt 2) := by
  refine ⟨div_nonneg (minimum_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _), ?_⟩
  by_cases hn : n ≤ 1
  · interval_cases n
    · simp [normalized, Real.sqrt_nonneg]
    · simp [normalized, minimum, worst, score, Fin.sum_univ_succ, Real.sqrt_nonneg]
  have hn' : 0 < n := by omega
  obtain ⟨k, hnk, hkn⟩ := exists_dyadic_bracket n hn'
  have hk : 0 < k := by
    by_contra! hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    simp [hk0] at hnk
    exact hn hnk
  have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn'
  have hpow : (2^k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hkn
  have hsqrt : Real.sqrt (2^k : ℝ) ≤ Real.sqrt 2 * Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt hpow
  have hden : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos,
      Real.rpow_one, Real.sqrt_eq_rpow]
  change normalized n ≤ Real.sqrt 2
  rw [normalized, hden, div_le_iff₀ (mul_pos hpos (Real.sqrt_pos.2 hpos))]
  calc
    minimum n ≤ minimum (2^k) := minimum_monotone hnk
    _ ≤ (2^k : ℝ) * Real.sqrt (2^k) / 2 := minimum_power_two_le k hk
    _ ≤ (2 * (n : ℝ)) * (Real.sqrt 2 * Real.sqrt (n : ℝ)) / 2 := by
      exact div_le_div_of_nonneg_right (mul_le_mul hpow hsqrt (by positivity) (by positivity))
        (by norm_num)
    _ = _ := by ring

/-- The normalized sequence has at least one finite subsequential limit. -/
theorem exists_normalized_subsequence_limit :
    ∃ (L : ℝ) (u : ℕ → ℕ), StrictMono u ∧ Tendsto (normalized ∘ u) atTop (nhds L) := by
  obtain ⟨L, _, hL⟩ := isCompact_Icc.exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := normalized)
    (le_principal_iff.2 (mem_map.2 (Eventually.of_forall normalized_mem_Icc)))
  obtain ⟨u, hu, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hL
  exact ⟨L, u, hu, hlim⟩

/-- Since a finite cluster point exists and the values stay in a compact interval,
the limit question is equivalent to uniqueness of the cluster point. -/
theorem limitExists_iff_unique_cluster_point :
    LimitExists ↔ {L | MapClusterPt L atTop normalized}.Subsingleton := by
  constructor
  · rintro ⟨L, hL⟩ a ha b hb
    obtain ⟨u, hu, hlima⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq ha
    obtain ⟨v, hv, hlimb⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hb
    exact (tendsto_nhds_unique hlima (hL.comp hu.tendsto_atTop)).trans
      (tendsto_nhds_unique (hL.comp hv.tendsto_atTop) hlimb)
  · intro h
    obtain ⟨L, _, hL⟩ := isCompact_Icc.exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := normalized)
      (le_principal_iff.2 (mem_map.2 (Eventually.of_forall normalized_mem_Icc)))
    refine ⟨L, isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall normalized_mem_Icc) ?_⟩
    intro x _ hx
    exact h hx hL

end Ivanisvili
