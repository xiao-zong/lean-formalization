import IPF.ProjectiveScalar
import IPF.ProjectiveGeometry

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

/-- A projective log-oscillation bound is a multiplicative cross-ratio bound. -/
theorem probability_cross_ratio_of_hilbert_le {A : Type*} [Finite A]
    {x y : A → ℝ} (hx : PositiveVector x) (hy : PositiveVector y)
    {E : ℝ} (hE : hilbert x y ≤ E) (i j : A) :
    x i * y j ≤ Real.exp E * (y i * x j) := by
  have hpair := (sub_le_osc (fun a => Real.log (x a) - Real.log (y a)) i j).trans hE
  have hlog : Real.log (x i * y j / (y i * x j)) ≤ E := by
    rw [Real.log_div (ne_of_gt (mul_pos (hx i) (hy j)))
      (ne_of_gt (mul_pos (hy i) (hx j))),
      Real.log_mul (ne_of_gt (hx i)) (ne_of_gt (hy j)),
      Real.log_mul (ne_of_gt (hy i)) (ne_of_gt (hx j))]
    linarith
  exact (div_le_iff₀ (mul_pos (hy i) (hx j))).mp
    ((Real.log_le_iff_le_exp (div_pos (mul_pos (hx i) (hy j)) (mul_pos (hy i) (hx j)))).mp hlog)

/-- The sharp conversion from Hilbert distance to L1 distance of probabilities. -/
theorem probability_l1_of_hilbert_le {A : Type*} [Fintype A]
    {x y : A → ℝ} (hx : PositiveVector x) (hy : PositiveVector y)
    (hsx : ∑ a, x a = 1) (hsy : ∑ a, y a = 1)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : hilbert x y ≤ E) :
    (∑ a, |x a - y a|) ≤ 2 * (Real.exp (E / 2) - 1) / (Real.exp (E / 2) + 1) := by
  have hb := probability_tv_bound x y (Real.exp E) (fun a => (hx a).le)
    (fun a => (hy a).le) hsx hsy (Real.one_le_exp hE0)
    (probability_cross_ratio_of_hilbert_le hx hy hE)
  have he : (Real.exp (E / 2))^2 = Real.exp E := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (Real.exp E) = Real.exp (E / 2) := by
    rw [← he, Real.sqrt_sq (Real.exp_nonneg _)]
  simpa only [hsqrt, mul_div_assoc] using hb

end IPF
