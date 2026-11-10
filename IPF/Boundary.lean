import IPF.Definitions
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators Topology
open Filter
noncomputable section
namespace IPF

lemma boundary_first : boundaryIterate 1 = boundaryFormula 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundaryIterate, iterate, step, rowScale, colScale, rowSum, colSum,
      boundarySeed, halfMargin, boundaryFormula, Fin.sum_univ_two]

lemma boundary_formula_step (n : ℕ) (hn : 0 < n) :
    step halfMargin halfMargin (boundaryFormula n) = boundaryFormula (n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (4 * (n : ℝ) + 2) ≠ 0 := by positivity
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsum : 1 / 2 + 1 / (4 * (n : ℝ) + 2) ≠ 0 := by positivity
  have hdiff : 1 / 2 - 1 / (4 * (n : ℝ) + 2) ≠ 0 := by
    have he : 1 / 2 - 1 / (4 * (n : ℝ) + 2) = 2 * n / (4 * n + 2) := by
      field_simp
      ring
    rw [he]
    positivity
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [step, rowScale, colScale, rowSum, colSum, halfMargin, boundaryFormula,
      Fin.sum_univ_two, Nat.cast_add, Nat.cast_one] <;>
    field_simp <;> ring

/-- Exact boundary trajectory after at least one complete normalization cycle. -/
theorem boundary_closed_form (n : ℕ) :
    boundaryIterate (n + 1) = boundaryFormula (n + 1) := by
  induction n with
  | zero => exact boundary_first
  | succ n ih =>
    change step halfMargin halfMargin (boundaryIterate (n + 1)) = boundaryFormula (n + 1 + 1)
    rw [ih, boundary_formula_step (n + 1) (by omega)]


/-- The disappearing off-diagonal entry has an exact polynomial asymptotic. -/
theorem boundary_polynomial_rate :
    Tendsto (fun n : ℕ => (n : ℝ) * boundaryIterate n 0 1) atTop (𝓝 (1 / 4)) := by
  have ht := tendsto_add_mul_div_add_mul_atTop_nhds (0 : ℝ) 2 1 (d := 4) (by norm_num)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [boundary_closed_form]
  simp [boundaryFormula, mul_comm, add_comm, div_eq_mul_inv]

/-- No global geometric upper bound is valid even for this fixed feasible example. -/
theorem boundary_no_geometric_rate (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ¬ (∀ n : ℕ, 0 < n → boundaryIterate n 0 1 ≤ C * ρ ^ n) := by
  intro h
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * (C * ρ ^ n)) atTop (𝓝 0) := by
    have hpow := (tendsto_pow_const_mul_const_pow_of_lt_one 1 hρ hρ1).const_mul C
    simpa [mul_left_comm, mul_comm, mul_assoc] using hpow
  have hle : (1 / 4 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto' boundary_polynomial_rate ht
    (fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · exact mul_le_mul_of_nonneg_left (h n (Nat.pos_of_ne_zero hn)) (Nat.cast_nonneg n))
  norm_num at hle

/-- Boundary convergence need not produce finite positive diagonal scaling factors. -/
theorem boundary_no_finite_scaling :
    ¬ ∃ (a b : Fin 2 → ℝ), (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      ∀ i j, a i * boundarySeed i j * b j = if i = j then 1 / 2 else 0 := by
  rintro ⟨a, b, ha, hb, he⟩
  have hz := he 0 1
  norm_num [boundarySeed] at hz
  exact hz.elim (ha 0).ne' (hb 1).ne'

end IPF
