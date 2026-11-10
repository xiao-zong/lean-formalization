import IPF.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

open scoped BigOperators Topology
open Filter Set

noncomputable section
namespace IPF

@[simp] theorem scalarKL_zero_left (y : ℝ) : scalarKL 0 y = y := by simp [scalarKL]
@[simp] theorem scalarKL_self (x : ℝ) : scalarKL x x = 0 := by simp [scalarKL]

 theorem scalarKL_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : y = 0 → x = 0) : 0 ≤ scalarKL x y := by
  by_cases hx0 : x = 0
  · simpa [hx0] using hy
  by_cases hy0 : y = 0
  · simp [hy0, hs hy0]
  have hlog := Real.log_le_sub_one_of_pos (div_pos (lt_of_le_of_ne hy (Ne.symm hy0))
    (lt_of_le_of_ne hx (Ne.symm hx0)))
  have hm := mul_le_mul_of_nonneg_left hlog hx
  rw [Real.log_div hy0 hx0] at hm
  have hd : x * (y / x) = y := mul_div_cancel₀ y hx0
  unfold scalarKL
  nlinarith

 theorem scalarKL_eq_zero_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : y = 0 → x = 0) : scalarKL x y = 0 ↔ x = y := by
  constructor
  · intro he
    by_contra hne
    have hx0 : x ≠ 0 := by
      intro h
      simp only [h, scalarKL_zero_left] at he
      exact hne (h.trans he.symm)
    have hy0 : y ≠ 0 := by
      intro h
      exact hne ((hs h).trans h.symm)
    have hxy : y / x ≠ 1 := by
      intro h
      exact hne ((div_eq_one_iff_eq hx0).mp h).symm
    have hlog := Real.log_lt_sub_one_of_pos
      (div_pos (lt_of_le_of_ne hy (Ne.symm hy0)) (lt_of_le_of_ne hx (Ne.symm hx0))) hxy
    have hm := mul_lt_mul_of_pos_left hlog (lt_of_le_of_ne hx (Ne.symm hx0))
    rw [Real.log_div hy0 hx0] at hm
    have hd : x * (y / x) = y := mul_div_cancel₀ y hx0
    unfold scalarKL at he
    nlinarith
  · rintro rfl
    exact scalarKL_self _

 theorem kl_nonneg {I J : Type*} [Fintype I] [Fintype J]
    {p q : Table I J} (hp : Nonnegative p) (hq : Nonnegative q) (hs : Supported p q) :
    0 ≤ kl p q := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    scalarKL_nonneg (hp i j) (hq i j) (hs i j)

 @[simp] theorem kl_self {I J : Type*} [Fintype I] [Fintype J] (p : Table I J) :
    kl p p = 0 := by simp [kl]

 theorem scalarKL_le_kl {I J : Type*} [Fintype I] [Fintype J]
    {p q : Table I J} (hp : Nonnegative p) (hq : Nonnegative q) (hs : Supported p q)
    (i : I) (j : J) : scalarKL (p i j) (q i j) ≤ kl p q := by
  exact (Finset.single_le_sum (fun k _ => scalarKL_nonneg (hp i k) (hq i k) (hs i k))
    (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
        scalarKL_nonneg (hp k l) (hq k l) (hs k l)) (Finset.mem_univ i))

 theorem kl_eq_zero_iff {I J : Type*} [Fintype I] [Fintype J]
    {p q : Table I J} (hp : Nonnegative p) (hq : Nonnegative q) (hs : Supported p q) :
    kl p q = 0 ↔ p = q := by
  constructor
  · intro h
    ext i j
    exact (scalarKL_eq_zero_iff (hp i j) (hq i j) (hs i j)).mp
      (le_antisymm (by simpa [h] using scalarKL_le_kl hp hq hs i j)
        (scalarKL_nonneg (hp i j) (hq i j) (hs i j)))
  · rintro rfl
    exact kl_self _

 theorem continuous_scalarKL_left (y : ℝ) : Continuous (fun x => scalarKL x y) := by
  unfold scalarKL
  fun_prop

 theorem continuous_kl_left {I J : Type*} [Fintype I] [Fintype J]
    (q : Table I J) : Continuous (fun p => kl p q) := by
  unfold kl scalarKL
  fun_prop

 theorem continuousAt_scalarKL_right_self (x : ℝ) :
    ContinuousAt (fun y => scalarKL x y) x := by
  by_cases hx : x = 0
  · simp only [hx, scalarKL_zero_left]
    exact continuousAt_id
  · unfold scalarKL
    fun_prop (disch := assumption)

 theorem scalarKL_tendsto_right_self {α : Type*} {l : Filter α} {x : ℝ} {q : α → ℝ}
    (hq : Tendsto q l (𝓝 x)) : Tendsto (fun n => scalarKL x (q n)) l (𝓝 0) := by
  simpa [Function.comp_def] using (continuousAt_scalarKL_right_self x).tendsto.comp hq

 theorem kl_tendsto_right_self {α I J : Type*} [Fintype I] [Fintype J]
    {l : Filter α} {p : Table I J} {q : α → Table I J}
    (hq : Tendsto q l (𝓝 p)) : Tendsto (fun n => kl p (q n)) l (𝓝 0) := by
  have hc : ContinuousAt (fun r : Table I J => kl p r) p := by
    unfold kl
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    have hev : ContinuousAt (fun r : Table I J => r i j) p :=
      (continuous_apply_apply i j).continuousAt
    simpa [Function.comp_def] using
      ((continuousAt_scalarKL_right_self (p i j)).comp (f := fun r : Table I J => r i j) hev).tendsto
  simpa [Function.comp_def] using hc.tendsto.comp hq

 theorem scalarKL_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : y = 0 → x = 0) : (Real.sqrt x - Real.sqrt y)^2 ≤ scalarKL x y := by
  have hx' := Real.sqrt_nonneg x
  have hy' := Real.sqrt_nonneg y
  have hxx := Real.sq_sqrt hx
  have hyy := Real.sq_sqrt hy
  have hs' : Real.sqrt y = 0 → Real.sqrt x = 0 := by
    intro h
    have : y = 0 := by nlinarith
    simp [hs this]
  have hn := scalarKL_nonneg hx' hy' hs'
  have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← hxx, Real.log_pow]
    norm_num
  have hlogy : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [← hyy, Real.log_pow]
    norm_num
  have hid : scalarKL x y - (Real.sqrt x - Real.sqrt y)^2 =
      2 * Real.sqrt x * scalarKL (Real.sqrt x) (Real.sqrt y) := by
    unfold scalarKL
    rw [hlogx, hlogy]
    linear_combination -(2 * Real.log (Real.sqrt x) - 2 * Real.log (Real.sqrt y) - 1) * hxx - hyy
  nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * Real.sqrt x) hn]

 theorem scalarKL_sq_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : y = 0 → x = 0) : (x - y)^2 ≤ 2 * (x + y) * scalarKL x y := by
  have hxx := Real.sq_sqrt hx
  have hyy := Real.sq_sqrt hy
  have hd := scalarKL_sqrt_le hx hy hs
  have hn := scalarKL_nonneg hx hy hs
  have hplus : (Real.sqrt x + Real.sqrt y)^2 ≤ 2 * (x + y) := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]
  have hid : (x-y)^2 = (Real.sqrt x - Real.sqrt y)^2 *
      (Real.sqrt x + Real.sqrt y)^2 := by
    calc
      (x-y)^2 = ((Real.sqrt x)^2 - (Real.sqrt y)^2)^2 := by rw [hxx, hyy]
      _ = _ := by ring
  rw [hid]
  exact (mul_le_mul_of_nonneg_right hd (sq_nonneg _)).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hplus hn])

 theorem coordinate_sq_le_kl {I J : Type*} [Fintype I] [Fintype J]
    {p q : Table I J} (hp : Nonnegative p) (hq : Nonnegative q) (hs : Supported p q)
    (i : I) (j : J) : (p i j - q i j)^2 ≤ 2 * (p i j + q i j) * kl p q := by
  exact (scalarKL_sq_le (hp i j) (hq i j) (hs i j)).trans
    (mul_le_mul_of_nonneg_left (scalarKL_le_kl hp hq hs i j)
      (mul_nonneg (by norm_num) (add_nonneg (hp i j) (hq i j))))

end IPF
