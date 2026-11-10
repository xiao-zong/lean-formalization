import IPF.ProjectiveDefinitions
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

private theorem sharp_sub_le_osc {A : Type*} [Fintype A] (h : A → ℝ) (a b : A) :
    h a - h b ≤ osc h := by
  have h₁ := le_csSup (Set.finite_range h).bddAbove (mem_range_self a)
  have h₂ := csInf_le (Set.finite_range h).bddBelow (mem_range_self b)
  exact sub_le_sub h₁ h₂

private theorem sharp_osc_le {A : Type*} [Fintype A] [Nonempty A]
    (h : A → ℝ) (a b : ℝ) (ha : ∀ x, a ≤ h x) (hb : ∀ x, h x ≤ b) :
    osc h ≤ b - a := by
  have h₁ : sSup (range h) ≤ b := csSup_le (range_nonempty h) (by rintro _ ⟨x, rfl⟩; exact hb x)
  have h₂ : a ≤ sInf (range h) := le_csInf (range_nonempty h) (by rintro _ ⟨x, rfl⟩; exact ha x)
  exact sub_le_sub h₁ h₂

private theorem sharp_matVec_pos {I J : Type*} [Fintype J] [Nonempty J]
    {K : Table I J} {v : J → ℝ} (hK : PositiveTable K) (hv : PositiveVector v) :
    PositiveVector (matVec K v) := by
  intro i
  exact Finset.sum_pos (fun j _ => mul_pos (hK i j) (hv j)) Finset.univ_nonempty

/-- Every global contraction factor bounds each one-coordinate logarithmic response. -/
theorem contraction_derivative_bound {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty J] {K : Table I J} (hK : PositiveTable K)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ u v : J → ℝ, PositiveVector u → PositiveVector v →
      hilbert (matVec K u) (matVec K v) ≤ c * hilbert u v)
    (v : J → ℝ) (hv : PositiveVector v) (i k : I) (j : J) :
    K i j * v j / matVec K v i - K k j * v j / matVec K v k ≤ c := by
  classical
  let u : ℝ → J → ℝ := fun t a => if a = j then v a * Real.exp t else v a
  have hu (t : ℝ) : PositiveVector (u t) := by
    intro a
    dsimp [u]
    split_ifs
    · exact mul_pos (hv a) (Real.exp_pos t)
    · exact hv a
  have hu0 : u 0 = v := by
    funext a
    simp [u]
  have hd (a : I) : HasDerivAt (fun t => matVec K (u t) a) (K a j * v j) 0 := by
    have hh (b : J) : HasDerivAt (fun t : ℝ => K a b * u t b)
        (if b = j then K a b * v b else 0) 0 := by
      by_cases hb : b = j
      · simp only [u, ite_eq_left hb]
        simpa using ((Real.hasDerivAt_exp 0).const_mul (v b)).const_mul (K a b)
      · simp only [u, ite_eq_right hb]
        exact hasDerivAt_const _ _
    simpa only [matVec, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
      (HasDerivAt.fun_sum (u := Finset.univ) fun b _ => hh b)
  let f : ℝ → ℝ := fun t => Real.log (matVec K (u t) i) - Real.log (matVec K (u t) k)
  have hdi := (hd i).log (by rw [hu0]; exact ne_of_gt (sharp_matVec_pos hK hv i))
  have hdk := (hd k).log (by rw [hu0]; exact ne_of_gt (sharp_matVec_pos hK hv k))
  have hdf : HasDerivAt f
      (K i j * v j / matVec K v i - K k j * v j / matVec K v k) 0 := by
    convert hdi.sub hdk using 1
    simp only [hu0]
  apply le_of_tendsto hdf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have hdistance : hilbert (u t) v ≤ t := by
    have he (a : J) : Real.log (u t a) - Real.log (v a) = if a = j then t else 0 := by
      dsimp [u]
      split_ifs with ha
      · rw [Real.log_mul (ne_of_gt (hv a)) (Real.exp_ne_zero t), Real.log_exp]
        ring
      · ring
    apply (sharp_osc_le _ 0 t ?_ ?_).trans_eq (sub_zero t)
    · intro a
      rw [he]
      split_ifs <;> linarith
    · intro a
      rw [he]
      split_ifs <;> linarith
  have hrows := sharp_sub_le_osc (fun a => Real.log (matVec K (u t) a) - Real.log (matVec K v a)) i k
  have hall := (hbound (u t) v (hu t) hv).trans (mul_le_mul_of_nonneg_left hdistance hc)
  have hnum : f t - f 0 ≤ c * t := by
    dsimp [f]
    rw [hu0]
    change _ ≤ hilbert (matVec K (u t)) (matVec K v) at hrows
    linarith
  simp only [zero_add, smul_eq_mul]
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ ht').2 hnum

/-- The derivative bound extends to boundary vectors by positive approximation. -/
theorem contraction_boundary_derivative_bound {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty J] {K : Table I J} (hK : PositiveTable K)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ u v : J → ℝ, PositiveVector u → PositiveVector v →
      hilbert (matVec K u) (matVec K v) ≤ c * hilbert u v)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hwK : PositiveVector (matVec K w))
    (i k : I) (j : J) :
    K i j * w j / matVec K w i - K k j * w j / matVec K w k ≤ c := by
  have hm (a : I) : ContinuousAt (fun t : ℝ => matVec K (fun b => w b + t) a) 0 := by
    unfold matVec
    fun_prop
  have hn (a : I) : ContinuousAt (fun t : ℝ => K a j * (w j + t)) 0 := by fun_prop
  have hz (a : I) : matVec K (fun b => w b + (0 : ℝ)) a ≠ 0 := by
    simpa using ne_of_gt (hwK a)
  have hcont := ((hn i).div (hm i) (hz i)).sub ((hn k).div (hm k) (hz k))
  have hlim : Tendsto (fun t : ℝ =>
      K i j * (w j + t) / matVec K (fun b => w b + t) i -
      K k j * (w j + t) / matVec K (fun b => w b + t) k) (𝓝[>] 0)
      (𝓝 (K i j * w j / matVec K w i - K k j * w j / matVec K w k)) := by
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  exact contraction_derivative_bound hK c hc hbound (fun b => w b + t)
    (fun b => add_pos_of_nonneg_of_pos (hw b) ht') i k j

theorem contraction_two_column_bound {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty J] {K : Table I J} (hK : PositiveTable K)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ u v : J → ℝ, PositiveVector u → PositiveVector v →
      hilbert (matVec K u) (matVec K v) ≤ c * hilbert u v)
    (i k : I) (j l : J) (hjl : j ≠ l) (w : ℝ) (hw : 0 ≤ w) :
    K i j * w / (K i j * w + K i l) -
      K k j * w / (K k j * w + K k l) ≤ c := by
  classical
  let v : J → ℝ := fun b => (if b = j then w else 0) + (if b = l then 1 else 0)
  have hv : ∀ b, 0 ≤ v b := by
    intro b
    dsimp [v]
    split_ifs <;> linarith
  have hm (a : I) : matVec K v a = K a j * w + K a l := by
    simp [matVec, v, mul_add, mul_ite, Finset.sum_add_distrib]
  have hvK : PositiveVector (matVec K v) := by
    intro a
    rw [hm]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (hK a j).le hw) (hK a l)
  have hh := contraction_boundary_derivative_bound hK c hc hbound v hv hvK i k j
  simpa [v, hjl, hm] using hh

private theorem sharp_balanced_algebra (a b d e s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) (hs : 0 < s)
    (hrel : s ^ 2 = a * e / (b * d)) :
    a * (b * s / a) / (a * (b * s / a) + b) -
      d * (b * s / a) / (d * (b * s / a) + e) = (s - 1) / (s + 1) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hsa : s + 1 ≠ 0 := ne_of_gt (by linarith)
  have hw : 0 < b * s / a := div_pos (mul_pos hb hs) ha
  have hden1 : a * (b * s / a) + b ≠ 0 := ne_of_gt (by positivity)
  have hden2 : d * (b * s / a) + e ≠ 0 := ne_of_gt (by positivity)
  have hrel' : s ^ 2 * (b * d) = a * e := (eq_div_iff (mul_ne_zero hb0 hd0)).mp hrel
  field_simp
  nlinarith [hrel']

/-- The Birkhoff--Hopf coefficient is the least global Hilbert contraction constant. -/
theorem projective_contraction_optimal {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (K : Table I J) (hK : PositiveTable K)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ u v : J → ℝ, PositiveVector u → PositiveVector v →
      hilbert (matVec K u) (matVec K v) ≤ c * hilbert u v) :
    contractionRatio K ≤ c := by
  classical
  let R : ((I × I) × (J × J)) → ℝ := fun p =>
    K p.1.1 p.2.1 * K p.1.2 p.2.2 / (K p.1.1 p.2.2 * K p.1.2 p.2.1)
  obtain ⟨⟨⟨i, k⟩, ⟨j, l⟩⟩, hmax⟩ :=
    (Set.range_nonempty R).csSup_mem (Set.finite_range R)
  change K i j * K k l / (K i l * K k j) = crossRatio K at hmax
  have hR : 0 < crossRatio K := by
    rw [← hmax]
    exact div_pos (mul_pos (hK i j) (hK k l)) (mul_pos (hK i l) (hK k j))
  let s : ℝ := Real.sqrt (crossRatio K)
  have hs : 0 < s := Real.sqrt_pos.2 hR
  have hs2 : s ^ 2 = crossRatio K := Real.sq_sqrt hR.le
  by_cases hs1 : s ≤ 1
  · have hr : contractionRatio K ≤ 0 := by
      unfold contractionRatio
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs1) (by positivity)
    exact hr.trans hc
  have hs1' : 1 < s := lt_of_not_ge hs1
  have hjl : j ≠ l := by
    intro heq
    subst l
    have hval : crossRatio K = 1 := by
      rw [← hmax]
      exact div_self (ne_of_gt (mul_pos (hK i j) (hK k j)))
    have : s = 1 := by simp [s, hval]
    linarith
  have hw : 0 ≤ K i l * s / K i j := (div_pos (mul_pos (hK i l) hs) (hK i j)).le
  have h := contraction_two_column_bound hK c hc hbound i k j l hjl
    (K i l * s / K i j) hw
  have hbal := sharp_balanced_algebra (K i j) (K i l) (K k j) (K k l) s
    (hK i j) (hK i l) (hK k j) (hK k l) hs (hs2.trans hmax.symm)
  rw [hbal] at h
  exact h

end IPF
