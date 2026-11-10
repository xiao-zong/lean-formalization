import IPF.ProjectivePath
import IPF.ProjectiveScalar

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

/-- Integrating the sharp comparison of the logarithmic derivatives of two
positive linear forms along a log-linear path. -/
lemma positive_forms_log_bound {J : Type*} [Fintype J] [Nonempty J]
    (a b u v : J → ℝ) (R : ℝ)
    (ha : PositiveVector a) (hb : PositiveVector b)
    (hu : PositiveVector u) (hv : PositiveVector v) (hR : 1 ≤ R)
    (hcross : ∀ j k, a j * b k ≤ R * (b j * a k)) :
    |(Real.log (∑ j, a j * u j) - Real.log (∑ j, a j * v j)) -
      (Real.log (∑ j, b j * u j) - Real.log (∑ j, b j * v j))| ≤
      ((Real.sqrt R - 1) / (Real.sqrt R + 1)) * hilbert u v := by
  let h : J → ℝ := fun j => Real.log (u j) - Real.log (v j)
  let f : ℝ → ℝ := fun t => Real.log (pathMass a v h t) - Real.log (pathMass b v h t)
  let f' : ℝ → ℝ := fun t =>
    (∑ j, pathWeight a v h t j * h j) - (∑ j, pathWeight b v h t j * h j)
  have hder : ∀ t, HasDerivAt f (f' t) t := fun t =>
    (log_pathMass_hasDerivAt ha v h t).sub (log_pathMass_hasDerivAt hb v h t)
  have hbnd : ∀ t, |f' t| ≤ ((Real.sqrt R - 1) / (Real.sqrt R + 1)) * osc h := by
    intro t
    exact probability_oscillation_bound (pathWeight a v h t) (pathWeight b v h t) h
      R (sInf (range h)) (sSup (range h))
      (fun j => le_of_lt (pathWeight_pos ha v h t j))
      (fun j => le_of_lt (pathWeight_pos hb v h t j))
      (sum_pathWeight ha v h t) (sum_pathWeight hb v h t) hR
      (pathWeight_cross ha hb v h t R hcross)
      (fun j => ⟨csInf_le (finite_range h).bddBelow (mem_range_self j),
        le_csSup (finite_range h).bddAbove (mem_range_self j)⟩)
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hder t).continuousAt)
  obtain ⟨t, _, ht⟩ := exists_hasDerivAt_eq_slope f f'
    (show (0 : ℝ) < 1 by norm_num) hcont.continuousOn (fun t _ => hder t)
  have h01 : |f 1 - f 0| ≤ ((Real.sqrt R - 1) / (Real.sqrt R + 1)) * osc h := by
    norm_num at ht
    rw [← ht]
    exact hbnd t
  have hf1 : f 1 = Real.log (∑ j, a j * u j) - Real.log (∑ j, b j * u j) := by
    simp only [f, pathMass, h, expPath_one hu]
  have hf0 : f 0 = Real.log (∑ j, a j * v j) - Real.log (∑ j, b j * v j) := by
    simp only [f, pathMass, expPath_zero hv]
  rw [hf1, hf0] at h01
  convert h01 using 2 <;> first | rfl | ring

/-- Birkhoff--Hopf contraction with the cross-ratio coefficient of the actual matrix. -/
theorem projective_contraction {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (K : Table I J) (hK : PositiveTable K)
    (u v : J → ℝ) (hu : PositiveVector u) (hv : PositiveVector v) :
    hilbert (matVec K u) (matVec K v) ≤ contractionRatio K * hilbert u v := by
  apply (osc_le_iff _ _).mpr
  intro i k
  have hcross : ∀ j l, K i j * K k l ≤ crossRatio K * (K k j * K i l) := by
    intro j l
    simpa only [mul_comm (K k j) (K i l)] using crossRatio_bound hK i k j l
  have h := positive_forms_log_bound (K i) (K k) u v (crossRatio K)
    (hK i) (hK k) hu hv (one_le_crossRatio hK) hcross
  exact (le_abs_self _).trans h

end IPF
