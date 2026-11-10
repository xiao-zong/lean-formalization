import IPF.ProjectiveGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

variable {J : Type*} [Fintype J] [Nonempty J]

def expPath (v h : J → ℝ) (t : ℝ) (j : J) : ℝ :=
  Real.exp (Real.log (v j) + t * h j)

def pathMass (a v h : J → ℝ) (t : ℝ) : ℝ := ∑ j, a j * expPath v h t j

def pathWeight (a v h : J → ℝ) (t : ℝ) (j : J) : ℝ :=
  a j * expPath v h t j / pathMass a v h t

lemma expPath_pos (v h : J → ℝ) (t : ℝ) (j : J) : 0 < expPath v h t j :=
  Real.exp_pos _

lemma pathMass_pos {a : J → ℝ} (ha : PositiveVector a) (v h : J → ℝ) (t : ℝ) :
    0 < pathMass a v h t :=
  Finset.sum_pos (fun j _ => mul_pos (ha j) (expPath_pos v h t j)) Finset.univ_nonempty

lemma pathWeight_pos {a : J → ℝ} (ha : PositiveVector a) (v h : J → ℝ) (t : ℝ) (j : J) :
    0 < pathWeight a v h t j :=
  div_pos (mul_pos (ha j) (expPath_pos v h t j)) (pathMass_pos ha v h t)

lemma sum_pathWeight {a : J → ℝ} (ha : PositiveVector a) (v h : J → ℝ) (t : ℝ) :
    (∑ j, pathWeight a v h t j) = 1 := by
  unfold pathWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (pathMass_pos ha v h t))

lemma expPath_hasDerivAt (v h : J → ℝ) (t : ℝ) (j : J) :
    HasDerivAt (fun s => expPath v h s j) (expPath v h t j * h j) t := by
  simpa [expPath] using (((hasDerivAt_id t).mul_const (h j)).const_add
    (Real.log (v j))).exp

lemma pathMass_hasDerivAt (a v h : J → ℝ) (t : ℝ) :
    HasDerivAt (pathMass a v h) (∑ j, a j * (expPath v h t j * h j)) t := by
  exact HasDerivAt.fun_sum fun j _ => (expPath_hasDerivAt v h t j).const_mul (a j)

lemma log_pathMass_hasDerivAt {a : J → ℝ} (ha : PositiveVector a) (v h : J → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.log (pathMass a v h s))
      (∑ j, pathWeight a v h t j * h j) t := by
  convert (pathMass_hasDerivAt a v h t).log (ne_of_gt (pathMass_pos ha v h t)) using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pathWeight]
  ring

lemma pathWeight_cross {a b : J → ℝ} (ha : PositiveVector a) (hb : PositiveVector b)
    (v h : J → ℝ) (t R : ℝ)
    (hab : ∀ j k, a j * b k ≤ R * (b j * a k)) (j k : J) :
    pathWeight a v h t j * pathWeight b v h t k ≤
      R * (pathWeight b v h t j * pathWeight a v h t k) := by
  have hma := ne_of_gt (pathMass_pos ha v h t)
  have hmb := ne_of_gt (pathMass_pos hb v h t)
  have hfactor : 0 ≤ expPath v h t j * expPath v h t k /
      (pathMass a v h t * pathMass b v h t) :=
    le_of_lt (div_pos (mul_pos (expPath_pos v h t j) (expPath_pos v h t k))
      (mul_pos (pathMass_pos ha v h t) (pathMass_pos hb v h t)))
  calc
    _ = (a j * b k) * (expPath v h t j * expPath v h t k /
          (pathMass a v h t * pathMass b v h t)) := by
      unfold pathWeight
      field_simp
      <;> ring
    _ ≤ (R * (b j * a k)) * (expPath v h t j * expPath v h t k /
          (pathMass a v h t * pathMass b v h t)) :=
      mul_le_mul_of_nonneg_right (hab j k) hfactor
    _ = _ := by
      unfold pathWeight
      field_simp
      <;> ring

lemma expPath_zero {v : J → ℝ} (hv : PositiveVector v) (h : J → ℝ) :
    expPath v h 0 = v := by
  funext j
  simp [expPath, Real.exp_log (hv j)]

lemma expPath_one {u v : J → ℝ} (hu : PositiveVector u) :
    expPath v (fun j => Real.log (u j) - Real.log (v j)) 1 = u := by
  funext j
  simp [expPath, Real.exp_log (hu j)]

end IPF
