import IPF.Definitions

open scoped BigOperators
open Finset
noncomputable section
namespace IPF

/-- The sharp two-event inequality behind the positive-kernel contraction. -/
theorem binary_cross_ratio_bound {A B R : ℝ}
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hBA : B ≤ A) (hR : 1 ≤ R)
    (hc : A * (1 - B) ≤ R * B * (1 - A)) :
    A - B ≤ (Real.sqrt R - 1) / (Real.sqrt R + 1) := by
  let s := Real.sqrt R
  have hs0 : 0 ≤ s := Real.sqrt_nonneg R
  have hs2 : s^2 = R := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by nlinarith
  have hD1 : A - B ≤ 1 := by linarith
  have hfactor : 0 < (s + 1) - (s - 1) * (A - B) := by
    have hn := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hD1)
    nlinarith
  have hn : 0 ≤ (s^2 - 1) * (A + B - 1)^2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have hcross : A * (1 - B) ≤ s^2 * B * (1 - A) := by simpa [hs2] using hc
  have hp : ((s + 1) * (A - B) - (s - 1)) *
      ((s + 1) - (s - 1) * (A - B)) ≤ 0 := by
    nlinarith only [hcross, hn]
  have he : (s + 1) * (A - B) - (s - 1) ≤ 0 :=
    le_of_not_gt (fun h => (not_lt_of_ge hp) (mul_pos h hfactor))
  change A - B ≤ (s - 1) / (s + 1)
  apply (le_div_iff₀ (by linarith : 0 < s + 1)).mpr
  nlinarith

/-- Cross-ratio constraints bound the difference of probability masses of any event. -/
theorem probability_event_bound {J : Type*} [Fintype J] [DecidableEq J]
    (a b : J → ℝ) (R : ℝ) (S : Finset J)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hsa : ∑ j, a j = 1) (hsb : ∑ j, b j = 1)
    (hR : 1 ≤ R) (hcross : ∀ i j, a i * b j ≤ R * (b i * a j))
    (hBA : ∑ j ∈ S, b j ≤ ∑ j ∈ S, a j) :
    (∑ j ∈ S, a j) - (∑ j ∈ S, b j) ≤
      (Real.sqrt R - 1) / (Real.sqrt R + 1) := by
  have haS : 0 ≤ ∑ j ∈ S, a j := Finset.sum_nonneg fun j _ => ha j
  have hbS : 0 ≤ ∑ j ∈ S, b j := Finset.sum_nonneg fun j _ => hb j
  have haC : 0 ≤ ∑ j ∈ Sᶜ, a j := Finset.sum_nonneg fun j _ => ha j
  have hbC : 0 ≤ ∑ j ∈ Sᶜ, b j := Finset.sum_nonneg fun j _ => hb j
  have hsumA : (∑ j ∈ S, a j) + (∑ j ∈ Sᶜ, a j) = 1 := by
    simpa [hsa] using S.sum_add_sum_compl a
  have hsumB : (∑ j ∈ S, b j) + (∑ j ∈ Sᶜ, b j) = 1 := by
    simpa [hsb] using S.sum_add_sum_compl b
  apply binary_cross_ratio_bound haS (by linarith) hbS (by linarith) hBA hR
  have hprod : (∑ i ∈ S, a i) * (∑ j ∈ Sᶜ, b j) ≤
      R * (∑ i ∈ S, b i) * (∑ j ∈ Sᶜ, a j) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ Sᶜ, a i * b j := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
      _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, R * (b i * a j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcross i j
      _ = _ := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
  have heA : (∑ j ∈ Sᶜ, a j) = 1 - (∑ j ∈ S, a j) := by linarith
  have heB : (∑ j ∈ Sᶜ, b j) = 1 - (∑ j ∈ S, b j) := by linarith
  rwa [heA, heB] at hprod

/-- A signed zero-mass vector acts on bounded functions through its positive mass. -/
theorem signed_oscillation_bound {J : Type*} [Fintype J] [DecidableEq J]
    (d h : J → ℝ) (S : Finset J) (L U : ℝ)
    (hs : ∑ j, d j = 0) (hpos : ∀ j ∈ S, 0 ≤ d j)
    (hneg : ∀ j ∈ Sᶜ, d j ≤ 0) (hh : ∀ j, L ≤ h j ∧ h j ≤ U) :
    |∑ j, d j * h j| ≤ (∑ j ∈ S, d j) * (U - L) := by
  have hsum : (∑ j ∈ S, d j) + (∑ j ∈ Sᶜ, d j) = 0 := by
    simpa [hs] using S.sum_add_sum_compl d
  have hc : (∑ j ∈ Sᶜ, d j) = -(∑ j ∈ S, d j) := by linarith
  have hu : (∑ j, d j * h j) ≤ (∑ j ∈ S, d j) * U + (∑ j ∈ Sᶜ, d j) * L := by
    rw [← S.sum_add_sum_compl (fun j => d j * h j)]
    apply add_le_add
    · rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hh j).2 (hpos j hj)
    · rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonpos_left (hh j).1 (hneg j hj)
  have hl : (∑ j ∈ S, d j) * L + (∑ j ∈ Sᶜ, d j) * U ≤ (∑ j, d j * h j) := by
    rw [← S.sum_add_sum_compl (fun j => d j * h j)]
    apply add_le_add
    · rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hh j).1 (hpos j hj)
    · rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonpos_left (hh j).2 (hneg j hj)
  rw [hc] at hu hl
  apply abs_le.mpr
  constructor <;> nlinarith only [hu, hl]

/-- Sharp oscillation bound for two probability vectors with bounded cross ratios. -/
theorem probability_oscillation_bound {J : Type*} [Fintype J]
    (a b h : J → ℝ) (R L U : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hsa : ∑ j, a j = 1) (hsb : ∑ j, b j = 1)
    (hR : 1 ≤ R) (hcross : ∀ i j, a i * b j ≤ R * (b i * a j))
    (hh : ∀ j, L ≤ h j ∧ h j ≤ U) :
    |(∑ j, a j * h j) - (∑ j, b j * h j)| ≤
      ((Real.sqrt R - 1) / (Real.sqrt R + 1)) * (U - L) := by
  classical
  let S : Finset J := Finset.univ.filter fun j => b j < a j
  have hpos : ∀ j ∈ S, 0 ≤ a j - b j := by
    intro j hj
    exact sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp hj).2)
  have hneg : ∀ j ∈ Sᶜ, a j - b j ≤ 0 := by
    intro j hj
    have hn : ¬ b j < a j := by simpa [S] using hj
    exact sub_nonpos.mpr (le_of_not_gt hn)
  have hBA : (∑ j ∈ S, b j) ≤ ∑ j ∈ S, a j :=
    Finset.sum_le_sum fun j hj => le_of_lt (Finset.mem_filter.mp hj).2
  have hd := probability_event_bound a b R S ha hb hsa hsb hR hcross hBA
  have hs : (∑ j, (a j - b j)) = 0 := by rw [Finset.sum_sub_distrib, hsa, hsb]; ring
  have hw := signed_oscillation_bound (fun j => a j - b j) h S L U hs hpos hneg hh
  have hLU : L ≤ U := by
    by_cases hne : Nonempty J
    · obtain ⟨j⟩ := hne
      exact (hh j).1.trans (hh j).2
    · haveI : IsEmpty J := not_nonempty_iff.mp hne
      simp at hsa
  calc
    _ = |∑ j, (a j - b j) * h j| := by simp_rw [sub_mul, Finset.sum_sub_distrib]
    _ ≤ (∑ j ∈ S, (a j - b j)) * (U - L) := hw
    _ = ((∑ j ∈ S, a j) - (∑ j ∈ S, b j)) * (U - L) := by rw [Finset.sum_sub_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hLU)

/-- Sharp total-variation consequence of pairwise probability cross-ratio bounds. -/
theorem probability_tv_bound {J : Type*} [Fintype J]
    (a b : J → ℝ) (R : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hsa : ∑ j, a j = 1) (hsb : ∑ j, b j = 1)
    (hR : 1 ≤ R) (hcross : ∀ i j, a i * b j ≤ R * (b i * a j)) :
    (∑ j, |a j - b j|) ≤ 2 * ((Real.sqrt R - 1) / (Real.sqrt R + 1)) := by
  classical
  let S : Finset J := Finset.univ.filter fun j => b j < a j
  have hpos : ∀ j ∈ S, 0 ≤ a j - b j := by
    intro j hj
    exact sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp hj).2)
  have hneg : ∀ j ∈ Sᶜ, a j - b j ≤ 0 := by
    intro j hj
    have hn : ¬ b j < a j := by simpa [S] using hj
    exact sub_nonpos.mpr (le_of_not_gt hn)
  have hBA : (∑ j ∈ S, b j) ≤ ∑ j ∈ S, a j :=
    Finset.sum_le_sum fun j hj => le_of_lt (Finset.mem_filter.mp hj).2
  have hd := probability_event_bound a b R S ha hb hsa hsb hR hcross hBA
  have hs : (∑ j, (a j - b j)) = 0 := by rw [Finset.sum_sub_distrib, hsa, hsb]; ring
  have hc : (∑ j ∈ S, (a j - b j)) + (∑ j ∈ Sᶜ, (a j - b j)) = 0 := by
    simpa [hs] using S.sum_add_sum_compl (fun j => a j - b j)
  have habs : (∑ j, |a j - b j|) = 2 * ((∑ j ∈ S, a j) - (∑ j ∈ S, b j)) := by
    rw [← S.sum_add_sum_compl (fun j => |a j - b j|)]
    have hp : (∑ j ∈ S, |a j - b j|) = ∑ j ∈ S, (a j - b j) :=
      Finset.sum_congr rfl fun j hj => abs_of_nonneg (hpos j hj)
    have hn : (∑ j ∈ Sᶜ, |a j - b j|) = -(∑ j ∈ Sᶜ, (a j - b j)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j hj => abs_of_nonpos (hneg j hj)
    rw [hp, hn, Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib] at hc
    linarith
  rw [habs]
  linarith

end IPF
