import IPF.PositiveProjection
import IPF.Projective
import IPF.ProjectiveVariation

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

lemma crossRatio_transpose (K : Table I J) : crossRatio (fun j i => K i j) = crossRatio K := by
  unfold crossRatio
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨j, l⟩, ⟨i, k⟩⟩, rfl⟩
    exact ⟨((i, k), (j, l)), by simp [mul_comm]⟩
  · rintro ⟨⟨⟨i, k⟩, ⟨j, l⟩⟩, rfl⟩
    exact ⟨((j, l), (i, k)), by simp [mul_comm]⟩

lemma contractionRatio_transpose (K : Table I J) :
    contractionRatio (fun j i => K i j) = contractionRatio K := by
  simp [contractionRatio, crossRatio_transpose]

lemma scalingMap_positive (K : Table I J) (r : I → ℝ) (c : J → ℝ)
    (hK : PositiveTable K) (hr : PositiveVector r) (hc : PositiveVector c)
    (v : J → ℝ) (hv : PositiveVector v) : PositiveVector (scalingMap K r c v) := by
  intro j
  exact div_pos (hc j) (Finset.sum_pos (fun i _ => mul_pos (hK i j)
    (div_pos (hr i) (matVec_positive hK hv i))) Finset.univ_nonempty)

/-- A complete positive scaling cycle contracts with the square of the sharp linear coefficient. -/
theorem scaling_contraction (K : Table I J) (r : I → ℝ) (c : J → ℝ)
    (hK : PositiveTable K) (hr : PositiveVector r) (hc : PositiveVector c)
    (u v : J → ℝ) (hu : PositiveVector u) (hv : PositiveVector v) :
    hilbert (scalingMap K r c u) (scalingMap K r c v) ≤
      contractionRatio K ^ 2 * hilbert u v := by
  let a := fun i => r i / matVec K u i
  let b := fun i => r i / matVec K v i
  have ha : PositiveVector a := fun i => div_pos (hr i) (matVec_positive hK hu i)
  have hb : PositiveVector b := fun i => div_pos (hr i) (matVec_positive hK hv i)
  have hKt : PositiveTable (fun j i => K i j) := fun j i => hK i j
  change hilbert (fun j => c j / matVec (fun j i => K i j) a j)
    (fun j => c j / matVec (fun j i => K i j) b j) ≤ _
  rw [hilbert_div_left hc (matVec_positive hKt ha) (matVec_positive hKt hb)]
  calc
    _ ≤ contractionRatio (fun j i => K i j) * hilbert a b :=
      projective_contraction _ hKt a b ha hb
    _ = contractionRatio K * hilbert (matVec K u) (matVec K v) := by
      rw [contractionRatio_transpose, hilbert_div_left hr (matVec_positive hK hu)
        (matVec_positive hK hv)]
    _ ≤ contractionRatio K * (contractionRatio K * hilbert u v) :=
      mul_le_mul_of_nonneg_left (projective_contraction K hK u v hu hv)
        (contractionRatio_nonneg hK)
    _ = _ := by ring

lemma scalingIterate_positive (K : Table I J) (r : I → ℝ) (c : J → ℝ)
    (hK : PositiveTable K) (hr : PositiveVector r) (hc : PositiveVector c)
    (v : J → ℝ) (hv : PositiveVector v) (n : ℕ) :
    PositiveVector (scalingIterate K r c v n) := by
  induction n with
  | zero => exact hv
  | succ n ih => exact scalingMap_positive K r c hK hr hc _ ih

lemma scaling_power_bound (K : Table I J) (r : I → ℝ) (c : J → ℝ)
    (hK : PositiveTable K) (hr : PositiveVector r) (hc : PositiveVector c)
    (v b : J → ℝ) (hv : PositiveVector v) (hb : PositiveVector b)
    (hfix : scalingMap K r c b = b) (n : ℕ) :
    hilbert (scalingIterate K r c v n) b ≤ (contractionRatio K ^ 2) ^ n * hilbert v b := by
  induction n with
  | zero => simp [scalingIterate]
  | succ n ih =>
    calc
      _ = hilbert (scalingMap K r c (scalingIterate K r c v n)) (scalingMap K r c b) := by
        rw [hfix]; rfl
      _ ≤ contractionRatio K ^ 2 * hilbert (scalingIterate K r c v n) b :=
        scaling_contraction K r c hK hr hc _ b (scalingIterate_positive K r c hK hr hc v hv n) hb
      _ ≤ contractionRatio K ^ 2 * ((contractionRatio K ^ 2) ^ n * hilbert v b) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by rw [pow_succ]; ring

lemma scaling_posterior_bound (K : Table I J) (r : I → ℝ) (c : J → ℝ)
    (hK : PositiveTable K) (hr : PositiveVector r) (hc : PositiveVector c)
    (v b : J → ℝ) (hv : PositiveVector v) (hb : PositiveVector b)
    (hfix : scalingMap K r c b = b) (n : ℕ) :
    hilbert (scalingIterate K r c v n) b ≤
      (contractionRatio K ^ 2) ^ n / (1 - contractionRatio K ^ 2) *
        hilbert (scalingMap K r c v) v := by
  have ht0 := contractionRatio_nonneg hK
  have ht1 := contractionRatio_lt_one (K := K)
  have hden : 0 < 1 - contractionRatio K ^ 2 := by nlinarith
  have h1 := scaling_contraction K r c hK hr hc v b hv hb
  rw [hfix] at h1
  have h2 := hilbert_triangle v (scalingMap K r c v) b
  rw [hilbert_symm v (scalingMap K r c v)] at h2
  have he : hilbert v b ≤ hilbert (scalingMap K r c v) v / (1 - contractionRatio K ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ (contractionRatio K ^ 2) ^ n * hilbert v b :=
      scaling_power_bound K r c hK hr hc v b hv hb hfix n
    _ ≤ (contractionRatio K ^ 2) ^ n *
        (hilbert (scalingMap K r c v) v / (1 - contractionRatio K ^ 2)) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg (sq_nonneg _) n)
    _ = _ := by ring

lemma scaledTable_positive (K : Table I J) (r : I → ℝ)
    (hK : PositiveTable K) (hr : PositiveVector r)
    (v : J → ℝ) (hv : PositiveVector v) : PositiveTable (scaledTable K r v) := by
  intro i j
  exact mul_pos (mul_pos (div_pos (hr i) (matVec_positive hK hv i)) (hK i j)) (hv j)

lemma scaledTable_rowSum (K : Table I J) (r : I → ℝ)
    (hK : PositiveTable K) (v : J → ℝ) (hv : PositiveVector v) :
    rowSum (scaledTable K r v) = r := by
  funext i
  change (∑ j, (r i / matVec K v i) * K i j * v j) = r i
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  exact div_mul_cancel₀ _ (matVec_positive hK hv i).ne'

lemma scaledTable_projective_bound (K : Table I J) (r : I → ℝ)
    (hK : PositiveTable K) (hr : PositiveVector r)
    (v b : J → ℝ) (hv : PositiveVector v) (hb : PositiveVector b) :
    hilbert (fun z : I × J => scaledTable K r v z.1 z.2)
      (fun z : I × J => scaledTable K r b z.1 z.2) ≤
      (1 + contractionRatio K) * hilbert v b := by
  have hvK := matVec_positive hK hv
  have hbK := matVec_positive hK hb
  have hd : ∀ i j, Real.log (scaledTable K r v i j) - Real.log (scaledTable K r b i j) =
      (Real.log (matVec K b i) - Real.log (matVec K v i)) +
        (Real.log (v j) - Real.log (b j)) := by
    intro i j
    simp only [scaledTable, Real.log_mul (mul_ne_zero (div_ne_zero (hr i).ne' (hvK i).ne')
      (hK i j).ne') (hv j).ne', Real.log_mul (div_ne_zero (hr i).ne' (hvK i).ne') (hK i j).ne',
      Real.log_mul (mul_ne_zero (div_ne_zero (hr i).ne' (hbK i).ne') (hK i j).ne') (hb j).ne',
      Real.log_mul (div_ne_zero (hr i).ne' (hbK i).ne') (hK i j).ne',
      Real.log_div (hr i).ne' (hvK i).ne', Real.log_div (hr i).ne' (hbK i).ne']
    ring
  apply (osc_le_iff _ _).mpr
  rintro ⟨i, j⟩ ⟨k, l⟩
  simp only [hd]
  have h1 := sub_le_osc (fun i => Real.log (matVec K b i) - Real.log (matVec K v i)) i k
  have h2 := sub_le_osc (fun j => Real.log (v j) - Real.log (b j)) j l
  have h3 := projective_contraction K hK b v hb hv
  rw [hilbert_symm b v] at h3
  change _ ≤ hilbert (matVec K b) (matVec K v) at h1
  change _ ≤ hilbert v b at h2
  nlinarith

lemma stopping_projective_bound (D : Problem I J) (p : Table I J)
    (hp : IsProjection D p) (hK : PositiveTable D.seed)
    (hr : PositiveVector D.row) (hc : PositiveVector D.col)
    (v : J → ℝ) (hv : PositiveVector v) (n : ℕ) :
    hilbert (fun z : I × J => scaledTable D.seed D.row
      (scalingIterate D.seed D.row D.col v n) z.1 z.2)
      (fun z : I × J => p z.1 z.2) ≤ stoppingBound D.seed D.row D.col v n := by
  obtain ⟨b, hb, hfix, htable⟩ := positive_projection_fixed D p hp hK hr hc
  rw [← htable]
  have hs := scaling_posterior_bound D.seed D.row D.col hK hr hc v b hv hb hfix n
  calc
    _ ≤ (1 + contractionRatio D.seed) *
        hilbert (scalingIterate D.seed D.row D.col v n) b :=
      scaledTable_projective_bound D.seed D.row hK hr _ b
        (scalingIterate_positive D.seed D.row D.col hK hr hc v hv n) hb
    _ ≤ (1 + contractionRatio D.seed) *
        ((contractionRatio D.seed ^ 2) ^ n / (1 - contractionRatio D.seed ^ 2) *
          hilbert (scalingMap D.seed D.row D.col v) v) :=
      mul_le_mul_of_nonneg_left hs (by linarith [contractionRatio_nonneg hK])
    _ = _ := by unfold stoppingBound; ring


/-- A fully explicit L1 stopping certificate with no unknown limit in its bound. -/
theorem certified_stopping_bound (D : Problem I J) (p : Table I J)
    (hp : IsProjection D p) (hK : PositiveTable D.seed)
    (hr : PositiveVector D.row) (hc : PositiveVector D.col)
    (v : J → ℝ) (hv : PositiveVector v) (n : ℕ) :
    (∑ i, ∑ j, |scaledTable D.seed D.row
      (scalingIterate D.seed D.row D.col v n) i j - p i j|) ≤
      2 * (Real.exp (stoppingBound D.seed D.row D.col v n / 2) - 1) /
        (Real.exp (stoppingBound D.seed D.row D.col v n / 2) + 1) := by
  let w := scalingIterate D.seed D.row D.col v n
  have hw : PositiveVector w := scalingIterate_positive D.seed D.row D.col hK hr hc v hv n
  let q := scaledTable D.seed D.row w
  have hq : PositiveTable q := scaledTable_positive D.seed D.row hK hr w hw
  have hpp : PositiveTable p := projection_positive D p hp hK hr hc
  have hqt : (∑ z : I × J, q z.1 z.2) = 1 := by
    rw [Fintype.sum_prod_type]
    change (∑ i, rowSum q i) = 1
    rw [scaledTable_rowSum D.seed D.row hK w hw, D.row_total]
  have hpt : (∑ z : I × J, p z.1 z.2) = 1 := by
    rw [Fintype.sum_prod_type]
    exact feasible_total hp.1
  have he := stopping_projective_bound D p hp hK hr hc v hv n
  have hE0 : 0 ≤ stoppingBound D.seed D.row D.col v n :=
    (hilbert_nonneg (fun z : I × J => q z.1 z.2) (fun z => p z.1 z.2)).trans he
  have hres := probability_l1_of_hilbert_le (fun z : I × J => hq z.1 z.2)
    (fun z : I × J => hpp z.1 z.2) hqt hpt hE0 he
  simpa only [Fintype.sum_prod_type] using hres

end IPF
