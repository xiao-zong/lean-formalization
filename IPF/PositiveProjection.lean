import IPF.Variational
import IPF.Convergence
import IPF.ProjectiveDefinitions

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

variable {I J : Type*} [Fintype I] [Fintype J]

lemma product_feasible (D : Problem I J) (hK : PositiveTable D.seed) :
    Feasible D.seed D.row D.col (fun i j => D.row i * D.col j) := by
  refine ⟨fun i j => mul_nonneg (D.row_nonnegative i) (D.col_nonnegative j), ?_, ?_, ?_⟩
  · intro i j h
    exact False.elim ((hK i j).ne' h)
  · funext i
    simp [rowSum, ← Finset.mul_sum, D.col_total]
  · funext j
    simp [colSum, ← Finset.sum_mul, D.row_total]

lemma projection_positive (D : Problem I J) (p : Table I J) (hp : IsProjection D p)
    (hK : PositiveTable D.seed) (hr : PositiveVector D.row) (hc : PositiveVector D.col) :
    PositiveTable p := by
  intro i j
  exact (projection_support D p hp i j).mpr
    ⟨_, product_feasible D hK, mul_pos (hr i) (hc j)⟩

private def CrossProducts (K q : Table I J) : Prop :=
  ∀ i k j l, q i j * q k l * K i l * K k j = q i l * q k j * K i j * K k l

private lemma cross_row (K q : Table I J) (r : I → ℝ) (h : CrossProducts K q) :
    CrossProducts K (rowScale r q) := by
  intro i k j l
  dsimp [rowScale]
  calc
    _ = (r i / rowSum q i * (r k / rowSum q k)) *
        (q i j * q k l * K i l * K k j) := by ring
    _ = _ := by rw [h i k j l]; ring

private lemma cross_col (K q : Table I J) (c : J → ℝ) (h : CrossProducts K q) :
    CrossProducts K (colScale c q) := by
  intro i k j l
  dsimp [colScale]
  calc
    _ = (c j / colSum q j * (c l / colSum q l)) *
        (q i j * q k l * K i l * K k j) := by ring
    _ = _ := by rw [h i k j l]; ring

private lemma cross_iterate (K : Table I J) (r : I → ℝ) (c : J → ℝ) (n : ℕ) :
    CrossProducts K (iterate K r c n) := by
  induction n with
  | zero => intro i k j l; dsimp [iterate]; ring
  | succ n ih => exact cross_col K _ c (cross_row K _ r ih)

private lemma projection_cross (D : Problem I J) (p : Table I J) (hp : IsProjection D p) :
    CrossProducts D.seed p := by
  intro i k j l
  have ht := iterates_converge D p hp
  have he : ∀ i j, Tendsto (fun n => iterate D.seed D.row D.col n i j) atTop (𝓝 (p i j)) :=
    fun i j => (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht i)) j
  have hl := (((he i j).mul (he k l)).mul_const (D.seed i l)).mul_const (D.seed k j)
  have hr := (((he i l).mul (he k j)).mul_const (D.seed i j)).mul_const (D.seed k l)
  exact tendsto_nhds_unique hl (hr.congr (fun n => (cross_iterate D.seed D.row D.col n i k j l).symm))

lemma positive_projection_factors [Nonempty I] [Nonempty J]
    (D : Problem I J) (p : Table I J) (hp : IsProjection D p)
    (hK : PositiveTable D.seed) (hr : PositiveVector D.row) (hc : PositiveVector D.col) :
    ∃ (a : I → ℝ) (b : J → ℝ), PositiveVector a ∧ PositiveVector b ∧
      ∀ i j, p i j = a i * D.seed i j * b j := by
  classical
  let i₀ : I := Classical.arbitrary I
  let j₀ : J := Classical.arbitrary J
  have hp0 := projection_positive D p hp hK hr hc
  refine ⟨fun i => p i j₀ / D.seed i j₀,
    fun j => p i₀ j * D.seed i₀ j₀ / (D.seed i₀ j * p i₀ j₀),
    fun i => div_pos (hp0 i j₀) (hK i j₀),
    fun j => div_pos (mul_pos (hp0 i₀ j) (hK i₀ j₀))
      (mul_pos (hK i₀ j) (hp0 i₀ j₀)), ?_⟩
  intro i j
  have he := projection_cross D p hp i i₀ j j₀
  have h1 := (hK i j₀).ne'
  have h2 := (hK i₀ j).ne'
  have h3 := (hp0 i₀ j₀).ne'
  field_simp [h1, h2, h3]
  nlinarith [he]

lemma positive_projection_fixed [Nonempty I] [Nonempty J]
    (D : Problem I J) (p : Table I J) (hp : IsProjection D p)
    (hK : PositiveTable D.seed) (hr : PositiveVector D.row) (hc : PositiveVector D.col) :
    ∃ b : J → ℝ, PositiveVector b ∧ scalingMap D.seed D.row D.col b = b ∧
      scaledTable D.seed D.row b = p := by
  obtain ⟨a, b, ha, hb, he⟩ := positive_projection_factors D p hp hK hr hc
  have hk : ∀ i, 0 < matVec D.seed b i := by
    intro i
    exact Finset.sum_pos (fun j _ => mul_pos (hK i j) (hb j)) Finset.univ_nonempty
  have har : ∀ i, D.row i / matVec D.seed b i = a i := by
    intro i
    apply (div_eq_iff (hk i).ne').mpr
    have hi := congrFun hp.1.2.2.1 i
    simp only [rowSum, he] at hi
    simpa [matVec, ← Finset.mul_sum, mul_assoc] using hi.symm
  refine ⟨b, hb, ?_, ?_⟩
  · funext j
    dsimp [scalingMap]
    simp only [har]
    have hs : 0 < ∑ i, D.seed i j * a i :=
      Finset.sum_pos (fun i _ => mul_pos (hK i j) (ha i)) Finset.univ_nonempty
    apply (div_eq_iff hs.ne').mpr
    have hj := congrFun hp.1.2.2.2 j
    simp only [colSum, he] at hj
    calc
      D.col j = ∑ i, a i * D.seed i j * b j := hj.symm
      _ = b j * ∑ i, D.seed i j * a i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  · funext i j
    simp only [scaledTable, har, ← he]

end IPF
