import IPF.Divergence
import IPF.Scaling
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.MonotoneConvergence

open scoped BigOperators Topology
open Filter Set

noncomputable section
namespace IPF

variable {I J : Type*} [Fintype I] [Fintype J]

lemma entry_le_total (q : Table I J) (hq : Nonnegative q) (i : I) (j : J) :
    q i j ≤ ∑ a, ∑ b, q a b := by
  exact (Finset.single_le_sum (fun b _ => hq i b) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => hq a b)
      (Finset.mem_univ i))

lemma rowSum_le_total (q : Table I J) (hq : Nonnegative q) (i : I) :
    rowSum q i ≤ ∑ a, ∑ b, q a b := by
  exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => hq a b)
    (Finset.mem_univ i)

lemma table_tendsto_of_kl_zero {p : Table I J} {q : ℕ → Table I J}
    (hp : Nonnegative p) (hq : ∀ n, Nonnegative (q n))
    (hs : ∀ n, Supported p (q n))
    (hp1 : ∀ i j, p i j ≤ 1) (hq1 : ∀ n i j, q n i j ≤ 1)
    (hk : Tendsto (fun n => kl p (q n)) atTop (𝓝 0)) :
    Tendsto q atTop (𝓝 p) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hk0 : ∀ n, 0 ≤ kl p (q n) := fun n => kl_nonneg hp (hq n) (hs n)
  have hb : ∀ n, (p i j - q n i j) ^ 2 ≤ 4 * kl p (q n) := by
    intro n
    calc
      _ ≤ 2 * (p i j + q n i j) * kl p (q n) :=
        coordinate_sq_le_kl hp (hq n) (hs n) i j
      _ ≤ 4 * kl p (q n) :=
        mul_le_mul_of_nonneg_right (by linarith [hp1 i j, hq1 n i j]) (hk0 n)
  have ht : Tendsto (fun n => (p i j - q n i j) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) hb (by simpa using hk.const_mul 4)
  have ha := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have ha' : Tendsto (fun n => |p i j - q n i j|) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using ha
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa [Real.dist_eq, abs_sub_comm] using ha')

lemma antitone_increment_tendsto_zero {u : ℕ → ℝ}
    (hu : Antitone u) (h0 : ∀ n, 0 ≤ u n) :
    Tendsto (fun n => u n - u (n + 1)) atTop (𝓝 0) := by
  have hb : BddBelow (range u) := ⟨0, by rintro x ⟨n, rfl⟩; exact h0 n⟩
  have ht := tendsto_atTop_ciInf hu hb
  have hts := ht.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, sub_self] using ht.sub hts

/-- A compactness and descent argument that does not require bounded scaling factors.
The shared decrement condition records that each marginal correction has the same
KL cost for every feasible first argument. -/
theorem converges_of_descent
    (D : Problem I J) (p : Table I J) (hp : IsProjection D p)
    (q : ℕ → Table I J) (err : ℕ → ℝ)
    (_hq0 : q 0 = D.seed)
    (hq : ∀ n, Nonnegative (q n))
    (hqK : ∀ n, Supported (q n) D.seed)
    (hs : ∀ t, Feasible D.seed D.row D.col t → ∀ n, Supported t (q n))
    (hcols : ∀ n, colSum (q (n + 1)) = D.col)
    (htotal : ∀ n, (∑ i, ∑ j, q (n + 1) i j) = 1)
    (he0 : ∀ n, 0 ≤ err n)
    (hrow : ∀ n i, (rowSum (q (n + 1)) i - D.row i)^2 ≤ 4 * err (n + 1))
    (hdescent : ∀ t, Feasible D.seed D.row D.col t → ∀ n,
      kl t (q (n + 1)) + err n ≤ kl t (q n))
    (hcommon : ∀ t, Feasible D.seed D.row D.col t → ∀ n,
      kl p (q n) - kl t (q n) = kl p D.seed - kl t D.seed) :
    Tendsto q atTop (𝓝 p) := by
  have hpF := hp.1
  have hanti : Antitone (fun n => kl p (q n)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hh := hdescent p hpF n
    linarith [he0 n]
  have hnonneg : ∀ n, 0 ≤ kl p (q n) := fun n => kl_nonneg hpF.1 (hq n) (hs p hpF n)
  have he_le : ∀ n, err n ≤ kl p (q n) - kl p (q (n + 1)) := by
    intro n
    linarith [hdescent p hpF n]
  have he_lim : Tendsto err atTop (𝓝 0) :=
    squeeze_zero he0 he_le (antitone_increment_tendsto_zero hanti hnonneg)
  have he_succ : Tendsto (fun n => err (n + 1)) atTop (𝓝 0) :=
    he_lim.comp (tendsto_add_atTop_nat 1)
  have hq1 : ∀ n i j, q (n + 1) i j ≤ 1 := by
    intro n i j
    simpa only [htotal n] using entry_le_total (q (n + 1)) (hq (n + 1)) i j
  have hbox : ∀ n, q (n + 1) ∈ Icc (0 : Table I J) 1 :=
    fun n => ⟨hq (n + 1), hq1 n⟩
  obtain ⟨z, hz, φ, hφ, hlim⟩ :=
    isCompact_Icc.tendsto_subseq hbox
  have hcoord : ∀ i j, Tendsto (fun n => q (φ n + 1) i j) atTop (𝓝 (z i j)) := by
    intro i j
    exact ((tendsto_pi_nhds.mp hlim) i |> tendsto_pi_nhds.mp) j
  have hzF : Feasible D.seed D.row D.col z := by
    refine ⟨hz.1, ?_, ?_, ?_⟩
    · intro i j hij
      have hh : ∀ n, q (φ n + 1) i j = 0 := fun n => hqK _ i j hij
      exact tendsto_nhds_unique (hcoord i j) (by simpa only [hh] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    · funext i
      have hsq : Tendsto (fun n => (rowSum (q (n + 1)) i - D.row i)^2)
          atTop (𝓝 0) :=
        squeeze_zero (fun n => sq_nonneg _) (fun n => hrow n i)
          (by simpa using he_succ.const_mul 4)
      have hsub : Tendsto (fun n => (rowSum (q (φ n + 1)) i - D.row i)^2)
          atTop (𝓝 0) := hsq.comp hφ.tendsto_atTop
      have hrowlim : Tendsto (fun n => rowSum (q (φ n + 1)) i)
          atTop (𝓝 (rowSum z i)) := by
        exact tendsto_finsetSum _ (fun j _ => hcoord i j)
      have hval := tendsto_nhds_unique ((hrowlim.sub tendsto_const_nhds).pow 2) hsub
      have : (rowSum z i - D.row i)^2 = 0 := hval
      nlinarith [sq_nonneg (rowSum z i - D.row i)]
    · funext j
      have hc : Tendsto (fun n => colSum (q (φ n + 1)) j) atTop (𝓝 (colSum z j)) := by
        exact tendsto_finsetSum _ (fun i _ => hcoord i j)
      have heq : ∀ n, colSum (q (φ n + 1)) j = D.col j :=
        fun n => congrFun (hcols (φ n)) j
      exact tendsto_nhds_unique hc (by simpa only [heq] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => D.col j) atTop (𝓝 (D.col j))))
  have hzKL : Tendsto (fun n => kl z (q (φ n + 1))) atTop (𝓝 0) :=
    kl_tendsto_right_self hlim
  have hpKLsub : Tendsto (fun n => kl p (q (φ n + 1))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hnonneg _) _ hzKL
    intro n
    have h := hcommon z hzF (φ n + 1)
    have hm := hp.2 z hzF
    linarith
  have hindex : Tendsto (fun n => φ n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hpKL : Tendsto (fun n => kl p (q n)) atTop (𝓝 0) :=
    (tendsto_iff_tendsto_subseq_of_antitone hanti hindex).mpr hpKLsub
  have hp1 : ∀ i j, p i j ≤ 1 := by
    intro i j
    have ht : (∑ i, ∑ j, p i j) = 1 := by
      calc
        _ = ∑ i, D.row i := by simpa [rowSum] using congrArg (fun f => ∑ i, f i) hpF.2.2.1
        _ = 1 := D.row_total
    simpa only [ht] using entry_le_total p hpF.1 i j
  have hsucc : Tendsto (fun n => q (n + 1)) atTop (𝓝 p) :=
    table_tendsto_of_kl_zero hpF.1 (fun n => hq (n + 1))
      (fun n => hs p hpF (n + 1)) hp1 hq1 (hpKL.comp (tendsto_add_atTop_nat 1))
  exact (tendsto_add_atTop_iff_nat 1).mp hsucc

theorem iterates_converge (D : Problem I J) (p : Table I J)
    (hp : IsProjection D p) :
    Tendsto (iterate D.seed D.row D.col) atTop (𝓝 p) := by
  let q := iterate D.seed D.row D.col
  let a : ℕ → Table I J := fun n => rowScale D.row (q n)
  let R : ℕ → ℝ := fun n => ∑ i, scalarKL (D.row i) (rowSum (q n) i)
  let C : ℕ → ℝ := fun n => ∑ j, scalarKL (D.col j) (colSum (a n) j)
  have hq : ∀ n, Nonnegative (q n) := iterate_nonnegative D
  have ha : ∀ n, Nonnegative (a n) := fun n => rowScale_nonnegative D.row_nonnegative (hq n)
  have hs : ∀ t, Feasible D.seed D.row D.col t → ∀ n, Supported t (q n) :=
    iterate_supported D
  have has : ∀ t, Feasible D.seed D.row D.col t → ∀ n, Supported t (a n) := by
    intro t ht n
    exact supported_rowScale ht.1 (hq n) (hs t ht n) ht.2.2.1
  have hRsup : ∀ n i, rowSum (q n) i = 0 → D.row i = 0 := by
    intro n i hz
    have hh := rowSum_zero_for_supported (hq n) (hs p hp.1 n) hz
    simpa only [hp.1.2.2.1] using hh
  have hCsup : ∀ n j, colSum (a n) j = 0 → D.col j = 0 := by
    intro n j hz
    have hh := colSum_zero_for_supported (ha n) (has p hp.1 n) hz
    simpa only [hp.1.2.2.2] using hh
  have hRterm : ∀ n i, 0 ≤ scalarKL (D.row i) (rowSum (q n) i) := fun n i =>
    scalarKL_nonneg (D.row_nonnegative i) (rowSum_nonneg (hq n) i) (hRsup n i)
  have hR : ∀ n, 0 ≤ R n := fun n => Finset.sum_nonneg (fun i _ => hRterm n i)
  have hC : ∀ n, 0 ≤ C n := by
    intro n
    exact Finset.sum_nonneg fun j _ => scalarKL_nonneg (D.col_nonnegative j)
      (colSum_nonneg (ha n) j) (hCsup n j)
  have hstep : ∀ t, Feasible D.seed D.row D.col t → ∀ n,
      kl t (q n) = kl t (q (n + 1)) + R n + C n := by
    intro t ht n
    have hr := row_pythagorean ht.1 (hq n) (hs t ht n) ht.2.2.1
    have hc := col_pythagorean ht.1 (ha n) (has t ht n) ht.2.2.2
    change kl t (q n) = kl t (a n) + R n at hr
    change kl t (a n) = kl t (q (n + 1)) + C n at hc
    linarith
  have hrow : ∀ n i, (rowSum (q (n + 1)) i - D.row i)^2 ≤ 4 * R (n + 1) := by
    intro n i
    have hs1 : rowSum (q (n + 1)) i ≤ 1 := by
      exact (rowSum_le_total (q (n + 1)) (hq (n + 1)) i).trans_eq
        (iterate_total_one D n)
    have hr1 : D.row i ≤ 1 := by
      simpa only [D.row_total] using component_le_sum D.row D.row_nonnegative i
    have hterm : scalarKL (D.row i) (rowSum (q (n + 1)) i) ≤ R (n + 1) :=
      Finset.single_le_sum (fun j _ => hRterm (n + 1) j) (Finset.mem_univ i)
    calc
      _ = (D.row i - rowSum (q (n + 1)) i)^2 := by ring
      _ ≤ 2 * (D.row i + rowSum (q (n + 1)) i) *
          scalarKL (D.row i) (rowSum (q (n + 1)) i) :=
        scalarKL_sq_le (D.row_nonnegative i) (rowSum_nonneg (hq (n + 1)) i) (hRsup (n + 1) i)
      _ ≤ 2 * (D.row i + rowSum (q (n + 1)) i) * R (n + 1) :=
        mul_le_mul_of_nonneg_left hterm
          (mul_nonneg (by norm_num) (add_nonneg (D.row_nonnegative i)
            (rowSum_nonneg (hq (n + 1)) i)))
      _ ≤ 4 * R (n + 1) := mul_le_mul_of_nonneg_right (by linarith) (hR (n + 1))
  apply converges_of_descent D p hp q R rfl hq (iterate_seed_supported D) hs
    (iterate_colSum D) (iterate_total_one D) hR hrow
  · intro t ht n
    linarith [hstep t ht n, hC n]
  · intro t ht n
    induction n with
    | zero => rfl
    | succ n ih => linarith [hstep p hp.1 n, hstep t ht n]

end IPF
