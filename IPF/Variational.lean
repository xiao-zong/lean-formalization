import IPF.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

open scoped BigOperators Topology
open Filter Set

noncomputable section
namespace IPF

variable {I J : Type*} [Fintype I] [Fintype J]

theorem feasible_total {D : Problem I J} {p : Table I J}
    (hp : Feasible D.seed D.row D.col p) : ∑ i, ∑ j, p i j = 1 := by
  change (∑ i, rowSum p i) = 1
  rw [hp.2.2.1, D.row_total]

theorem feasible_le_one {D : Problem I J} {p : Table I J}
    (hp : Feasible D.seed D.row D.col p) (i : I) (j : J) : p i j ≤ 1 := by
  calc
    p i j ≤ ∑ j, p i j := Finset.single_le_sum (fun j _ => hp.1 i j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, p i j := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => hp.1 i j)) (Finset.mem_univ i)
    _ = 1 := feasible_total hp

theorem isClosed_feasible (D : Problem I J) :
    IsClosed {p : Table I J | Feasible D.seed D.row D.col p} := by
  have hc (i : I) (j : J) : Continuous (fun p : Table I J => p i j) :=
    (continuous_apply j).comp (continuous_apply i)
  simp only [Feasible, Nonnegative, Supported, Set.ofPred_and, funext_iff,
    rowSum, colSum, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (hc i j)
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_eq
      (continuous_finsetSum _ fun j _ => hc i j) continuous_const
  · exact isClosed_iInter fun j => isClosed_eq
      (continuous_finsetSum _ fun i _ => hc i j) continuous_const

theorem isCompact_feasible (D : Problem I J) :
    IsCompact {p : Table I J | Feasible D.seed D.row D.col p} := by
  apply (isCompact_Icc : IsCompact (Icc (0 : Table I J) 1)).of_isClosed_subset
    (isClosed_feasible D)
  intro p hp
  exact ⟨hp.1, feasible_le_one hp⟩

theorem feasible_mix {K : Table I J} {r : I → ℝ} {c : J → ℝ}
    {p q : Table I J} (hp : Feasible K r c p) (hq : Feasible K r c q)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Feasible K r c (fun i j => a * p i j + b * q i j) := by
  refine ⟨fun i j => add_nonneg (mul_nonneg ha (hp.1 i j)) (mul_nonneg hb (hq.1 i j)),
    fun i j h => ?_, ?_, ?_⟩
  · change a * p i j + b * q i j = 0
    rw [hp.2.1 i j h, hq.2.1 i j h]
    ring
  · funext i
    simp only [rowSum, Finset.sum_add_distrib, ← Finset.mul_sum]
    change a * rowSum p i + b * rowSum q i = r i
    rw [hp.2.2.1, hq.2.2.1, ← add_mul, hab, one_mul]
  · funext j
    simp only [colSum, Finset.sum_add_distrib, ← Finset.mul_sum]
    change a * colSum p j + b * colSum q j = c j
    rw [hp.2.2.2, hq.2.2.2, ← add_mul, hab, one_mul]

theorem continuous_kl_objective (K : Table I J) : Continuous (fun p => kl p K) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hc : Continuous (fun p : Table I J => p i j) :=
    (continuous_apply j).comp (continuous_apply i)
  exact (((Real.continuous_mul_log.comp hc).sub (hc.mul continuous_const)).sub hc).add
    continuous_const

theorem exists_projection (D : Problem I J) : ∃ p, IsProjection D p := by
  obtain ⟨p, hp, hmin⟩ := (isCompact_feasible D).exists_isMinOn D.feasible
    (continuous_kl_objective D.seed).continuousOn
  exact ⟨p, hp, hmin⟩

theorem scalarKL_mix_le {x y a b : ℝ} (z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    scalarKL (a * x + b * y) z ≤ a * scalarKL x z + b * scalarKL y z := by
  have h := Real.convexOn_mul_log.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h
  unfold scalarKL
  nlinarith [congrArg (fun t : ℝ => t * z) hab]

theorem scalarKL_mix_lt {x y a b : ℝ} (z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    scalarKL (a * x + b * y) z < a * scalarKL x z + b * scalarKL y z := by
  have h := Real.strictConvexOn_mul_log.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at h
  unfold scalarKL
  nlinarith [congrArg (fun t : ℝ => t * z) hab]

theorem kl_mix_lt {p q K : Table I J} (hp : Nonnegative p) (hq : Nonnegative q)
    (hpq : p ≠ q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    kl (fun i j => a * p i j + b * q i j) K < a * kl p K + b * kl q K := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hpq
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  have hle (i : I) (j : J) := scalarKL_mix_le (K i j) (hp i j) (hq i j) ha.le hb.le hab
  have hlt := scalarKL_mix_lt (K i j) (hp i j) (hq i j) hj ha hb hab
  have hs := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => Finset.sum_le_sum (fun j _ => hle i j))
    ⟨i, Finset.mem_univ i, Finset.sum_lt_sum (fun j _ => hle i j)
      ⟨j, Finset.mem_univ j, hlt⟩⟩
  simpa only [kl, Finset.sum_add_distrib, Finset.mul_sum] using hs

theorem projection_unique (D : Problem I J) {p q : Table I J}
    (hp : IsProjection D p) (hq : IsProjection D q) : p = q := by
  by_contra hne
  have hf := feasible_mix hp.1 hq.1 (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hlt := kl_mix_lt hp.1.1 hq.1.1 hne (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (K := D.seed)
  have hl := hp.2 _ hf
  have heq := hq.2 p hp.1
  linarith

theorem exists_unique_projection (D : Problem I J) : ∃! p, IsProjection D p := by
  obtain ⟨p, hp⟩ := exists_projection D
  exact ⟨p, hp, fun q hq => projection_unique D hq hp⟩

theorem scalarKL_creation_slope (a z : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => (scalarKL (t * a) z - scalarKL 0 z) / t)
      (𝓝[>] 0) atBot := by
  have he : (fun t : ℝ => (scalarKL (t * a) z - scalarKL 0 z) / t) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => a * Real.log t + (a * Real.log a - a * Real.log z - a)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    simp only [scalarKL, zero_mul, sub_zero, zero_add]
    rw [Real.log_mul ht' (ne_of_gt ha)]
    field_simp
    ring
  apply (tendsto_congr' he).mpr
  exact (Real.tendsto_log_nhdsGT_zero.const_mul_atBot ha).atBot_add
    (tendsto_const_nhds (x := a * Real.log a - a * Real.log z - a))

/-- A boundary minimizer cannot omit a coordinate available to a feasible competitor. -/
theorem entropy_min_support {Ω : Type*} [Fintype Ω]
    (p q K : Ω → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hmin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∑ s, scalarKL (p s) (K s)) ≤
      ∑ s, scalarKL ((1 - t) * p s + t * q s) (K s)) :
    ∀ s, p s = 0 → q s = 0 := by
  classical
  intro s hs
  by_contra hqs
  have hqpos : 0 < q s := lt_of_le_of_ne (hq s) (Ne.symm hqs)
  let delta : Ω → ℝ := fun x => scalarKL (q x) (K x) - scalarKL (p x) (K x)
  let C : ℝ := ∑ x ∈ Finset.univ.erase s, delta x
  have hneg := (scalarKL_creation_slope (q s) (K s) hqpos).eventually
    (eventually_lt_atBot (-C))
  have hone : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht0, ht1, hts⟩ := (hpos.and (hone.and hneg)).exists
  have htpos : 0 < t := ht0
  let slope : Ω → ℝ := fun x =>
    (scalarKL ((1 - t) * p x + t * q x) (K x) - scalarKL (p x) (K x)) / t
  have hslope (x : Ω) : slope x ≤ delta x := by
    dsimp [slope, delta]
    apply (div_le_iff₀ htpos).2
    have h := scalarKL_mix_le (K x) (hp x) (hq x)
      (a := 1 - t) (b := t) (by linarith) htpos.le (by ring)
    nlinarith
  have hslope_s : slope s < -C := by
    simpa only [slope, hs, mul_zero, zero_add] using hts
  have hsum : (∑ x, slope x) < 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
    have hle : (∑ x ∈ Finset.univ.erase s, slope x) ≤ C :=
      Finset.sum_le_sum fun x _ => hslope x
    linarith
  have hsum_eq : (∑ x, slope x) =
      ((∑ x, scalarKL ((1 - t) * p x + t * q x) (K x)) -
      ∑ x, scalarKL (p x) (K x)) / t := by
    dsimp only [slope]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hsum_eq] at hsum
  have hmin' := hmin t htpos.le ht1.le
  have hnonneg : 0 ≤
      ((∑ x, scalarKL ((1 - t) * p x + t * q x) (K x)) -
      ∑ x, scalarKL (p x) (K x)) / t := div_nonneg (sub_nonneg.mpr hmin') htpos.le
  linarith

theorem projection_dominates (D : Problem I J) {p q : Table I J}
    (hp : IsProjection D p) (hq : Feasible D.seed D.row D.col q) : Supported q p := by
  have hm : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∑ s : I × J, scalarKL (p s.1 s.2) (D.seed s.1 s.2)) ≤
      ∑ s : I × J, scalarKL ((1 - t) * p s.1 s.2 + t * q s.1 s.2) (D.seed s.1 s.2) := by
    intro t ht ht1
    have h := hp.2 _ (feasible_mix hp.1 hq (a := 1-t) (b := t)
      (by linarith) ht (by ring))
    simpa only [Fintype.sum_prod_type, kl] using h
  have h := entropy_min_support (fun s : I × J => p s.1 s.2)
    (fun s : I × J => q s.1 s.2) (fun s : I × J => D.seed s.1 s.2)
    (fun s => hp.1.1 s.1 s.2) (fun s => hq.1 s.1 s.2) hm
  exact fun i j hz => h (i,j) hz

theorem projection_support (D : Problem I J) (p : Table I J)
    (hp : IsProjection D p) (i : I) (j : J) :
    0 < p i j ↔ ∃ q, Feasible D.seed D.row D.col q ∧ 0 < q i j := by
  constructor
  · intro h
    exact ⟨p, hp.1, h⟩
  · rintro ⟨q, hq, hqpos⟩
    have hdom := projection_dominates D hp hq
    by_contra h
    have hz : p i j = 0 := le_antisymm (le_of_not_gt h) (hp.1.1 i j)
    have hqz := hdom i j hz
    linarith

theorem feasible_line_eventually (D : Problem I J) {p q : Table I J}
    (hp : Feasible D.seed D.row D.col p) (hq : Feasible D.seed D.row D.col q)
    (hs : Supported q p) :
    ∀ᶠ t : ℝ in 𝓝 0, Feasible D.seed D.row D.col
      (fun i j => p i j + t * (q i j - p i j)) := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ∀ i j, 0 ≤ p i j + t * (q i j - p i j) := by
    apply (eventually_all).2
    intro i
    apply (eventually_all).2
    intro j
    by_cases hpz : p i j = 0
    · have hqz := hs i j hpz
      exact Filter.Eventually.of_forall (by simp [hpz, hqz])
    · have hpp : 0 < p i j := lt_of_le_of_ne (hp.1 i j) (Ne.symm hpz)
      have hc : Continuous (fun t : ℝ => p i j + t * (q i j - p i j)) := by fun_prop
      have hlim : Tendsto (fun t : ℝ => p i j + t * (q i j - p i j)) (𝓝 0) (𝓝 (p i j)) := by
        simpa using hc.tendsto (0 : ℝ)
      filter_upwards [hlim.eventually (eventually_gt_nhds hpp)] with t ht
      exact ht.le
  filter_upwards [hn] with t ht
  refine ⟨ht, ?_, ?_, ?_⟩
  · intro i j hz
    change p i j + t * (q i j - p i j) = 0
    rw [hp.2.1 i j hz, hq.2.1 i j hz]
    ring
  · funext i
    simp only [rowSum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    change rowSum p i + t * (rowSum q i - rowSum p i) = D.row i
    rw [hp.2.2.1, hq.2.2.1]
    ring
  · funext j
    simp only [colSum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    change colSum p j + t * (colSum q j - colSum p j) = D.col j
    rw [hp.2.2.2, hq.2.2.2]
    ring

theorem scalarKL_line_hasDerivAt (p q K : ℝ) (hs : p = 0 → q = 0) :
    HasDerivAt (fun t : ℝ => scalarKL (p + t * (q - p)) K)
      ((q-p) * (Real.log p - Real.log K)) 0 := by
  by_cases hp : p = 0
  · have hq := hs hp
    simp only [hp, hq, sub_self, mul_zero, add_zero, zero_mul]
    exact hasDerivAt_const _ _
  · have hx : HasDerivAt (fun t : ℝ => p + t * (q-p)) (q-p) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).mul_const (q-p)).const_add p using 1 <;> simp
    have hm : HasDerivAt (fun t : ℝ =>
        (p + t * (q-p)) * Real.log (p + t * (q-p)))
        ((Real.log p + 1) * (q-p)) 0 := by
      simpa only [zero_mul, add_zero, Function.comp_def] using
        (Real.hasDerivAt_mul_log (x := p + 0 * (q-p)) (by simpa using hp)).comp 0 hx
    convert ((hm.sub (hx.mul_const (Real.log K))).sub hx).add_const K using 1
    · rfl
    · ring

theorem pythagorean (D : Problem I J) (p : Table I J)
    (hp : IsProjection D p) (q : Table I J)
    (hq : Feasible D.seed D.row D.col q) :
    kl q D.seed = kl q p + kl p D.seed := by
  have hs := projection_dominates D hp hq
  let f : ℝ → ℝ := fun t => kl (fun i j => p i j + t * (q i j - p i j)) D.seed
  have hloc : IsLocalMin f 0 := by
    filter_upwards [feasible_line_eventually D hp.1 hq hs] with t ht
    have h := hp.2 _ ht
    simpa only [f, zero_mul, add_zero] using h
  have hd : HasDerivAt f (∑ i, ∑ j,
      (q i j - p i j) * (Real.log (p i j) - Real.log (D.seed i j))) 0 := by
    exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      scalarKL_line_hasDerivAt _ _ _ (hs i j)
  have hz := hloc.hasDerivAt_eq_zero hd
  have he : kl q D.seed - (kl q p + kl p D.seed) =
      ∑ i, ∑ j, (q i j - p i j) * (Real.log (p i j) - Real.log (D.seed i j)) := by
    simp only [kl, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold scalarKL
    ring
  linarith

end IPF
