import IPF.ProjectiveDefinitions

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

variable {A I J : Type*}

lemma sub_le_osc [Finite A] (h : A → ℝ) (a b : A) : h a - h b ≤ osc h := by
  exact sub_le_sub (le_csSup (finite_range h).bddAbove (mem_range_self a))
    (csInf_le (finite_range h).bddBelow (mem_range_self b))

lemma osc_le_iff [Finite A] [Nonempty A] (h : A → ℝ) (c : ℝ) :
    osc h ≤ c ↔ ∀ a b, h a - h b ≤ c := by
  constructor
  · intro hc a b
    exact (sub_le_osc h a b).trans hc
  · intro hh
    obtain ⟨a, ha⟩ := (range_nonempty h).csSup_mem (finite_range h)
    obtain ⟨b, hb⟩ := (range_nonempty h).csInf_mem (finite_range h)
    simpa [osc, ha, hb] using hh a b

lemma osc_nonneg [Finite A] [Nonempty A] (h : A → ℝ) : 0 ≤ osc h := by
  obtain ⟨a⟩ := ‹Nonempty A›
  simpa using sub_le_osc h a a

lemma osc_le_of_bounds [Finite A] [Nonempty A] (h : A → ℝ) {l u : ℝ}
    (hl : ∀ a, l ≤ h a) (hu : ∀ a, h a ≤ u) : osc h ≤ u - l := by
  apply (osc_le_iff h _).mpr
  intro a b
  exact sub_le_sub (hu a) (hl b)

lemma osc_eq_of_diff_eq [Finite A] [Nonempty A] (h g : A → ℝ)
    (he : ∀ a b, h a - h b = g a - g b) : osc h = osc g := by
  apply le_antisymm
  · apply (osc_le_iff h _).mpr
    intro a b
    rw [he]
    exact sub_le_osc g a b
  · apply (osc_le_iff g _).mpr
    intro a b
    rw [← he]
    exact sub_le_osc h a b

@[simp] lemma osc_neg [Finite A] [Nonempty A] (h : A → ℝ) :
    osc (fun a => -h a) = osc h := by
  apply le_antisymm
  · apply (osc_le_iff _ _).mpr
    intro a b
    simpa only [neg_sub_neg] using sub_le_osc h b a
  · apply (osc_le_iff _ _).mpr
    intro a b
    simpa only [neg_sub_neg] using sub_le_osc (fun a => -h a) b a

lemma osc_add_le [Finite A] [Nonempty A] (h g : A → ℝ) :
    osc (fun a => h a + g a) ≤ osc h + osc g := by
  apply (osc_le_iff _ _).mpr
  intro a b
  linarith [sub_le_osc h a b, sub_le_osc g a b]

lemma hilbert_nonneg [Finite A] [Nonempty A] (x y : A → ℝ) : 0 ≤ hilbert x y :=
  osc_nonneg _

lemma hilbert_symm [Finite A] [Nonempty A] (x y : A → ℝ) :
    hilbert x y = hilbert y x := by
  unfold hilbert
  have he : (fun a => Real.log (x a) - Real.log (y a)) =
      fun a => -(Real.log (y a) - Real.log (x a)) := by funext a; ring
  rw [he, osc_neg]

lemma hilbert_triangle [Finite A] [Nonempty A] (x y z : A → ℝ) :
    hilbert x z ≤ hilbert x y + hilbert y z := by
  unfold hilbert
  have he : (fun a => Real.log (x a) - Real.log (z a)) =
      fun a => (Real.log (x a) - Real.log (y a)) +
        (Real.log (y a) - Real.log (z a)) := by funext a; ring
  rw [he]
  exact osc_add_le _ _

lemma hilbert_div_left [Finite A] [Nonempty A] {r x y : A → ℝ}
    (hr : PositiveVector r) (hx : PositiveVector x) (hy : PositiveVector y) :
    hilbert (fun a => r a / x a) (fun a => r a / y a) = hilbert x y := by
  rw [hilbert_symm x y]
  apply osc_eq_of_diff_eq
  intro a b
  simp only [Real.log_div (ne_of_gt (hr a)) (ne_of_gt (hx a)),
    Real.log_div (ne_of_gt (hr a)) (ne_of_gt (hy a)),
    Real.log_div (ne_of_gt (hr b)) (ne_of_gt (hx b)),
    Real.log_div (ne_of_gt (hr b)) (ne_of_gt (hy b))]
  ring

lemma matVec_positive [Fintype J] [Nonempty J] {K : Table I J} {x : J → ℝ}
    (hK : PositiveTable K) (hx : PositiveVector x) : PositiveVector (matVec K x) := by
  intro i
  exact Finset.sum_pos (fun j _ => mul_pos (hK i j) (hx j)) Finset.univ_nonempty

lemma crossRatio_bound [Finite I] [Finite J] {K : Table I J}
    (hK : PositiveTable K) (i k : I) (j l : J) :
    K i j * K k l ≤ crossRatio K * (K i l * K k j) := by
  have hm : K i j * K k l / (K i l * K k j) ≤ crossRatio K :=
    le_csSup (finite_range _).bddAbove (mem_range_self ((i, k), (j, l)))
  exact (div_le_iff₀ (mul_pos (hK i l) (hK k j))).mp hm

lemma one_le_crossRatio [Finite I] [Finite J] [Nonempty I] [Nonempty J]
    {K : Table I J} (hK : PositiveTable K) : 1 ≤ crossRatio K := by
  obtain ⟨i⟩ := ‹Nonempty I›
  obtain ⟨j⟩ := ‹Nonempty J›
  have hm : K i j * K i j / (K i j * K i j) ≤ crossRatio K :=
    le_csSup (finite_range _).bddAbove (mem_range_self ((i, i), (j, j)))
  simpa [ne_of_gt (hK i j)] using hm

lemma contractionRatio_nonneg [Finite I] [Finite J] [Nonempty I] [Nonempty J]
    {K : Table I J} (hK : PositiveTable K) : 0 ≤ contractionRatio K := by
  unfold contractionRatio
  exact div_nonneg (sub_nonneg.mpr (Real.one_le_sqrt.mpr (one_le_crossRatio hK)))
    (by positivity)

lemma contractionRatio_lt_one {K : Table I J} : contractionRatio K < 1 := by
  unfold contractionRatio
  apply (div_lt_one (by positivity : 0 < Real.sqrt (crossRatio K) + 1)).mpr
  linarith

end IPF
