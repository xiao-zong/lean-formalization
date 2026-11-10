import IPF.Definitions

open scoped BigOperators Topology
open Filter
noncomputable section
namespace IPF

lemma component_le_sum {A : Type*} [Fintype A] (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a) (a : A) : x a ≤ ∑ b, x b := by
  classical
  exact Finset.single_le_sum (fun b _ => hx b) (Finset.mem_univ a)

lemma component_zero_of_sum_zero {A : Type*} [Fintype A] (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a) (hs : ∑ a, x a = 0) (a : A) : x a = 0 := by
  have h := component_le_sum x hx a
  rw [hs] at h
  exact le_antisymm h (hx a)

lemma supported_refl {I J : Type*} (p : Table I J) : Supported p p := by
  intro i j h
  exact h

lemma supported_trans {I J : Type*} {p q k : Table I J}
    (hpq : Supported p q) (hqk : Supported q k) : Supported p k := by
  intro i j hk
  exact hpq i j (hqk i j hk)

lemma rowSum_nonneg {I J : Type*} [Fintype J] {q : Table I J}
    (hq : Nonnegative q) (i : I) : 0 ≤ rowSum q i := Finset.sum_nonneg (fun j _ => hq i j)

lemma colSum_nonneg {I J : Type*} [Fintype I] {q : Table I J}
    (hq : Nonnegative q) (j : J) : 0 ≤ colSum q j := Finset.sum_nonneg (fun i _ => hq i j)

lemma row_zero {I J : Type*} [Fintype J] {q : Table I J}
    (hq : Nonnegative q) {i : I} (hs : rowSum q i = 0) (j : J) : q i j = 0 :=
  component_zero_of_sum_zero (q i) (hq i) hs j

lemma col_zero {I J : Type*} [Fintype I] {q : Table I J}
    (hq : Nonnegative q) {j : J} (hs : colSum q j = 0) (i : I) : q i j = 0 :=
  component_zero_of_sum_zero (fun i => q i j) (fun i => hq i j) hs i

lemma rowScale_nonnegative {I J : Type*} [Fintype J] {r : I → ℝ} {q : Table I J}
    (hr : ∀ i, 0 ≤ r i) (hq : Nonnegative q) : Nonnegative (rowScale r q) := by
  intro i j
  exact mul_nonneg (div_nonneg (hr i) (rowSum_nonneg hq i)) (hq i j)

lemma colScale_nonnegative {I J : Type*} [Fintype I] {c : J → ℝ} {q : Table I J}
    (hc : ∀ j, 0 ≤ c j) (hq : Nonnegative q) : Nonnegative (colScale c q) := by
  intro i j
  exact mul_nonneg (div_nonneg (hc j) (colSum_nonneg hq j)) (hq i j)

lemma rowScale_supported {I J : Type*} [Fintype J] (r : I → ℝ) (q : Table I J) :
    Supported (rowScale r q) q := by
  intro i j h
  simp [rowScale, h]

lemma colScale_supported {I J : Type*} [Fintype I] (c : J → ℝ) (q : Table I J) :
    Supported (colScale c q) q := by
  intro i j h
  simp [colScale, h]

lemma rowSum_zero_for_supported {I J : Type*} [Fintype J] {p q : Table I J}
    (hq : Nonnegative q) (hs : Supported p q) {i : I} (hz : rowSum q i = 0) :
    rowSum p i = 0 := by
  unfold rowSum
  apply Finset.sum_eq_zero
  intro j _
  exact hs i j (row_zero hq hz j)

lemma colSum_zero_for_supported {I J : Type*} [Fintype I] {p q : Table I J}
    (hq : Nonnegative q) (hs : Supported p q) {j : J} (hz : colSum q j = 0) :
    colSum p j = 0 := by
  unfold colSum
  apply Finset.sum_eq_zero
  intro i _
  exact hs i j (col_zero hq hz i)

lemma supported_rowScale {I J : Type*} [Fintype J] {p q : Table I J} {r : I → ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) (hs : Supported p q)
    (hr : rowSum p = r) : Supported p (rowScale r q) := by
  intro i j h
  rcases mul_eq_zero.mp h with hz | hz
  · rcases (div_eq_zero_iff).mp hz with hz | hz
    · exact row_zero hp (by rw [hr]; exact hz) j
    · exact hs i j (row_zero hq hz j)
  · exact hs i j hz

lemma supported_colScale {I J : Type*} [Fintype I] {p q : Table I J} {c : J → ℝ}
    (hp : Nonnegative p) (hq : Nonnegative q) (hs : Supported p q)
    (hc : colSum p = c) : Supported p (colScale c q) := by
  intro i j h
  rcases mul_eq_zero.mp h with hz | hz
  · rcases (div_eq_zero_iff).mp hz with hz | hz
    · exact col_zero hp (by rw [hc]; exact hz) i
    · exact hs i j (col_zero hq hz i)
  · exact hs i j hz

lemma rowSum_rowScale {I J : Type*} [Fintype J] {p q : Table I J} {r : I → ℝ}
    (hq : Nonnegative q) (hs : Supported p q) (hr : rowSum p = r) :
    rowSum (rowScale r q) = r := by
  funext i
  change (∑ j, (r i / rowSum q i) * q i j) = r i
  rw [← Finset.mul_sum]
  change r i / rowSum q i * rowSum q i = r i
  by_cases hz : rowSum q i = 0
  · have h := rowSum_zero_for_supported hq hs hz
    rw [hr] at h
    simp [h]
  · exact div_mul_cancel₀ _ hz

lemma colSum_colScale {I J : Type*} [Fintype I] {p q : Table I J} {c : J → ℝ}
    (hq : Nonnegative q) (hs : Supported p q) (hc : colSum p = c) :
    colSum (colScale c q) = c := by
  funext j
  change (∑ i, (c j / colSum q j) * q i j) = c j
  rw [← Finset.mul_sum]
  change c j / colSum q j * colSum q j = c j
  by_cases hz : colSum q j = 0
  · have h := colSum_zero_for_supported hq hs hz
    rw [hc] at h
    simp [h]
  · exact div_mul_cancel₀ _ hz

lemma iterate_nonnegative {I J : Type*} [Fintype I] [Fintype J]
    (D : Problem I J) (n : ℕ) : Nonnegative (iterate D.seed D.row D.col n) := by
  induction n with
  | zero => exact D.seed_nonnegative
  | succ n ih =>
    exact colScale_nonnegative D.col_nonnegative
      (rowScale_nonnegative D.row_nonnegative ih)

lemma iterate_supported {I J : Type*} [Fintype I] [Fintype J]
    (D : Problem I J) (p : Table I J) (hp : Feasible D.seed D.row D.col p) (n : ℕ) :
    Supported p (iterate D.seed D.row D.col n) := by
  induction n with
  | zero => exact hp.2.1
  | succ n ih =>
    exact supported_colScale hp.1
      (rowScale_nonnegative D.row_nonnegative (iterate_nonnegative D n))
      (supported_rowScale hp.1 (iterate_nonnegative D n) ih hp.2.2.1) hp.2.2.2

lemma iterate_seed_supported {I J : Type*} [Fintype I] [Fintype J]
    (D : Problem I J) (n : ℕ) : Supported (iterate D.seed D.row D.col n) D.seed := by
  induction n with
  | zero => exact supported_refl D.seed
  | succ n ih =>
    exact supported_trans (colScale_supported _ _)
      (supported_trans (rowScale_supported _ _) ih)

lemma iterate_colSum {I J : Type*} [Fintype I] [Fintype J]
    (D : Problem I J) (n : ℕ) : colSum (iterate D.seed D.row D.col (n + 1)) = D.col := by
  obtain ⟨p, hp⟩ := D.feasible
  exact colSum_colScale
    (rowScale_nonnegative D.row_nonnegative (iterate_nonnegative D n))
    (supported_rowScale hp.1 (iterate_nonnegative D n) (iterate_supported D p hp n)
      hp.2.2.1) hp.2.2.2

lemma iterate_total_one {I J : Type*} [Fintype I] [Fintype J]
    (D : Problem I J) (n : ℕ) : (∑ i, ∑ j, iterate D.seed D.row D.col (n + 1) i j) = 1 := by
  rw [Finset.sum_comm]
  change (∑ j, colSum (iterate D.seed D.row D.col (n + 1)) j) = 1
  rw [iterate_colSum, D.col_total]


lemma scalarKL_scaling (x y a : ℝ) (ha : 0 < a) (hs : y = 0 → x = 0) :
    scalarKL x y = scalarKL x (a * y) + x * Real.log a + y - a * y := by
  by_cases hx : x = 0
  · simp [scalarKL, hx]
  have hy : y ≠ 0 := fun h => hx (hs h)
  rw [scalarKL, scalarKL, Real.log_mul ha.ne' hy]
  ring

lemma normalize_pythagorean {A : Type*} [Fintype A]
    (p q : A → ℝ) (r : ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hs : ∀ a, q a = 0 → p a = 0) (hr : ∑ a, p a = r) :
    (∑ a, scalarKL (p a) (q a)) =
      (∑ a, scalarKL (p a) ((r / ∑ b, q b) * q a)) +
        scalarKL r (∑ a, q a) := by
  classical
  have hrn : 0 ≤ r := hr ▸ Finset.sum_nonneg (fun a _ => hp a)
  have hsn : 0 ≤ ∑ a, q a := Finset.sum_nonneg (fun a _ => hq a)
  have hs0 : (∑ a, q a) = 0 → r = 0 := by
    intro hz
    rw [← hr]
    apply Finset.sum_eq_zero
    intro a _
    exact hs a (component_zero_of_sum_zero q hq hz a)
  by_cases hz : r = 0
  · have hp0 : ∀ a, p a = 0 := component_zero_of_sum_zero p hp (hr.trans hz)
    simp [hp0, hz, scalarKL]
  have hrp : 0 < r := lt_of_le_of_ne hrn (Ne.symm hz)
  have hsne : (∑ a, q a) ≠ 0 := fun h => hz (hs0 h)
  have hsp : 0 < ∑ a, q a := lt_of_le_of_ne hsn (Ne.symm hsne)
  have ha : 0 < r / ∑ a, q a := div_pos hrp hsp
  have hid := fun a => scalarKL_scaling (p a) (q a) (r / ∑ b, q b) ha (hs a)
  calc
    (∑ a, scalarKL (p a) (q a)) =
        ∑ a, (scalarKL (p a) ((r / ∑ b, q b) * q a) +
          p a * Real.log (r / ∑ b, q b) + q a - (r / ∑ b, q b) * q a) :=
      Finset.sum_congr rfl (fun a _ => hid a)
    _ = (∑ a, scalarKL (p a) ((r / ∑ b, q b) * q a)) +
        scalarKL r (∑ a, q a) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, hr, div_mul_cancel₀ _ hsne]
      rw [scalarKL, Real.log_div hz hsne]
      ring

lemma row_pythagorean {I J : Type*} [Fintype I] [Fintype J]
    {p q : Table I J} {r : I → ℝ} (hp : Nonnegative p) (hq : Nonnegative q)
    (hs : Supported p q) (hr : rowSum p = r) :
    kl p q = kl p (rowScale r q) + ∑ i, scalarKL (r i) (rowSum q i) := by
  unfold kl rowScale rowSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact normalize_pythagorean (p i) (q i) (r i) (hp i) (hq i) (hs i)
    (congrFun hr i)

lemma col_pythagorean {I J : Type*} [Fintype I] [Fintype J]
    {p q : Table I J} {c : J → ℝ} (hp : Nonnegative p) (hq : Nonnegative q)
    (hs : Supported p q) (hc : colSum p = c) :
    kl p q = kl p (colScale c q) + ∑ j, scalarKL (c j) (colSum q j) := by
  unfold kl colScale colSum
  rw [Finset.sum_comm (f := fun i j => scalarKL (p i j) (q i j)),
    Finset.sum_comm (f := fun i j => scalarKL (p i j) ((c j / ∑ k, q k j) * q i j)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact normalize_pythagorean (fun i => p i j) (fun i => q i j) (c j)
    (fun i => hp i j) (fun i => hq i j) (fun i => hs i j) (congrFun hc j)

end IPF
