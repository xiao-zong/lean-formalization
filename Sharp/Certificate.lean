import Mathlib


open scoped BigOperators

namespace Sharp

def expectation {Ω R : Type*} [Fintype Ω] [Semiring R]
    (p f : Ω → R) : R := ∑ s, p s * f s

def Admissible {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℝ) (b : J → ℝ) (p : Ω → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ (∑ s, p s) = 1 ∧ ∀ j, expectation p (A j) ≤ b j

def RationalFeasible {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (p : Ω → ℚ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ (∑ s, p s) = 1 ∧ ∀ j, expectation p (A j) ≤ b j

def DualValid {Ω J R : Type*} [Fintype Ω] [Fintype J] [Semiring R] [LE R]
    (A : J → Ω → R) (c : Ω → R) (z : R) (lam : J → R) : Prop :=
  (∀ j, 0 ≤ lam j) ∧ ∀ s, c s ≤ z + ∑ j, lam j * A j s

def dualBudget {J R : Type*} [Fintype J] [Semiring R]
    (b : J → R) (z : R) (lam : J → R) : R := z + ∑ j, lam j * b j

/-- The complete instance-general contract for exact certificates.
The fractional clauses range over all real laws with positive conditioning mass.
The last three clauses connect rational certificate arithmetic to real semantics. -/
structure CertificateSoundness (Ω J : Type*) [Fintype Ω] [Fintype J] : Prop where
  weakDuality : ∀ (A : J → Ω → ℝ) (b : J → ℝ) (p c : Ω → ℝ)
    (z : ℝ) (lam : J → ℝ), Admissible A b p → DualValid A c z lam →
    expectation p c ≤ dualBudget b z lam
  conditionalLower : ∀ (A : J → Ω → ℝ) (b : J → ℝ) (p N D : Ω → ℝ)
    (l z : ℝ) (lam : J → ℝ), Admissible A b p →
    DualValid A (fun s => l * D s - N s) z lam → dualBudget b z lam ≤ 0 →
    0 < expectation p D → l ≤ expectation p N / expectation p D
  conditionalUpper : ∀ (A : J → Ω → ℝ) (b : J → ℝ) (p N D : Ω → ℝ)
    (u z : ℝ) (lam : J → ℝ), Admissible A b p →
    DualValid A (fun s => N s - u * D s) z lam → dualBudget b z lam ≤ 0 →
    0 < expectation p D → expectation p N / expectation p D ≤ u
  farkasInfeasible : ∀ (A : J → Ω → ℝ) (b : J → ℝ) (z : ℝ) (lam : J → ℝ),
    DualValid A (fun _ => 0) z lam → dualBudget b z lam < 0 →
    ¬ ∃ p, Admissible A b p
  nullConditioning : ∀ (A : J → Ω → ℝ) (b : J → ℝ) (D : Ω → ℝ)
    (z : ℝ) (lam : J → ℝ), (∀ s, 0 ≤ D s) →
    DualValid A D z lam → dualBudget b z lam ≤ 0 →
    ∀ p, Admissible A b p → expectation p D = 0
  rationalFeasibleCast : ∀ (A : J → Ω → ℚ) (b : J → ℚ) (p : Ω → ℚ),
    RationalFeasible A b p →
    Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ))
      (fun s => (p s : ℝ))
  rationalAttainmentCast : ∀ (A : J → Ω → ℚ) (b : J → ℚ) (p N D : Ω → ℚ)
    (v : ℚ), RationalFeasible A b p → 0 < expectation p D →
    expectation p N = v * expectation p D →
    Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ))
        (fun s => (p s : ℝ)) ∧
      0 < expectation (fun s => (p s : ℝ)) (fun s => (D s : ℝ)) ∧
      expectation (fun s => (p s : ℝ)) (fun s => (N s : ℝ)) /
        expectation (fun s => (p s : ℝ)) (fun s => (D s : ℝ)) = (v : ℝ)
  rationalDualCast : ∀ (A : J → Ω → ℚ) (b : J → ℚ) (c : Ω → ℚ)
    (z : ℚ) (lam : J → ℚ), DualValid A c z lam →
    DualValid (fun j s => (A j s : ℝ)) (fun s => (c s : ℝ))
        (z : ℝ) (fun j => (lam j : ℝ)) ∧
      dualBudget (fun j => (b j : ℝ)) (z : ℝ) (fun j => (lam j : ℝ)) =
        ((dualBudget b z lam : ℚ) : ℝ)

private lemma weak_duality {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℝ) (b : J → ℝ) (p c : Ω → ℝ) (z : ℝ) (lam : J → ℝ)
    (hp : Admissible A b p) (hd : DualValid A c z lam) :
    expectation p c ≤ dualBudget b z lam := by
  classical
  calc
    expectation p c ≤ ∑ s, p s * (z + ∑ j, lam j * A j s) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hd.2 s) (hp.1 s)
    _ = z + ∑ j, lam j * expectation p (A j) := by
      simp only [expectation, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [← Finset.sum_mul, hp.2.1, one_mul, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ dualBudget b z lam := by
      unfold dualBudget
      exact add_le_add le_rfl
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp.2.2 j) (hd.1 j))

private lemma expectation_scalar_sub {Ω : Type*} [Fintype Ω]
    (p N D : Ω → ℝ) (v : ℝ) :
    expectation p (fun s => v * D s - N s) =
      v * expectation p D - expectation p N := by
  classical
  simp only [expectation, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

private lemma expectation_sub_scalar {Ω : Type*} [Fintype Ω]
    (p N D : Ω → ℝ) (v : ℝ) :
    expectation p (fun s => N s - v * D s) =
      expectation p N - v * expectation p D := by
  classical
  simp only [expectation, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

private lemma expectation_cast {Ω : Type*} [Fintype Ω] (p f : Ω → ℚ) :
    expectation (fun s => (p s : ℝ)) (fun s => (f s : ℝ)) =
      ((expectation p f : ℚ) : ℝ) := by
  simp [expectation]

private lemma feasible_cast {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (p : Ω → ℚ)
    (hp : RationalFeasible A b p) :
    Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ))
      (fun s => (p s : ℝ)) := by
  refine ⟨fun s => ?_, ?_, fun j => ?_⟩
  · change (0 : ℝ) ≤ (p s : ℝ)
    exact_mod_cast hp.1 s
  · change (∑ s, (p s : ℝ)) = 1
    exact_mod_cast hp.2.1
  · rw [expectation_cast]
    change ((expectation p (A j) : ℚ) : ℝ) ≤ (b j : ℝ)
    exact_mod_cast hp.2.2 j

theorem certificate_soundness (Ω J : Type*) [Fintype Ω] [Fintype J] :
    CertificateSoundness Ω J := by
  classical
  constructor
  · exact weak_duality
  · intro A b p N D l z lam hp hd hb hpos
    have h := (weak_duality A b p _ z lam hp hd).trans hb
    rw [expectation_scalar_sub] at h
    apply (le_div_iff₀ hpos).2
    linarith
  · intro A b p N D u z lam hp hd hb hpos
    have h := (weak_duality A b p _ z lam hp hd).trans hb
    rw [expectation_sub_scalar] at h
    apply (div_le_iff₀ hpos).2
    linarith
  · intro A b z lam hd hb ⟨p, hp⟩
    have h := weak_duality A b p _ z lam hp hd
    simp only [expectation, mul_zero, Finset.sum_const_zero] at h
    linarith
  · intro A b D z lam hD hd hb p hp
    apply le_antisymm ((weak_duality A b p D z lam hp hd).trans hb)
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hp.1 s) (hD s)
  · exact feasible_cast
  · intro A b p N D v hp hpos heq
    refine ⟨feasible_cast A b p hp, ?_, ?_⟩
    · rw [expectation_cast]
      exact_mod_cast hpos
    · rw [expectation_cast, expectation_cast]
      have hpos' : ((expectation p D : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
      apply (div_eq_iff hpos').2
      exact_mod_cast heq
  · intro A b c z lam hd
    refine ⟨⟨fun j => ?_, fun s => ?_⟩, ?_⟩
    · change (0 : ℝ) ≤ (lam j : ℝ)
      exact_mod_cast hd.1 j
    · change (c s : ℝ) ≤ (z : ℝ) + ∑ j, (lam j : ℝ) * (A j s : ℝ)
      exact_mod_cast hd.2 s
    · simp [dualBudget]

end Sharp


open scoped BigOperators
namespace Sharp

def SparseLaw {Ω J : Type*} [Fintype Ω] [Fintype J] (p : Ω → ℚ) : Prop :=
  (Finset.univ.filter (fun s => p s ≠ 0)).card ≤ Fintype.card J + 3

def InfeasibleCertificate {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) : Prop :=
  ∃ (z : ℚ) (lam : J → ℚ), DualValid A (fun _ => 0) z lam ∧ dualBudget b z lam < 0

def NullCertificate {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (D : Ω → ℚ) : Prop :=
  ∃ (p : Ω → ℚ) (z : ℚ) (lam : J → ℚ),
    RationalFeasible A b p ∧ SparseLaw (J := J) p ∧
      DualValid A D z lam ∧ dualBudget b z lam ≤ 0

def LowerEndpointCertificate {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (N D : Ω → ℚ) (l : ℚ) : Prop :=
  ∃ (p : Ω → ℚ) (z : ℚ) (lam : J → ℚ),
    RationalFeasible A b p ∧ SparseLaw (J := J) p ∧ 0 < expectation p D ∧
      expectation p N = l * expectation p D ∧
      DualValid A (fun s => l * D s - N s) z lam ∧ dualBudget b z lam ≤ 0

def UpperEndpointCertificate {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (N D : Ω → ℚ) (u : ℚ) : Prop :=
  ∃ (p : Ω → ℚ) (z : ℚ) (lam : J → ℚ),
    RationalFeasible A b p ∧ SparseLaw (J := J) p ∧ 0 < expectation p D ∧
      expectation p N = u * expectation p D ∧
      DualValid A (fun s => N s - u * D s) z lam ∧ dualBudget b z lam ≤ 0

/-- Existence, not merely soundness, of exact finite rational certificates.
There is no strict-feasibility, rank or positive-conditioning lower-bound hypothesis. -/
structure CertificateCompleteness (Ω J : Type*) [Fintype Ω] [Fintype J] : Prop where
  rationalFeasibility : ∀ (A : J → Ω → ℚ) (b : J → ℚ),
    (∃ p : Ω → ℝ, Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p) ↔
      ∃ p : Ω → ℚ, RationalFeasible A b p
  linearDualCompleteness : ∀ (A : J → Ω → ℚ) (b : J → ℚ) (c : Ω → ℚ) (r : ℚ),
    (∀ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p →
      expectation p (fun s => (c s : ℝ)) ≤ (r : ℝ)) ↔
      ∃ (z : ℚ) (lam : J → ℚ), DualValid A c z lam ∧ dualBudget b z lam ≤ r
  conditionalAlternative : ∀ (A : J → Ω → ℚ) (b : J → ℚ) (N D : Ω → ℚ),
    (∀ s, 0 ≤ N s ∧ N s ≤ D s) →
      InfeasibleCertificate A b ∨ NullCertificate A b D ∨
        ∃ l u : ℚ, 0 ≤ l ∧ l ≤ u ∧ u ≤ 1 ∧
          LowerEndpointCertificate A b N D l ∧ UpperEndpointCertificate A b N D u

end Sharp


open scoped BigOperators

namespace SharpHard

/-- A finite family of lower and upper bounds has a common point exactly when
every lower bound lies below every upper bound. Empty families are allowed. -/
theorem finite_sandwich {I K : Type*} [Fintype I] [LinearOrder K] [Inhabited K]
    (lower upper : I → K) (L U : Finset I)
    (h : ∀ i ∈ L, ∀ j ∈ U, lower i ≤ upper j) :
    ∃ t, (∀ i ∈ L, lower i ≤ t) ∧ ∀ j ∈ U, t ≤ upper j := by
  classical
  by_cases hl : L.Nonempty
  · obtain ⟨i, hi, hmax⟩ := L.exists_max_image lower hl
    exact ⟨lower i, hmax, fun j hj => h i hi j hj⟩
  · by_cases hu : U.Nonempty
    · obtain ⟨j, hj, hmin⟩ := U.exists_min_image upper hu
      exact ⟨upper j, fun i hi => (hl ⟨i,hi⟩).elim, hmin⟩
    · exact ⟨default, fun i hi => (hl ⟨i,hi⟩).elim,
        fun j hj => (hu ⟨j,hj⟩).elim⟩

def dot {K I : Type*} [Fintype I] [Semiring K] (a x : I → K) : K :=
  ∑ i, a i * x i

def Feasible (n : ℕ) {I : Type*} [Fintype I]
    (a : I → Fin n → ℚ) (b : I → ℚ) : Prop :=
  ∃ x : Fin n → ℚ, ∀ i, dot (a i) x ≤ b i

def RealFeasible (n : ℕ) {I : Type*} [Fintype I]
    (a : I → Fin n → ℚ) (b : I → ℚ) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i, dot (fun k => (a i k : ℝ)) x ≤ (b i : ℝ)

def eliminateA {n : ℕ} {I : Type*} (a : I → Fin (n+1) → ℚ) :
    I ⊕ (I × I) → Fin n → ℚ
  | Sum.inl i => if a i 0 = 0 then fun k => a i k.succ else 0
  | Sum.inr (i,j) => if 0 < a i 0 ∧ a j 0 < 0 then
      fun k => a i 0 * a j k.succ - a j 0 * a i k.succ else 0

def eliminateB {n : ℕ} {I : Type*} (a : I → Fin (n+1) → ℚ) (b : I → ℚ) :
    I ⊕ (I × I) → ℚ
  | Sum.inl i => if a i 0 = 0 then b i else 0
  | Sum.inr (i,j) => if 0 < a i 0 ∧ a j 0 < 0 then
      a i 0 * b j - a j 0 * b i else 0

lemma dot_cons {K : Type*} [Semiring K] {n : ℕ}
    (a : Fin (n+1) → K) (t : K) (x : Fin n → K) :
    dot a (Fin.cons t x) = a 0 * t + dot (fun k => a k.succ) x := by
  simp [dot, Fin.sum_univ_succ]

lemma dot_sub {K I : Type*} [Fintype I] [Ring K]
    (a b x : I → K) (c d : K) :
    dot (fun k => c * a k - d * b k) x = c * dot a x - d * dot b x := by
  simp [dot, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem reconstruct {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) (x : Fin n → ℚ)
    (h : ∀ i, dot (eliminateA a i) x ≤ eliminateB a b i) :
    ∃ t : ℚ, ∀ i, dot (a i) (Fin.cons t x) ≤ b i := by
  classical
  let tail (i : I) := dot (fun k => a i k.succ) x
  have hz (i : I) (hi : a i 0 = 0) : tail i ≤ b i := by
    simpa [eliminateA, eliminateB, hi, tail] using h (Sum.inl i)
  have hp (i j : I) (hi : 0 < a i 0) (hj : a j 0 < 0) :
      a i 0 * tail j - a j 0 * tail i ≤ a i 0 * b j - a j 0 * b i := by
    have hij : 0 < a i 0 ∧ a j 0 < 0 := ⟨hi,hj⟩
    simpa only [eliminateA, eliminateB, ite_eq_left hij, dot_sub] using
      h (Sum.inr (i,j))
  let L : Finset I := Finset.univ.filter fun i => a i 0 < 0
  let U : Finset I := Finset.univ.filter fun i => 0 < a i 0
  obtain ⟨t, htL, htU⟩ := finite_sandwich
      (fun i => (tail i - b i) / (-a i 0))
      (fun i => (b i - tail i) / a i 0) L U (by
    intro j hj i hi
    have hj' : a j 0 < 0 := (Finset.mem_filter.mp hj).2
    have hi' : 0 < a i 0 := (Finset.mem_filter.mp hi).2
    rw [div_le_div_iff₀ (neg_pos.mpr hj') hi']
    nlinarith [hp i j hi' hj'])
  refine ⟨t, fun i => ?_⟩
  rw [dot_cons]
  change a i 0 * t + tail i ≤ b i
  rcases lt_trichotomy (a i 0) 0 with hi | hi | hi
  · have hh := (div_le_iff₀ (neg_pos.mpr hi)).mp (htL i (by simp [L, hi]))
    nlinarith
  · simpa [hi] using hz i hi
  · have hh := (le_div_iff₀ hi).mp (htU i (by simp [U, hi]))
    nlinarith

theorem project {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) (t : ℚ) (x : Fin n → ℚ)
    (h : ∀ i, dot (a i) (Fin.cons t x) ≤ b i) :
    ∀ i, dot (eliminateA a i) x ≤ eliminateB a b i := by
  intro idx
  have hh (i : I) := h i
  simp only [dot_cons] at hh
  rcases idx with i | ⟨i,j⟩
  · by_cases hi : a i 0 = 0
    · simpa [eliminateA, eliminateB, hi] using hh i
    · simp [eliminateA, eliminateB, hi, dot]
  · by_cases hij : 0 < a i 0 ∧ a j 0 < 0
    · have h₁ := mul_le_mul_of_nonneg_left (hh j) (le_of_lt hij.1)
      have h₂ := mul_le_mul_of_nonneg_left (hh i) (le_of_lt (neg_pos.mpr hij.2))
      simp only [eliminateA, eliminateB, ite_eq_left hij, dot_sub]
      nlinarith
    · simp [eliminateA, eliminateB, hij, dot]

theorem eliminate_feasible_iff {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) :
    Feasible n (eliminateA a) (eliminateB a b) ↔ Feasible (n+1) a b := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨t,ht⟩ := reconstruct a b x hx
    exact ⟨Fin.cons t x, ht⟩
  · rintro ⟨x,hx⟩
    refine ⟨fun k => x k.succ, ?_⟩
    apply project a b (x 0)
    have heq : Fin.cons (x 0) (fun k => x k.succ) = x := by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k <;> simp
    simpa only [heq] using hx

theorem feasible_iff_eliminate {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) :
    Feasible (n+1) a b ↔ Feasible n (eliminateA a) (eliminateB a b) :=
  (eliminate_feasible_iff a b).symm

theorem project_real {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) (t : ℝ) (x : Fin n → ℝ)
    (h : ∀ i, dot (fun k => (a i k : ℝ)) (Fin.cons t x) ≤ (b i : ℝ)) :
    ∀ i, dot (fun k => (eliminateA a i k : ℝ)) x ≤ (eliminateB a b i : ℝ) := by
  intro idx
  have hh (i : I) := h i
  simp only [dot_cons] at hh
  rcases idx with i | ⟨i,j⟩
  · by_cases hi : a i 0 = 0
    · simpa [eliminateA, eliminateB, hi] using hh i
    · simp [eliminateA, eliminateB, hi, dot]
  · by_cases hij : 0 < a i 0 ∧ a j 0 < 0
    · have hi : (0:ℝ) < a i 0 := by exact_mod_cast hij.1
      have hj : (a j 0:ℝ) < 0 := by exact_mod_cast hij.2
      have h₁ := mul_le_mul_of_nonneg_left (hh j) (le_of_lt hi)
      have h₂ := mul_le_mul_of_nonneg_left (hh i) (le_of_lt (neg_pos.mpr hj))
      simp only [eliminateA, eliminateB, ite_eq_left hij, Rat.cast_sub, Rat.cast_mul]
      rw [dot_sub]
      nlinarith
    · simp [eliminateA, eliminateB, hij, dot]

theorem reconstruct_real {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) (x : Fin n → ℝ)
    (h : ∀ i, dot (fun k => (eliminateA a i k : ℝ)) x ≤
      (eliminateB a b i : ℝ)) :
    ∃ t : ℝ, ∀ i, dot (fun k => (a i k : ℝ)) (Fin.cons t x) ≤ (b i : ℝ) := by
  classical
  let tail (i : I) := dot (fun k => (a i k.succ : ℝ)) x
  have hz (i : I) (hi : a i 0 = 0) : tail i ≤ (b i : ℝ) := by
    simpa [eliminateA, eliminateB, hi, tail] using h (Sum.inl i)
  have hp (i j : I) (hi : 0 < a i 0) (hj : a j 0 < 0) :
      (a i 0:ℝ) * tail j - (a j 0:ℝ) * tail i ≤
        (a i 0:ℝ) * (b j:ℝ) - (a j 0:ℝ) * (b i:ℝ) := by
    have hij : 0 < a i 0 ∧ a j 0 < 0 := ⟨hi,hj⟩
    simpa only [eliminateA, eliminateB, ite_eq_left hij,
      Rat.cast_sub, Rat.cast_mul, dot_sub] using h (Sum.inr (i,j))
  let L : Finset I := Finset.univ.filter fun i => a i 0 < 0
  let U : Finset I := Finset.univ.filter fun i => 0 < a i 0
  obtain ⟨t, htL, htU⟩ := finite_sandwich
      (fun i => (tail i - (b i:ℝ)) / (-(a i 0:ℝ)))
      (fun i => ((b i:ℝ) - tail i) / (a i 0:ℝ)) L U (by
    intro j hj i hi
    have hj' : a j 0 < 0 := (Finset.mem_filter.mp hj).2
    have hi' : 0 < a i 0 := (Finset.mem_filter.mp hi).2
    have hir : (0:ℝ) < a i 0 := by exact_mod_cast hi'
    have hjr : (a j 0:ℝ) < 0 := by exact_mod_cast hj'
    rw [div_le_div_iff₀ (neg_pos.mpr hjr) hir]
    nlinarith [hp i j hi' hj'])
  refine ⟨t, fun i => ?_⟩
  rw [dot_cons]
  change (a i 0:ℝ) * t + tail i ≤ (b i:ℝ)
  rcases lt_trichotomy (a i 0) 0 with hi | hi | hi
  · have hir : (a i 0:ℝ) < 0 := by exact_mod_cast hi
    have hh := (div_le_iff₀ (neg_pos.mpr hir)).mp (htL i (by simp [L, hi]))
    nlinarith
  · simpa [hi] using hz i hi
  · have hir : (0:ℝ) < a i 0 := by exact_mod_cast hi
    have hh := (le_div_iff₀ hir).mp (htU i (by simp [U, hi]))
    nlinarith

theorem real_feasible_iff_eliminate {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) :
    RealFeasible (n+1) a b → RealFeasible n (eliminateA a) (eliminateB a b) := by
  rintro ⟨x,hx⟩
  refine ⟨fun k => x k.succ, ?_⟩
  apply project_real a b (x 0)
  have heq : Fin.cons (x 0) (fun k => x k.succ) = x := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simpa only [heq] using hx

/-- Rational systems of non-strict finite linear inequalities have a rational
solution whenever they have a real solution. No interior-point hypothesis is
needed; the feasible set can be a proper affine face. -/
theorem rational_feasible_of_real (n : ℕ) {I : Type*} [Fintype I]
    (a : I → Fin n → ℚ) (b : I → ℚ) :
    RealFeasible n a b → Feasible n a b := by
  induction n generalizing I with
  | zero =>
      rintro ⟨x,hx⟩
      refine ⟨fun k => Fin.elim0 k, fun i => ?_⟩
      have hi : (0:ℝ) ≤ (b i : ℝ) := by simpa [dot] using hx i
      have hb : (0:ℚ) ≤ b i := by exact_mod_cast hi
      simpa [dot] using hb
  | succ n ih =>
      intro hr
      have hr' := real_feasible_iff_eliminate a b hr
      exact (eliminate_feasible_iff a b).mp
        (ih (eliminateA a) (eliminateB a b) hr')

theorem real_feasible_iff_rational (n : ℕ) {I : Type*} [Fintype I]
    (a : I → Fin n → ℚ) (b : I → ℚ) :
    RealFeasible n a b ↔ Feasible n a b := by
  refine ⟨rational_feasible_of_real n a b, ?_⟩
  rintro ⟨x,hx⟩
  refine ⟨fun k => (x k : ℝ), fun i => ?_⟩
  have hi : ((dot (a i) x : ℚ) : ℝ) ≤ (b i : ℝ) := by exact_mod_cast hx i
  simpa [dot] using hi

end SharpHard


open scoped BigOperators
namespace SharpHard

/-- An exact nonnegative combination of rows witnessing inconsistency. -/
def InfeasibilityCertificate {V I : Type*} [Fintype I] [Fintype V]
    (a : I → V → ℚ) (b : I → ℚ) : Prop :=
  ∃ lam : I → ℚ, (∀ i, 0 ≤ lam i) ∧
    (∀ k, ∑ i, lam i * a i k = 0) ∧ ∑ i, lam i * b i < 0

noncomputable def eliminationWeights {n : ℕ} {I : Type*}
    (a : I → Fin (n+1) → ℚ) : I ⊕ (I × I) → I → ℚ := by
  classical
  exact fun r k => match r with
    | Sum.inl i => if a i 0 = 0 then (if k = i then 1 else 0) else 0
    | Sum.inr (i,j) => if 0 < a i 0 ∧ a j 0 < 0 then
        (-a j 0) * (if k = i then 1 else 0) +
          a i 0 * (if k = j then 1 else 0) else 0

lemma eliminationWeights_nonneg {n : ℕ} {I : Type*}
    (a : I → Fin (n+1) → ℚ) (r : I ⊕ (I × I)) (k : I) :
    0 ≤ eliminationWeights a r k := by
  classical
  rcases r with i | ⟨i,j⟩
  · simp only [eliminationWeights]
    split_ifs <;> norm_num
  · simp only [eliminationWeights]
    split_ifs with h hi hj
    all_goals try positivity
    all_goals linarith [h.1, h.2]

lemma elimination_row_zero {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (r : I ⊕ (I × I)) :
    ∑ k, eliminationWeights a r k * a k 0 = 0 := by
  classical
  rcases r with i | ⟨i,j⟩
  · by_cases h : a i 0 = 0 <;> simp [eliminationWeights, h]
  · by_cases h : 0 < a i 0 ∧ a j 0 < 0
    · simp [eliminationWeights, h, add_mul, Finset.sum_add_distrib]
      ring
    · simp [eliminationWeights, h]

lemma elimination_row_tail {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (r : I ⊕ (I × I)) (k : Fin n) :
    ∑ j, eliminationWeights a r j * a j k.succ = eliminateA a r k := by
  classical
  rcases r with i | ⟨i,j⟩
  · by_cases h : a i 0 = 0 <;> simp [eliminationWeights, eliminateA, h]
  · by_cases h : 0 < a i 0 ∧ a j 0 < 0
    · simp [eliminationWeights, eliminateA, h, add_mul, Finset.sum_add_distrib]
      ring
    · simp [eliminationWeights, eliminateA, h]

lemma elimination_budget {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ) (r : I ⊕ (I × I)) :
    ∑ j, eliminationWeights a r j * b j = eliminateB a b r := by
  classical
  rcases r with i | ⟨i,j⟩
  · by_cases h : a i 0 = 0 <;> simp [eliminationWeights, eliminateB, h]
  · by_cases h : 0 < a i 0 ∧ a j 0 < 0
    · simp [eliminationWeights, eliminateB, h, add_mul, Finset.sum_add_distrib]
      ring
    · simp [eliminationWeights, eliminateB, h]

lemma weighted_sum_swap {I R : Type*} [Fintype I] [Fintype R]
    (lam : R → ℚ) (W : R → I → ℚ) (v : I → ℚ) :
    ∑ i, (∑ r, lam r * W r i) * v i = ∑ r, lam r * (∑ i, W r i * v i) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma lift_infeasibility_certificate {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin (n+1) → ℚ) (b : I → ℚ)
    (h : InfeasibilityCertificate (eliminateA a) (eliminateB a b)) :
    InfeasibilityCertificate a b := by
  classical
  obtain ⟨lam, hn, ha, hb⟩ := h
  refine ⟨fun j => ∑ r, lam r * eliminationWeights a r j, ?_, ?_, ?_⟩
  · intro j
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hn r) (eliminationWeights_nonneg a r j)
  · intro k
    rw [weighted_sum_swap]
    refine Fin.cases ?_ (fun k => ?_) k
    · simp_rw [elimination_row_zero]
      simp
    · simp_rw [elimination_row_tail]
      exact ha k
  · rw [weighted_sum_swap]
    simpa only [elimination_budget] using hb

theorem infeasible_certificate (n : ℕ) :
    ∀ {I : Type*} [Fintype I] (a : I → Fin n → ℚ) (b : I → ℚ),
      ¬ Feasible n a b → InfeasibilityCertificate a b := by
  classical
  induction n with
  | zero =>
    intro I _ a b h
    have hex : ∃ i, b i < 0 := by
      by_contra! hn
      apply h
      refine ⟨Fin.elim0, fun i => ?_⟩
      simpa [dot] using hn i
    obtain ⟨i, hi⟩ := hex
    refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i <;> simp [hj]
    · intro k
      exact Fin.elim0 k
    · simpa using hi
  | succ n ih =>
    intro I _ a b h
    apply lift_infeasibility_certificate a b
    apply ih
    intro hr
    exact h ((feasible_iff_eliminate a b).mpr hr)

theorem certificate_not_feasible {I V : Type*} [Fintype I] [Fintype V]
    (a : I → V → ℚ) (b : I → ℚ)
    (hc : InfeasibilityCertificate a b) :
    ¬ ∃ x : V → ℚ, ∀ i, dot (a i) x ≤ b i := by
  obtain ⟨lam, hn, ha, hb⟩ := hc
  rintro ⟨x, hx⟩
  have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hx i) (hn i))
  have heq : ∑ i, lam i * dot (a i) x = 0 := by
    simp only [dot, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ha, zero_mul]
    simp
  rw [heq] at hle
  exact (not_lt_of_ge hle) hb

/-- A finite affine inequality system has an exact rational infeasibility
certificate precisely when it has no rational solution. -/
theorem farkas_iff {I V : Type*} [Fintype I] [Fintype V]
    (a : I → V → ℚ) (b : I → ℚ) :
    (¬ ∃ x : V → ℚ, ∀ i, dot (a i) x ≤ b i) ↔
      ∃ lam : I → ℚ, (∀ i, 0 ≤ lam i) ∧
        (∀ k, ∑ i, lam i * a i k = 0) ∧ ∑ i, lam i * b i < 0 := by
  classical
  constructor
  · intro h
    let e := Fintype.equivFin V
    let a' : I → Fin (Fintype.card V) → ℚ := fun i k => a i (e.symm k)
    have hh : ¬ Feasible (Fintype.card V) a' b := by
      rintro ⟨x, hx⟩
      apply h
      refine ⟨fun v => x (e v), fun i => ?_⟩
      have hs := e.sum_comp (fun k => a i (e.symm k) * x k)
      simpa [dot, a'] using hs.trans_le (hx i)
    obtain ⟨lam, hn, ha, hb⟩ := infeasible_certificate _ a' b hh
    refine ⟨lam, hn, fun v => ?_, hb⟩
    simpa [a'] using ha (e v)
  · exact certificate_not_feasible a b

end SharpHard


open scoped BigOperators

namespace SharpHard

universe u

lemma dot_equiv {U V K : Type*} [Fintype U] [Fintype V] [Semiring K]
    (e : U ≃ V) (a x : V → K) :
    dot (fun k => a (e k)) (fun k => x (e k)) = dot a x :=
  e.sum_comp (fun k => a k * x k)

lemma eliminateB_sub_mul {n : ℕ} {I : Type*}
    (a : I → Fin (n+1) → ℚ) (b d : I → ℚ) (t : ℚ)
    (i : I ⊕ (I × I)) :
    eliminateB a (fun j => b j - d j * t) i =
      eliminateB a b i - eliminateB a d i * t := by
  rcases i with i | ⟨i,j⟩
  · by_cases hi : a i 0 = 0 <;> simp [eliminateB, hi]
  · by_cases h : 0 < a i 0 ∧ a j 0 < 0
    · simp only [eliminateB, ite_eq_left h]
      ring
    · simp [eliminateB, h]

/-- Fourier–Motzkin projection onto a single retained rational coordinate. -/
theorem rational_parameter_projection (n : ℕ) {I : Type u} [Fintype I]
    (a : I → Fin n → ℚ) (d b : I → ℚ) :
    ∃ (J : Type u) (_ : Fintype J) (p q : J → ℚ),
      ∀ t : ℚ, (∃ x : Fin n → ℚ, ∀ i, dot (a i) x + d i * t ≤ b i) ↔
        ∀ j, p j * t ≤ q j := by
  induction n generalizing I with
  | zero =>
      refine ⟨I, inferInstance, d, b, fun t => ?_⟩
      simp [dot]
  | succ n ih =>
      obtain ⟨J, instJ, p, q, hpq⟩ :=
        ih (eliminateA a) (eliminateB a d) (eliminateB a b)
      refine ⟨J, instJ, p, q, fun t => ?_⟩
      rw [← hpq t]
      have he := feasible_iff_eliminate a (fun i => b i - d i * t)
      change (∃ x, ∀ i, dot (a i) x + d i * t ≤ b i) ↔
        ∃ x, ∀ i, dot (eliminateA a i) x + eliminateB a d i * t ≤ eliminateB a b i
      simpa only [Feasible, eliminateB_sub_mul, le_sub_iff_add_le] using he

theorem univariate_max_attained {I : Type*} [Fintype I] (p q : I → ℚ)
    (hne : ∃ t : ℚ, ∀ i, p i * t ≤ q i)
    (hb : ∃ M : ℚ, ∀ t, (∀ i, p i * t ≤ q i) → t ≤ M) :
    ∃ t : ℚ, (∀ i, p i * t ≤ q i) ∧
      ∀ s, (∀ i, p i * s ≤ q i) → s ≤ t := by
  classical
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨M,hM⟩ := hb
  let U : Finset I := Finset.univ.filter fun i => 0 < p i
  have hU : U.Nonempty := by
    by_contra h
    have hp (i : I) : p i ≤ 0 := by
      by_contra hi
      exact h ⟨i, by simp [U, lt_of_not_ge hi]⟩
    let t := max t₀ M + 1
    have ht : ∀ i, p i * t ≤ q i := by
      intro i
      have htt : t₀ ≤ t := by dsimp [t]; exact le_trans (le_max_left _ _) (by linarith)
      exact (mul_le_mul_of_nonpos_left htt (hp i)).trans (ht₀ i)
    have := hM t ht
    dsimp [t] at this
    have := le_max_right t₀ M
    linarith
  obtain ⟨i,hi,hmin⟩ := U.exists_min_image (fun i => q i / p i) hU
  have hpi : 0 < p i := (Finset.mem_filter.mp hi).2
  let t := q i / p i
  have ht₀t : t₀ ≤ t := (le_div_iff₀ hpi).mpr (by simpa [mul_comm] using ht₀ i)
  refine ⟨t, fun j => ?_, fun s hs => ?_⟩
  · by_cases hpj : 0 < p j
    · have htj := hmin j (by simp [U, hpj])
      simpa [t, mul_comm] using (le_div_iff₀ hpj).mp htj
    · exact (mul_le_mul_of_nonpos_left ht₀t (le_of_not_gt hpj)).trans (ht₀ j)
  · exact (le_div_iff₀ hpi).mpr (by simpa [mul_comm] using hs i)

theorem parameter_max_attained (n : ℕ) {I : Type*} [Fintype I]
    (a : I → Fin n → ℚ) (d b : I → ℚ)
    (hne : ∃ (t : ℚ) (x : Fin n → ℚ), ∀ i, dot (a i) x + d i * t ≤ b i)
    (hb : ∃ M : ℚ, ∀ (t : ℚ) (x : Fin n → ℚ),
      (∀ i, dot (a i) x + d i * t ≤ b i) → t ≤ M) :
    ∃ (t : ℚ) (x : Fin n → ℚ), (∀ i, dot (a i) x + d i * t ≤ b i) ∧
      ∀ (s : ℚ) (y : Fin n → ℚ),
        (∀ i, dot (a i) y + d i * s ≤ b i) → s ≤ t := by
  obtain ⟨J,instJ,p,q,hproj⟩ := rational_parameter_projection n a d b
  have hpne : ∃ t, ∀ j, p j * t ≤ q j := by
    obtain ⟨t,x,hx⟩ := hne
    exact ⟨t,(hproj t).mp ⟨x,hx⟩⟩
  have hpb : ∃ M, ∀ t, (∀ j, p j * t ≤ q j) → t ≤ M := by
    obtain ⟨M,hM⟩ := hb
    refine ⟨M, fun t ht => ?_⟩
    obtain ⟨x,hx⟩ := (hproj t).mpr ht
    exact hM t x hx
  obtain ⟨t,ht,hmax⟩ := univariate_max_attained p q hpne hpb
  obtain ⟨x,hx⟩ := (hproj t).mpr ht
  exact ⟨t,x,hx,fun s y hy => hmax s ((hproj s).mp ⟨y,hy⟩)⟩

theorem rational_linear_max_attained_fin (n : ℕ) {I : Type*} [Fintype I]
    (a : I → Fin n → ℚ) (b : I → ℚ) (c : Fin n → ℚ)
    (hne : ∃ x, ∀ i, dot (a i) x ≤ b i)
    (hb : ∃ M : ℚ, ∀ x, (∀ i, dot (a i) x ≤ b i) → dot c x ≤ M) :
    ∃ x, (∀ i, dot (a i) x ≤ b i) ∧
      ∀ y, (∀ i, dot (a i) y ≤ b i) → dot c y ≤ dot c x := by
  let aa : I ⊕ Bool → Fin n → ℚ
    | Sum.inl i => a i
    | Sum.inr false => c
    | Sum.inr true => -c
  let dd : I ⊕ Bool → ℚ
    | Sum.inl _ => 0
    | Sum.inr false => -1
    | Sum.inr true => 1
  let bb : I ⊕ Bool → ℚ
    | Sum.inl i => b i
    | Sum.inr _ => 0
  have hcon (t : ℚ) (x : Fin n → ℚ) :
      (∀ i, dot (aa i) x + dd i * t ≤ bb i) ↔
        (∀ i, dot (a i) x ≤ b i) ∧ dot c x = t := by
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · simpa [aa,dd,bb] using h (Sum.inl i)
      · have hlo := h (Sum.inr false)
        have hhi := h (Sum.inr true)
        simp [aa,dd,bb,dot,neg_mul,Finset.sum_neg_distrib] at hlo hhi
        dsimp [dot]
        linarith
    · rintro ⟨hx, ht⟩ idx
      rcases idx with i | (_ | _)
      · simpa [aa,dd,bb] using hx i
      · simp [aa,dd,bb,ht]
      · simp [aa,dd,bb,dot,neg_mul,Finset.sum_neg_distrib] at ht ⊢
        linarith
  have hne' : ∃ t x, ∀ i, dot (aa i) x + dd i * t ≤ bb i := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨dot c x,x,(hcon _ _).mpr ⟨hx,rfl⟩⟩
  have hb' : ∃ M : ℚ, ∀ t x, (∀ i, dot (aa i) x + dd i * t ≤ bb i) → t ≤ M := by
    obtain ⟨M,hM⟩ := hb
    refine ⟨M,fun t x hx => ?_⟩
    obtain ⟨hf,he⟩ := (hcon t x).mp hx
    simpa only [he] using hM x hf
  obtain ⟨t,x,hx,hmax⟩ := parameter_max_attained n aa dd bb hne' hb'
  obtain ⟨hf,he⟩ := (hcon t x).mp hx
  refine ⟨x,hf,fun y hy => ?_⟩
  rw [he]
  exact hmax (dot c y) y ((hcon _ _).mpr ⟨hy,rfl⟩)

/-- A nonempty rational polyhedron with a rationally bounded linear objective
has a rational maximizer. The feasible polyhedron itself need not be bounded. -/
theorem rational_linear_max_attained {I V : Type*} [Fintype I] [Fintype V]
    (a : I → V → ℚ) (b : I → ℚ) (c : V → ℚ)
    (hne : ∃ x, ∀ i, dot (a i) x ≤ b i)
    (hb : ∃ M : ℚ, ∀ x, (∀ i, dot (a i) x ≤ b i) → dot c x ≤ M) :
    ∃ x, (∀ i, dot (a i) x ≤ b i) ∧
      ∀ y, (∀ i, dot (a i) y ≤ b i) → dot c y ≤ dot c x := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let af (i : I) (k : Fin (Fintype.card V)) := a i (e k)
  let cf (k : Fin (Fintype.card V)) := c (e k)
  have hd (v : V → ℚ) (x : Fin (Fintype.card V) → ℚ) :
      dot (fun k => v (e k)) x = dot v (fun k => x (e.symm k)) := by
    simpa using dot_equiv e v (fun k => x (e.symm k))
  have hne' : ∃ x, ∀ i, dot (af i) x ≤ b i := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨fun k => x (e k), fun i => ?_⟩
    simpa only [af, dot_equiv] using hx i
  have hb' : ∃ M : ℚ, ∀ x, (∀ i, dot (af i) x ≤ b i) → dot cf x ≤ M := by
    obtain ⟨M,hM⟩ := hb
    refine ⟨M,fun x hx => ?_⟩
    simpa only [cf, hd] using hM (fun k => x (e.symm k))
      (fun i => by simpa only [af, hd] using hx i)
  obtain ⟨x,hx,hmax⟩ := rational_linear_max_attained_fin _ af b cf hne' hb'
  refine ⟨fun k => x (e.symm k), fun i => ?_, fun y hy => ?_⟩
  · simpa only [af, hd] using hx i
  · have hy' : ∀ i, dot (af i) (fun k => y (e k)) ≤ b i := by
      intro i
      simpa only [af, dot_equiv] using hy i
    have hh := hmax (fun k => y (e k)) hy'
    simpa only [cf, dot_equiv, hd, e.apply_symm_apply] using hh

end SharpHard


open scoped BigOperators

namespace SharpHard

/-- Real and rational feasibility coincide for a finite rational linear system,
with arbitrary finite coordinate and row types. -/
theorem real_feasible_iff_rational_general {I V : Type*} [Fintype I] [Fintype V]
    (a : I → V → ℚ) (b : I → ℚ) :
    (∃ x : V → ℝ, ∀ i, dot (fun v => (a i v : ℝ)) x ≤ (b i : ℝ)) ↔
      ∃ x : V → ℚ, ∀ i, dot (a i) x ≤ b i := by
  classical
  constructor
  · rintro ⟨x,hx⟩
    let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
    let af (i : I) (k : Fin (Fintype.card V)) := a i (e k)
    have hr : RealFeasible (Fintype.card V) af b := by
      refine ⟨fun k => x (e k), fun i => ?_⟩
      change dot (fun k => (a i (e k):ℝ)) (fun k => x (e k)) ≤ (b i:ℝ)
      rw [dot_equiv e (fun v => (a i v:ℝ)) x]
      exact hx i
    obtain ⟨q,hq⟩ := rational_feasible_of_real (Fintype.card V) af b hr
    refine ⟨fun v => q (e.symm v), fun i => ?_⟩
    have hd := dot_equiv e (a i) (fun v => q (e.symm v))
    rw [← hd]
    simpa only [af, e.symm_apply_apply] using hq i
  · rintro ⟨x,hx⟩
    refine ⟨fun v => (x v : ℝ), fun i => ?_⟩
    have hi : ((dot (a i) x : ℚ) : ℝ) ≤ (b i : ℝ) := by exact_mod_cast hx i
    simpa [dot] using hi

end SharpHard

namespace Sharp

private abbrev BridgeRow (Ω J : Type*) := J ⊕ (Ω ⊕ (Unit ⊕ Unit))

private noncomputable def bridgeRows {Ω J : Type*} (A : J → Ω → ℚ) :
    BridgeRow Ω J → Ω → ℚ := by
  classical
  exact fun i s => match i with
    | .inl j => A j s
    | .inr (.inl t) => if s = t then -1 else 0
    | .inr (.inr (.inl _)) => 1
    | .inr (.inr (.inr _)) => -1

private def bridgeRhs {Ω J : Type*} (b : J → ℚ) : BridgeRow Ω J → ℚ
  | .inl j => b j
  | .inr (.inl _) => 0
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr _)) => -1

/-- Every feasible real moment model has a rational feasible law. This includes
models on proper faces and models with no positive conditioning mass. -/
theorem real_feasible_iff_rational_feasible {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) :
    (∃ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p) ↔
      ∃ p : Ω → ℚ, RationalFeasible A b p := by
  classical
  constructor
  · rintro ⟨p, hn, hs, ha⟩
    have hr : ∃ p : Ω → ℝ, ∀ i,
        SharpHard.dot (fun s => (bridgeRows A i s : ℝ)) p ≤ (bridgeRhs b i : ℝ) := by
      refine ⟨p, fun i => ?_⟩
      rcases i with j | (s | (u | u))
      · simpa [bridgeRows, bridgeRhs, SharpHard.dot, expectation, mul_comm] using ha j
      · have hc (t : Ω) : ((if t = s then -1 else 0 : ℚ):ℝ) =
            if t = s then -1 else 0 := by split_ifs <;> norm_num
        simpa [bridgeRows, bridgeRhs, SharpHard.dot, hc] using neg_nonpos.mpr (hn s)
      · simp [bridgeRows, bridgeRhs, SharpHard.dot, hs]
      · simp [bridgeRows, bridgeRhs, SharpHard.dot, hs]
    obtain ⟨q,hq⟩ :=
      (SharpHard.real_feasible_iff_rational_general (bridgeRows A) (bridgeRhs b)).mp hr
    refine ⟨q, ?_, ?_, ?_⟩
    · intro s
      have h := hq (.inr (.inl s))
      simp [bridgeRows, bridgeRhs, SharpHard.dot] at h
      linarith
    · have h₁ := hq (.inr (.inr (.inl ())))
      have h₂ := hq (.inr (.inr (.inr ())))
      simp [bridgeRows, bridgeRhs, SharpHard.dot] at h₁ h₂
      linarith
    · intro j
      simpa [bridgeRows, bridgeRhs, SharpHard.dot, expectation, mul_comm] using hq (.inl j)
  · rintro ⟨p,hp⟩
    exact ⟨fun s => (p s : ℝ), (certificate_soundness Ω J).rationalFeasibleCast A b p hp⟩

end Sharp


open scoped BigOperators

namespace SharpHard

/-- A rational probability vector admits a rational probability vector supported on at
most one more atom than the number of moment coordinates, with exactly the same moments.
No positivity, independence, or nonredundancy assumption is imposed on the coordinates. -/
theorem rational_moment_sparsification
    {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq Ω]
    (F : J → Ω → ℚ) (p : Ω → ℚ)
    (hp : ∀ s, 0 ≤ p s) (hsum : ∑ s, p s = 1) :
    ∃ q : Ω → ℚ,
      (∀ s, 0 ≤ q s) ∧ (∑ s, q s) = 1 ∧
      (∀ j, ∑ s, q s * F j s = ∑ s, p s * F j s) ∧
      (Finset.univ.filter (fun s => q s ≠ 0)).card ≤ Fintype.card J + 1 := by
  classical
  let f : Ω → J → ℚ := fun s j => F j s
  let x : J → ℚ := ∑ s, p s • f s
  have hx : x ∈ convexHull ℚ (Set.range f) := by
    apply (convex_convexHull ℚ (Set.range f)).sum_mem
    · intro s _
      exact hp s
    · simpa using hsum
    · intro s _
      exact subset_convexHull ℚ (Set.range f) (Set.mem_range_self s)
  obtain ⟨ι, _, z, w, hz, hi, hw, hw_sum, hw_x⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  let pick : ι → Ω := fun i => Classical.choose (hz (Set.mem_range_self i))
  have hpick (i : ι) : f (pick i) = z i :=
    Classical.choose_spec (hz (Set.mem_range_self i))
  let q : Ω → ℚ := fun s => ∑ i, if pick i = s then w i else 0
  have hq_nonneg : ∀ s, 0 ≤ q s := by
    intro s
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact (hw i).le
    · exact le_rfl
  have hq_sum : ∑ s, q s = 1 := by
    simp only [q]
    rw [Finset.sum_comm]
    simpa using hw_sum
  have hq_moments (j : J) :
      ∑ s, q s * F j s = ∑ s, p s * F j s := by
    have hcoord := congrFun hw_x j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    calc
      ∑ s, q s * F j s = ∑ i, w i * F j (pick i) := by
        simp only [q, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = ∑ i, w i * z i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hpick i]
      _ = ∑ s, p s * F j s := by simpa only [x, f, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul] using hcoord
  have hcard : Fintype.card ι ≤ Fintype.card J + 1 := by
    calc
      Fintype.card ι ≤
          Module.finrank ℚ (vectorSpan ℚ (Set.range z)) + 1 :=
        hi.card_le_finrank_succ
      _ ≤ Module.finrank ℚ (J → ℚ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = Fintype.card J + 1 := by simp
  refine ⟨q, hq_nonneg, hq_sum, hq_moments, ?_⟩
  calc
    (Finset.univ.filter (fun s => q s ≠ 0)).card ≤
        (Finset.univ.image pick).card := by
      apply Finset.card_le_card
      intro s hs
      apply Finset.mem_image.mpr
      have hq := (Finset.mem_filter.mp hs).2
      have hex : ∃ i, pick i = s := by
        by_contra hn
        push Not at hn
        simp [q, hn] at hq
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_univ i, hi⟩
    _ ≤ Fintype.card ι := by simpa using Finset.card_image_le (s := Finset.univ) (f := pick)
    _ ≤ Fintype.card J + 1 := hcard

/-- Simultaneously preserve all observation moments and both coordinates of a
conditional probability. Thus sparsification also preserves strict positivity of
the conditioning mass and any exact lower or upper attainment identity. -/
theorem rational_conditional_sparsification
    {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq Ω]
    (A : J → Ω → ℚ) (N D p : Ω → ℚ)
    (hp : ∀ s, 0 ≤ p s) (hsum : ∑ s, p s = 1) :
    ∃ q : Ω → ℚ,
      (∀ s, 0 ≤ q s) ∧ (∑ s, q s) = 1 ∧
      (∀ j, ∑ s, q s * A j s = ∑ s, p s * A j s) ∧
      (∑ s, q s * N s) = (∑ s, p s * N s) ∧
      (∑ s, q s * D s) = (∑ s, p s * D s) ∧
      (Finset.univ.filter (fun s => q s ≠ 0)).card ≤ Fintype.card J + 3 := by
  let F : J ⊕ Bool → Ω → ℚ := Sum.elim A (fun b => if b then D else N)
  obtain ⟨q, hq, hsumq, hmom, hcard⟩ :=
    rational_moment_sparsification F p hp hsum
  refine ⟨q, hq, hsumq, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hmom (Sum.inl j)
  · exact hmom (Sum.inr false)
  · exact hmom (Sum.inr true)
  · simpa only [Fintype.card_sum, Fintype.card_bool, Nat.add_assoc] using hcard

end SharpHard


open scoped BigOperators

namespace Sharp

abbrev PrimalRow (Ω J : Type*) := J ⊕ (Ω ⊕ (Unit ⊕ Unit))

noncomputable def primalRows {Ω J : Type*} (A : J → Ω → ℚ) :
    PrimalRow Ω J → Ω → ℚ := by
  classical
  exact fun i s => match i with
    | .inl j => A j s
    | .inr (.inl t) => if s = t then -1 else 0
    | .inr (.inr (.inl _)) => 1
    | .inr (.inr (.inr _)) => -1

def primalRhs {Ω J : Type*} (b : J → ℚ) : PrimalRow Ω J → ℚ
  | .inl j => b j
  | .inr (.inl _) => 0
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr _)) => -1

lemma primal_feasible_iff {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) :
    (∃ p : Ω → ℚ, ∀ i, SharpHard.dot (primalRows A i) p ≤ primalRhs b i) ↔
      ∃ p : Ω → ℚ, RationalFeasible A b p := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_, ?_, ?_⟩
    · intro s
      have h := hp (.inr (.inl s))
      simp [primalRows, primalRhs, SharpHard.dot] at h
      linarith
    · have h₁ := hp (.inr (.inr (.inl ())))
      have h₂ := hp (.inr (.inr (.inr ())))
      simp [primalRows, primalRhs, SharpHard.dot] at h₁ h₂
      linarith
    · intro j
      simpa [primalRows, primalRhs, SharpHard.dot, expectation, mul_comm]
        using hp (.inl j)
  · rintro ⟨p, hn, hs, ha⟩
    refine ⟨p, fun i => ?_⟩
    rcases i with j | (s | (u | u))
    · simpa [primalRows, primalRhs, SharpHard.dot, expectation, mul_comm] using ha j
    · simpa [primalRows, primalRhs, SharpHard.dot] using neg_nonpos.mpr (hn s)
    · simp [primalRows, primalRhs, SharpHard.dot, hs]
    · simp [primalRows, primalRhs, SharpHard.dot, hs]

theorem infeasible_complete {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ)
    (h : ¬ ∃ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p) :
    ∃ (z : ℚ) (lam : J → ℚ),
      DualValid A (fun _ => 0) z lam ∧ dualBudget b z lam < 0 := by
  classical
  have hq : ¬ ∃ p : Ω → ℚ, RationalFeasible A b p := by
    rintro ⟨p, hp⟩
    exact h ⟨fun s => (p s : ℝ), (certificate_soundness Ω J).rationalFeasibleCast A b p hp⟩
  have he : ¬ ∃ p : Ω → ℚ, ∀ i,
      SharpHard.dot (primalRows A i) p ≤ primalRhs b i := by
    exact fun hp => hq ((primal_feasible_iff A b).mp hp)
  obtain ⟨w, hw, hc, hb⟩ := (SharpHard.farkas_iff (primalRows A) (primalRhs b)).mp he
  refine ⟨w (.inr (.inr (.inl ()))) - w (.inr (.inr (.inr ()))),
    fun j => w (.inl j), ⟨fun j => hw (.inl j), ?_⟩, ?_⟩
  · intro s
    have hs := hc s
    have hn := hw (.inr (.inl s))
    simp [primalRows, Fintype.sum_sum_type] at hs
    linarith
  · simpa [dualBudget, primalRhs, Fintype.sum_sum_type, add_comm, add_left_comm,
      add_assoc, sub_eq_add_neg] using hb

private abbrev UpperRow (Ω J : Type*) := J ⊕ (Ω ⊕ Unit)
private abbrev UpperVariable (J : Type*) := J ⊕ Unit

private noncomputable def upperRows {Ω J : Type*} (A : J → Ω → ℚ) (b : J → ℚ) :
    UpperRow Ω J → UpperVariable J → ℚ := by
  classical
  exact fun i k => match i, k with
    | .inl j, .inl k => if k = j then -1 else 0
    | .inl _, .inr _ => 0
    | .inr (.inl s), .inl j => -A j s
    | .inr (.inl _), .inr _ => -1
    | .inr (.inr _), .inl j => b j
    | .inr (.inr _), .inr _ => 1

private def upperRhs {Ω J : Type*} (c : Ω → ℚ) (r : ℚ) : UpperRow Ω J → ℚ
  | .inl _ => 0
  | .inr (.inl s) => -c s
  | .inr (.inr _) => r

private lemma upper_feasible_iff {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (c : Ω → ℚ) (r : ℚ) :
    (∃ x : UpperVariable J → ℚ, ∀ i,
      SharpHard.dot (upperRows A b i) x ≤ upperRhs c r i) ↔
    ∃ (z : ℚ) (lam : J → ℚ), DualValid A c z lam ∧ dualBudget b z lam ≤ r := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x (.inr ()), fun j => x (.inl j), ⟨?_, ?_⟩, ?_⟩
    · intro j
      have h := hx (.inl j)
      simp [upperRows, upperRhs, SharpHard.dot, Fintype.sum_sum_type] at h
      linarith
    · intro s
      have h := hx (.inr (.inl s))
      simp [upperRows, upperRhs, SharpHard.dot, Fintype.sum_sum_type, mul_comm] at h
      simpa only [mul_comm] using h
    · simpa [dualBudget, upperRows, upperRhs, SharpHard.dot, Fintype.sum_sum_type,
        mul_comm, add_comm] using hx (.inr (.inr ()))
  · rintro ⟨z, lam, ⟨hn, ha⟩, hb⟩
    refine ⟨Sum.elim lam (fun _ => z), fun i => ?_⟩
    rcases i with j | (s | u)
    · simpa [upperRows, upperRhs, SharpHard.dot, Fintype.sum_sum_type]
        using neg_nonpos.mpr (hn j)
    · have h := ha s
      simp [upperRows, upperRhs, SharpHard.dot, Fintype.sum_sum_type, mul_comm]
      simpa only [mul_comm] using h
    · simpa [dualBudget, upperRows, upperRhs, SharpHard.dot, Fintype.sum_sum_type,
        mul_comm, add_comm] using hb

theorem rational_bound_complete {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (c : Ω → ℚ) (r : ℚ)
    (hvalid : ∀ p : Ω → ℚ, RationalFeasible A b p → expectation p c ≤ r) :
    ∃ (z : ℚ) (lam : J → ℚ), DualValid A c z lam ∧ dualBudget b z lam ≤ r := by
  classical
  by_contra h
  have he : ¬ ∃ x : UpperVariable J → ℚ, ∀ i,
      SharpHard.dot (upperRows A b i) x ≤ upperRhs c r i := by
    exact fun hx => h ((upper_feasible_iff A b c r).mp hx)
  obtain ⟨w, hw, hc, hb⟩ := (SharpHard.farkas_iff (upperRows A b) (upperRhs c r)).mp he
  let q : Ω → ℚ := fun s => w (.inr (.inl s))
  let t : ℚ := w (.inr (.inr ()))
  have hq : ∀ s, 0 ≤ q s := fun s => hw (.inr (.inl s))
  have ht : 0 ≤ t := hw (.inr (.inr ()))
  have hsum : ∑ s, q s = t := by
    have hcol := hc (.inr ())
    simp [upperRows, Fintype.sum_sum_type] at hcol
    linarith
  have hrow : ∀ j, expectation q (A j) ≤ t * b j := by
    intro j
    have hcol := hc (.inl j)
    have hn := hw (.inl j)
    simp [upperRows, Fintype.sum_sum_type, mul_comm] at hcol
    have hle : (∑ s, A j s * w (.inr (.inl s))) ≤ b j * w (.inr (.inr ())) := by
      linarith
    simpa [expectation, q, t, mul_comm] using hle
  have hstrict : t * r < expectation q c := by
    simp [upperRhs, Fintype.sum_sum_type] at hb
    dsimp [expectation, q, t]
    linarith
  have htpos : 0 < t := by
    by_contra! htzero
    have hz : t = 0 := le_antisymm htzero ht
    have hqzero : ∀ s, q s = 0 := by
      intro s
      have hs : q s ≤ ∑ k, q k :=
        Finset.single_le_sum (fun k _ => hq k) (Finset.mem_univ s)
      rw [hsum, hz] at hs
      exact le_antisymm hs (hq s)
    simp [hqzero, hz, expectation] at hstrict
  let p : Ω → ℚ := fun s => q s / t
  have hp : RationalFeasible A b p := by
    refine ⟨fun s => div_nonneg (hq s) ht, ?_, fun j => ?_⟩
    · simp [p, ← Finset.sum_div, hsum, ne_of_gt htpos]
    · have heq : expectation p (A j) = expectation q (A j) / t := by
        simp [expectation, p, div_mul_eq_mul_div, Finset.sum_div]
      rw [heq]
      exact (div_le_iff₀ htpos).mpr (by simpa [mul_comm] using hrow j)
  have heq : expectation p c = expectation q c / t := by
    simp [expectation, p, div_mul_eq_mul_div, Finset.sum_div]
  have hlt : r < expectation p c := by
    rw [heq]
    exact (lt_div_iff₀ htpos).mpr (by simpa [mul_comm] using hstrict)
  exact (not_lt_of_ge (hvalid p hp)) hlt

theorem real_bound_iff_rational_certificate {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (c : Ω → ℚ) (r : ℚ) :
    (∀ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p →
      expectation p (fun s => (c s : ℝ)) ≤ (r : ℝ)) ↔
    ∃ (z : ℚ) (lam : J → ℚ), DualValid A c z lam ∧ dualBudget b z lam ≤ r := by
  constructor
  · intro hv
    apply rational_bound_complete A b c r
    intro p hp
    have h := hv (fun s => (p s : ℝ))
      ((certificate_soundness Ω J).rationalFeasibleCast A b p hp)
    have h' : ((expectation p c : ℚ) : ℝ) ≤ (r : ℝ) := by
      simpa [expectation] using h
    exact_mod_cast h'
  · rintro ⟨z, lam, hd, hb⟩ p hp
    obtain ⟨hd', hb'⟩ := (certificate_soundness Ω J).rationalDualCast A b c z lam hd
    have h := (certificate_soundness Ω J).weakDuality _ _ p _ _ _ hp hd'
    rw [hb'] at h
    exact h.trans (by exact_mod_cast hb)

theorem rational_infeasible_iff_certificate {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) :
    (¬ ∃ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p) ↔
    ∃ (z : ℚ) (lam : J → ℚ),
      DualValid A (fun _ => 0) z lam ∧ dualBudget b z lam < 0 := by
  constructor
  · exact infeasible_complete A b
  · rintro ⟨z, lam, hd, hb⟩
    obtain ⟨hd', hb'⟩ := (certificate_soundness Ω J).rationalDualCast A b (fun _ => 0) z lam hd
    have hd'' : DualValid (fun j s => (A j s : ℝ)) (fun _ => 0) (z : ℝ)
        (fun j => (lam j : ℝ)) := by simpa using hd'
    apply (certificate_soundness Ω J).farkasInfeasible _ _ _ _ hd''
    rw [hb']
    exact_mod_cast hb

end Sharp


open scoped BigOperators

namespace SharpHard

private def ccRow {Ω J K : Type*} [DecidableEq Ω] [Field K]
    (A : J → Ω → K) (b : J → K) (D : Ω → K) :
    Ω ⊕ (J ⊕ Bool) → Ω → K
  | Sum.inl v => fun s => if s = v then -1 else 0
  | Sum.inr (Sum.inl j) => fun s => A j s - b j
  | Sum.inr (Sum.inr k) => fun s => if k then -D s else D s

private def ccRhs {Ω J K : Type*} [Field K] : Ω ⊕ (J ⊕ Bool) → K
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr k) => if k then -1 else 1

private theorem cc_iff {Ω J K : Type*} [Fintype Ω] [Fintype J]
    [DecidableEq Ω] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : J → Ω → K) (b : J → K) (D q : Ω → K) :
    (∀ i, dot (ccRow A b D i) q ≤ ccRhs i) ↔
      (∀ s, 0 ≤ q s) ∧
      (∀ j, dot (A j) q ≤ b j * ∑ s, q s) ∧ dot D q = 1 := by
  classical
  have hj (j : J) : dot (ccRow A b D (Sum.inr (Sum.inl j))) q =
      dot (A j) q - b j * ∑ s, q s := by
    simp [ccRow, dot, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro s
      have hs := h (Sum.inl s)
      simpa [ccRow, ccRhs, dot] using hs
    · intro j
      have hh := h (Sum.inr (Sum.inl j))
      rw [hj] at hh
      simpa [ccRhs, sub_nonpos] using hh
    · have hl := h (Sum.inr (Sum.inr false))
      have hu := h (Sum.inr (Sum.inr true))
      simp only [ccRow, ccRhs, Bool.false_eq_true, ↓reduceIte] at hl
      simp only [ccRow, ccRhs, ↓reduceIte, dot, neg_mul, Finset.sum_neg_distrib] at hu
      change -dot D q ≤ -1 at hu
      exact le_antisymm hl (by linarith)
  · rintro ⟨hn, ha, hd⟩ idx
    rcases idx with s | j | k
    · simpa [ccRow, ccRhs, dot] using hn s
    · rw [hj]
      simpa [ccRhs, sub_nonpos] using ha j
    · cases k <;> simp [ccRow, ccRhs, dot, ← hd]

private theorem ccRow_cast {Ω J : Type*} [DecidableEq Ω]
    (A : J → Ω → ℚ) (b : J → ℚ) (D : Ω → ℚ)
    (i : Ω ⊕ (J ⊕ Bool)) (s : Ω) :
    ((ccRow A b D i s : ℚ) : ℝ) =
      ccRow (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ))
        (fun s => (D s : ℝ)) i s := by
  rcases i with v | j | k
  · by_cases h : s = v <;> simp [ccRow, h]
  · simp [ccRow]
  · cases k <;> simp [ccRow]

private theorem ccRhs_cast {Ω J : Type*} (i : Ω ⊕ (J ⊕ Bool)) :
    ((ccRhs i : ℚ) : ℝ) = (ccRhs i : ℝ) := by
  rcases i with v | j | k
  · simp [ccRhs]
  · simp [ccRhs]
  · cases k <;> simp [ccRhs]

private theorem dot_div {Ω K : Type*} [Fintype Ω] [Field K]
    (a p : Ω → K) (d : K) :
    dot a (fun s => p s / d) = dot a p / d := by
  simp [dot, mul_div_assoc, Finset.sum_div]

/-- Charnes--Cooper normalization yields a rational law attaining the largest
conditional value. The admissible region may contain laws with zero conditioning
mass, and it need not have a strictly feasible law. -/
theorem rational_conditional_max_attained
    {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq Ω]
    (A : J → Ω → ℚ) (b : J → ℚ) (N D : Ω → ℚ)
    (hND : ∀ s, 0 ≤ N s ∧ N s ≤ D s)
    (hne : ∃ p : Ω → ℝ,
      Sharp.Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p ∧
      0 < Sharp.expectation p (fun s => (D s : ℝ))) :
    ∃ p : Ω → ℚ, Sharp.RationalFeasible A b p ∧
      0 < Sharp.expectation p D ∧
      ∀ r : Ω → ℚ, Sharp.RationalFeasible A b r →
        0 < Sharp.expectation r D →
        Sharp.expectation r N / Sharp.expectation r D ≤
          Sharp.expectation p N / Sharp.expectation p D := by
  classical
  have hex : ∃ q : Ω → ℚ, ∀ i, dot (ccRow A b D i) q ≤ ccRhs i := by
    apply (real_feasible_iff_rational_general (ccRow A b D) ccRhs).mp
    obtain ⟨r, hr, hrD⟩ := hne
    let Dr : Ω → ℝ := fun s => (D s : ℝ)
    have hrD' : 0 < dot Dr r := by
      simpa [Dr, Sharp.expectation, dot, mul_comm] using hrD
    let q : Ω → ℝ := fun s => r s / dot Dr r
    have hcc : ∀ i,
        dot (ccRow (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) Dr i) q ≤
          ccRhs i := by
      apply (cc_iff _ _ _ _).mpr
      refine ⟨fun s => div_nonneg (hr.1 s) hrD'.le, ?_, ?_⟩
      · intro j
        change dot (fun s => (A j s : ℝ)) (fun s => r s / dot Dr r) ≤
          (b j : ℝ) * ∑ s, r s / dot Dr r
        rw [dot_div, ← Finset.sum_div, hr.2.1]
        have hj : dot (fun s => (A j s : ℝ)) r ≤ (b j : ℝ) := by
          simpa [Sharp.expectation, dot, mul_comm] using hr.2.2 j
        exact (div_le_iff₀ hrD').mpr (by simpa [mul_div_assoc, ne_of_gt hrD'] using hj)
      · change dot Dr (fun s => r s / dot Dr r) = 1
        rw [dot_div, div_self (ne_of_gt hrD')]
    refine ⟨q, fun i => ?_⟩
    simpa only [ccRow_cast, ccRhs_cast] using hcc i
  have hb : ∃ M : ℚ, ∀ q : Ω → ℚ,
      (∀ i, dot (ccRow A b D i) q ≤ ccRhs i) → dot N q ≤ M := by
    refine ⟨1, ?_⟩
    intro q hq
    obtain ⟨hn, ha, hd⟩ := (cc_iff A b D q).mp hq
    calc
      dot N q ≤ dot D q := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_right (hND s).2 (hn s)
      _ = 1 := hd
  obtain ⟨q, hq, hmax⟩ := rational_linear_max_attained
    (ccRow A b D) ccRhs N hex hb
  obtain ⟨hn, ha, hd⟩ := (cc_iff A b D q).mp hq
  have ht : 0 < ∑ s, q s := by
    by_contra ht
    have hzero : ∑ s, q s = 0 :=
      le_antisymm (le_of_not_gt ht) (Finset.sum_nonneg fun s _ => hn s)
    have hz : ∀ s, q s = 0 := fun s =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hn s)).mp hzero s (Finset.mem_univ s)
    simp [dot, hz] at hd
  let p : Ω → ℚ := fun s => q s / ∑ u, q u
  have hp : Sharp.RationalFeasible A b p := by
    refine ⟨fun s => div_nonneg (hn s) ht.le, ?_, ?_⟩
    · simp [p, ← Finset.sum_div, ne_of_gt ht]
    · intro j
      have hj : dot (A j) p ≤ b j := by
        rw [show dot (A j) p = dot (A j) q / ∑ s, q s by exact dot_div _ _ _]
        exact (div_le_iff₀ ht).mpr (ha j)
      simpa [Sharp.expectation, dot, mul_comm] using hj
  have hpD : Sharp.expectation p D = 1 / ∑ s, q s := by
    change (∑ s, p s * D s) = _
    simpa [p, dot, mul_comm, Finset.sum_div, mul_div_assoc] using
      congrArg (fun d : ℚ => d / ∑ s, q s) hd
  refine ⟨p, hp, hpD ▸ div_pos (by norm_num) ht, ?_⟩
  intro r hr hrD
  have hrD' : 0 < dot D r := by simpa [Sharp.expectation, dot, mul_comm] using hrD
  have hccr : ∀ i,
      dot (ccRow A b D i) (fun s => r s / dot D r) ≤ ccRhs i := by
    apply (cc_iff A b D _).mpr
    refine ⟨fun s => div_nonneg (hr.1 s) hrD'.le, ?_, ?_⟩
    · intro j
      rw [dot_div, ← Finset.sum_div, hr.2.1, one_div]
      have hj : dot (A j) r ≤ b j := by
        simpa [dot, Sharp.expectation, mul_comm] using hr.2.2 j
      exact (div_le_iff₀ hrD').mpr (by simpa [mul_div_assoc, ne_of_gt hrD'] using hj)
    · rw [dot_div, div_self (ne_of_gt hrD')]
  have hm := hmax (fun s => r s / dot D r) hccr
  rw [dot_div] at hm
  have hpN : Sharp.expectation p N = dot N q / ∑ s, q s := by
    simp [Sharp.expectation, dot, p, mul_comm, mul_div_assoc, Finset.sum_div]
  rw [hpN, hpD]
  have hrN : Sharp.expectation r N = dot N r := by
    simp [Sharp.expectation, dot, mul_comm]
  have hrDd : Sharp.expectation r D = dot D r := by
    simp [Sharp.expectation, dot, mul_comm]
  rw [hrN, hrDd]
  simpa [div_div, ne_of_gt ht] using hm

end SharpHard


open scoped BigOperators

namespace Sharp

private lemma expectation_bounds {Ω : Type*} [Fintype Ω]
    (N D p : Ω → ℚ) (hND : ∀ s, 0 ≤ N s ∧ N s ≤ D s)
    (hp : ∀ s, 0 ≤ p s) :
    0 ≤ expectation p N ∧ expectation p N ≤ expectation p D := by
  exact ⟨Finset.sum_nonneg (fun s _ => mul_nonneg (hp s) (hND s).1),
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hND s).2 (hp s))⟩

private lemma expectation_sub_scaled {Ω : Type*} [Fintype Ω]
    (p N D : Ω → ℚ) (v : ℚ) :
    expectation p (fun s => N s - v * D s) =
      expectation p N - v * expectation p D := by
  classical
  simp only [expectation, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Every nonnull rational moment model has a sparse rational upper attainer
and a matching exact dual certificate, even if feasible conditioning masses
have infimum zero and the observation system is degenerate. -/
theorem upper_endpoint_exists {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (N D : Ω → ℚ)
    (hND : ∀ s, 0 ≤ N s ∧ N s ≤ D s)
    (hne : ∃ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p ∧
      0 < expectation p (fun s => (D s : ℝ))) :
    ∃ u : ℚ, 0 ≤ u ∧ u ≤ 1 ∧ UpperEndpointCertificate A b N D u := by
  classical
  obtain ⟨p, hp, hpD, hmax⟩ :=
    SharpHard.rational_conditional_max_attained A b N D hND hne
  let u : ℚ := expectation p N / expectation p D
  have hpND := expectation_bounds N D p hND hp.1
  have hu0 : 0 ≤ u := div_nonneg hpND.1 hpD.le
  have hu1 : u ≤ 1 := (div_le_iff₀ hpD).mpr (by simpa using hpND.2)
  have hvalid : ∀ r : Ω → ℚ, RationalFeasible A b r →
      expectation r (fun s => N s - u * D s) ≤ 0 := by
    intro r hr
    rw [expectation_sub_scaled]
    have hrND := expectation_bounds N D r hND hr.1
    by_cases hrD : 0 < expectation r D
    · have hv : expectation r N / expectation r D ≤ u := hmax r hr hrD
      have hle := (div_le_iff₀ hrD).mp hv
      linarith
    · have hd : expectation r D = 0 :=
        le_antisymm (le_of_not_gt hrD) (hrND.1.trans hrND.2)
      have hn : expectation r N = 0 :=
        le_antisymm (hd ▸ hrND.2) hrND.1
      simp [hd, hn]
  obtain ⟨z, lam, hdual, hbudget⟩ :=
    rational_bound_complete A b (fun s => N s - u * D s) 0 hvalid
  obtain ⟨q, hq, hsum, hA, hN, hD, hcard⟩ :=
    SharpHard.rational_conditional_sparsification A N D p hp.1 hp.2.1
  have hqfeasible : RationalFeasible A b q := by
    refine ⟨hq, hsum, fun j => ?_⟩
    change (∑ s, q s * A j s) ≤ b j
    rw [hA j]
    exact hp.2.2 j
  have hN' : expectation q N = expectation p N := hN
  have hD' : expectation q D = expectation p D := hD
  refine ⟨u, hu0, hu1, q, z, lam, hqfeasible, hcard, ?_, ?_, hdual, hbudget⟩
  · rw [hD']
    exact hpD
  · rw [hN', hD']
    exact (div_mul_cancel₀ _ (ne_of_gt hpD)).symm

/-- Complementing the numerator turns the exact maximum certificate into a
sparse exact minimum certificate without any extra optimization premise. -/
theorem lower_endpoint_exists {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (N D : Ω → ℚ)
    (hND : ∀ s, 0 ≤ N s ∧ N s ≤ D s)
    (hne : ∃ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p ∧
      0 < expectation p (fun s => (D s : ℝ))) :
    ∃ l : ℚ, 0 ≤ l ∧ l ≤ 1 ∧ LowerEndpointCertificate A b N D l := by
  classical
  have hcomp : ∀ s, 0 ≤ D s - N s ∧ D s - N s ≤ D s := by
    intro s
    constructor <;> linarith [(hND s).1, (hND s).2]
  obtain ⟨v, hv0, hv1, p, z, lam, hp, hsp, hpD, hatt, hd, hb⟩ :=
    upper_endpoint_exists A b (fun s => D s - N s) D hcomp hne
  have hexp : expectation p (fun s => D s - N s) = expectation p D - expectation p N := by
    simp [expectation, mul_sub, Finset.sum_sub_distrib]
  rw [hexp] at hatt
  have hatt' : expectation p N = (1 - v) * expectation p D := by
    linarith
  have hobj : (fun s => D s - N s - v * D s) =
      (fun s => (1 - v) * D s - N s) := by
    funext s
    ring
  rw [hobj] at hd
  exact ⟨1 - v, by linarith, by linarith, p, z, lam, hp, hsp, hpD, hatt', hd, hb⟩

end Sharp


open scoped BigOperators
namespace Sharp

private theorem null_certificate_exists
    {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (D : Ω → ℚ)
    (hne : ∃ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p)
    (hnull : ¬ ∃ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p ∧
      0 < expectation p (fun s => (D s : ℝ))) :
    NullCertificate A b D := by
  classical
  obtain ⟨p, hp⟩ := (real_feasible_iff_rational_feasible A b).mp hne
  have hbound : ∀ p : Ω → ℝ,
      Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p →
      expectation p (fun s => (D s : ℝ)) ≤ (0 : ℚ) := by
    intro p hp
    by_contra! hpos
    exact hnull ⟨p, hp, by simpa using hpos⟩
  obtain ⟨z, lam, hd, hb⟩ := (real_bound_iff_rational_certificate A b D 0).mp hbound
  obtain ⟨q, hqn, hqs, hqA, _, _, hcard⟩ :=
    SharpHard.rational_conditional_sparsification A (fun _ => 0) D p hp.1 hp.2.1
  refine ⟨q, z, lam, ⟨hqn, hqs, ?_⟩, hcard, hd, hb⟩
  intro j
  change (∑ s, q s * A j s) ≤ b j
  rw [hqA j]
  exact hp.2.2 j

private theorem endpoint_order
    {Ω J : Type*} [Fintype Ω] [Fintype J]
    (A : J → Ω → ℚ) (b : J → ℚ) (N D : Ω → ℚ) (l u : ℚ)
    (hl : LowerEndpointCertificate A b N D l)
    (hu : UpperEndpointCertificate A b N D u) : l ≤ u := by
  obtain ⟨_, zl, ll, _, _, _, _, hdl, hbl⟩ := hl
  obtain ⟨p, _, _, hp, _, hpD, hpN, _, _⟩ := hu
  let sound := certificate_soundness Ω J
  obtain ⟨hp', hpD', hpN'⟩ := sound.rationalAttainmentCast A b p N D u hp hpD hpN
  obtain ⟨hdl', hbudget⟩ := sound.rationalDualCast A b
    (fun s => l * D s - N s) zl ll hdl
  have hdual : DualValid (fun j s => (A j s : ℝ))
      (fun s => (l : ℝ) * (D s : ℝ) - (N s : ℝ))
      (zl : ℝ) (fun j => (ll j : ℝ)) := by
    simpa using hdl'
  have hbudget' : dualBudget (fun j => (b j : ℝ)) (zl : ℝ)
      (fun j => (ll j : ℝ)) ≤ 0 := by
    rw [hbudget]
    exact_mod_cast hbl
  have h := sound.conditionalLower (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ))
    (fun s => (p s : ℝ)) (fun s => (N s : ℝ)) (fun s => (D s : ℝ))
    (l : ℝ) (zl : ℝ) (fun j => (ll j : ℝ)) hp' hdual hbudget' hpD'
  rw [hpN'] at h
  exact_mod_cast h

theorem certificate_completeness (Ω J : Type*) [Fintype Ω] [Fintype J] :
    CertificateCompleteness Ω J := by
  classical
  constructor
  · exact real_feasible_iff_rational_feasible
  · exact real_bound_iff_rational_certificate
  · intro A b N D hND
    by_cases hne : ∃ p : Ω → ℝ,
        Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p
    · by_cases hpos : ∃ p : Ω → ℝ,
          Admissible (fun j s => (A j s : ℝ)) (fun j => (b j : ℝ)) p ∧
          0 < expectation p (fun s => (D s : ℝ))
      · obtain ⟨l, hl0, _, hl⟩ := lower_endpoint_exists A b N D hND hpos
        obtain ⟨u, _, hu1, hu⟩ := upper_endpoint_exists A b N D hND hpos
        exact Or.inr (Or.inr ⟨l, u, hl0, endpoint_order A b N D l u hl hu, hu1, hl, hu⟩)
      · exact Or.inr (Or.inl (null_certificate_exists A b D hne hpos))
    · exact Or.inl (infeasible_complete A b hne)

end Sharp
