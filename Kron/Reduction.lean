import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

open scoped BigOperators
open Finset Matrix

namespace Kron

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Nonnegative symmetric conductances of a finite loopless network. -/
structure Conductance (V : Type*) [Fintype V] [DecidableEq V] where
  weights : Matrix V V ℝ
  symm : weights.IsSymm
  nonneg : ∀ i j, 0 ≤ weights i j
  zero_diag : ∀ i, weights i i = 0

def support (N : Conductance V) : SimpleGraph V where
  Adj i j := 0 < N.weights i j
  symm := ⟨by intro i j h; simpa [N.symm.apply i j] using h⟩
  loopless := ⟨by intro i; simp [N.zero_diag i]⟩

def Connected (N : Conductance V) : Prop := (support N).Connected

def laplacian (N : Conductance V) : Matrix V V ℝ :=
  Matrix.diagonal (fun i => ∑ j, N.weights i j) - N.weights

theorem laplacian_apply_ne (N : Conductance V) {i j : V} (hij : i ≠ j) :
    laplacian N i j = -N.weights i j := by
  simp [laplacian, Matrix.diagonal, hij]

theorem laplacian_isSymm (N : Conductance V) : (laplacian N).IsSymm :=
  (Matrix.isSymm_diagonal _).sub N.symm

theorem laplacian_isHermitian (N : Conductance V) : (laplacian N).IsHermitian := by
  exact Matrix.isHermitian_iff_isSymm.mpr (laplacian_isSymm N)

theorem laplacian_mulVec_apply (N : Conductance V) (u : V → ℝ) (i : V) :
    (laplacian N *ᵥ u) i = ∑ j, N.weights i j * (u i - u j) := by
  rw [laplacian, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem laplacian_mulVec_one (N : Conductance V) :
    laplacian N *ᵥ (fun _ => 1) = 0 := by
  ext i
  simp [laplacian_mulVec_apply]

theorem laplacian_energy (N : Conductance V) (x : V → ℝ) :
    x ⬝ᵥ (laplacian N *ᵥ x) =
      (∑ i, ∑ j, N.weights i j * (x i - x j) ^ 2) / 2 := by
  have hswap :
      (∑ i, ∑ j, N.weights i j * x j ^ 2) =
      ∑ i, ∑ j, N.weights i j * x i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1 with i
    congr 1 with j
    rw [N.symm.apply]
  have hexpand :
      (∑ i, ∑ j, N.weights i j * (x i - x j) ^ 2) =
      (∑ i, ∑ j, N.weights i j * x i ^ 2) -
      2 * (∑ i, ∑ j, N.weights i j * x i * x j) +
      ∑ i, ∑ j, N.weights i j * x j ^ 2 := by
    calc
      _ = ∑ i, ∑ j, (N.weights i j * x i ^ 2 -
          2 * (N.weights i j * x i * x j) + N.weights i j * x j ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hq : x ⬝ᵥ (laplacian N *ᵥ x) =
      (∑ i, ∑ j, N.weights i j * x i ^ 2) -
      ∑ i, ∑ j, N.weights i j * x i * x j := by
    simp only [dotProduct, laplacian_mulVec_apply, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ j, (N.weights i j * x i ^ 2 -
          N.weights i j * x i * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib]
  rw [hq, hexpand, hswap]
  ring

theorem laplacian_posSemidef (N : Conductance V) : (laplacian N).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (laplacian_isHermitian N)
  intro x
  rw [star_trivial, laplacian_energy]
  exact div_nonneg (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (N.nonneg i j) (sq_nonneg _)) (by norm_num)

theorem energy_zero_iff_edges (N : Conductance V) (x : V → ℝ) :
    x ⬝ᵥ (laplacian N *ᵥ x) = 0 ↔
      ∀ i j, 0 < N.weights i j → x i = x j := by
  rw [laplacian_energy]
  have hterm (i j : V) : 0 ≤ N.weights i j * (x i - x j) ^ 2 :=
    mul_nonneg (N.nonneg i j) (sq_nonneg _)
  rw [div_eq_zero_iff, or_iff_left (by norm_num : (2 : ℝ) ≠ 0)]
  constructor
  · intro h i j hij
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hterm i j))).mp h i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hterm i j)).mp hi j (Finset.mem_univ j)
    have hs : (x i - x j) ^ 2 = 0 := (mul_eq_zero.mp hj).resolve_left (ne_of_gt hij)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hw : N.weights i j = 0
    · simp [hw]
    · simp [h i j (lt_of_le_of_ne (N.nonneg i j) (Ne.symm hw))]

theorem energy_zero_iff_constant (N : Conductance V) (hN : Connected N) (x : V → ℝ) :
    x ⬝ᵥ (laplacian N *ᵥ x) = 0 ↔ ∀ i j, x i = x j := by
  rw [energy_zero_iff_edges]
  constructor
  · intro h i j
    change (support N).Connected at hN
    obtain ⟨w⟩ := hN i j
    induction w with
    | nil => rfl
    | cons hA _ ih => exact (h _ _ hA).trans ih
  · intro h i j _
    exact h i j

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

theorem dirichlet_posDef [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N) :
    (laplacian N).toBlocks₂₂.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (M := (laplacian N).toBlocks₂₂)
    ((laplacian_isHermitian N).submatrix Sum.inr)
  intro x hx
  let z : B ⊕ I → ℝ := Sum.elim 0 x
  have henergy : z ⬝ᵥ (laplacian N *ᵥ z) =
      x ⬝ᵥ ((laplacian N).toBlocks₂₂ *ᵥ x) := by
    simp [z, dotProduct, Matrix.mulVec, Matrix.toBlocks₂₂, Fintype.sum_sum_type]
  rw [star_trivial]
  apply lt_of_le_of_ne'
  · rw [← henergy]
    simpa using (laplacian_posSemidef N).dotProduct_mulVec_nonneg z
  · intro heq
    have hc := (energy_zero_iff_constant N hN z).mp (henergy.trans heq)
    obtain ⟨b⟩ := ‹Nonempty B›
    apply hx
    funext i
    exact hc (Sum.inr i) (Sum.inl b)

end Kron

open scoped BigOperators
open Matrix

namespace Kron

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

noncomputable def response (M : Matrix (B ⊕ I) (B ⊕ I) ℝ) : Matrix B B ℝ :=
  M.toBlocks₁₁ - M.toBlocks₁₂ * M.toBlocks₂₂⁻¹ * M.toBlocks₂₁

noncomputable def harmonicExtension (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (f : B → ℝ) : B ⊕ I → ℝ :=
  Sum.elim f (-(M.toBlocks₂₂⁻¹ *ᵥ (M.toBlocks₂₁ *ᵥ f)))

def Harmonic (M : Matrix (B ⊕ I) (B ⊕ I) ℝ) (u : B ⊕ I → ℝ) : Prop :=
  ∀ i, (M *ᵥ u) (Sum.inr i) = 0

def energy {V : Type*} [Fintype V] (M : Matrix V V ℝ) (u : V → ℝ) : ℝ :=
  u ⬝ᵥ (M *ᵥ u)

@[simp] theorem harmonicExtension_inl (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (f : B → ℝ) (b : B) : harmonicExtension M f (Sum.inl b) = f b := rfl

theorem block_mulVec (M : Matrix (B ⊕ I) (B ⊕ I) ℝ) (f : B → ℝ) (g : I → ℝ) :
    M *ᵥ Sum.elim f g = Sum.elim
      (M.toBlocks₁₁ *ᵥ f + M.toBlocks₁₂ *ᵥ g)
      (M.toBlocks₂₁ *ᵥ f + M.toBlocks₂₂ *ᵥ g) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  simpa using Matrix.fromBlocks_mulVec M.toBlocks₁₁ M.toBlocks₁₂
    M.toBlocks₂₁ M.toBlocks₂₂ (Sum.elim f g)

theorem harmonicExtension_mulVec (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hD : IsUnit M.toBlocks₂₂) (f : B → ℝ) :
    M *ᵥ harmonicExtension M f = Sum.elim (response M *ᵥ f) 0 := by
  letI := hD.nonempty_invertible.some
  rw [harmonicExtension, block_mulVec]
  congr 1
  · simp [response, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_neg,
      sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.mul_assoc]
  · simp [Matrix.mulVec_neg, Matrix.mulVec_mulVec]

theorem harmonicExtension_harmonic (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hD : IsUnit M.toBlocks₂₂) (f : B → ℝ) : Harmonic M (harmonicExtension M f) := by
  intro i
  simp [harmonicExtension_mulVec M hD f]

theorem harmonic_extension_unique (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hD : IsUnit M.toBlocks₂₂) (f : B → ℝ) (u : B ⊕ I → ℝ)
    (hb : ∀ b, u (Sum.inl b) = f b) (hu : Harmonic M u) :
    u = harmonicExtension M f := by
  have hs : u = Sum.elim f (u ∘ Sum.inr) := by
    funext v
    cases v with
    | inl b => exact hb b
    | inr i => rfl
  have hi : M.toBlocks₂₂ *ᵥ (u ∘ Sum.inr) = -(M.toBlocks₂₁ *ᵥ f) := by
    ext i
    have h := hu i
    rw [hs, block_mulVec] at h
    dsimp only [Sum.elim_inr, Pi.add_apply] at h
    dsimp only [Pi.neg_apply]
    linarith
  letI := hD.nonempty_invertible.some
  have hi' : u ∘ Sum.inr = -(M.toBlocks₂₂⁻¹ *ᵥ (M.toBlocks₂₁ *ᵥ f)) := by
    apply Matrix.mulVec_injective_of_isUnit hD
    simpa [Matrix.mulVec_neg, Matrix.mulVec_mulVec] using hi
  rw [hs, harmonicExtension, hi']

theorem harmonic_energy (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hD : IsUnit M.toBlocks₂₂) (f : B → ℝ) :
    energy M (harmonicExtension M f) = energy (response M) f := by
  simp [energy, harmonicExtension_mulVec M hD f, dotProduct, Fintype.sum_sum_type]

theorem harmonic_pairing (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hD : IsUnit M.toBlocks₂₂) (f g : B → ℝ) :
    harmonicExtension M f ⬝ᵥ (M *ᵥ harmonicExtension M g) =
      f ⬝ᵥ (response M *ᵥ g) := by
  simp [harmonicExtension_mulVec M hD g, dotProduct, Fintype.sum_sum_type]

theorem response_symm (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hM : M.IsSymm) (hD : IsUnit M.toBlocks₂₂) : (response M).IsSymm := by
  have hp (f g : B → ℝ) : f ⬝ᵥ (response M *ᵥ g) = g ⬝ᵥ (response M *ᵥ f) := by
    rw [← harmonic_pairing M hD f g, ← harmonic_pairing M hD g f]
    exact hM.dotProduct_mulVec_comm
  ext i j
  simpa only [single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply] using
    hp (Pi.single j 1) (Pi.single i 1)

theorem harmonic_energy_decomposition (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hM : M.IsSymm) (hD : IsUnit M.toBlocks₂₂) (f : B → ℝ)
    (u : B ⊕ I → ℝ) (hb : ∀ b, u (Sum.inl b) = f b) :
    energy M u = energy M (harmonicExtension M f) +
      energy M (u - harmonicExtension M f) := by
  let h := harmonicExtension M f
  let v := u - h
  have hv : v ⬝ᵥ (M *ᵥ h) = 0 := by
    simp [v, h, harmonicExtension_mulVec M hD f, dotProduct,
      Fintype.sum_sum_type, hb]
  have hv' : h ⬝ᵥ (M *ᵥ v) = 0 := hM.dotProduct_mulVec_comm.trans hv
  have hu : u = h + v := by dsimp [v]; abel
  change energy M u = energy M h + energy M v
  rw [hu]
  simp only [energy, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [hv, hv']
  ring

theorem harmonic_energy_min (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hM : M.PosSemidef) (hD : IsUnit M.toBlocks₂₂) (f : B → ℝ)
    (u : B ⊕ I → ℝ) (hb : ∀ b, u (Sum.inl b) = f b) :
    energy M (harmonicExtension M f) ≤ energy M u := by
  have hsym : M.IsSymm := by simpa [Matrix.IsHermitian, Matrix.IsSymm,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hM.1
  rw [harmonic_energy_decomposition M hsym hD f u hb]
  have hn : 0 ≤ energy M (u - harmonicExtension M f) := by
    simpa [energy] using hM.dotProduct_mulVec_nonneg (u - harmonicExtension M f)
  exact le_add_of_nonneg_right hn

theorem harmonic_energy_eq_iff (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hM : M.PosSemidef) (hD : IsUnit M.toBlocks₂₂) (f : B → ℝ)
    (u : B ⊕ I → ℝ) (hb : ∀ b, u (Sum.inl b) = f b) :
    energy M u = energy M (harmonicExtension M f) ↔ u = harmonicExtension M f := by
  constructor
  · intro heq
    have hsym : M.IsSymm := by simpa [Matrix.IsHermitian, Matrix.IsSymm,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hM.1
    have hd : energy M (u - harmonicExtension M f) = 0 := by
      have := harmonic_energy_decomposition M hsym hD f u hb
      linarith
    have hz : M *ᵥ (u - harmonicExtension M f) = 0 := by
      apply hM.dotProduct_mulVec_zero_iff.mp
      simpa [energy] using hd
    apply harmonic_extension_unique M hD f u hb
    intro i
    have h := congrFun hz (Sum.inr i)
    simp only [Matrix.mulVec_sub, Pi.sub_apply, Pi.zero_apply] at h
    rw [harmonicExtension_mulVec M hD f] at h
    simpa using h
  · rintro rfl
    rfl

theorem response_posSemidef (M : Matrix (B ⊕ I) (B ⊕ I) ℝ)
    (hM : M.PosSemidef) (hD : IsUnit M.toBlocks₂₂) : (response M).PosSemidef := by
  have hsym : M.IsSymm := by simpa [Matrix.IsHermitian, Matrix.IsSymm,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hM.1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
      response_symm M hsym hD
  · intro f
    rw [star_trivial]
    change 0 ≤ energy (response M) f
    rw [← harmonic_energy M hD f]
    simpa [energy] using hM.dotProduct_mulVec_nonneg (harmonicExtension M f)

end Kron

open scoped BigOperators
open Finset Matrix

namespace Kron

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

/-- The discrete maximum principle for a connected conductance network. -/
theorem harmonic_nonneg [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N)
    (u : B ⊕ I → ℝ) (hb : ∀ b, 0 ≤ u (Sum.inl b))
    (hi : ∀ i, (laplacian N *ᵥ u) (Sum.inr i) = 0) :
    ∀ v, 0 ≤ u v := by
  classical
  change (support N).Connected at hN
  obtain ⟨b⟩ := ‹Nonempty B›
  obtain ⟨x, _, hmin⟩ := Finset.univ.exists_min_image u (Finset.univ_nonempty)
  have hmin' : ∀ y, u x ≤ u y := fun y => hmin y (Finset.mem_univ y)
  by_contra! hbad
  obtain ⟨v, hv⟩ := hbad
  have hx : u x < 0 := lt_of_le_of_lt (hmin' v) hv
  have hprop (i j : B ⊕ I) (hix : u i = u x)
      (hij : (support N).Adj i j) : u j = u x := by
    have hih : (laplacian N *ᵥ u) i = 0 := by
      cases i with
      | inl a => exfalso; have := hb a; rw [hix] at this; linarith
      | inr a => exact hi a
    rw [laplacian_mulVec_apply] at hih
    have hterms (k : B ⊕ I) (_ : k ∈ Finset.univ) :
        N.weights i k * (u i - u k) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (N.nonneg i k)
      rw [hix]
      exact sub_nonpos.mpr (hmin' k)
    have heq := (Finset.sum_eq_zero_iff_of_nonpos hterms).mp hih j (Finset.mem_univ j)
    have hweight : N.weights i j ≠ 0 := ne_of_gt hij
    have hu : u i = u j := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hweight)
    exact hu.symm.trans hix
  have hwalk (i j : B ⊕ I) (w : (support N).Walk i j) :
      u i = u x → u j = u x := by
    induction w with
    | nil => exact id
    | cons hA _ ih => intro h; exact ih (hprop _ _ h hA)
  obtain ⟨w⟩ := hN x (Sum.inl b)
  have heq := hwalk x (Sum.inl b) w rfl
  have := hb b
  rw [heq] at this
  linarith

/-- Boundary upper bounds extend to every vertex of a harmonic function. -/
theorem harmonic_le [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N)
    (u : B ⊕ I → ℝ) (a : ℝ) (hb : ∀ b, u (Sum.inl b) ≤ a)
    (hi : ∀ i, (laplacian N *ᵥ u) (Sum.inr i) = 0) :
    ∀ v, u v ≤ a := by
  have hh : ∀ i, (laplacian N *ᵥ (fun v => a - u v)) (Sum.inr i) = 0 := by
    intro i
    rw [laplacian_mulVec_apply]
    have heq : (∑ j, N.weights (Sum.inr i) j *
        ((a - u (Sum.inr i)) - (a - u j))) =
        - ∑ j, N.weights (Sum.inr i) j * (u (Sum.inr i) - u j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq, ← laplacian_mulVec_apply, hi i, neg_zero]
  have h := harmonic_nonneg N hN (fun v => a - u v)
    (fun b => sub_nonneg.mpr (hb b)) hh
  intro v
  exact sub_nonneg.mp (h v)

/-- Boundary lower bounds extend to every vertex of a harmonic function. -/
theorem harmonic_ge [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N)
    (u : B ⊕ I → ℝ) (a : ℝ) (hb : ∀ b, a ≤ u (Sum.inl b))
    (hi : ∀ i, (laplacian N *ᵥ u) (Sum.inr i) = 0) :
    ∀ v, a ≤ u v := by
  have hh : ∀ i, (laplacian N *ᵥ (-u)) (Sum.inr i) = 0 := by
    intro i
    simp only [Matrix.mulVec_neg, Pi.neg_apply, hi i, neg_zero]
  have h := harmonic_le N hN (-u) (-a) (fun b => neg_le_neg (hb b)) hh
  intro v
  exact neg_le_neg_iff.mp (h v)

/-- Harmonic extensions of constant boundary data are constant. -/
theorem harmonic_constant [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N)
    (u : B ⊕ I → ℝ) (a : ℝ) (hb : ∀ b, u (Sum.inl b) = a)
    (hi : ∀ i, (laplacian N *ᵥ u) (Sum.inr i) = 0) :
    u = fun _ => a := by
  have hlo := harmonic_ge N hN u a (fun b => (hb b).ge) hi
  have hup := harmonic_le N hN u a (fun b => (hb b).le) hi
  funext v
  exact le_antisymm (hup v) (hlo v)

/-- A nonnegative harmonic potential with zero potential at a boundary vertex
has nonpositive outward current at that vertex. -/
theorem boundary_flux_nonpos [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N)
    (u : B ⊕ I → ℝ) (hb : ∀ b, 0 ≤ u (Sum.inl b))
    (hi : ∀ i, (laplacian N *ᵥ u) (Sum.inr i) = 0)
    (b : B) (hz : u (Sum.inl b) = 0) :
    (laplacian N *ᵥ u) (Sum.inl b) ≤ 0 := by
  have hnonneg := harmonic_nonneg N hN u hb hi
  rw [laplacian_mulVec_apply, hz]
  apply Finset.sum_nonpos
  intro j _
  exact mul_nonpos_of_nonneg_of_nonpos (N.nonneg _ _) (by simpa using neg_nonpos.mpr (hnonneg j))

/-- Every off-diagonal entry of the boundary response operator is nonpositive. -/
theorem response_offdiag [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N)
    {i j : B} (hij : i ≠ j) : response (laplacian N) i j ≤ 0 := by
  classical
  let f : B → ℝ := Pi.single j 1
  let u := harmonicExtension (laplacian N) f
  have hD : IsUnit (laplacian N).toBlocks₂₂ := (dirichlet_posDef N hN).isUnit
  have hb : ∀ b, 0 ≤ u (Sum.inl b) := by
    intro b
    change 0 ≤ f b
    simp only [f, Pi.single_apply]
    split_ifs <;> norm_num
  have hi : ∀ a, (laplacian N *ᵥ u) (Sum.inr a) = 0 :=
    harmonicExtension_harmonic (laplacian N) hD f
  have hz : u (Sum.inl i) = 0 := by
    change f i = 0
    simp [f, hij, Ne.symm hij]
  have h := boundary_flux_nonpos N hN u hb hi i hz
  dsimp only [u] at h
  rw [harmonicExtension_mulVec (laplacian N) hD f] at h
  simpa [f, Matrix.mulVec_single_one] using h

/-- The boundary response operator annihilates constant potentials. -/
theorem response_mulVec_one [Nonempty B] (N : Conductance (B ⊕ I)) (hN : Connected N) :
    response (laplacian N) *ᵥ (fun _ => 1) = 0 := by
  have hD : IsUnit (laplacian N).toBlocks₂₂ := (dirichlet_posDef N hN).isUnit
  have hh : Harmonic (laplacian N) (fun _ => (1 : ℝ)) := by
    intro i
    simp [laplacian_mulVec_one]
  have hext : harmonicExtension (laplacian N) (fun _ => (1 : ℝ)) = (fun _ => 1) :=
    (harmonic_extension_unique (laplacian N) hD (fun _ => 1) (fun _ => 1)
      (fun _ => rfl) hh).symm
  ext b
  have h := congrFun (harmonicExtension_mulVec (laplacian N) hD (fun _ => 1)) (Sum.inl b)
  rw [hext, laplacian_mulVec_one] at h
  simpa using h.symm

end Kron

open scoped BigOperators
open Finset Matrix

namespace Kron

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Recover conductances from the off-diagonal entries of a Laplacian. -/
noncomputable def conductanceOfLaplacian (M : Matrix V V ℝ) (hM : M.IsSymm)
    (hOff : ∀ i j, i ≠ j → M i j ≤ 0) : Conductance V where
  weights := Matrix.of fun i j => if i = j then 0 else -M i j
  symm := by
    apply Matrix.IsSymm.ext
    intro i j
    change (if j = i then (0 : ℝ) else -M j i) =
      (if i = j then 0 else -M i j)
    by_cases hij : i = j
    · subst j; simp
    · simp only [if_neg hij, if_neg (Ne.symm hij)]
      congr 1
      exact hM.apply i j
  nonneg := by
    intro i j
    change 0 ≤ (if i = j then (0 : ℝ) else -M i j)
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_neg hij]
      exact neg_nonneg.mpr (hOff i j hij)
  zero_diag := by intro i; simp

/-- The zero-row-sum property reconstructs the diagonal entries as well. -/
theorem laplacian_conductanceOfLaplacian (M : Matrix V V ℝ) (hM : M.IsSymm)
    (hOff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hrow : M *ᵥ (fun _ => 1) = 0) :
    laplacian (conductanceOfLaplacian M hM hOff) = M := by
  classical
  have hrs (i : V) : ∑ j, M i j = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hrow i
  have hw (i : V) : (∑ j, if i = j then (0 : ℝ) else -M i j) = M i i := by
    calc
      _ = ∑ j, (-M i j + if i = j then M i i else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j; simp
        · simp [hij]
      _ = -(∑ j, M i j) + M i i := by
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
        simp
      _ = M i i := by rw [hrs]; simp
  ext i j
  simp only [laplacian, conductanceOfLaplacian, Matrix.sub_apply,
    Matrix.diagonal, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    simp [hw]
  · simp [hij]


end Kron

open scoped BigOperators
open Matrix

namespace Kron

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def Conductance.reindex (N : Conductance V) (e : V ≃ W) : Conductance W where
  weights := Matrix.reindex e e N.weights
  symm := N.symm.reindex e
  nonneg i j := N.nonneg (e.symm i) (e.symm j)
  zero_diag i := N.zero_diag (e.symm i)

theorem laplacian_reindex (N : Conductance V) (e : V ≃ W) :
    laplacian (N.reindex e) = Matrix.reindex e e (laplacian N) := by
  unfold laplacian
  rw [Matrix.reindex_apply, Matrix.submatrix_sub]
  apply congrArg₂ (fun A B : Matrix W W ℝ => A - B)
  · rw [Matrix.submatrix_diagonal_equiv]
    apply congrArg Matrix.diagonal
    funext i
    exact e.symm.sum_comp (fun j => N.weights (e.symm i) j)
  · rfl

theorem connected_reindex (N : Conductance V) (hN : Connected N) (e : V ≃ W) :
    Connected (N.reindex e) := by
  let iso : support N ≃g support (N.reindex e) :=
    { toEquiv := e
      map_rel_iff' := by
        intro i j
        simp [support, Conductance.reindex, Matrix.reindex_apply] }
  change (support N).Connected at hN
  exact hN.map iso.toHom e.surjective

theorem connected_of_energy_zero_constant [Nonempty V] (N : Conductance V)
    (h : ∀ x : V → ℝ, x ⬝ᵥ (laplacian N *ᵥ x) = 0 → ∀ i j, x i = x j) :
    Connected N := by
  classical
  let root := Classical.arbitrary V
  have hr : ∀ w, (support N).Reachable root w := by
    intro w
    by_contra hw
    let x : V → ℝ := fun v => if (support N).Reachable root v then 1 else 0
    have hedge : ∀ i j, 0 < N.weights i j → x i = x j := by
      intro i j hij
      have ha : (support N).Adj i j := hij
      by_cases hi : (support N).Reachable root i
      · have hj := hi.trans ha.reachable
        simp [x, hi, hj]
      · have hj : ¬ (support N).Reachable root j :=
          fun hj => hi (hj.trans ha.symm.reachable)
        simp [x, hi, hj]
    have he := (energy_zero_iff_edges N x).mpr hedge
    have hc := h x he root w
    simpa [x, hw] using hc
  change (support N).Connected
  exact ⟨fun i j => (hr i).symm.trans (hr j)⟩

end Kron

open scoped BigOperators
open Matrix

namespace Kron

variable {V W : Type*} [Fintype V] [Fintype W]

theorem reindex_mulVec_transport (M : Matrix V V ℝ) (e : V ≃ W) (u : V → ℝ) :
    Matrix.reindex e e M *ᵥ (u ∘ e.symm) = (M *ᵥ u) ∘ e.symm := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm, Function.comp_def, Equiv.symm_apply_apply]

variable {B J I : Type*} [Fintype B] [Fintype J] [Fintype I]
  [DecidableEq B] [DecidableEq J] [DecidableEq I]

def reassoc (M : Matrix ((B ⊕ J) ⊕ I) ((B ⊕ J) ⊕ I) ℝ) :
    Matrix (B ⊕ (J ⊕ I)) (B ⊕ (J ⊕ I)) ℝ :=
  Matrix.reindex (Equiv.sumAssoc B J I) (Equiv.sumAssoc B J I) M

theorem response_composition
    (M : Matrix ((B ⊕ J) ⊕ I) ((B ⊕ J) ⊕ I) ℝ)
    (hI : IsUnit M.toBlocks₂₂)
    (hJ : IsUnit (response M).toBlocks₂₂)
    (hJI : IsUnit (reassoc M).toBlocks₂₂) :
    response (response M) = response (reassoc M) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro f
  let e := Equiv.sumAssoc B J I
  let g := harmonicExtension (response M) f
  let u := harmonicExtension M g
  let v := u ∘ e.symm
  have hg : response M *ᵥ g = Sum.elim (response (response M) *ᵥ f) 0 :=
    harmonicExtension_mulVec (response M) hJ f
  have hu : M *ᵥ u = Sum.elim (response M *ᵥ g) 0 :=
    harmonicExtension_mulVec M hI g
  have hvflux : reassoc M *ᵥ v = Sum.elim (response (response M) *ᵥ f) 0 := by
    rw [show reassoc M = Matrix.reindex e e M from rfl,
      show v = u ∘ e.symm from rfl, reindex_mulVec_transport, hu, hg]
    funext w
    rcases w with b | (j | i) <;> rfl
  have hvboundary : ∀ b, v (Sum.inl b) = f b := by
    intro b
    simp [v, e, u, g]
  have hvharmonic : Harmonic (reassoc M) v := by
    intro i
    simp [hvflux]
  have hveq : v = harmonicExtension (reassoc M) f :=
    harmonic_extension_unique (reassoc M) hJI f v hvboundary hvharmonic
  have hfinal := harmonicExtension_mulVec (reassoc M) hJI f
  rw [← hveq, hvflux] at hfinal
  funext b
  exact congrFun hfinal (Sum.inl b)

end Kron

open scoped BigOperators
open Matrix

namespace Kron

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

theorem response_zero_energy_iff [Nonempty B] (N : Conductance (B ⊕ I))
    (hN : Connected N) (f : B → ℝ) :
    energy (response (laplacian N)) f = 0 ↔ ∀ i j, f i = f j := by
  have hD := (dirichlet_posDef N hN).isUnit
  rw [← harmonic_energy (laplacian N) hD f]
  change harmonicExtension (laplacian N) f ⬝ᵥ
    (laplacian N *ᵥ harmonicExtension (laplacian N) f) = 0 ↔ _
  rw [energy_zero_iff_constant N hN]
  constructor
  · intro h i j
    exact h (Sum.inl i) (Sum.inl j)
  · intro h
    obtain ⟨b⟩ := ‹Nonempty B›
    have hext := harmonic_constant N hN (harmonicExtension (laplacian N) f)
      (f b) (fun i => h i b) (harmonicExtension_harmonic (laplacian N) hD f)
    intro i j
    rw [hext]

theorem response_kernel [Nonempty B] (N : Conductance (B ⊕ I))
    (hN : Connected N) (f : B → ℝ) :
    response (laplacian N) *ᵥ f = 0 ↔ ∀ i j, f i = f j := by
  have hD := (dirichlet_posDef N hN).isUnit
  have hp := response_posSemidef (laplacian N) (laplacian_posSemidef N) hD
  rw [← hp.dotProduct_mulVec_zero_iff]
  exact response_zero_energy_iff N hN f

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem response_dirichlet_posDef [Nonempty B] (N : Conductance ((B ⊕ J) ⊕ I))
    (hN : Connected N) : (response (laplacian N)).toBlocks₂₂.PosDef := by
  have hD := (dirichlet_posDef N hN).isUnit
  have hp := response_posSemidef (laplacian N) (laplacian_posSemidef N) hD
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hp.1.submatrix Sum.inr)
  intro x hx
  let z : B ⊕ J → ℝ := Sum.elim 0 x
  have he : energy (response (laplacian N)) z =
      x ⬝ᵥ ((response (laplacian N)).toBlocks₂₂ *ᵥ x) := by
    simp [energy, z, dotProduct, Matrix.mulVec, Matrix.toBlocks₂₂,
      Fintype.sum_sum_type]
  rw [star_trivial]
  apply lt_of_le_of_ne'
  · change 0 ≤ x ⬝ᵥ ((response (laplacian N)).toBlocks₂₂ *ᵥ x)
    rw [← he]
    exact hp.dotProduct_mulVec_nonneg z
  · intro hz
    have hc := (response_zero_energy_iff N hN z).mp (he.trans hz)
    obtain ⟨b⟩ := ‹Nonempty B›
    apply hx
    funext j
    exact hc (Sum.inr j) (Sum.inl b)

theorem network_response_composition [Nonempty B]
    (N : Conductance ((B ⊕ J) ⊕ I)) (hN : Connected N) :
    response (response (laplacian N)) = response (reassoc (laplacian N)) := by
  apply response_composition
  · exact (dirichlet_posDef N hN).isUnit
  · exact (response_dirichlet_posDef N hN).isUnit
  · let e := Equiv.sumAssoc B J I
    have h := dirichlet_posDef (N.reindex e) (connected_reindex N hN e)
    rw [laplacian_reindex] at h
    exact h.isUnit

end Kron

open scoped BigOperators
open Finset Matrix

namespace Kron

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

/-- Conductances of the Kron-reduced network. -/
noncomputable def reducedNetwork [Nonempty B] (N : Conductance (B ⊕ I))
    (hN : Connected N) : Conductance B :=
  conductanceOfLaplacian (response (laplacian N))
    (response_symm (laplacian N) (laplacian_isSymm N) (dirichlet_posDef N hN).isUnit)
    (fun _ _ hij => response_offdiag N hN hij)

/-- The reduced conductances recover precisely the Schur response operator. -/
theorem laplacian_reducedNetwork [Nonempty B] (N : Conductance (B ⊕ I))
    (hN : Connected N) : laplacian (reducedNetwork N hN) = response (laplacian N) := by
  unfold reducedNetwork
  exact laplacian_conductanceOfLaplacian _ _ _ (response_mulVec_one N hN)

/-- Kron reduction preserves connectedness of the positive-conductance support. -/
theorem connected_reducedNetwork [Nonempty B] (N : Conductance (B ⊕ I))
    (hN : Connected N) : Connected (reducedNetwork N hN) := by
  apply connected_of_energy_zero_constant (reducedNetwork N hN)
  intro f hf
  apply (response_zero_energy_iff N hN f).mp
  simpa [energy, laplacian_reducedNetwork] using hf

/-- A boundary-equivalent connected weighted network exists after elimination. -/
theorem reducedNetwork_exists [Nonempty B] (N : Conductance (B ⊕ I))
    (hN : Connected N) :
    ∃ Nred : Conductance B, laplacian Nred = response (laplacian N) ∧ Connected Nred := by
  exact ⟨reducedNetwork N hN, laplacian_reducedNetwork N hN, connected_reducedNetwork N hN⟩

end Kron
