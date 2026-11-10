import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators Topology
open Filter

noncomputable section
namespace IPF

abbrev Table (I J : Type*) := I → J → ℝ

def rowSum {I J : Type*} [Fintype J] (q : Table I J) (i : I) : ℝ := ∑ j, q i j

def colSum {I J : Type*} [Fintype I] (q : Table I J) (j : J) : ℝ := ∑ i, q i j

def Nonnegative {I J : Type*} (q : Table I J) : Prop := ∀ i j, 0 ≤ q i j

/-- Every nonzero entry of p is permitted by the support of q. -/
def Supported {I J : Type*} (p q : Table I J) : Prop := ∀ i j, q i j = 0 → p i j = 0

def Feasible {I J : Type*} [Fintype I] [Fintype J]
    (K : Table I J) (r : I → ℝ) (c : J → ℝ) (p : Table I J) : Prop :=
  Nonnegative p ∧ Supported p K ∧ rowSum p = r ∧ colSum p = c

/-- Feasibility is required, but strict feasibility and positive marginals are not. -/
structure Problem (I J : Type*) [Fintype I] [Fintype J] where
  seed : Table I J
  row : I → ℝ
  col : J → ℝ
  seed_nonnegative : Nonnegative seed
  row_nonnegative : ∀ i, 0 ≤ row i
  col_nonnegative : ∀ j, 0 ≤ col j
  row_total : ∑ i, row i = 1
  col_total : ∑ j, col j = 1
  feasible : ∃ p, Feasible seed row col p

/-- This real-valued formula is used only for nonnegative, support-compatible pairs.
At x = 0 its value is y, including when y = 0. -/
def scalarKL (x y : ℝ) : ℝ := x * Real.log x - x * Real.log y - x + y

def kl {I J : Type*} [Fintype I] [Fintype J] (p q : Table I J) : ℝ :=
  ∑ i, ∑ j, scalarKL (p i j) (q i j)

def rowScale {I J : Type*} [Fintype J] (r : I → ℝ) (q : Table I J) : Table I J :=
  fun i j => (r i / rowSum q i) * q i j

def colScale {I J : Type*} [Fintype I] (c : J → ℝ) (q : Table I J) : Table I J :=
  fun i j => (c j / colSum q j) * q i j

def step {I J : Type*} [Fintype I] [Fintype J]
    (r : I → ℝ) (c : J → ℝ) (q : Table I J) : Table I J :=
  colScale c (rowScale r q)

def iterate {I J : Type*} [Fintype I] [Fintype J]
    (K : Table I J) (r : I → ℝ) (c : J → ℝ) : ℕ → Table I J
  | 0 => K
  | n + 1 => step r c (iterate K r c n)

def IsProjection {I J : Type*} [Fintype I] [Fintype J]
    (D : Problem I J) (p : Table I J) : Prop :=
  Feasible D.seed D.row D.col p ∧
    ∀ q, Feasible D.seed D.row D.col q → kl p D.seed ≤ kl q D.seed

def boundarySeed : Table (Fin 2) (Fin 2) := fun i j => if i = 1 ∧ j = 0 then 0 else 1

def halfMargin : Fin 2 → ℝ := fun _ => 1 / 2

def boundaryIterate (n : ℕ) : Table (Fin 2) (Fin 2) :=
  iterate boundarySeed halfMargin halfMargin n

def boundaryFormula (n : ℕ) : Table (Fin 2) (Fin 2) := fun i j =>
  if j = 0 then (if i = 0 then 1 / 2 else 0)
  else if i = 0 then 1 / (4 * (n : ℝ) + 2)
  else 1 / 2 - 1 / (4 * (n : ℝ) + 2)

end IPF
