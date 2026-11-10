import IPF.Definitions
import Mathlib.Order.ConditionallyCompleteLattice.Finset

open scoped BigOperators Topology
open Filter Set
noncomputable section
namespace IPF

def PositiveVector {A : Type*} (x : A → ℝ) : Prop := ∀ a, 0 < x a

def PositiveTable {I J : Type*} (K : Table I J) : Prop := ∀ i j, 0 < K i j

def matVec {I J : Type*} [Fintype J] (K : Table I J) (x : J → ℝ) : I → ℝ :=
  fun i => ∑ j, K i j * x j

def osc {A : Type*} (h : A → ℝ) : ℝ := sSup (range h) - sInf (range h)

/-- Hilbert projective distance, used only on strictly positive vectors. -/
def hilbert {A : Type*} (x y : A → ℝ) : ℝ := osc (fun a => Real.log (x a) - Real.log (y a))

def crossRatio {I J : Type*} (K : Table I J) : ℝ :=
  sSup (range (fun p : (I × I) × (J × J) =>
    K p.1.1 p.2.1 * K p.1.2 p.2.2 / (K p.1.1 p.2.2 * K p.1.2 p.2.1)))

def contractionRatio {I J : Type*} (K : Table I J) : ℝ :=
  (Real.sqrt (crossRatio K) - 1) / (Real.sqrt (crossRatio K) + 1)

/-- One full update of the column scaling vector for a positive table. -/
def scalingMap {I J : Type*} [Fintype I] [Fintype J]
    (K : Table I J) (r : I → ℝ) (c : J → ℝ) (v : J → ℝ) : J → ℝ :=
  fun j => c j / (∑ i, K i j * (r i / matVec K v i))

def scalingIterate {I J : Type*} [Fintype I] [Fintype J]
    (K : Table I J) (r : I → ℝ) (c : J → ℝ) (v : J → ℝ) : ℕ → (J → ℝ)
  | 0 => v
  | n + 1 => scalingMap K r c (scalingIterate K r c v n)


/-- A row-normalized table reconstructed from a positive column scaling vector. -/
def scaledTable {I J : Type*} [Fintype I] [Fintype J]
    (K : Table I J) (r : I → ℝ) (v : J → ℝ) : Table I J :=
  fun i j => (r i / matVec K v i) * K i j * v j

/-- Computable projective error bound using the first pair of scaling iterates. -/
def stoppingBound {I J : Type*} [Fintype I] [Fintype J]
    (K : Table I J) (r : I → ℝ) (c : J → ℝ) (v : J → ℝ) (n : ℕ) : ℝ :=
  (1 + contractionRatio K) * (contractionRatio K ^ 2) ^ n /
    (1 - contractionRatio K ^ 2) * hilbert (scalingMap K r c v) v

end IPF
