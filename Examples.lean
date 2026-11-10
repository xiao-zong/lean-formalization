import Kron
import Sharp
import IPF

/-! Small examples of using the public libraries. -/

-- Every conductance Laplacian annihilates constant potentials.
example {V : Type*} [Fintype V] [DecidableEq V] (N : Kron.Conductance V) :
    Matrix.mulVec (Kron.laplacian N) (fun _ => 1) = 0 :=
  Kron.laplacian_mulVec_one N

-- Exact certificate soundness and completeness are available together.
example (Ω J : Type*) [Fintype Ω] [Fintype J] :
    Sharp.CertificateSoundness Ω J ∧ Sharp.CertificateCompleteness Ω J :=
  ⟨Sharp.certificate_soundness Ω J, Sharp.certificate_completeness Ω J⟩

-- Explore the matrix-scaling interface in your editor.
#check IPF.exists_unique_projection
#check IPF.iterates_converge
#check IPF.projective_contraction_optimal
#check IPF.certified_stopping_bound
#check IPF.boundary_no_geometric_rate
