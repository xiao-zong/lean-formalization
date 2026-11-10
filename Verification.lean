import Kron
import Sharp
import IPF
import Lean.Util.CollectAxioms

/-! Fail the audit if a showcased theorem uses an unexpected transitive axiom. -/

open Lean Elab Command in
run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let results : Array Name := #[
    ``Kron.laplacian_energy,
    ``Kron.dirichlet_posDef,
    ``Kron.harmonicExtension_harmonic,
    ``Kron.harmonic_extension_unique,
    ``Kron.harmonic_energy,
    ``Kron.harmonic_energy_min,
    ``Kron.harmonic_energy_eq_iff,
    ``Kron.response_symm,
    ``Kron.response_posSemidef,
    ``Kron.response_offdiag,
    ``Kron.response_mulVec_one,
    ``Kron.response_kernel,
    ``Kron.reducedNetwork_exists,
    ``Kron.network_response_composition,
    ``Sharp.certificate_soundness,
    ``Sharp.certificate_completeness,
    ``IPF.exists_unique_projection,
    ``IPF.projection_support,
    ``IPF.pythagorean,
    ``IPF.iterates_converge,
    ``IPF.projective_contraction,
    ``IPF.projective_contraction_optimal,
    ``IPF.scaling_contraction,
    ``IPF.certified_stopping_bound,
    ``IPF.boundary_closed_form,
    ``IPF.boundary_polynomial_rate,
    ``IPF.boundary_no_geometric_rate,
    ``IPF.boundary_no_finite_scaling]
  for result in results do
    let axioms ← Lean.collectAxioms result
    let unexpected := axioms.filter fun axiomName => !permitted.contains axiomName
    unless unexpected.isEmpty do
      throwError "{result} uses unexpected axioms: {unexpected}"
    logInfo m!"Checked {result}: {axioms}"
  logInfo m!"Axiom audit passed for {results.size} main theorems."
