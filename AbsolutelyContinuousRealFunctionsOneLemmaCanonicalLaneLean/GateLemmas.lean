import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean

/-- The gate closure condition for an admissible class in the context of
absolute continuity: either the endpoint condition is satisfied or the
carried remainder is recorded. -/
def gateClosed (A : AdmissibleClass) : Prop :=
  A.endpointSatisfied ∨ A.remainderRecorded

/-- The canonical bridge from admissibility to gate closure. -/
theorem gate_from_admissible_class (A : AdmissibleClass) :
    gateClosed A := by
  exact A.gateWitness

/-- Domain-specific bridge predicate for absolutely continuous real functions. -/
def ACBridgeClosed (A : AdmissibleClass) : Prop :=
  A.endpointSatisfied ∨ A.remainderRecorded

/-- The bridge predicate for absolute continuity coincides with the gate closure. -/
theorem ac_bridge_closed_iff_gate_closed (A : AdmissibleClass) :
    ACBridgeClosed A ↔ gateClosed A := by
  rfl

end AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean
end HautevilleHouse