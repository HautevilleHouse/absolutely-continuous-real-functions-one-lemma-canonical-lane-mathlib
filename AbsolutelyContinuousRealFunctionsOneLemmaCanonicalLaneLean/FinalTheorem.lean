import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean

def ConstrainedAbsoluteContinuityOneLemmaClosure (A : AdmissibleClass) : Prop :=
  bridgeClosed A ∧ gateClosed A

theorem constrained_absolute_continuity_one_lemma_endgame (A : AdmissibleClass) :
    ConstrainedAbsoluteContinuityOneLemmaClosure A := by
  exact And.intro (bridge_from_admissible_class A) (gate_from_admissible_class A)

end AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean
end HautevilleHouse