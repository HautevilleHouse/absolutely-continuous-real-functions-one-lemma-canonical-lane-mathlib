import canonicalLaneMathlib.AdmissibleClass
import Mathlib

noncomputable section

open scoped BigOperators

namespace HautevilleHouse
namespace AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean

/-- The variation of a function `f` over a partition `p`, i.e. the sum of absolute differences over adjacent points. -/
def variation (f : ℝ → ℝ) (p : List ℝ) : ℝ :=
  (p.zip p.tail).map (fun (x, y) => |f y - f x|) |>.sum

lemma variation_nonneg (f : ℝ → ℝ) (p : List ℝ) : 0 ≤ variation f p := by
  unfold variation
  exact List.sum_nonneg (fun u hu => by
    rw [List.mem_map] at hu
    rcases hu with ⟨w, hw, rfl⟩
    rcases w with ⟨x, y⟩
    exact abs_nonneg (f y - f x))

/-- Absolute continuity on the interval `[a,b]`: for every `ε > 0`, there is a `δ > 0` such that every finite partition with total length `< δ` has total variation `< ε`. -/
def AbsoluteContinuityOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (p : List ℝ),
    p.head? = some a →
    p.getLast? = some b →
    p.Pairwise (· < ·) →
    variation (fun x : ℝ => x) p < δ →
    variation f p < ε

/-- Bounded variation on the interval `[a,b]`: there is a uniform bound on the variation over every partition. -/
def HasBoundedVariationOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ M : ℝ, ∀ (p : List ℝ),
    p.head? = some a →
    p.getLast? = some b →
    p.Pairwise (· < ·) →
    variation f p ≤ M

/-- An object in the domain: a real function on a compact interval together with a proof of absolute continuity. -/
structure AbsolutelyContinuousObject where
  f : ℝ → ℝ
  a : ℝ
  b : ℝ
  ac : AbsoluteContinuityOn f a b

/-- Bridge property: the function is uniformly continuous on the interval. -/
def BridgeProperty (o : AbsolutelyContinuousObject) : Prop :=
  UniformContinuousOn o.f (Set.Icc o.a o.b)

/-- Gate property: the function has bounded variation on the interval. -/
def GateProperty (o : AbsolutelyContinuousObject) : Prop :=
  HasBoundedVariationOn o.f o.a o.b

/-- An admissible class bundles an absolutely continuous object with witnesses for the bridge and gate properties. -/
structure AdmissibleClass where
  object : AbsolutelyContinuousObject
  bridge : BridgeProperty object
  gate : GateProperty object

/-- The bridge closure condition for an admissible class. -/
def bridgeClosed (A : AdmissibleClass) : Prop :=
  BridgeProperty A.object

/-- The gate closure condition for an admissible class. -/
def gateClosed (A : AdmissibleClass) : Prop :=
  GateProperty A.object

/-- The constrained theorem closure: both bridge and gate are satisfied. -/
def ConstrainedAbsolutelyContinuousClosure (A : AdmissibleClass) : Prop :=
  bridgeClosed A ∧ gateClosed A

/-- The bridge is always available from an admissible class. -/
theorem bridge_from_admissible_class (A : AdmissibleClass) : bridgeClosed A :=
  A.bridge

/-- The gate is always available from an admissible class. -/
theorem gate_from_admissible_class (A : AdmissibleClass) : gateClosed A :=
  A.gate

/-- The epistemological endgame: every admissible class is a constrained closure. -/
theorem constrained_absolutely_continuous_endgame (A : AdmissibleClass) :
    ConstrainedAbsolutelyContinuousClosure A := by
  exact And.intro (bridge_from_admissible_class A) (gate_from_admissible_class A)

end AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean
end HautevilleHouse