import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.Calculus.Deriv.Basic
import canonicalLaneMathlib.AdmissibleClass

open scoped BigOperators

namespace HautevilleHouse
namespace AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean

noncomputable section

def AbsolutelyContinuousOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ → ∀ (x y : ℕ → ℝ) (n : ℕ),
    (∀ i : ℕ, i < n → a ≤ x i ∧ x i ≤ y i ∧ y i ≤ b) →
    (∑ i in Finset.range n, (y i - x i)) < δ →
    (∑ i in Finset.range n, |f (y i) - f (x i)|) < ε

def DerivativeZeroAlmostEverywhere (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.Ioo a b → HasDerivAt f 0 x

structure AdmissibleClass where
  f : ℝ → ℝ
  a : ℝ
  b : ℝ
  a_le_b : a ≤ b
  ac : AbsolutelyContinuousOn f a b
  dz : DerivativeZeroAlmostEverywhere f a b
  one_lemma : AbsolutelyContinuousOn f a b → DerivativeZeroAlmostEverywhere f a b → f a = f b

def bridgeClosed (A : AdmissibleClass) : Prop :=
  A.f A.a = A.f A.b

theorem bridge_from_admissible_class (A : AdmissibleClass) :
    bridgeClosed A := by
  exact A.one_lemma A.ac A.dz

def gateClosed (A : AdmissibleClass) : Prop :=
  A.a ≤ A.b

theorem gate_from_admissible_class (A : AdmissibleClass) :
    gateClosed A := by
  exact A.a_le_b

def carriedRemainder (A : AdmissibleClass) : Prop :=
  A.ac → A.dz → A.f A.a = A.f A.b

theorem carried_remainder_from_admissible_class (A : AdmissibleClass) :
    carriedRemainder A := by
  exact A.one_lemma

def AbsolutelyContinuousOneLemmaClosure (A : AdmissibleClass) : Prop :=
  bridgeClosed A ∧ gateClosed A

theorem absolutely_continuous_one_lemma_endgame (A : AdmissibleClass) :
    AbsolutelyContinuousOneLemmaClosure A := by
  exact And.intro (bridge_from_admissible_class A) (gate_from_admissible_class A)

theorem bridgeClosed_iff_constant_of_admissible (A : AdmissibleClass) :
    bridgeClosed A ↔ A.ac → A.dz → A.f A.a = A.f A.b := by
  constructor
  · intro h _ _
    exact h
  · intro h
    exact h A.ac A.dz

end
end AbsolutelyContinuousRealFunctionsOneLemmaCanonicalLaneLean
end HautevilleHouse