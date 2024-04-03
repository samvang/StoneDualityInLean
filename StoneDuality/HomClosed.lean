import Mathlib.Topology.Basic
import Mathlib.Topology.Separation

open TopologicalSpace

/- This file shows that the condition of being a homomorphism is a closed subset of the
    function space in a topological algebra.
    TODO: finish this. -/

--TODO: Use a library result suggested by Anatole

/-- When Y is a T2 space with a continuous binary operation and X is a set with a binary operation,
  the set of functions from X to Y that preserve the operation is closed as a subspace of X → Y. -/
theorem IsClosed_PreserveBinary_T2 [TopologicalSpace Y] [T2Space Y] (x₁ x₂ : X) (oX : X → X → X)
 (oY : Y → Y → Y) (hcts : Continuous (fun (y₁,y₂) ↦ oY y₁ y₂)) :
 IsClosed { f : X → Y | f (oX x₁ x₂) = oY (f x₁) (f x₂)} := by
    let g2 (f : X → Y) := oY (f x₁) (f x₂)
    let g (f : X → Y) := (f (oX x₁ x₂), g2 f)
    have : { f : X → Y | f (oX x₁ x₂) = oY (f x₁) (f x₂)} = g⁻¹' (Set.diagonal Y) := by ext x; simp
    rw [this]
    let k (f : X → Y) := (f x₁, f x₂)
    have kcts : Continuous k := by continuity --or: by simp [continuous_prod_mk, continuous_apply]
    have g2cts : Continuous g2 := Continuous.comp hcts kcts
    exact IsClosed.preimage (by continuity) isClosed_diagonal

/- Proof sketch of what is happening above:
  When x ∈ X, I write π_x for the x-coordinate projection map (X → Y) → Y.
  Note that the set in question can be written as
  g⁻¹ (Δ)
  where Δ is the diagonal in Y × Y, which is closed because Y is T2.
  g is the function (X → Y) → (Y × Y) defined by
  g(f) := (f (oX x₁ x₂), oY (f x₁) (f x₂)).
  And g is continuous because each component is:
  the first component is equal to π_x where x := oX x₁ x₂
  and the second component is the composite oY ∘ ⟨π_(x₁), π_(x₂)⟩.
  [NB: I had to do some hacking with currying oY, sometimes we want it to have type
  Y → Y → Y (like when we apply it below) and sometimes type Y × Y → Y (like when we reason about
  the diagonal as a closed subset of Y × Y). This can probably be improved.]
-/

/-- When Y is a pointed T1 space and X is a pointed set, the set of functions from X to Y that
    preserve the point is closed as a subspace of X → Y. -/
theorem IsClosed_PreserveNullary_T1 [TopologicalSpace Y] [T1Space Y] (x : X) (y : Y) :
  IsClosed { f : X → Y | f x = y } :=
  (IsClosed.preimage (by continuity) (by simp [T1Space.t1 y])
    : IsClosed ((fun (f : X → Y) ↦ f x)⁻¹' {y}))
