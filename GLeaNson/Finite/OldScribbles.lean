import Mathlib.Order.Birkhoff
import Mathlib.Order.GaloisConnection

open LatticeHom Set
variable (α : Type)
variable [DistribLattice α] [Fintype α] [DecidableEq α] [@DecidablePred α SupIrred]


-- TODO: Make this an abbreviation
def J := {a : α // SupIrred a}

example : PartialOrder {a : α // SupIrred a} := Subtype.partialOrder fun a ↦ SupIrred a

#check OrderIso.lowerSetSupIrred
-- example (f : α → α) : range f = range f := by sorry
-- TODO Perhaps find a way to use `birkhoffFinset` rather than `birkhoffSet`
lemma InImageBirkhoffIff (u : (Set ({a : α // SupIrred a}))) :
  u ∈ range (birkhoffSet α) ↔ IsLowerSet u := by sorry

/- (in this proof blueprint below, just for readability,
I write f for birkhoffSet and J α for {a : α // SupIrred a} )
first suppose u = f a for some a : α.
we show that f a is a lower set.
suppose x ∈ f a and y : J α  with y ≤ x.
by def of f a, x ≤ a.
now y ≤ a by transitivity.
thus,  y ∈ f a as required.

conversely, suppose u is a lower set.
we define a := sup u, and we claim that f(sup u) = u.
let x : J α. We have:
x ∈ f (sup u) ↔ x ≤ sup u (definition of f)
↔ x ≤ y for some y ∈ u (lemma about join-prime in distributive lattices)
↔ x ∈ u (since u is a lower set)
-/

/- Actually, I just realized that the above proof is already in mathlib under `OrderIso.lowerSetSupIrred`. -/


/- There is also
"the other unitor of Birkhoff's representation theorem"
`noncomputable def OrderIso.supIrredLowerSet`
but it only applies to α which is DistribLattice, and this is not general enough.
In order to establish the dual equivalence between finite DL's and finite posets, what we will
need is the following statement, which is strictly more general: -/

variable (β : Type)
variable [PartialOrder β] [Fintype β]
noncomputable def OrderIso.supIrredLowerSet' :
  β ≃o {s : LowerSet β // SupIrred s} := sorry
