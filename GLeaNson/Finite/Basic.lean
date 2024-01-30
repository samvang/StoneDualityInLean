import Mathlib.Order.Birkhoff

open LatticeHom Set

variable (α : Type)
variable [DistribLattice α] [Fintype α] [DecidableEq α] [@DecidablePred α SupIrred]


-- TODO: Make this an abbreviation
def J := {a : α // SupIrred a}

example : PartialOrder {a : α // SupIrred a} := by exact Subtype.partialOrder fun a ↦ SupIrred a

-- example (f : α → α) : range f = range f := by sorry
-- TODO Perhaps find a way to use `birkhoofFinset` rather than `birkhooSet`
lemma InImageBirkhoffIff (u : (Set ({a : α // SupIrred a}))) :
  u ∈ range (birkhoffSet α) ↔ IsLowerSet u := by sorry
