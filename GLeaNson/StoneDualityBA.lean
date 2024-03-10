import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Order.Category.BoolAlg

open CategoryTheory TopologicalSpace

namespace StoneDuality

@[simps obj]
def Clp : Profiniteᵒᵖ ⥤ BoolAlg where
  obj S := BoolAlg.of (Clopens S.unop)
  map f := by
    refine ⟨⟨⟨fun s ↦ ⟨f.unop ⁻¹' s.1, IsClopen.preimage s.2 f.unop.2⟩, ?_⟩, ?_⟩, ?_, ?_⟩
    all_goals intros; congr

lemma Clp_map_toLatticeHom_toSupHom_toFun_coe {X Y : Profiniteᵒᵖ} (f : X ⟶ Y) (s : Clopens X.unop) :
  (Clp.map f s).carrier = f.unop ⁻¹' s.carrier := by rfl

namespace Spec

open BoolAlg

instance instTopBoolAlg (A : BoolAlg) : TopologicalSpace (A ⟶ of Prop) :=
  induced (fun f ↦ (f : A → Prop)) (Pi.topologicalSpace (t₂ := fun _ ↦ ⊥))

instance (A : BoolAlg) : CompactSpace (A ⟶ of Prop) := sorry

instance (A : BoolAlg) : T2Space (A ⟶ of Prop) := sorry

instance (A : BoolAlg) : TotallySeparatedSpace (A ⟶ of Prop) := sorry

end Spec

open Spec

def Spec : BoolAlgᵒᵖ ⥤ Profinite where
  obj A := Profinite.of (A.unop ⟶ BoolAlg.of Prop)
  map f := ⟨fun y ↦ f.unop ≫ y, sorry⟩


def Equiv : Profinite ≌ BoolAlgᵒᵖ where
  functor := Clp.rightOp
  inverse := Spec
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end StoneDuality
