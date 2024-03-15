import Mathlib.Logic.Function.ofArity
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation

set_option autoImplicit false

open scoped PiNotation

-- universe u

section Basic

variable {α β : Type}
variable {I : Type} {ι : I → ℕ}
variable (LHS RHS : (α → β) → Π i, (Fin (ι i) → α) → β)

def SatisfiesAlgCond (f : α → β) := Π i : I, LHS f i = RHS f i

structure RespectingMaps where
  val : α → β
  satisfies : SatisfiesAlgCond LHS RHS val

end Basic

section AddMonoid

inductive I_AddMonoid where
  | algcond_add : I_AddMonoid
  | algcond_zero : I_AddMonoid

abbrev ι_AddMonoid : I_AddMonoid → ℕ
  | .algcond_add => 2
  | .algcond_zero => 0

variable {A B : Type} [AddMonoid A] [AddMonoid B] (f : A → B)

abbrev LHS_AddMonoid : Π i, (Fin (ι_AddMonoid i) → A) → B := by
  rintro ⟨add, zero⟩
  · intro φ
    use f (φ 0 + φ 1)
  · intro _
    use f 0

abbrev RHS_AddMonoid : Π i, (Fin (ι_AddMonoid i) → A) → B := by
  rintro ⟨add, zero⟩
  · intro φ
    use f (φ 0) + f (φ 1)
  · intro _
    use 0

def Satisfies_AlgCondAddMon (g : A →+ B) :
    SatisfiesAlgCond (LHS_AddMonoid) (RHS_AddMonoid) g :=
  fun _ ↦ by simp only [LHS_AddMonoid, map_add, map_zero]

end AddMonoid

section Ring

inductive I_Ring where
  | algcond_add : I_Ring
  | algcond_mul : I_Ring
  | algcond_zero : I_Ring
  | algcond_one : I_Ring

abbrev ι_Ring : I_Ring → ℕ
  | .algcond_add => 2
  | .algcond_mul => 2
  | .algcond_zero => 0
  | .algcond_one => 0

variable {A B : Type} [CommRing A] [CommRing B] (f : A → B)

abbrev LHS_Ring : Π i, (Fin (ι_Ring i) → A) → B := by
  rintro ⟨add, mul, zero, one⟩
  · intro φ
    use f (φ 0 + φ 1)
  · intro φ
    use f (φ 0 * φ 1)
  · intro _
    use f 0
  · intro _
    use f 1

abbrev RHS_Ring : Π i, (Fin (ι_Ring i) → A) → B := by
  rintro ⟨add, mul, zero, one⟩
  · intro φ
    use f (φ 0) + f (φ 1)
  · intro φ
    use f (φ 0) * f (φ 1)
  · intro _
    use 0
  · intro _
    use 1

def SatisfiesAlgCond_Ring (g : A →+* B) :
    SatisfiesAlgCond (LHS_Ring) (RHS_Ring) g :=
  fun _ ↦ by simp only [LHS_Ring, map_add, map_mul, map_zero, map_one, RHS_Ring]

end Ring

section TopologicalSpace

variable (α Y : Type) [TopologicalSpace Y] [T2Space Y]
variable {I : Type} {ι : I → ℕ}-- [Finite I]
variable (LHS RHS : (α → Y) → Π i, (Fin (ι i) → α) → Y)

lemma aux (i : I) : IsClosed {f : α → Y | LHS f i = RHS f i} := by
  classical
  rw [← isOpen_compl_iff]
  rw [isOpen_pi_iff]
  intro f hf
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Function.ne_iff] at hf
  obtain ⟨φ, hφ⟩ := hf
  by_cases H : ι i = 0
  · sorry
  · obtain ⟨k, h_succ⟩ := Nat.exists_eq_succ_of_ne_zero H
    have hk :  k < ι i := sorry
    use Finset.image φ {⟨k, hk⟩}
    simp_all only [ne_eq, Nat.succ_ne_zero, not_false_eq_true, Finset.image_singleton,
      Finset.mem_singleton, forall_eq, Finset.coe_singleton, Set.singleton_pi]



theorem foo : IsClosed {f : α → Y | SatisfiesAlgCond LHS RHS f} := by
  have : {f : α → Y | SatisfiesAlgCond LHS RHS f} =
    Set.iInter (fun i ↦ {f : α → Y | LHS f i = RHS f i}) := by
    ext
    simp only [SatisfiesAlgCond, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  apply isClosed_iInter
  intro i
  apply aux


theorem bar [CompactSpace Y] : CompactSpace {f : α → Y | SatisfiesAlgCond LHS RHS f} := by
  have := @IsClosed.isCompact (α → Y) _ _ _ (foo α Y LHS RHS)
  exact isCompact_iff_compactSpace.mp this --bleah




end TopologicalSpace
