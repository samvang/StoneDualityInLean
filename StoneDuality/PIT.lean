/-
Copyright (c) 2024 Sam van Gool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool
-/

import Mathlib.Order.PrimeIdeal
import Mathlib.Order.Zorn


/-!
# Prime ideal theorem

In a bounded distributive lattice, if a ≰ b then there exists a prime ideal containing b and not a.
We prove a slightly more general statement: if $F$ is a filter, $I$ is an ideal, and $F$ and $I$
are disjoint, then there exists a prime ideal $J$ containing $I$ with $J$ still disjoint from $F$.
This theorem is a crucial ingredient to Stone duality and relies on Zorn's lemma.

## Tags

ideal, filter, prime, distributive lattice

-/

namespace DistribLattice

variable  [DistribLattice α] [BoundedOrder α]

open Order Ideal Set


variable {F : PFilter α} {I : Ideal α}

/-- A union of a chain of ideals of sets is an ideal. -/
lemma IsIdeal_sUnion_chain (C : Set (Set α)) (hidl : ∀ I ∈ C, IsIdeal I) (hC : IsChain (· ⊆ ·) C) :
  IsIdeal C.sUnion := by sorry


theorem prime_ideal_of_disjoint_filter_ideal
  (F : PFilter α) (I : Ideal α)
  (hFI : Disjoint (F : Set α) (I : Set α)) :
  ∃ J : Ideal α, (IsPrime J) ∧ I ≤ J ∧ Disjoint (F : Set α) J := by

  -- Let S be the set of proper ideals containing I and disjoint from F
  set S : Set (Set α) := { J : Set α | IsIdeal J ∧ ⊤ ∉ J ∧ I ≤ J ∧ Disjoint (F : Set α) J }

  -- Then I is in S...
  have IinS : ↑I ∈ S := by
    refine ⟨Order.Ideal.isIdeal I,
    ⟨fun h ↦ Set.Nonempty.not_disjoint ⟨⊤, ⟨Order.PFilter.top_mem, h⟩⟩ hFI, by trivial⟩⟩

  -- ...and S contains upper bounds for any non-empty chains.
  have chainub : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →  ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intros c hcS hcC hcNe
    use sUnion c
    refine ⟨?_, fun s hs ↦ le_sSup hs⟩
    simp [S]
    refine ⟨IsIdeal_sUnion_chain c (fun _ hJ ↦ (hcS hJ).1) hcC,
      ⟨fun J hJ ↦ (hcS hJ).2.1,
      ⟨?_,
      fun J hJ ↦ (hcS hJ).2.2.2⟩⟩⟩
    · obtain ⟨J, hJ⟩ := hcNe
      exact le_trans (hcS hJ).2.2.1 (le_sSup hJ)

  -- Thus, by Zorn's lemma, we can pick a maximal ideal J in S.
  have zorn := zorn_subset_nonempty S chainub I IinS
  have hJ := Exists.choose_spec zorn
  set Jset := Exists.choose zorn
  obtain ⟨JinS, Jmax⟩ := hJ
  simp only [ge_iff_le, Set.le_eq_subset, S] at JinS
  let J := IsIdeal.toIdeal JinS.1
  use J

  -- By construction, J contains I and is disjoint from F. It remains to prove that J is prime.
  refine ⟨?_, JinS.2.2⟩

  have Jpr : IsProper J := isProper_of_not_mem JinS.2.1
  rw [isPrime_iff_mem_or_mem]
  intros a b

  -- From here on the proof is unfinished and the strategy needs some re-thinking.
  contrapose!
  rintro ⟨ha, hb⟩ hab
  let Ja := J ⊔ Ideal.principal a
  let Jb := J ⊔ Ideal.principal b
  have ainJa : a ∈ Ja := by
    simp [Ja]
    use ⊥
    simp only [bot_mem, ge_iff_le, bot_le, sup_of_le_right, true_and]
    use a
  have binJb : b ∈ Jb := by
    simp [Jb]
    use ⊥
    simp only [bot_mem, ge_iff_le, bot_le, sup_of_le_right, true_and]
    use b
  have Ja_ne_J : Ja.carrier ≠ Jset := ne_of_mem_of_not_mem' ainJa ha
  have J_in_Ja : J ≤ Ja := by simp only [le_sup_left, Ja]
  -- have JanS : ¬ S Ja := by sorry fun SJa ↦ Ja_ne_J (Jmax Ja SJa J_in_Ja)
  have Jb_ne_J : Jb.carrier ≠ Jset := ne_of_mem_of_not_mem' binJb hb
  have J_in_Jb : J ≤ Jb := by simp only [le_sup_left, Jb]
  -- have JbnS : ¬ S Jb := fun SJb ↦ Jb_ne_J (Jmax Jb SJb J_in_Jb)
  have IleJa : I ≤ Ja := by
    refine le_trans ?_ J_in_Ja
    exact JinS.2.2.1
  have IleJb : I ≤ Jb := by
    refine le_trans ?_ J_in_Jb
    exact JinS.2.2.1
  have Japroper : ⊤ ∉ Ja := by
    sorry
    -- intro j hj y hy hjy
  have Jbproper : ⊤ ∉ Jb := by sorry
  have Ja_ndis_F : Set.Nonempty ((Ja : Set α) ∩ F) := by sorry
    -- simp only [le_eq_subset, Order.Ideal.isIdeal Ja, SetLike.mem_coe, Japroper, not_false_eq_true,
    --   SetLike.coe_subset_coe, IleJa, true_and, S] at JanS
    -- rw [Set.nonempty_iff_ne_empty]
    -- exact JanS
  have Jb_ndis_F : Set.Nonempty ((Jb : Set α) ∩ F) := by sorry
    -- simp only [le_eq_subset, Order.Ideal.isIdeal Jb, SetLike.mem_coe, Jbproper, not_false_eq_true,
    --   SetLike.coe_subset_coe, IleJb, true_and, S] at JbnS
    -- rw [Set.nonempty_iff_ne_empty]
    -- exact JbnS
  apply inter_nonempty_iff_exists_right.1 at Ja_ndis_F
  apply inter_nonempty_iff_exists_right.1 at Jb_ndis_F
  obtain ⟨c, ⟨hcF, hcJa⟩⟩ := Ja_ndis_F
  obtain ⟨d, ⟨hdF, hdJb⟩⟩ := Jb_ndis_F
  have c_meet_d_inF := PFilter.inf_mem hcF hdF
  have cd_le_ab : c ⊓ d ≤ a ⊓ b := by sorry
  have : a ⊓ b ∈ F := PFilter.mem_of_le cd_le_ab c_meet_d_inF
  have habJF : a ⊓ b ∈ Jset ∩ F := ⟨hab, this⟩
  sorry
  -- exact (Set.mem_empty_iff_false _).1 habJF



-- below a sketch for a way that one may separate definitions (but not sure yet how it works with Zorn)

-- def separatingSet (hFI : Disjoint (F : Set α) I) : Set α := by
--   set S : Set (Set α) := { J : Set α | IsIdeal J ∧ ⊤ ∉ J ∧ I ≤ J ∧ Disjoint (F : Set α) J }
--   have IS : ↑I ∈ S := by
--     refine ⟨Order.Ideal.isIdeal I,
--     ⟨fun h ↦ Set.Nonempty.not_disjoint ⟨⊤, ⟨Order.PFilter.top_mem, h⟩⟩ hFI, by trivial⟩⟩

--   have chainub : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →  ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
--     intros c hcS hcC hcNe

--     use sUnion c
--     refine ⟨?_, fun s hs ↦ le_sSup hs⟩
--     simp [S]
--     refine ⟨IsIdeal_sUnion_chain c (fun _ hJ ↦ (hcS hJ).1) hcC,
--       ⟨fun J hJ ↦ (hcS hJ).2.1,
--       ⟨?_,
--       fun J hJ ↦ (hcS hJ).2.2.2⟩⟩⟩
--     · obtain ⟨J, hJ⟩ := hcNe
--       exact le_trans (hcS hJ).2.2.1 (le_sSup hJ)

--   have zorn := zorn_subset_nonempty S chainub I IS
--   -- have hJ := Exists.choose_spec zorn
--   use Exists.choose zorn

-- def separatingIdeal (hFI : Disjoint (F : Set α) I) : Ideal α := by sorry

-- def separatingIdeal_isPrime (hFI : Disjoint (F : Set α) I) : IsPrime (separatingIdeal hFI) := by sorry

-- def separator (hFI : Disjoint (F : Set α) I) : PrimePair α :=
--   Order.Ideal.IsPrime.toPrimePair (separatingIdeal_isPrime hFI)

-- variable (hFI : Disjoint (F : Set α) I)


-- theorem separatorI_contains_I : (I : Set α) ⊆ (separator hFI).I := by sorry
-- theorem separatorF_contains_F : (F : Set α) ⊆ (separator hFI).F := by sorry

-- theorem separatorI_isPrime : IsPrime (separator hFI).I := by sorry
-- theorem separatorF_isPrime : Order.PFilter.IsPrime (separator hFI).F := by sorry
