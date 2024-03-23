import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Order.Category.BoolAlg
import StoneDuality.HomClosed

open CategoryTheory TopologicalSpace

open scoped Classical

namespace StoneDuality

@[simps obj]
def Clp : Profiniteᵒᵖ ⥤ BoolAlg where
  obj S := BoolAlg.of (Clopens S.unop)
  map f := by
    refine ⟨⟨⟨fun s ↦ ⟨f.unop ⁻¹' s.1, IsClopen.preimage s.2 f.unop.2⟩, ?_⟩, ?_⟩, ?_, ?_⟩
    all_goals intros; congr

@[simp] -- the one generated by `simps` was too ugly
lemma Clp_map_toLatticeHom_toSupHom_toFun_coe {X Y : Profiniteᵒᵖ} (f : X ⟶ Y) (s : Clopens X.unop) :
  (Clp.map f s).carrier = f.unop ⁻¹' s.carrier := by rfl

namespace Spec

open BoolAlg

variable (A : BoolAlg)

def basis : Set (Set (A ⟶ of Prop)) :=
  let U : A → Set (A ⟶ of Prop) := fun a ↦ {x | x.1 a = ⊤}
  Set.range U

instance instTopHomBoolAlgProp : TopologicalSpace (A ⟶ of Prop) := generateFrom <| basis A
  --induced (fun f ↦ (f : A → Prop)) (Pi.topologicalSpace (t₂ := fun _ ↦ ⊥))

theorem basis_is_basis : IsTopologicalBasis (basis A) where
  exists_subset_inter := by
    rintro t₁ ⟨a₁, rfl⟩ t₂ ⟨a₂, rfl⟩ x hx
    simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, eq_iff_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq] at hx
    refine ⟨{x | x.1.1.1 (a₁ ⊓ a₂) = ⊤}, ⟨(a₁ ⊓ a₂), rfl⟩, ?_, ?_⟩
    · simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, eq_iff_iff, Set.mem_setOf_eq]
      rw [x.map_inf']
      tauto
    · intro y (hy : y.1.1.1 _ = ⊤)
      rw [y.map_inf'] at hy
      simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, inf_Prop_eq, eq_iff_iff] at hy
      simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, eq_iff_iff, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      tauto
  sUnion_eq := by
    rw [Set.sUnion_eq_univ_iff]
    intro x
    simp only [basis, BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, eq_iff_iff, Set.mem_range,
      exists_exists_eq_and, Set.mem_setOf_eq]
    exact ⟨⊤, eq_iff_iff.mp x.2⟩
  eq_generateFrom := rfl

noncomputable def emb : (A ⟶ of Prop) → (A → Bool) := fun f a ↦ decide (f a)


-- TODO: Check that with
-- attribute [-instance] sierpinskiSpace
-- def discreteProp : TopologicalSpace Prop := sorry
-- the following might replace `emb` still being continuous
def emb' : (A ⟶ of Prop) → (A → Prop) := (·)

instance (A : BoolAlg) : BooleanAlgebra ((forget BoolAlg).obj A) :=
  (inferInstance : BooleanAlgebra A)

instance (A B : BoolAlg) : BoundedLatticeHomClass (A ⟶ B) A B :=
  (inferInstance : BoundedLatticeHomClass (BoundedLatticeHom A B) A B)

instance (A B : BoolAlg) :
    BoundedLatticeHomClass (A ⟶ B) A ((forget BoolAlg).obj B) :=
  (inferInstance : BoundedLatticeHomClass (BoundedLatticeHom A B) A B)

instance (A B : BoolAlg) :
    BoundedLatticeHomClass (A ⟶ B) ((forget BoolAlg).obj A) B :=
  (inferInstance : BoundedLatticeHomClass (BoundedLatticeHom A B) A B)

instance (A B : BoolAlg) :
    BoundedLatticeHomClass (A ⟶ B) ((forget BoolAlg).obj A) ((forget BoolAlg).obj B) :=
  (inferInstance : BoundedLatticeHomClass (BoundedLatticeHom A B) A B)

theorem continuous_emb : Continuous (emb A) := by
  apply continuous_pi
  intro a
  simp only [emb, BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of]
  rw [continuous_discrete_rng]
  rintro ⟨⟩
  · refine (basis_is_basis A).isOpen ⟨aᶜ, ?_⟩
    ext x
    have hc := map_compl' x a
    rw [eq_iff_iff, compl_iff_not] at hc -- why doesn't `simp` work?
    simpa [Prop.top_eq_true] using hc
  · refine (basis_is_basis A).isOpen ⟨a, ?_⟩
    ext x
    simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, Prop.top_eq_true, eq_iff_iff,
      iff_true, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    rfl

theorem inducing_emb : Inducing (emb A) where
  induced := by
    refine eq_of_ge_of_not_gt (le_generateFrom fun s hs ↦ ?_)
        (not_lt_of_le (continuous_emb _).le_induced)
    rw [isOpen_induced_iff]
    obtain ⟨a, rfl⟩ := hs
    refine ⟨Set.pi {a} fun _ ↦ {true}, ?_, ?_⟩
    · exact isOpen_set_pi (Set.finite_singleton _) fun _ _ ↦ trivial
    · ext x
      simp only [Bool.univ_eq, Set.singleton_pi, ↓reduceIte, Set.mem_preimage, Function.eval, emb,
        Set.mem_singleton_iff, decide_eq_true_eq, BddDistLat.coe_toBddLat, coe_toBddDistLat,
        coe_of, Prop.top_eq_true, eq_iff_iff, iff_true, Set.mem_setOf_eq]
      rfl


theorem closedEmbedding_emb : ClosedEmbedding (emb A) := by
  refine closedEmbedding_of_continuous_injective_closed ?_ ?_ ?_
  · exact continuous_emb _
  · intro _ _ h
    ext
    rw [eq_iff_iff]
    simpa [emb] using congrFun h _
  · refine (inducing_emb _).isClosedMap ?_
    let J : A → A → (Set (A → Bool)) := fun a b ↦ {x | x (a ⊔ b) = (x a ∨ x b)}
    let I : A → A → (Set (A → Bool)) := fun a b ↦ {x | x (a ⊓ b) = (x a ∧ x b)}
    let T : Set (A → Bool) := {x | x ⊤ = true}
    let B : Set (A → Bool) := {x | x ⊥ = false}
    have : Set.range (emb A) = (⋂ (a : A) (b : A), J a b) ∩ (⋂ (a : A) (b : A), I a b) ∩ T ∩ B := by
      ext x
      constructor
      · rintro ⟨x, rfl⟩
        simp only [Bool.decide_coe, Set.mem_inter_iff,
          Set.mem_iInter, Set.mem_setOf_eq, emb, map_sup, map_inf, map_top, decide_eq_true_eq,
          map_bot, decide_eq_false_iff_not]
        rw [Prop.top_eq_true, Prop.bot_eq_false]
        simp only [and_true, not_false_eq_true]
        refine ⟨fun a b ↦ ?_, fun a b ↦ ?_⟩
        all_goals congr
      · intro ⟨⟨⟨h_map_sup, h_map_inf⟩, h_map_top⟩, h_map_bot⟩
        refine ⟨⟨⟨⟨fun a ↦ (x a : Prop), ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
        · simp only [Set.mem_iInter, Set.mem_setOf_eq] at h_map_sup
          simp [h_map_sup]
        · simp only [Set.mem_iInter, Set.mem_setOf_eq] at h_map_inf
          simp [h_map_inf]
        · simpa [Prop.top_eq_true] using h_map_top
        · simpa [Prop.bot_eq_false] using h_map_bot
        · ext a
          simp only [emb, BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of]
          have : (decide (x a = true)) = x a := by simp only [Bool.decide_coe]
          rw [← this]
          congr
    rw [this]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · refine isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ ?_))
      simp only [Bool.decide_or, Bool.decide_coe]
      exact (IsClosed_PreserveBinary_T2 i j (Sup.sup) (or) (by continuity))
    · refine isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ ?_))
      simp only [Bool.decide_and, Bool.decide_coe]
      exact (IsClosed_PreserveBinary_T2 i j (Inf.inf) (and) (by continuity))
    · exact (IsClosed_PreserveNullary_T1 ⊤ true)
    · exact (IsClosed_PreserveNullary_T1 ⊥ false)

lemma mem_basis (p : Prop) : {x : A ⟶ of Prop | x a = p} ∈ basis A := by
  cases Classical.dec p with
  | isFalse h =>
    have : p = ⊥ := Mathlib.Meta.NormNum.eq_of_false h fun a ↦ a
    rw [this]
    use aᶜ
    ext x
    simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, Prop.top_eq_true, eq_iff_iff,
      iff_true, Set.mem_setOf_eq]
    rw [eq_iff_iff]
    simp only [Prop.bot_eq_false, iff_false]
    rw [← compl_iff_not, ← map_compl' x a ]
    rfl
  | isTrue h =>
    have : p = ⊤ := propext { mp := fun _ ↦ trivial, mpr := fun _ ↦ h }
    rw [this]
    use a
    ext x
    simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, eq_iff_iff, Set.mem_setOf_eq]
    rw [eq_iff_iff]
    simp only [Prop.top_eq_true, Prop.bot_eq_false, iff_false, iff_true]
    rfl

instance : CompactSpace (A ⟶ of Prop) where
  isCompact_univ := by
    let K := Set.range (emb A)
    have hK : IsCompact K := (closedEmbedding_emb A).closed_range.isCompact
    rw [← Set.preimage_range]
    exact (closedEmbedding_emb A).isCompact_preimage hK

instance : TotallySeparatedSpace (A ⟶ of Prop) where
  isTotallySeparated_univ := by
    intro x _ y _ h
    rw [DFunLike.ne_iff] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨{z | z a = x a}, {z | z a = y a}, ?_⟩
    refine ⟨(basis_is_basis A).isOpen (mem_basis _ _), (basis_is_basis A).isOpen (mem_basis _ _),
      rfl, rfl, ?_, ?_⟩
    · intro z _
      simp
      cases Classical.dec (x a) with
      | isFalse h =>
        have : x a = ⊥ := Mathlib.Meta.NormNum.eq_of_false h fun a ↦ a
        rw [this]
        have hy : y a = ⊤ := by
          rw [Prop.bot_eq_false, eq_iff_iff] at this
          rw [this] at ha
          simp at ha
          rw [eq_iff_iff] at ha
          simp at ha
          rw [Prop.top_eq_true, eq_iff_iff]
          simpa using ha
        rw [hy, eq_iff_iff, eq_iff_iff, Prop.top_eq_true, Prop.bot_eq_false]
        simpa using em' (z a)
      | isTrue h =>
        have : x a = ⊤ := top_unique fun a ↦ h
        rw [this]
        have hy : y a = ⊥ := by
          rw [Prop.top_eq_true, eq_iff_iff] at this
          rw [this] at ha
          simp at ha
          rw [eq_iff_iff] at ha
          simp at ha
          rw [Prop.bot_eq_false, eq_iff_iff]
          simpa using ha
        rw [hy, eq_iff_iff, eq_iff_iff, Prop.top_eq_true, Prop.bot_eq_false]
        simpa using (em' (z a)).symm
    · rw [Set.disjoint_iff]
      intro z ⟨hxz, hyz⟩
      simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, eq_iff_iff, Set.mem_setOf_eq]
        at hxz
      simp only [BddDistLat.coe_toBddLat, coe_toBddDistLat, coe_of, eq_iff_iff, Set.mem_setOf_eq]
        at hyz
      rw [hxz] at hyz
      exact ha hyz

-- Is this really not in mathlib?
instance TotallySeparatedSpace.t2Space (α : Type*) [TopologicalSpace α] [TotallySeparatedSpace α] :
    T2Space α where
  t2 x y h := by
    obtain ⟨u, v, h₁, h₂, h₃, h₄, _, h₅⟩ :=
      TotallySeparatedSpace.isTotallySeparated_univ x (by triv) y (by triv) h
    exact ⟨u, v, h₁, h₂, h₃, h₄, h₅⟩

end Spec

open Spec

theorem Spec_map_cont {X Y : BoolAlg} (f : Y ⟶ X) :
    Continuous fun (y : X ⟶ BoolAlg.of Prop) ↦ f ≫ y := by
  rw [continuous_generateFrom_iff]
  rintro _ ⟨a, rfl⟩
  exact isOpen_generateFrom_of_mem ⟨f a, rfl⟩

@[simps]
def Spec : BoolAlgᵒᵖ ⥤ Profinite where
  obj A := Profinite.of (A.unop ⟶ BoolAlg.of Prop)
  map f := ⟨fun y ↦ f.unop ≫ y, Spec_map_cont f.unop⟩


def Equiv : Profinite ≌ BoolAlgᵒᵖ where
  functor := Clp.rightOp
  inverse := Spec
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end StoneDuality