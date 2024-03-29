import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Order.Category.BoolAlg
import StoneDuality.HomClosed

open CategoryTheory TopologicalSpace

open scoped Classical
noncomputable section

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
          map_bot, decide_eq_false_iff_not, J, I, T, B]
        rw [Prop.top_eq_true, Prop.bot_eq_false]
        simp only [and_true, not_false_eq_true]
        refine ⟨fun a b ↦ ?_, fun a b ↦ ?_⟩
        all_goals congr
      · intro ⟨⟨⟨h_map_sup, h_map_inf⟩, h_map_top⟩, h_map_bot⟩
        refine ⟨⟨⟨⟨fun a ↦ (x a : Prop), ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
        · simp only [Set.mem_iInter, Set.mem_setOf_eq, J, I, T, B] at h_map_sup
          simp [h_map_sup]
        · simp only [Set.mem_iInter, Set.mem_setOf_eq, J, I, T, B] at h_map_inf
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
      simp only [Bool.decide_or, Bool.decide_coe, J, I, T, B]
      exact (IsClosed_PreserveBinary_T2 i j (Sup.sup) (or) (by continuity))
    · refine isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ ?_))
      simp only [Bool.decide_and, Bool.decide_coe, J, I, T, B]
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
    have hK : IsCompact K := (closedEmbedding_emb A).isClosed_range.isCompact
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
        have : x a = ⊤ := top_unique fun _ ↦ h
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

-- Added to mathlib in #11449 (merged)
-- TODO: refer to the mathlib instance instead
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

-- ## Definition of epsilon
def epsilonObjObj {X : Profinite} (x : X) : BoundedLatticeHom (Clopens X) Prop
where
  toFun := fun K ↦ (x ∈ K)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

lemma preimage_epsilonObjObj_eq {X : Profinite} (a : Clopens X) :
  (epsilonObjObj ⁻¹' {x | x.toLatticeHom a ↔ ⊤}) = a := Set.ext fun _ ↦ iff_true_iff


def epsilonCont {X : Profinite} : ContinuousMap X (Profinite.of
   (BoolAlg.of (Clopens X) ⟶ (BoolAlg.of Prop))) where
     toFun := epsilonObjObj
     continuous_toFun := by
      let A := BoolAlg.of (Clopens X)
      let hB := basis_is_basis A
      rw [TopologicalSpace.IsTopologicalBasis.continuous_iff hB]
      intro U hU
      simp only [basis, BoolAlg.coe_of, BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat,
        eq_iff_iff, Set.mem_range] at hU
      obtain ⟨a, ha⟩ := hU
      simp_rw [← ha]
      have : (epsilonObjObj ⁻¹' {x | x.toLatticeHom a ↔ ⊤}) = _ := Set.ext fun _ ↦ iff_true_iff
      erw [this]
      exact (Clopens.isClopen a).2


lemma coerce_bijective [TopologicalSpace X] [TopologicalSpace Y] (f : ContinuousMap X Y)
    (h : Function.Bijective f.toFun) : Function.Bijective f := by
  constructor; exact h.1; exact h.2


-- TODO move to Order/Hom/Lattice.lean
theorem BoundedLatticeHom.ext_iff {α β : Type*} [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] {f g : BoundedLatticeHom α β } : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff

-- TODO: add to Profinite/Basic
@[simp]
lemma Profinite.coe_of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] : (Profinite.of X).toCompHaus = CompHaus.of X :=
  rfl



theorem coercionhell {X : Profinite} (F G : ↑(Profinite.of (BoolAlg.of
    (Clopens ↑X.toCompHaus.toTop) ⟶ BoolAlg.of Prop)).toCompHaus.toTop)
    (h : F.toFun = G.toFun) : F = G := by
  apply BoundedLatticeHom.ext
  intro a
  exact congrFun h a


-- TODO: A bounded lattice homomorphism of Boolean algebras preserves negation.
-- theorem map_neg_of_bddlathom {A B : BoolAlg} (f : A ⟶ B) (a : A) : f (¬ a) = ¬ f a := by sorry

lemma epsilonSurj {X : Profinite} : Function.Surjective (@epsilonCont X).toFun := by
    intro F
    set Fclp : Set (Clopens X) := (F.toFun)⁻¹' {True} with Fclpeq
    set asSets : Set (Set X) := Clopens.Simps.coe '' Fclp with hClp
    set K : Set X := Set.sInter asSets with Keq
    haveI : Nonempty asSets := by
      use Set.univ
      rw [hClp]
      use ⊤
      constructor
      have : F.toFun ⊤ := by rw [F.map_top']; trivial
      rw [Fclpeq]
      simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of,
        SupHom.toFun_eq_coe, LatticeHom.coe_toSupHom, BoundedLatticeHom.coe_toLatticeHom,
        Set.preimage_singleton_true, Set.mem_setOf_eq, map_top]
      trivial
      trivial

    have hK : IsClosed K := by
      rw[Keq]
      apply isClosed_sInter
      rw [hClp]
      simp
      intro a ha
      exact a.2.1
    have Xiscompact := X.toCompHaus.is_compact.isCompact_univ

    have hSd : DirectedOn (fun (x x_1 : Set X) => x ⊇ x_1) asSets := by sorry
    have hSn : ∀ U ∈ asSets, Set.Nonempty U := by sorry

    have hSc : ∀ U ∈ asSets, IsCompact U := by
      rw [hClp]
      intro U hU
      apply IsClosed.isCompact
      apply IsClopen.isClosed
      let ⟨⟨U_shadow, r⟩, ⟨ hl, hr⟩ ⟩ := hU
      sorry -- TODO just make use of the fact that U_shadow is Clopen and coerces to U somehow...

    have hScl : ∀ U ∈ asSets, IsClosed U := by sorry

    have Kne : K.Nonempty := by
      refine IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hSd hSn hSc hScl
    obtain ⟨x, hx⟩ := Kne
    use x
    simp only [epsilonCont, epsilonObjObj]
    dsimp only [Profinite.coe_of, CompHaus.coe_of]
    apply coercionhell
    simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of]
    ext L

    have inF_implies_xin (U : Clopens X) (h : F.toFun U) : x ∈ U := by
      have : K ⊆ U := by
        rw[Keq, hClp]
        apply Set.sInter_subset_of_mem
        simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of,
          Set.preimage_singleton_true, Set.mem_image, Set.mem_setOf_eq]
        use U
        rw [Fclpeq]
        simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of,
          SupHom.toFun_eq_coe, LatticeHom.coe_toSupHom, BoundedLatticeHom.coe_toLatticeHom,
          Set.preimage_singleton_true, Set.mem_setOf_eq]
        exact ⟨h, by trivial⟩
      exact this hx

    have key (U : Clopens X) : U ∈ Fclp ↔ x ∈ U := by
      rw [Fclpeq]
      simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of,
        Set.preimage_singleton_true, Set.mem_setOf_eq]
      constructor
      · apply inF_implies_xin
      · intro h
        have := inF_implies_xin (Uᶜ)
        sorry


        -- exact this

    constructor
    · intro hxL
      rw [← key, Fclpeq] at hxL
      simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of,
        Set.preimage_singleton_true, Set.mem_setOf_eq] at hxL
      exact hxL
    · intro hFL
      rw [← key]
      rw [Fclpeq]
      simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of,
        Set.preimage_singleton_true, Set.mem_setOf_eq]
      exact hFL

def epsilonObj {X : Profinite} : X ≅ (Profinite.of (BoolAlg.of (Clopens X) ⟶ (BoolAlg.of Prop))) :=
  by
  refine Profinite.isoOfBijective epsilonCont ?_
  apply coerce_bijective
  constructor
  · intro x y
    simp only [epsilonCont]
    rw [BoundedLatticeHom.ext_iff]
    contrapose!
    intro hne
    obtain ⟨K, hK⟩ := exists_isClopen_of_totally_separated hne
    exists ⟨K, hK.1⟩
    simp only [ne_eq, eq_iff_iff, epsilonObjObj, BoundedLatticeHom.coe_mk, LatticeHom.coe_mk,
    SupHom.coe_mk, Clopens.mem_mk]
    push_neg
    left
    exact hK.2
  · exact epsilonSurj


def epsilon : 𝟭 Profinite ≅ Clp.rightOp ⋙ Spec := by
  refine NatIso.ofComponents (fun X ↦ epsilonObj) ?_
  intro X Y f
  ext x
  apply BoundedLatticeHom.ext
  intro a
  rfl

-- ## Definition of eta
def etaObjObjSet {A : BoolAlg} (a : A) :
  Set (Profinite.of (A ⟶ BoolAlg.of Prop)) := { x | x.toFun a = ⊤ }

def IsClopen_etaObjObj {A : BoolAlg} (a : A)  : IsClopen (etaObjObjSet a) := by
  constructor
  · sorry -- TODO: show that eta a is closed
  · sorry -- TOOD: show that eta a is open

def etaObjObj {A : BoolAlg} (a : A) : (BoolAlg.of (Clopens (Profinite.of (A ⟶ BoolAlg.of Prop)))) := by
  refine ⟨etaObjObjSet a, IsClopen_etaObjObj a⟩

-- the following is probably already in library somewhere (we'll need the same for inf, top and bot)
lemma supeqtop (a b : Prop) : a ⊔ b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rw [Prop.top_eq_true]
  simp only [sup_Prop_eq, eq_iff_iff, iff_true]

def etaObj_real (A : BoolAlg) : A ⟶ (BoolAlg.of (Clopens (Profinite.of (A ⟶ BoolAlg.of Prop)))) where
  toFun := etaObjObj
  map_sup' := by
    intros a b
    simp only [BddDistLat.coe_toBddLat, BoolAlg.coe_toBddDistLat, BoolAlg.coe_of, etaObjObj,
     etaObjObjSet]
    ext x
    simp only [Clopens.coe_mk, Clopens.coe_sup, Set.mem_union, Set.mem_setOf_eq]
    rw [x.map_sup']
    apply supeqtop
  -- TODO: fill these (but hopefully can shorten the above proof?)
  map_inf' := sorry
  map_top' := sorry
  map_bot' := sorry

lemma etaObj_real_bijective (A : BoolAlg) : Function.Bijective (etaObj_real A) := sorry

/--
This is used in the blueprint, doesn't seem to be in mathlib. Probably easiest to construct using
`BoolAlg.Iso.mk`.
-/
lemma BoolAlg.iso_of_bijective {A B : BoolAlg} (f : A ⟶ B) (hf : Function.Bijective f) : A ≅ B where
  hom := f
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

def etaObj_real_iso (A : BoolAlg) : A ≅ (BoolAlg.of (Clopens (Profinite.of (A ⟶ BoolAlg.of Prop)))) :=
  BoolAlg.iso_of_bijective (etaObj_real A) (etaObj_real_bijective A)
  -- BoolAlg.Iso.mk (etaObj_real_orderIso A)

def etaObj (A : BoolAlgᵒᵖ) : (Spec ⋙ Clp.rightOp).obj A ≅ (𝟭 BoolAlgᵒᵖ).obj A :=
  (etaObj_real_iso A.unop).op

def eta : Spec ⋙ Clp.rightOp ≅ 𝟭 BoolAlgᵒᵖ := by
  refine NatIso.ofComponents (fun A ↦ etaObj A) ?_
  intro X Y ⟨f⟩
  simp [etaObj]
  change _ = _ ≫ f.op
  simp only [← op_comp]
  congr 1
  simp [etaObj_real_iso]
  unfold BoolAlg.iso_of_bijective
  change (etaObj_real Y.unop) ≫ _ = f ≫ etaObj_real X.unop
  apply BoundedLatticeHom.ext
  intro a
  rfl

section

/-!
This approach might also work, but if the above works, ignore this.
-/

def etaObj_real_orderIso (A : BoolAlg) : A ≃o (BoolAlg.of (Clopens (Profinite.of (A ⟶ BoolAlg.of Prop)))) where
  toFun := etaObjObj
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

def etaObj_real_iso' (A : BoolAlg) : A ≅ (BoolAlg.of (Clopens (Profinite.of (A ⟶ BoolAlg.of Prop)))) :=
  BoolAlg.Iso.mk (etaObj_real_orderIso A)

-- etc.

end

/- If we want to know that `epsilon` and `eta` are actually the unit and counit of
   this equivalence, then we need to prove: -/

/- theorem triangle : ∀ (X : Profinite),
  Clp.rightOp.map (epsilon.hom.app X) ≫ eta.hom.app (Clp.rightOp.obj X) =
    𝟙 (Clp.rightOp.obj X) := by
    intro X
    simp [eta, etaObj, etaObj_real_iso]
    unfold BoolAlg.iso_of_bijective
    change _ ≫ (etaObj_real _).op = _
    rw [← op_comp]
    change _ = (𝟙 _).op
    congr 1
    apply BoundedLatticeHom.ext
    intro a
    let f := Clp.map (epsilon.hom.app X).op
    let g := etaObj_real (BoolAlg.of (Clopens X))
    -- change f (g x) = x
    let y := g a
    erw [id_apply, comp_apply]
    simp
    ext x
    sorry
    -- This is a different triangle law from what's proved in the blueprint

def Equiv : Profinite ≌ BoolAlgᵒᵖ where
  functor := Clp.rightOp
  inverse := Spec
  unitIso := epsilon
  counitIso := eta
  functor_unitIso_comp := sorry
-/
/-
If we don't care whether `epsilon` and `eta` are actually the unit/counit of this adjoint
equivalence, then we don't need to prove the triangle law, and can use the following approach
instead:
-/

def Equiv : Profinite ≌ BoolAlgᵒᵖ := CategoryTheory.Equivalence.mk Clp.rightOp Spec epsilon eta

theorem equiv_functor : Equiv.functor = Clp.rightOp := rfl

theorem equiv_inverse : Equiv.inverse = Spec := rfl


end StoneDuality
