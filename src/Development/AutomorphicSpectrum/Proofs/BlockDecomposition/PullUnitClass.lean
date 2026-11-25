module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CxPairing

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

theorem pull_unit_class {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{0} R) (A' : C' ⥤ CommAlgCat.{0} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  unfold CH.Mor.pull CH.oneH
  generalize_proofs p1 p2
  have h1 : m.hom.f 0 (fun _ => (1 : A.obj _)) = (fun _ => (1 : A'.obj _)) := funext fun _ => h _
  have p1' : (CH.cx (CH.modF A')).d 0 (m.hom.f 0 (fun _ => (1 : A.obj _))) = 0 := by rw [h1]; exact p2
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 (fun _ => (1 : A.obj _)) p1 p1').trans ?_
  congr 1

theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := by
  intro R R' _ _ C C' _ _ Φ Φ' σ m
  refine ⟨?_, pull_unit_class _ _ m.o (fun T => RingHom.map_one (m.ρ T))⟩
  intro i j k h x y
  have hz : ∀ n (c : (CH.cx (CH.modF Φ.A)).X n), c ∈ (CH.cx (CH.modF Φ.A)).Z n →
      m.o.hom.f n c ∈ (CH.cx (CH.modF Φ'.A)).Z n := by
    intro n c hc
    refine LinearMap.mem_ker.mpr ?_
    rw [m.o.hom.comm, LinearMap.mem_ker.mp hc, map_zero]
  have ex := CrystallineSemistableComparison.Auxff.cls_out _ x
  generalize Quotient.out x = z at ex
  subst ex
  have ey := CrystallineSemistableComparison.Auxff.cls_out _ y
  generalize Quotient.out y = w at ey
  subst ey
  obtain ⟨a, ha⟩ := z
  obtain ⟨b, hb⟩ := w
  have cup_cls {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
      {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
      {p q n : ℕ} (h : p + q = n) (a : CH.Cn F₁ p) (b : CH.Cn F₂ q) ha hb :
      ∃ hc, P.cup h ((CH.cx F₁).cls a ha) ((CH.cx F₂).cls b hb) =
        (CH.cx F₃).cls (P.cupC h a b) hc := by
    have ce (x : CH.H F₁ p) (y : CH.H F₂ q) :
        P.cup h x y = (CrystallineSemistableComparison.Auxff.toCx P).cup h x y := by
      unfold CH.Pairing.cup CxPairing.cup
      split_ifs with hz
      · rfl
      · exact absurd ((CrystallineSemistableComparison.Auxff.toCx P).leib h _ _ |>.trans (by
          rw [show CH.d F₁ p (Quotient.out x).1 = 0 from (Quotient.out x).2,
            show CH.d F₂ q (Quotient.out y).1 = 0 from (Quotient.out y).2]; simp)) hz
    exact ⟨CrystallineSemistableComparison.Auxff.closed (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb,
      (ce _ _).trans
        (CrystallineSemistableComparison.P.cxcup_cls (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb _)⟩
  obtain ⟨hc, e⟩ := cup_cls (CH.mulP Φ.A) h a b ha hb
  obtain ⟨hc', e'⟩ := cup_cls (CH.mulP Φ'.A) h _ _ (hz _ _ ha) (hz _ _ hb)
  rw [e]
  unfold CH.Mor.pull
  have ha' := CrystallineSemistableComparison.P.mapH_cls m.o.hom i a ha (hz _ _ ha)
  have hb' := CrystallineSemistableComparison.P.mapH_cls m.o.hom j b hb (hz _ _ hb)
  have hc'2 := CrystallineSemistableComparison.P.mapH_cls m.o.hom k _ hc (hz _ _ hc)
  have hfn : m.o.hom.f k ((CH.mulP Φ.A).cupC h a b) = (CH.mulP Φ'.A).cupC h (m.o.hom.f i a) (m.o.hom.f j b) := by
    funext s
    simp only [CH.Mor.hom, CH.Mor.pullC, CH.mulP, CH.Pairing.cupC, SMor.o, CH.term, CH.modF, LinearMap.coe_mk, AddHom.coe_mk, ModuleCat.hom_ofHom, LinearMap.mk₂_apply]
    exact (map_mul (m.ρ (s.obj (Fin.last k))) _ _).trans (congrArg₂ (· * ·) (m.nat _ _) (m.nat _ _))
  have hcls : (CH.cx (CH.modF Φ'.A)).cls (m.o.hom.f k ((CH.mulP Φ.A).cupC h a b)) (hz _ _ hc) =
      (CH.cx (CH.modF Φ'.A)).cls ((CH.mulP Φ'.A).cupC h (m.o.hom.f i a) (m.o.hom.f j b)) hc' := by
    congr 1
  exact hc'2.trans (hcls.trans (e'.symm.trans (by rw [ha', hb'])))

end GlobalTheory.CompanionTheory.SiteCup
