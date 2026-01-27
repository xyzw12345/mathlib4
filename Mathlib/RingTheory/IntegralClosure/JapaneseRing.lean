/-
Copyright (c) 2026 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.NormalClosure
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink

/-!
# Japanese rings

## References

* [Stacks: Japanese Rings](https://stacks.math.columbia.edu/tag/0BI1)
-/

@[expose] public section

universe u

open Polynomial

variable (R : Type u) [CommRing R]

local notation "K" => FractionRing R

section IntegralClosureTower

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- The canonical map `integralClosure R A → integralClosure S A` in a tower `R → S → A`. -/
noncomputable def integralClosureMapOfTower : integralClosure R A →+* integralClosure S A :=
  { toFun := fun x => ⟨(x : A), (IsIntegral.tower_top (A := S) (B := A) x.2)⟩
    map_one' := by ext; rfl
    map_mul' := by intro x y; ext; rfl
    map_zero' := by ext; rfl
    map_add' := by intro x y; ext; rfl }

@[simp]
theorem integralClosureMapOfTower_coe (x : integralClosure R A) :
    (integralClosureMapOfTower (R := R) (S := S) (A := A) x : A) = x :=
  rfl

-- Prefer having `integralClosure S A` as an `R`-algebra in a tower `R → S → A`.
noncomputable instance (priority := 100) : Algebra R (integralClosure S A) :=
  ((algebraMap S (integralClosure S A)).comp (algebraMap R S)).toAlgebra

noncomputable instance (priority := 100) : IsScalarTower R S (integralClosure S A) :=
  IsScalarTower.of_algebraMap_eq fun _ => by
    ext
    simpa [IsScalarTower.algebraMap_apply] using (IsScalarTower.algebraMap_apply R S A _)

/-!
Reusable constructions for integral closures in a tower.

We keep these as named definitions/lemmas (rather than global instances) to avoid expensive
typeclass search in downstream proofs.
-/

/-- The induced algebra structure on integral closures in a tower `R → S → A`. -/
noncomputable def integralClosureAlgebraOfTower :
    Algebra (integralClosure R A) (integralClosure S A) :=
  (integralClosureMapOfTower (R := R) (S := S) (A := A)).toAlgebra

/-- `R → integralClosure R A → integralClosure S A` is a scalar tower for the induced algebra. -/
theorem isScalarTower_integralClosure_left_ofTower :
    letI : Algebra (integralClosure R A) (integralClosure S A) :=
      integralClosureAlgebraOfTower (R := R) (S := S) (A := A)
    IsScalarTower R (integralClosure R A) (integralClosure S A) := by
  classical
  letI : Algebra (integralClosure R A) (integralClosure S A) :=
    integralClosureAlgebraOfTower (R := R) (S := S) (A := A)
  refine IsScalarTower.of_algebraMap_eq fun _ => ?_
  ext
  simp [RingHom.algebraMap_toAlgebra, integralClosureMapOfTower]

/-- `integralClosure R A → integralClosure S A → A` is a scalar tower for the induced algebra. -/
theorem isScalarTower_integralClosure_right_ofTower :
    letI : Algebra (integralClosure R A) (integralClosure S A) :=
      integralClosureAlgebraOfTower (R := R) (S := S) (A := A)
    IsScalarTower (integralClosure R A) (integralClosure S A) A := by
  classical
  letI : Algebra (integralClosure R A) (integralClosure S A) :=
    integralClosureAlgebraOfTower (R := R) (S := S) (A := A)
  refine IsScalarTower.of_algebraMap_eq fun _ => rfl

end IntegralClosureTower

lemma Localization.Away.isDomain {R : Type*} [CommRing R] [IsDomain R] (r : R) (hr : r ≠ 0) :
    IsDomain (Localization.Away r) := by
  refine IsLocalization.isDomain_localization (R := R) fun x ↦ ?_
  rintro ⟨n, rfl⟩
  simp [hr]

@[mk_iff]
class IsN1Ring [IsDomain R] : Prop where
  integralClosure_finite : Module.Finite R (integralClosure R K)

@[mk_iff]
class IsN2Ring [IsDomain R] : Prop where
  extension_integralClosure_finite' :
    ∀ (L : Type u) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [Module.Finite K L],
    Module.Finite R (integralClosure R L)

-- alias IsJapaneseRing := IsN2Ring

instance [IsDomain R] [inst : IsN2Ring R] : IsN1Ring R where
  integralClosure_finite := inst.extension_integralClosure_finite' K

lemma IsN2Ring.extension_integralClosure_finite [IsDomain R] [inst : IsN2Ring R]
    (L : Type*) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [Module.Finite K L] :
    Module.Finite R (integralClosure R L) := by
  have : Small.{u} L := Module.Finite.small K L
  have : Module.Finite K (Shrink.{u} L) :=
    (Module.Finite.equiv_iff (Shrink.linearEquiv K L)).mpr ‹_›
  let e := AlgEquiv.mapIntegralClosure <| Shrink.algEquiv R L
  have : IsScalarTower R K (Shrink.{u} L) := ⟨fun x y z ↦ (equivShrink L).symm.injective (by simp)⟩
  exact (Module.Finite.equiv_iff e.toLinearEquiv).mp <|
    inst.extension_integralClosure_finite' (Shrink.{u} L)

variable {R} [IsDomain R]

omit [IsDomain R] in
private def nonzeroSubset (s : Set R) : Set R :=
  {r | r ∈ s ∧ r ≠ 0}

omit [IsDomain R] in
private lemma span_nonzeroSubset_eq_top (s : Set R) (hs : Ideal.span s = ⊤) :
    Ideal.span (nonzeroSubset (R := R) s) = ⊤ := by
  apply top_le_iff.mp
  have hle : Ideal.span s ≤ Ideal.span (nonzeroSubset (R := R) s) := by
    refine Ideal.span_le.2 ?_
    intro r hr
    by_cases hzr : r = 0
    · simp [nonzeroSubset, hzr]
    · exact Ideal.subset_span (show r ∈ nonzeroSubset (R := R) s from ⟨hr, hzr⟩)
  simpa [hs] using hle

private lemma isUnit_algebraMap_fractionRing (r : R) (hr : r ≠ 0) :
    IsUnit (algebraMap R (FractionRing R) r) := by
  have : algebraMap R (FractionRing R) r ≠ 0 := by
    intro h0
    exact hr <| (IsFractionRing.injective R (FractionRing R)) (by simpa using h0)
  exact (isUnit_iff_ne_zero).2 this

section AwayFractionRing

variable (R : Type*) [CommRing R]

private noncomputable def awayFractionRingAlgebra [IsDomain R] (r : R) (hr : r ≠ 0) :
    Algebra (Localization.Away r) (FractionRing R) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (S := Localization.Away r)
    (T := FractionRing R)
    (Submonoid.powers r)
    (nonZeroDivisors R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hr)

private lemma awayFractionRing_isScalarTower [IsDomain R] (r : R) (hr : r ≠ 0) :
    letI : Algebra (Localization.Away r) (FractionRing R) := awayFractionRingAlgebra (R := R) r hr
    IsScalarTower R (Localization.Away r) (FractionRing R) := by
  letI : Algebra (Localization.Away r) (FractionRing R) := awayFractionRingAlgebra (R := R) r hr
  have hMN : Submonoid.powers r ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr
  simpa using
    (IsLocalization.localization_isScalarTower_of_submonoid_le (S := Localization.Away r)
      (T := FractionRing R) (Submonoid.powers r) (nonZeroDivisors R) hMN)

private lemma awayFractionRing_isFractionRing [IsDomain R] (r : R) (hr : r ≠ 0) :
    letI : Algebra (Localization.Away r) (FractionRing R) := awayFractionRingAlgebra (R := R) r hr
    IsFractionRing (Localization.Away r) (FractionRing R) := by
  letI : Algebra (Localization.Away r) (FractionRing R) := awayFractionRingAlgebra (R := R) r hr
  haveI : IsScalarTower R (Localization.Away r) (FractionRing R) :=
    awayFractionRing_isScalarTower (R := R) r hr
  haveI : IsDomain (Localization.Away r) := Localization.Away.isDomain r hr
  exact
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (R := R) (M := Submonoid.powers r) (Localization.Away r) (FractionRing R)

private lemma awayFractionRing_isLocalization [IsDomain R] (r : R) (hr : r ≠ 0) :
    IsLocalization
      (Algebra.algebraMapSubmonoid (FractionRing R) (Submonoid.powers r))
      (FractionRing R) := by
  refine IsLocalization.self ?_
  rintro x hx
  rcases hx with ⟨m, hm, rfl⟩
  rcases (Submonoid.mem_powers_iff m r).1 hm with ⟨n, hn⟩
  have hmap :
      algebraMap R (FractionRing R) r ^ n = algebraMap R (FractionRing R) m := by
    simpa [map_pow] using congrArg (algebraMap R (FractionRing R)) hn
  exact hmap ▸ (isUnit_algebraMap_fractionRing (R := R) r hr).pow n

end AwayFractionRing

@[stacks 032G "first part"]
theorem IsN1Ring.of_isLocalization (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] [IsN1Ring R] [IsDomain S] : IsN1Ring S := by
  classical
  -- Let `K` be the fraction field of `R`.
  -- First, construct an `S`-algebra structure on `K` using the universal property of localization.
  have h0 : (0 : R) ∉ M := by
    intro h0
    haveI : Subsingleton S := IsLocalization.subsingleton (S := S) (M := M) h0
    exact (zero_ne_one (α := S)) (Subsingleton.elim 0 1)
  have hM : ∀ y : M, IsUnit ((algebraMap R K) (y : R)) := by
    intro y
    have hy0 : (y : R) ≠ 0 := by
      intro hy0
      exact h0 (by simpa [hy0] using y.2)
    have : (algebraMap R K (y : R)) ≠ 0 := by
      intro hy
      exact hy0 <| (IsFractionRing.injective R K) <| by simpa using hy
    exact (isUnit_iff_ne_zero).2 this
  let g : S →+* K := IsLocalization.lift (M := M) (S := S) (g := (algebraMap R K)) hM
  letI : Algebra S K := g.toAlgebra
  letI : IsScalarTower R S K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      -- `IsLocalization.lift` agrees with `algebraMap` on `R`.
      change algebraMap R K x = g (algebraMap R S x)
      simp [g]
  -- `K` is a localization of `K` at the image of `M`.
  haveI : IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
    refine IsLocalization.self ?_
    rintro x hx
    rcases hx with ⟨m, hm, rfl⟩
    exact hM ⟨m, hm⟩
  -- Use the induced map on integral closures in the tower `R → S → K`.
  letI : Algebra (integralClosure R K) (integralClosure S K) :=
    integralClosureAlgebraOfTower (R := R) (S := S) (A := K)
  letI : IsScalarTower R (integralClosure R K) (integralClosure S K) :=
    (isScalarTower_integralClosure_left_ofTower (R := R) (S := S) (A := K))
  letI : IsScalarTower (integralClosure R K) (integralClosure S K) K :=
    (isScalarTower_integralClosure_right_ofTower (R := R) (S := S) (A := K))
  -- Taking integral closure commutes with localization,
  -- hence we can localize the finiteness result.
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R K) M)
    (integralClosure S K) :=
    IsLocalization.integralClosure (R := R) (S := K) (Rf := S) (Sf := K) M
  have hfinK : Module.Finite S (integralClosure S K) :=
    (by
      letI : Module.Finite R (integralClosure R K) := (IsN1Ring.integralClosure_finite (R := R))
      exact Module.Finite.of_isLocalization R (integralClosure R K) (M := M))
  -- Replace `K` by the fraction field of `S`.
  haveI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (R := R) (M := M) S K
  let e : integralClosure S (FractionRing S) ≃ₐ[S] integralClosure S K :=
    AlgEquiv.mapIntegralClosure (FractionRing.algEquiv (A := S) K)
  refine ⟨(Module.Finite.equiv_iff e.toLinearEquiv).mpr hfinK⟩

@[stacks 032G "second part"]
theorem IsN2Ring.of_isLocalization (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] [IsN2Ring R] [IsDomain S] : IsN2Ring S := by
  classical
  -- Let `K` be the fraction field of `R`. We first construct an `S`-algebra structure on `K`.
  have h0 : (0 : R) ∉ M := by
    intro h0
    haveI : Subsingleton S := IsLocalization.subsingleton (S := S) (M := M) h0
    exact (zero_ne_one (α := S)) (Subsingleton.elim 0 1)
  have hM : ∀ y : M, IsUnit ((algebraMap R K) (y : R)) := by
    intro y
    have hy0 : (y : R) ≠ 0 := by
      intro hy0
      exact h0 (by simpa [hy0] using y.2)
    have : (algebraMap R K (y : R)) ≠ 0 := by
      intro hy
      exact hy0 <| (IsFractionRing.injective R K) <| by simpa using hy
    exact (isUnit_iff_ne_zero).2 this
  let g : S →+* FractionRing R :=
    IsLocalization.lift (M := M) (S := S) (g := (algebraMap R (FractionRing R))) hM
  letI : Algebra S (FractionRing R) := g.toAlgebra
  letI : IsScalarTower R S (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap R (FractionRing R) x = g (algebraMap R S x)
      simp [g]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (FractionRing R) M) (FractionRing R) := by
    refine IsLocalization.self ?_
    rintro x hx
    rcases hx with ⟨m, hm, rfl⟩
    exact hM ⟨m, hm⟩
  haveI : IsFractionRing S (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (R := R) (M := M) S (FractionRing R)
  -- Now let `L` be a finite extension of the fraction field of `S`.
  refine ⟨?_⟩
  intro L _ _ _ _ _
  classical
  -- Use the composed algebra structure `R → S → L`.
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S L :=
    IsScalarTower.of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  -- View `L` as a `K`-algebra via the canonical equivalence `FractionRing S ≃ₐ[S] K`.
  let e : FractionRing S ≃ₐ[S] FractionRing R := FractionRing.algEquiv (A := S) (FractionRing R)
  letI : Algebra (FractionRing R) L :=
    ((algebraMap (FractionRing S) L).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower R (FractionRing R) L :=
    IsScalarTower.of_algebraMap_eq fun x => by
      -- Reduce to the corresponding statement over `S` using the tower `R → S → L`.
      change algebraMap R L x =
        (algebraMap (FractionRing S) L) (e.symm (algebraMap R (FractionRing R) x))
      -- Rewrite `algebraMap R L` through `S` and `FractionRing S`.
      rw [IsScalarTower.algebraMap_apply R S L]
      rw [IsScalarTower.algebraMap_apply S (FractionRing S) L]
      -- Use that `e.symm` commutes with `S`-algebra maps, and `algebraMap R K` factors through `S`.
      have :
          e.symm (algebraMap R (FractionRing R) x) =
            algebraMap S (FractionRing S) (algebraMap R S x) := by
        -- `algebraMap R (FractionRing R) = algebraMap S (FractionRing R) ∘ algebraMap R S`
        have hx :
            algebraMap R (FractionRing R) x =
              algebraMap S (FractionRing R) (algebraMap R S x) := by
          simp [IsScalarTower.algebraMap_apply R S (FractionRing R)]
        -- apply `e.symm` and use commutativity with `S`
        simp [hx]
      simp [this]
  haveI : Module.Finite (FractionRing R) L := by
    -- Transfer finiteness along the isomorphism `FractionRing S ≃+* K`.
    refine
      Module.Finite.of_equiv_equiv (A₁ := FractionRing S) (B₁ := L) (A₂ := FractionRing R)
        (B₂ := L)
      e.toRingEquiv (RingEquiv.refl L) ?_
    ext x
    simp [RingHom.algebraMap_toAlgebra]
    simpa using e.toRingEquiv.symm_apply_apply x
  -- Apply the `N-2` condition on `R` to get finiteness of `integralClosure R L`.
  have hfinR : Module.Finite R (integralClosure R L) :=
    IsN2Ring.extension_integralClosure_finite (R := R) (L := L)
  -- Localize the finiteness statement to get `Module.Finite S (integralClosure S L)`.
  have hM_L : ∀ y : M, IsUnit ((algebraMap R L) (y : R)) := by
    intro y
    -- Elements of `M` map to units in `S`, hence to units in `L`.
    have : IsUnit ((algebraMap R S) (y : R)) := IsLocalization.map_units (S := S) y
    have : IsUnit ((algebraMap S L) ((algebraMap R S) (y : R))) := this.map (algebraMap S L)
    simpa [IsScalarTower.algebraMap_apply R S L] using this
  haveI : IsLocalization (Algebra.algebraMapSubmonoid L M) L := by
    refine IsLocalization.self ?_
    rintro x hx
    rcases hx with ⟨m, hm, rfl⟩
    exact hM_L ⟨m, hm⟩
  -- Define the canonical map between integral closures induced by `R ⊂ S`.
  let φ : integralClosure R L →+* integralClosure S L :=
    { toFun := fun x => ⟨(x : L), (IsIntegral.tower_top (A := S) (B := L) x.2)⟩
      map_one' := by ext; rfl
      map_mul' := by intro x y; ext; rfl
      map_zero' := by ext; rfl
      map_add' := by intro x y; ext; rfl }
  letI : Algebra (integralClosure R L) (integralClosure S L) := φ.toAlgebra
  letI : IsScalarTower R (integralClosure R L) (integralClosure S L) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      ext; rfl
  letI : IsScalarTower (integralClosure R L) (integralClosure S L) L :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rfl
  haveI :
      IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) M) (integralClosure S L) :=
    IsLocalization.integralClosure (R := R) (S := L) (Rf := S) (Sf := L) M
  letI : Module.Finite R (integralClosure R L) := hfinR
  exact Module.Finite.of_isLocalization R (integralClosure R L) (M := M)

@[stacks 032H "first part"]
theorem IsN1Ring.of_localized_span (s : Set R) (spn : Ideal.span s = ⊤)
    (h : ∀ (r : s) (_ : r.1 ≠ 0), @IsN1Ring (Localization.Away r.1) _
    (Localization.Away.isDomain r.1 ‹_›)) : IsN1Ring R := by
  classical
  -- Remove `0` from the spanning set.
  let s0 : Set R := nonzeroSubset (R := R) s
  have spn0 : Ideal.span s0 = ⊤ := span_nonzeroSubset_eq_top (R := R) s spn
  -- Local data for the localization at `r`.
  let Rₚ : s0 → Type u := fun r => Localization.Away r.1
  -- Use the `Algebra`-based scalar action on localizations.
  letI : SMul R (FractionRing R) := (inferInstance : Algebra R (FractionRing R)).toSMul
  letI (r : s0) : SMul R (Rₚ r) := (inferInstance : Algebra R (Rₚ r)).toSMul
  letI (r : s0) : Algebra (Rₚ r) (FractionRing R) :=
    awayFractionRingAlgebra (R := R) r.1 r.2.2
  haveI (r : s0) : IsScalarTower R (Rₚ r) (FractionRing R) := by
    simpa [Rₚ] using awayFractionRing_isScalarTower (R := R) r.1 r.2.2
  haveI (r : s0) : IsDomain (Rₚ r) := Localization.Away.isDomain r.1 r.2.2
  haveI (r : s0) : IsFractionRing (Rₚ r) (FractionRing R) := by
    simpa [Rₚ] using awayFractionRing_isFractionRing (R := R) r.1 r.2.2
  haveI (r : s0) :
      IsLocalization (Algebra.algebraMapSubmonoid (FractionRing R) (Submonoid.powers r.1))
        (FractionRing R) := by
    simpa using awayFractionRing_isLocalization (R := R) r.1 r.2.2
  -- The integral closure of `R` in `Frac(R)` is finite if it is finite after localizing at `s0`.
  refine ⟨?_⟩
  letI (r : s0) :
      Algebra (integralClosure R (FractionRing R)) (integralClosure (Rₚ r) (FractionRing R)) :=
    integralClosureAlgebraOfTower (R := R) (S := Rₚ r) (A := FractionRing R)
  letI (r : s0) :
      IsScalarTower R (integralClosure R (FractionRing R))
        (integralClosure (Rₚ r) (FractionRing R)) :=
    isScalarTower_integralClosure_left_ofTower (R := R) (S := Rₚ r) (A := FractionRing R)
  letI (r : s0) :
      IsScalarTower (integralClosure R (FractionRing R))
        (integralClosure (Rₚ r) (FractionRing R)) (FractionRing R) :=
    isScalarTower_integralClosure_right_ofTower (R := R) (S := Rₚ r) (A := FractionRing R)
  haveI (r : s0) :
      IsLocalization
        (Algebra.algebraMapSubmonoid (integralClosure R (FractionRing R)) (Submonoid.powers r.1))
        (integralClosure (Rₚ r) (FractionRing R)) :=
    IsLocalization.integralClosure
      (R := R)
      (S := FractionRing R)
      (Rf := Rₚ r)
      (Sf := FractionRing R)
      (Submonoid.powers r.1)
  let f : ∀ r : s0,
      (integralClosure R (FractionRing R)) →ₗ[R] (integralClosure (Rₚ r) (FractionRing R)) :=
    fun r =>
      (IsScalarTower.toAlgHom R (integralClosure R (FractionRing R))
        (integralClosure (Rₚ r) (FractionRing R))).toLinearMap
  have H : ∀ r : s0, Module.Finite (Rₚ r) (integralClosure (Rₚ r) (FractionRing R)) := by
    intro r
    haveI : IsN1Ring (Rₚ r) := h ⟨r.1, r.2.1⟩ r.2.2
    let e :
        integralClosure (Rₚ r) (FractionRing (Rₚ r)) ≃ₐ[Rₚ r]
          integralClosure (Rₚ r) (FractionRing R) :=
      AlgEquiv.mapIntegralClosure (FractionRing.algEquiv (A := Rₚ r) (FractionRing R))
    exact (Module.Finite.equiv_iff e.toLinearEquiv).1 (IsN1Ring.integralClosure_finite (R := Rₚ r))
  exact
    Module.Finite.of_localizationSpan' (R := R) (M := (integralClosure R (FractionRing R)))
      (t := s0) spn0 (Rₚ := Rₚ) (Mₚ := fun r => integralClosure (Rₚ r) (FractionRing R))
      (f := f) (H := H)

@[stacks 032H "second part"]
theorem IsN2Ring.of_localized_span (s : Set R) (spn : Ideal.span s = ⊤)
    (h : ∀ (r : s) (_ : r.1 ≠ 0), @IsN2Ring (Localization.Away r.1) _
    (Localization.Away.isDomain r.1 ‹_›)) : IsN2Ring R := by
  classical
  refine ⟨?_⟩
  intro L _ _ _ _ _
  classical
  -- Remove `0` from the spanning set.
  let s0 : Set R := nonzeroSubset (R := R) s
  have spn0 : Ideal.span s0 = ⊤ := span_nonzeroSubset_eq_top (R := R) s spn
  -- Local data for the localization at `r`.
  let Rₚ : s0 → Type u := fun r => Localization.Away r.1
  -- Use the `Algebra`-based scalar action on localizations.
  letI : SMul R (FractionRing R) := (inferInstance : Algebra R (FractionRing R)).toSMul
  letI (r : s0) : SMul R (Rₚ r) := (inferInstance : Algebra R (Rₚ r)).toSMul
  letI (r : s0) : Algebra (Rₚ r) (FractionRing R) :=
    awayFractionRingAlgebra (R := R) r.1 r.2.2
  haveI (r : s0) : IsScalarTower R (Rₚ r) (FractionRing R) := by
    simpa [Rₚ] using awayFractionRing_isScalarTower (R := R) r.1 r.2.2
  haveI (r : s0) : IsDomain (Rₚ r) := Localization.Away.isDomain r.1 r.2.2
  haveI (r : s0) : IsFractionRing (Rₚ r) (FractionRing R) := by
    simpa [Rₚ] using awayFractionRing_isFractionRing (R := R) r.1 r.2.2
  haveI (r : s0) :
      IsLocalization (Algebra.algebraMapSubmonoid (FractionRing R) (Submonoid.powers r.1))
        (FractionRing R) := by
    simpa using awayFractionRing_isLocalization (R := R) r.1 r.2.2
  -- Build the algebra structure `Rᵣ → L` through `Frac(R) → L`.
  letI (r : s0) : Algebra (Rₚ r) L :=
    ((algebraMap (FractionRing R) L).comp (algebraMap (Rₚ r) (FractionRing R))).toAlgebra
  haveI (r : s0) : IsScalarTower (Rₚ r) (FractionRing R) L :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  haveI (r : s0) : IsScalarTower R (Rₚ r) L :=
    IsScalarTower.of_algebraMap_eq fun x => by
      -- Compare the two ways of mapping `R` into `L` via `Frac(R)`.
      rw [IsScalarTower.algebraMap_apply R (FractionRing R) L x]
      simp [RingHom.algebraMap_toAlgebra]
  -- Now use the localization-span lemma for `Module.Finite`.
  haveI (r : s0) :
      IsLocalization (Algebra.algebraMapSubmonoid L (Submonoid.powers r.1)) L := by
    refine IsLocalization.self ?_
    rintro x hx
    rcases hx with ⟨m, hm, rfl⟩
    rcases (Submonoid.mem_powers_iff m r.1).1 hm with ⟨n, hn⟩
    change IsUnit ((algebraMap R L) m)
    have hmap : (algebraMap R L) r.1 ^ n = (algebraMap R L) m := by
      simpa [map_pow] using congrArg (algebraMap R L) hn
    -- `r` maps to a unit in `L` since it maps to a nonzero element.
    have hr0 : algebraMap R L r.1 ≠ 0 := by
      intro hr0
      have : algebraMap R (FractionRing R) r.1 = 0 := by
        apply (algebraMap (FractionRing R) L).injective
        simpa [IsScalarTower.algebraMap_apply R (FractionRing R) L] using hr0
      exact r.2.2 <| (IsFractionRing.injective R (FractionRing R)) (by simpa using this)
    exact hmap ▸ ((isUnit_iff_ne_zero).2 hr0).pow n
  letI (r : s0) : Algebra (integralClosure R L) (integralClosure (Rₚ r) L) :=
    integralClosureAlgebraOfTower (R := R) (S := Rₚ r) (A := L)
  letI (r : s0) : IsScalarTower R (integralClosure R L) (integralClosure (Rₚ r) L) :=
    isScalarTower_integralClosure_left_ofTower (R := R) (S := Rₚ r) (A := L)
  letI (r : s0) : IsScalarTower (integralClosure R L) (integralClosure (Rₚ r) L) L :=
    isScalarTower_integralClosure_right_ofTower (R := R) (S := Rₚ r) (A := L)
  haveI (r : s0) :
      IsLocalization
        (Algebra.algebraMapSubmonoid (integralClosure R L) (Submonoid.powers r.1))
        (integralClosure (Rₚ r) L) :=
    IsLocalization.integralClosure (R := R) (S := L) (Rf := Rₚ r) (Sf := L)
      (Submonoid.powers r.1)
  let f : ∀ r : s0, (integralClosure R L) →ₗ[R] (integralClosure (Rₚ r) L) :=
    fun r =>
      (IsScalarTower.toAlgHom R (integralClosure R L) (integralClosure (Rₚ r) L)).toLinearMap
  have H : ∀ r : s0, Module.Finite (Rₚ r) (integralClosure (Rₚ r) L) := by
    intro r
    haveI : IsN2Ring (Rₚ r) := h ⟨r.1, r.2.1⟩ r.2.2
    -- Transfer finiteness along the identification of fraction fields.
    let e : FractionRing (Rₚ r) ≃ₐ[Rₚ r] FractionRing R :=
      FractionRing.algEquiv (A := Rₚ r) (FractionRing R)
    -- View `L` as an algebra over `Frac(Rᵣ)` through the equivalence.
    letI : Algebra (FractionRing (Rₚ r)) L :=
      ((algebraMap (FractionRing R) L).comp e.toRingEquiv.toRingHom).toAlgebra
    haveI : IsScalarTower (Rₚ r) (FractionRing (Rₚ r)) L :=
      IsScalarTower.of_algebraMap_eq fun x => by
        -- Rewrite the two `algebraMap`s coming from the `toAlgebra` instances
        -- (but keep `algebraMap (Rₚ r) (FractionRing (Rₚ r))` untouched).
        have h₁ :
            algebraMap (Rₚ r) L =
              (algebraMap (FractionRing R) L).comp (algebraMap (Rₚ r) (FractionRing R)) := by
          simpa using
            (RingHom.algebraMap_toAlgebra
              ((algebraMap (FractionRing R) L).comp (algebraMap (Rₚ r) (FractionRing R))))
        have h₂ :
            algebraMap (FractionRing (Rₚ r)) L =
              (algebraMap (FractionRing R) L).comp e.toRingEquiv.toRingHom := by
          simpa using
            (RingHom.algebraMap_toAlgebra
              ((algebraMap (FractionRing R) L).comp e.toRingEquiv.toRingHom))
        -- Now it is a direct computation using `e.commutes`.
        -- We keep this as a `simp` step to unfold the compositions.
        -- (The only nontrivial rewrite is `e.commutes x`.)
        simp [h₁, h₂, RingHom.comp_apply, e.commutes x]
    haveI : Module.Finite (FractionRing (Rₚ r)) L := by
      -- Transfer finiteness from `Frac(R)` along `e`.
      refine
        Module.Finite.of_equiv_equiv (A₁ := FractionRing R) (B₁ := L) (A₂ := FractionRing (Rₚ r))
          (B₂ := L) e.symm.toRingEquiv (RingEquiv.refl L) ?_
      ext x
      -- Unfold `algebraMap (FractionRing (Rₚ r)) L` from the `toAlgebra` definition above.
      have h₂ :
          algebraMap (FractionRing (Rₚ r)) L =
            (algebraMap (FractionRing R) L).comp e.toRingEquiv.toRingHom := by
        simpa using
          (RingHom.algebraMap_toAlgebra
            ((algebraMap (FractionRing R) L).comp e.toRingEquiv.toRingHom))
      -- Then reduce to `e.apply_symm_apply`.
      simp only [h₂, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
        AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv, RingHom.comp_apply,
        RingHom.coe_coe, RingEquiv.coe_ringHom_refl, RingHomCompTriple.comp_eq, algebraMap.coe_inj]
      exact e.toRingEquiv.apply_symm_apply x
    -- Now apply the `N-2` condition for `Rᵣ`.
    exact IsN2Ring.extension_integralClosure_finite (R := Rₚ r) (L := L)
  exact
    Module.Finite.of_localizationSpan' (R := R) (M := (integralClosure R L))
      (t := s0) spn0 (Rₚ := Rₚ) (Mₚ := fun r => integralClosure (Rₚ r) L)
      (f := f) (H := H)

variable (R) [IsNoetherianRing R] (S : Type*) [CommRing S] [IsDomain S] (f : R →+* S)

@[stacks 032I]
theorem IsN2Ring.of_quasiFinite [IsN2Ring R] (hf_inj : Function.Injective f)
    (hf : f.FiniteType) (hf_qf : f.QuasiFinite) : IsN2Ring S := sorry

@[stacks 032J]
theorem IsN1Ring.of_polynomial_localize_X [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
    [IsLocalization (.powers (.X : R[X])) S] [IsN1Ring S] : IsN1Ring R := sorry

@[stacks 032K "first part"]
theorem IsN1Ring.of_finite_extension (hf_inj : Function.Injective f)
    (hf : f.Finite) [IsN1Ring S] : IsN1Ring R := by
  classical
  -- Use the `Algebra` structure induced by `f`.
  letI : Algebra R S := f.toAlgebra
  haveI : Module.Finite R S := hf
  -- Work with the fraction fields.
  let KR := FractionRing R
  let KS := FractionRing S
  -- The induced map on fraction fields.
  let φK : KR →+* KS := IsFractionRing.map (A := R) (B := S) (j := f) hf_inj
  -- `algebraMap` commutes with `φK` by construction.
  have hφK : (algebraMap S KS).comp f = φK.comp (algebraMap R KR) := by
    ext r
    simp [KR, KS, φK, IsFractionRing.map]
  -- Use the `R`-algebra structure on `integralClosure S KS` induced by `f`.
  letI : Algebra R (integralClosure S KS) :=
    ((algebraMap S (integralClosure S KS)).comp f).toAlgebra
  letI : IsScalarTower R S (integralClosure S KS) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rfl
  -- The integral closure of `S` in its fraction field is finite over `R`.
  haveI : Module.Finite S (integralClosure S KS) := IsN1Ring.integralClosure_finite (R := S)
  haveI : Module.Finite R (integralClosure S KS) := Module.Finite.trans S (integralClosure S KS)
  haveI : IsNoetherian R (integralClosure S KS) :=
    isNoetherian_of_isNoetherianRing_of_finite (R := R) (M := integralClosure S KS)
  -- Map `integralClosure R (Frac(R))` into `integralClosure S (Frac(S))`.
  let φ :
      integralClosure R KR →ₐ[R] integralClosure S KS :=
    { toFun := fun x =>
        ⟨φK (x : KR), by
          rcases x.2 with ⟨p, hp, hpx⟩
          refine ⟨p.map f, hp.map _, ?_⟩
          -- Use `map_aeval_eq_aeval_map` to transport the equation `p(x)=0`.
          have h :=
            (Polynomial.map_aeval_eq_aeval_map (S := KR) (T := S) (U := KS) (φ := f) (ψ := φK) hφK p
              (x : KR))
          have h' :
              eval₂ (algebraMap S KS) (φK (x : KR)) (p.map f) =
                φK (eval₂ (algebraMap R KR) (x : KR) p) := by
            simpa [Polynomial.aeval_def] using h.symm
          simpa [hpx] using h'⟩
      map_one' := by ext; simp [φK]
      map_mul' := by intro x y; ext; simp [φK]
      map_zero' := by ext; simp [φK]
      map_add' := by intro x y; ext; simp [φK]
      commutes' := by
        intro r
        ext
        -- Reduce to `hφK`.
        simpa [KR, KS, φK, RingHom.algebraMap_toAlgebra] using
          (congrArg (fun g => g r) hφK).symm }
  -- `φ` is injective since `φK` is injective.
  have hφK_inj : Function.Injective φK :=
    -- Any ring hom from a field is injective.
    RingHom.injective φK
  have hφ : Function.Injective φ := by
    intro x y hxy
    ext
    apply hφK_inj
    simpa [φ] using congrArg (fun z : integralClosure S KS => (z : KS)) hxy
  -- Conclude finiteness for `integralClosure R (Frac(R))`.
  refine ⟨Module.Finite.of_injective φ.toLinearMap hφ⟩

@[stacks 032K "second part"]
theorem IsN2Ring.of_finite_extension (hf_inj : Function.Injective f)
    (hf : f.Finite) [IsN2Ring S] : IsN2Ring R := sorry

-- 10.161.10 0AE0

@[stacks 032M "if part"]
theorem IsN2Ring.of_isN1Ring_of_charZero [IsN1Ring R] [CharZero R] : IsN2Ring R := sorry

@[stacks 032M]
theorem isJapaneseRing_iff_isN1Ring_of_charZero [CharZero R] : IsN2Ring R ↔ IsN1Ring R :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ IsN2Ring.of_isN1Ring_of_charZero R⟩

-- 10.161.12 032N

@[stacks 032O "first part"]
theorem IsN1Ring.polynomial [IsN1Ring R] : IsN1Ring R[X] := sorry

@[stacks 032O "second part"]
theorem IsN2Ring.polynomial [IsN2Ring R] : IsN2Ring R[X] := sorry
