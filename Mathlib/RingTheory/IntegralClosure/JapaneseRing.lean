/-
Copyright (c) 2026 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
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

#check IsLocalization.integralClosure
@[stacks 032G "first part"]
theorem IsN1Ring.of_isLocalization (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] [IsN1Ring R] [IsDomain S] : IsN1Ring S := by
  refine (isN1Ring_iff S).mpr ?_
  let R' := integralClosure R K
  let S' := integralClosure S (FractionRing S)
  let _ : FaithfulSMul R S := by sorry
  let _ : Algebra K (FractionRing S) := Ring.instAlgebraFractionRing R S
  let _ : Algebra R' S' := by
    unfold R' S'
    -- apply?
    sorry
  have : IsScalarTower R' S' (FractionRing S) := by sorry
  have : IsScalarTower R R' S' := IsScalarTower.to₁₂₃ R R' S' (FractionRing S)
  have : IsScalarTower R K (FractionRing S) := FractionRing.instIsScalarTower R (FractionRing S)
  let _ : IsLocalization (Algebra.algebraMapSubmonoid R' M) S' := by
    have : IsLocalization (Algebra.algebraMapSubmonoid K M) (FractionRing S) := by
      sorry
    exact IsLocalization.integralClosure ..
  let _ : Module.Finite R R' := IsN1Ring.integralClosure_finite
  exact Module.Finite.of_isLocalization R R' (Rₚ := S) (Sₚ := S') M

@[stacks 032G "first part"]
theorem IsN2Ring.of_isLocalization (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] [IsN2Ring R] [IsDomain S] : IsN2Ring S := sorry

@[stacks 032H "first part"]
theorem IsN1Ring.of_localized_span (s : Set R) (spn : Ideal.span s = ⊤)
    (h : ∀ (r : s) (_ : r.1 ≠ 0), @IsN1Ring (Localization.Away r.1) _
    (Localization.Away.isDomain r.1 ‹_›)) : IsN1Ring R := sorry

@[stacks 032H "second part"]
theorem IsN2Ring.of_localized_span (s : Set R) (spn : Ideal.span s = ⊤)
    (h : ∀ (r : s) (_ : r.1 ≠ 0), @IsN2Ring (Localization.Away r.1) _
    (Localization.Away.isDomain r.1 ‹_›)) : IsN2Ring R := sorry

variable (R) [IsNoetherianRing R] (S : Type*) [CommRing S] [IsDomain S] (f : R →+* S)

@[stacks 032I]
theorem IsN2Ring.of_quasiFinite [IsN2Ring R] (hf_inj : Function.Injective f)
    (hf : f.FiniteType) (hf_qf : f.QuasiFinite) : IsN2Ring S := sorry

@[stacks 032J]
theorem IsN1Ring.of_polynomial_localize_X [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
    [IsLocalization (.powers (.X : R[X])) S] [IsN1Ring S] : IsN1Ring R := sorry

@[stacks 032K "first part"]
theorem IsN1Ring.of_finite_extension (hf_inj : Function.Injective f)
    (hf : f.Finite) [IsN1Ring S] : IsN1Ring R := sorry

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
