/-
Copyright (c) 2026 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Basis of exterior power

In this file we construct a basis of the exterior power `⋀[R]^n M` given a linearly ordered
basis of `M`, and deduce that exterior powers of free modules are free.
-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

namespace exteriorPower

/-- Given a linearly ordered basis `b : Module.Basis ι R M`, the `n`th exterior power `⋀[R]^n M`
has a basis indexed by order embeddings `Fin n ↪o ι`. -/
noncomputable def basis {ι : Type*} [LinearOrder ι] (b : Module.Basis ι R M) (n : ℕ) :
    Module.Basis (Fin n ↪o ι) R (⋀[R]^n M) := by
  let e : (Fin n ↪o ι) → ⋀[R]^n M := fun a ↦ ιMulti R n (fun i ↦ b (a i))
  refine Module.Basis.mk (v := e) ?_ ?_
  · refine (linearIndependent_iff).2 fun l hl ↦ Finsupp.ext fun a0 ↦ ?_
    have h₁ (i : ι) : b.coord i (b i) = (1 : R) := by simp [Module.Basis.coord]
    have h₀ (i j : ι) (hij : i ≠ j) : b.coord i (b j) = (0 : R) := by simp [Module.Basis.coord, hij]
    let φ : ⋀[R]^n M →ₗ[R] R := pairingDual R M n (ιMulti R n (fun i ↦ b.coord (a0 i)))
    have hx : φ ((Finsupp.linearCombination R e) l) = 0 := by simpa using congr(φ $hl)
    have hx' : φ ((Finsupp.linearCombination R e) l) = l a0 := by
      simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
      refine (Finsupp.sum_eq_single a0 ?_ fun ha0 ↦ by simp).trans ?_
      · intro a ha hne
        have : φ (e a) = 0 := pairingDual_apply_apply_eq_one_zero b b.coord h₀ n a0 a hne.symm
        simp [this]
      · have : φ (e a0) = 1 := pairingDual_apply_apply_eq_one b b.coord h₁ h₀ n a0
        simp [this, smul_eq_mul]
    exact hx'.symm.trans hx
  · let S : Submodule R (⋀[R]^n M) := Submodule.span R (Set.range e)
    have mem_S_of_injective (v : Fin n → ι) (hv : Function.Injective v) :
        ιMulti R n (b ∘ v) ∈ S := by
      let σ : Equiv.Perm (Fin n) := Tuple.sort v
      have hmono : Monotone (v ∘ σ) := Tuple.monotone_sort v
      have hinj : Function.Injective (v ∘ σ) := hv.comp σ.injective
      let a : Fin n ↪o ι := OrderEmbedding.ofStrictMono (v ∘ σ) (hmono.strictMono_of_injective hinj)
      have hperm : ιMulti R n (b ∘ v) = Equiv.Perm.sign σ • ιMulti R n (b ∘ a) := by
        rw [← Equiv.Perm.sign_inv]
        convert AlternatingMap.map_perm (ιMulti R n) (b ∘ a) σ⁻¹
        simp [a, Function.comp_assoc]
      rw [hperm]
      exact S.smul_mem _ (Submodule.subset_span ⟨a, rfl⟩)
    let ψ : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M ⧸ S) := S.mkQ.compAlternatingMap (ιMulti R n)
    have hψ : ψ = 0 := by
      refine Module.Basis.ext_alternating b fun v hv ↦ ?_
      simpa [ψ] using (Submodule.Quotient.mk_eq_zero S).2 (mem_S_of_injective v hv)
    have hrange : Set.range (ιMulti R n (M := M)) ⊆ S := by
      rintro _ ⟨m, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero S).1 (show ψ m = 0 from by simp [hψ])
    simpa [S, ιMulti_span R n M] using Submodule.span_le.mpr hrange

end exteriorPower

/-- We show that exterior power of a free module is free. -/
instance Module.Free.exteriorPower (n : ℕ) [Module.Free R M] : Module.Free R (⋀[R]^n M) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R M
  letI : LinearOrder ι := linearOrderOfSTO (WellOrderingRel (α := ι))
  exact Module.Free.of_basis
    (exteriorPower.basis (R := R) (M := M) (ι := ι) (Module.Free.chooseBasis R M) n)
