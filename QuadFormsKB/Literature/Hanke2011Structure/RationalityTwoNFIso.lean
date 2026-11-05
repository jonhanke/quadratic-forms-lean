/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.LocalDensity.NFBridge

/-!
# Paper 6, Theorem 5.4 at $F_{\mathfrak p} = \mathbb Q_2$ of a number field: the ring isomorphism

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23-24.

For a prime $\mathfrak p$ of a number field $F$ with $N\mathfrak p = 2$ and $2 \notin \mathfrak p^2$
(so $F_{\mathfrak p} \cong \mathbb Q_2$) we construct the ring isomorphism
$\mathfrak o_{\mathfrak p} \cong \mathbb Z_2$ (`twoAdicEquiv`).  The abstract part (`twoAdicEquiv`) is stated for any
local domain $R$ with maximal ideal $(2)$, $2$-adically complete, with $|R/2^k| = 2^k$ for all $k$.
*Proof:* $\mathbb Z/2^k \to R/2^k$ is injective (an odd integer is a unit of $R$) hence bijective by counting; these
assemble by `PadicInt.lift` to $R \to \mathbb Z_2$, injective by Hausdorffness and surjective by completeness.
-/

open IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.RatTwoNF

noncomputable section

section Abstract

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  (hm : IsLocalRing.maximalIdeal R = Ideal.span {(2 : R)})
  (hcard : ∀ k : ℕ, Nat.card (R ⧸ Ideal.span {(2 : R) ^ k}) = 2 ^ k)

include hm in
theorem two_mem_max : (2 : R) ∈ IsLocalRing.maximalIdeal R := by
  rw [hm]; exact Ideal.subset_span rfl

include hm hcard in
theorem two_ne_zero_abs : (2 : R) ≠ 0 := by
  intro h
  have h1 := hcard 1
  have h2 := hcard 2
  have e : (2 : R) ^ 2 = (2 : R) ^ 1 := by rw [h]; simp
  rw [e, h1] at h2
  omega

include hm in
theorem odd_isUnit {b : ℤ} (hb : Odd b) : IsUnit (b : R) := by
  by_contra hu
  have hmem : (b : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hu
  rw [hm, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨m, hmb⟩ := hb
  have : (2 : R) * (c - m) = 1 := by
    have h2 : (b : R) = 2 * (m : R) + 1 := by rw [hmb]; push_cast; ring
    rw [h2] at hc
    linear_combination -hc
  have hu2 : IsUnit (2 : R) := isUnit_iff_exists_inv.2 ⟨_, this⟩
  exact (IsLocalRing.mem_maximalIdeal _).1 (two_mem_max hm) hu2

include hm hcard in
theorem int_dvd_of_pow_dvd (k : ℕ) : ∀ a : ℤ, (2 : R) ^ k ∣ (a : R) → (2 : ℤ) ^ k ∣ a := by
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    have h2 : (2 : R) ∣ (a : R) := (dvd_pow_self _ (Nat.succ_ne_zero k)).trans ha
    have hev : Even a := by
      by_contra hodd
      have hodd' : Odd a := Int.not_even_iff_odd.mp hodd
      have hu := odd_isUnit hm (R := R) hodd'
      have : IsUnit (2 : R) := isUnit_of_dvd_unit h2 hu
      exact (IsLocalRing.mem_maximalIdeal _).1 (two_mem_max hm) this
    obtain ⟨a', ha'⟩ := hev
    have ha2 : a = 2 * a' := by omega
    subst ha2
    push_cast at ha
    rw [pow_succ'] at ha
    have := (mul_dvd_mul_iff_left (two_ne_zero_abs hm hcard)).1 ha
    have := ih a' this
    rw [pow_succ']
    exact mul_dvd_mul_left 2 this

theorem zmod_aux (k : ℕ) :
    (Int.castRingHom (R ⧸ Ideal.span {(2 : R) ^ k})) (((2 ^ k : ℕ)) : ℤ) = 0 := by
  rw [map_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : R ⧸ Ideal.span {(2 : R) ^ k}) = Ideal.Quotient.mk _ 2 from (map_ofNat _ 2).symm, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/-- The ring map $\mathbb Z/2^k \to R/2^k$. -/
def zmodToQuot (k : ℕ) : ZMod (2 ^ k) →+* R ⧸ Ideal.span {(2 : R) ^ k} :=
  (Ideal.Quotient.lift (Ideal.span {((2 ^ k : ℕ) : ℤ)}) (Int.castRingHom (R ⧸ Ideal.span {(2 : R) ^ k}))
    (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
      rw [map_mul, zmod_aux, zero_mul])).comp (Int.quotientSpanNatEquivZMod (2 ^ k)).symm.toRingHom

theorem zmodToQuot_intCast (k : ℕ) (a : ℤ) :
    zmodToQuot (R := R) k (a : ZMod (2 ^ k)) = Ideal.Quotient.mk _ (a : R) := by
  unfold zmodToQuot
  have : (a : ZMod (2 ^ k)) = Int.quotientSpanNatEquivZMod (2 ^ k) (Ideal.Quotient.mk _ a) := by simp
  rw [this]
  simp

include hm hcard in
theorem zmodToQuot_injective (k : ℕ) : Function.Injective (zmodToQuot (R := R) k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [zmodToQuot_intCast, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  have := int_dvd_of_pow_dvd hm hcard k a hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast this

include hm hcard in
theorem zmodToQuot_bijective (k : ℕ) : Function.Bijective (zmodToQuot (R := R) k) := by
  have hfin : Finite (R ⧸ Ideal.span {(2 : R) ^ k}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine (zmodToQuot_injective hm hcard k).bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_zmod]

/-- $\mathbb Z/2^k \cong R/2^k$. -/
def eqvK (hm : IsLocalRing.maximalIdeal R = Ideal.span {(2 : R)})
    (hcard : ∀ k : ℕ, Nat.card (R ⧸ Ideal.span {(2 : R) ^ k}) = 2 ^ k) (k : ℕ) :
    ZMod (2 ^ k) ≃+* R ⧸ Ideal.span {(2 : R) ^ k} :=
  RingEquiv.ofBijective _ (zmodToQuot_bijective hm hcard k)

/-- The reductions $R \to \mathbb Z/2^k$. -/
def psiK (hm : IsLocalRing.maximalIdeal R = Ideal.span {(2 : R)})
    (hcard : ∀ k : ℕ, Nat.card (R ⧸ Ideal.span {(2 : R) ^ k}) = 2 ^ k) (k : ℕ) : R →+* ZMod (2 ^ k) :=
  (eqvK hm hcard k).symm.toRingHom.comp (Ideal.Quotient.mk _)

theorem psiK_eq_zero_iff (k : ℕ) (x : R) : psiK hm hcard k x = 0 ↔ (2 : R) ^ k ∣ x := by
  unfold psiK
  show (eqvK hm hcard k).symm (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [RingEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem eqvK_cast (k k' : ℕ) (hk : k ≤ k') (y : ZMod (2 ^ k')) :
    eqvK hm hcard k (ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k)) y) =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hk)) (eqvK hm hcard k' y) := by
  have : (eqvK hm hcard k).toRingHom.comp (ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k))) =
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hk))).comp
        (eqvK hm hcard k').toRingHom := RingHom.ext_zmod _ _
  exact RingHom.congr_fun this y

theorem psiK_compat (k k' : ℕ) (hk : k ≤ k') :
    (ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k))).comp (psiK hm hcard k') = psiK hm hcard k := by
  ext x
  apply (eqvK hm hcard k).injective
  simp only [RingHom.comp_apply]
  rw [eqvK_cast hm hcard k k' hk]
  unfold psiK
  simp

/-- The ring homomorphism $R \to \mathbb Z_2$ induced by the reductions. -/
def toZ2 (hm : IsLocalRing.maximalIdeal R = Ideal.span {(2 : R)})
    (hcard : ∀ k : ℕ, Nat.card (R ⧸ Ideal.span {(2 : R) ^ k}) = 2 ^ k) : R →+* ℤ_[2] :=
  PadicInt.lift (psiK_compat hm hcard)

theorem toZModPow_toZ2 (k : ℕ) (x : R) : PadicInt.toZModPow k (toZ2 hm hcard x) = psiK hm hcard k x :=
  RingHom.congr_fun (PadicInt.lift_spec (psiK_compat hm hcard) k) x

include hm in
theorem smod_iff (k : ℕ) (x y : R) :
    x ≡ y [SMOD ((IsLocalRing.maximalIdeal R) ^ k • ⊤ : Submodule R R)] ↔ (2 : R) ^ k ∣ (x - y) := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem toZ2_injective [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : Function.Injective (toZ2 hm hcard) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal R) R) x fun k => ?_
  rw [smod_iff hm, sub_zero, ← psiK_eq_zero_iff hm hcard, ← toZModPow_toZ2 hm hcard, hx, map_zero]

theorem toZ2_surjective [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : Function.Surjective (toZ2 hm hcard) := by
  intro z
  have hsurj : ∀ k, ∃ x : R, psiK hm hcard k x = PadicInt.toZModPow k z := by
    intro k
    obtain ⟨q, hq⟩ := (eqvK hm hcard k).symm.surjective (PadicInt.toZModPow k z)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨x, hq⟩
  choose xs hxs using hsurj
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      xs m ≡ xs n [SMOD ((IsLocalRing.maximalIdeal R) ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [smod_iff hm, ← psiK_eq_zero_iff hm hcard, map_sub, hxs m, ← psiK_compat hm hcard m n hmn,
      RingHom.comp_apply, hxs n]
    have hc := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow (p := 2) m n hmn) z
    rw [RingHom.comp_apply] at hc
    rw [hc, sub_self]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal R) xs hcauchy
  refine ⟨L, ?_⟩
  rw [← PadicInt.ext_of_toZModPow]
  intro k
  rw [toZModPow_toZ2, ← hxs k]
  have := (smod_iff hm k _ _).1 (hL k)
  have h0 : psiK hm hcard k (xs k - L) = 0 := (psiK_eq_zero_iff hm hcard k _).2 this
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

/-- **$\mathfrak o_R \cong \mathbb Z_2$** for a local domain $R$ with maximal ideal $(2)$, $2$-adically complete, with
$|R/2^k| = 2^k$. -/
def twoAdicEquiv [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {(2 : R)})
    (hcard : ∀ k : ℕ, Nat.card (R ⧸ Ideal.span {(2 : R) ^ k}) = 2 ^ k) : R ≃+* ℤ_[2] :=
  RingEquiv.ofBijective (toZ2 hm hcard) ⟨toZ2_injective hm hcard, toZ2_surjective hm hcard⟩

theorem twoAdicEquiv_apply [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {(2 : R)})
    (hcard : ∀ k : ℕ, Nat.card (R ⧸ Ideal.span {(2 : R) ^ k}) = 2 ^ k) (x : R) :
    twoAdicEquiv hm hcard x = toZ2 hm hcard x := rfl

end Abstract

/-! ### The completion of a number field at a prime with $N\mathfrak p = 2$, $2 \notin \mathfrak p^2$ -/

section NF

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The conditions on $\mathfrak p$ making $F_{\mathfrak p} \cong \mathbb Q_2$: $2 \in \mathfrak p$, $2 \notin \mathfrak p^2$ (ramification
index $1$) and $N\mathfrak p = 2$ (residue degree $1$). -/
structure IsQ2Prime : Prop where
  two_mem : (2 : 𝓞 F) ∈ v.asIdeal
  two_not_mem_sq : (2 : 𝓞 F) ∉ v.asIdeal ^ 2
  absNorm_eq : Ideal.absNorm v.asIdeal = 2

variable {v}

theorem IsQ2Prime.associated (h : IsQ2Prime v) : Associated (LocalDensity.NF.π v) (2 : 𝔬) := by
  have h1 : LocalDensity.NF.π v ∣ (2 : 𝔬) := by
    have := (LocalDensity.NF.π_pow_dvd_ι_iff v 1 2).2 (by rw [pow_one]; exact h.two_mem)
    rwa [pow_one, map_ofNat] at this
  have h2 : ¬ LocalDensity.NF.π v ^ 2 ∣ (2 : 𝔬) := by
    have := (LocalDensity.NF.π_pow_dvd_ι_iff v 2 2).not.2 h.two_not_mem_sq
    rwa [map_ofNat] at this
  obtain ⟨u, hu⟩ := h1
  have hπ := LocalDensity.NF.irreducible_π v
  have hu' : IsUnit u := by
    by_contra hnu
    apply h2
    have hmem : u ∈ IsLocalRing.maximalIdeal 𝔬 := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, by rw [hu, hw]; ring⟩
  exact ⟨hu'.unit, by rw [hu]; simp [mul_comm]⟩

theorem IsQ2Prime.maximalIdeal_eq (h : IsQ2Prime v) :
    IsLocalRing.maximalIdeal 𝔬 = Ideal.span {(2 : 𝔬)} := by
  rw [(LocalDensity.NF.irreducible_π v).maximalIdeal_eq]
  exact Ideal.span_singleton_eq_span_singleton.2 h.associated

theorem IsQ2Prime.card (h : IsQ2Prime v) (k : ℕ) : Nat.card (𝔬 ⧸ Ideal.span {(2 : 𝔬) ^ k}) = 2 ^ k := by
  rw [← Ideal.span_singleton_pow, ← h.maximalIdeal_eq, (LocalDensity.NF.irreducible_π v).maximalIdeal_eq,
    Ideal.span_singleton_pow, LocalDensity.NF.card_quot_π_pow, h.absNorm_eq]

/-- **The ring isomorphism $\mathfrak o_{\mathfrak p} \cong \mathbb Z_2$** at a prime $\mathfrak p$ of a number field with
$N\mathfrak p = 2$ and $2 \notin \mathfrak p^2$. -/
def IsQ2Prime.equiv (h : IsQ2Prime v) : 𝔬 ≃+* ℤ_[2] :=
  twoAdicEquiv h.maximalIdeal_eq h.card

end NF

end

end QuadFormsKB.Hanke2011Structure.RatTwoNF

#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.IsQ2Prime.equiv
