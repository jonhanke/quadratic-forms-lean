/-
# Kneser neighbours over $\mathcal O_F$, part 5: neighbours stay in the genus

**Main theorem** (`sameGenus_latOf_nbLat`): let $F$ be a number field with $\mathcal O_F$ a PID, $Q$ a form on $F^n$, $M = \gamma\mathcal O_F^n$
an integral lattice with Gram form $Q_\gamma$, $\pi$ a prime with $\pi \nmid 2\det H(Q_\gamma)$, and $M'$ a $\pi$-neighbour of $M$. Then $M'$ is in
the genus of $M$ (Kneser 1957, Satz 1 [unverified]; over $\mathbb Q$: `Siegel.Kneser.sameGenus_of_neighbor`).

*Proof.* $M' = \gamma N$ with $N = L(\vec v)$ the explicit neighbour of $\mathcal O_F^n$ for $Q_\gamma$, and $N = \delta\mathcal O_F^n$ (PID).
* At a prime $\mathfrak q \ne (\pi)$: $\pi\mathcal O_F^n \subseteq N \subseteq \pi^{-1}\mathcal O_F^n$ and $\pi$ is a unit at $\mathfrak q$, so $N_\mathfrak q = \mathfrak o_\mathfrak q^n$
  (`loc_nbLat_eq`).
* At $\mathfrak p = (\pi)$: the Gram form $Q_{\gamma\delta}$ of $M'$ is **unimodular at $\pi$** (`not_dvd_det_gram_nbLat`; elementary: if
  $B(x, N) \subseteq \pi\mathcal O_F$ for $x \in N$ then $x \in \pi N$, `eq_smul_of_bv_dvd`, using $(\bar v^\perp)^\perp = k\bar v$), and it is isometric to
  $Q_\gamma$ over $F_\mathfrak p$ (by $\delta$). Two unimodular forms isometric over $F_\mathfrak p$ are isometric over $\mathfrak o_\mathfrak p$
  (`isometricGL_of_unimodular_of_isometricIn`, O'Meara 92:2), which gives the local isometry (`exists_locAct_of_isometricGL`).
-/
import QuadFormsKB.Lattices.NeighborGenus
import QuadFormsKB.Lattices.UnimodularDVR

open Matrix NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

namespace QuadFormsKB.Lattices.Nbr

/-! ### Self-duality of $L(\vec v)$ at $\pi$ (generic) -/

section SelfDual

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ} {Q : QuadForm R n} {π : R} [(Ideal.span {π}).IsMaximal] [Fintype (Res π)] [DecidableEq (Res π)]
  (hπ : Prime π) (hdet : ¬ π ∣ Q.hessian.det)
include hπ hdet

/-- **Nondegeneracy mod $\pi$**: if $\pi \mid B(\vec y, \vec z)$ for all $\vec z$ then $\pi \mid \vec y$. -/
lemma red_eq_zero_of_bv_dvd {y : Fin n → R} (h : ∀ z : Fin n → R, π ∣ bv R Q y z) : red π y = 0 := by
  by_contra hy
  obtain ⟨z, hz⟩ := exists_bv_eq_one (Q := Q) hdet hy
  have := (dvd_of_red (π := π) _).mpr (h z)
  rw [bv_comm, hz] at this
  exact one_ne_zero this

/-- **$L(\vec v)$ is self-dual at $\pi$** (Kneser 1957 [unverified]): if $x \in L(\vec v)$ and $B(x, z) \in \pi R$ for every $z \in L(\vec v)$, then
$x \in \pi L(\vec v)$. -/
theorem eq_smul_of_bv_dvd {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) (hv0 : red π v ≠ 0) {x : Fin n → K}
    (hx : x ∈ nbLat (K := K) Q π v)
    (hB : ∀ z ∈ nbLat (K := K) Q π v, ∃ b : R, π ∣ b ∧ bv K Q x z = algebraMap R K b) :
    ∃ x' ∈ nbLat (K := K) Q π v, x = algebraMap R K π • x' := by
  have h0 := πK_ne_zero (K := K) hπ
  -- step 1: `x = cv y'`
  obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
  have hy0 : red π y = 0 := by
    refine red_eq_zero_of_bv_dvd hπ hdet fun z => ?_
    obtain ⟨b, hb, he⟩ := hB _ (smul_cv_mem_nbLat (K := K) hπ hv z)
    rw [cv_smul, bv_smul_left, bv_smul_right, ← mul_assoc, inv_mul_cancel₀ h0, one_mul, bv_cv] at he
    rw [IsFractionRing.injective R K he]; exact hb
  obtain ⟨y', rfl⟩ := eq_smul_of_red_eq_zero hπ hy0
  rw [cv_eq_inv_smul hπ] at hB ⊢
  have hB' : ∀ z : Fin n → R, cv K z ∈ nbLat (K := K) Q π v → π ∣ bv R Q y' z := by
    intro z hz
    obtain ⟨b, hb, he⟩ := hB _ hz
    rw [bv_cv] at he
    rw [IsFractionRing.injective R K he]; exact hb
  -- step 2: `ȳ' ∈ k v̄`
  obtain ⟨w₀, hw₀⟩ := exists_bv_eq_one (Q := Q) hdet hv0
  set t := bv R Q y' w₀ with ht
  have hperp : ∀ z : Fin n → R, π ∣ bv R Q (y' - t • v) z := by
    intro z
    set c := bv R Q z v
    have hz' : cv K (z - c • w₀) ∈ nbLat (K := K) Q π v := by
      rw [cv_mem_nbLat_iff hπ hv, ← dvd_of_red, sub_eq_add_neg, bv_add_left, ← neg_smul,
        bv_smul_left, map_add, map_mul, hw₀]
      simp [c]
    have h1 := hB' _ hz'
    rw [← dvd_of_red] at h1 ⊢
    rw [sub_eq_add_neg, bv_add_right, ← neg_smul, bv_smul_right, map_add, map_mul] at h1
    rw [sub_eq_add_neg, bv_add_left, ← neg_smul, bv_smul_left, map_add, map_mul, bv_comm v z]
    simp only [map_neg] at h1 ⊢
    linear_combination h1
  have hy'' := red_eq_zero_of_bv_dvd hπ hdet hperp
  obtain ⟨z₁, hz₁⟩ := eq_smul_of_red_eq_zero hπ hy''
  have hy' : y' = t • v + π • z₁ := by rw [← hz₁]; abel
  -- step 3: `z₁ ∈ L_v`
  obtain ⟨d, hd⟩ := hv
  have hz₁v : cv K z₁ ∈ nbLat (K := K) Q π v := by
    rw [cv_mem_nbLat_iff hπ ⟨d, hd⟩]
    obtain ⟨b, hb, he⟩ := hB _ (inv_smul_mem_nbLat (K := K) hπ ⟨d, hd⟩)
    rw [bv_smul_right, bv_cv, hy', bv_add_left, bv_smul_left, bv_smul_left, bv_self, hd] at he
    have he'' : t * (2 * (π ^ 2 * d)) + π * bv R Q z₁ v = π * b := by
      apply IsFractionRing.injective R K
      rw [map_mul (algebraMap R K) π b, ← he]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      field_simp
    have : π * bv R Q z₁ v = π * (b - t * (2 * π * d)) := by linear_combination he''
    rw [mul_left_cancel₀ hπ.ne_zero this]
    exact dvd_sub hb (Dvd.intro_left _ (by ring : t * (2 * d) * π = t * (2 * π * d)))
  -- step 4
  refine ⟨t • ((algebraMap R K π)⁻¹ • cv K v) + cv K z₁,
    (nbLat Q π v).add_mem ((nbLat Q π v).smul_mem t (inv_smul_mem_nbLat hπ ⟨d, hd⟩)) hz₁v, ?_⟩
  rw [hy', cv_add, cv_smul, cv_smul, smul_add, algebra_compatible_smul K t, smul_smul, smul_smul]
  congr 1
  congr 1
  field_simp

end SelfDual

end QuadFormsKB.Lattices.Nbr
