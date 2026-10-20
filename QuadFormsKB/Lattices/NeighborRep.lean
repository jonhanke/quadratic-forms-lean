/-
# Kneser neighbours over a Dedekind domain, part 3: the neighbour relation for representation numbers

**Layer:** as in `Lattices/Neighbors.lean`: $R$ a domain with fraction field $K$, $Q$ a form over $R$ on $L = R^n$, $\pi$ a prime with
finite residue field $k = R/\pi$ of size $q$, $\operatorname{char}k \ne 2$, $\pi \nmid \det H$, and $Q$ with finitely many representations of
each $m$ (`hfin`; true for totally positive definite forms over $\mathcal O_F$).

**Defines** the representation numbers of a lattice $r_{L'}(m) = \#\{\vec x \in L' : Q(\vec x) = m\}$ (`latRep`) and $r_Q(m) = r_{R^n}(m)$
(`repNum`).

**Proves** the **single-lattice neighbour relation** at $\pi \nmid m$ (Eichler's commutation relation for the $\pi$-neighbour operator,
coefficient level; Eichler 1952, Kneser 1957): for $n$ even, if $\bar Q$ takes every nonzero value of $k$ equally often (`hconst`;
Table 1),
$$(q - 1)\sum_{L' \sim_\pi R^n} r_{L'}(m) = (q-1)\,r_Q(\pi^2m) + (q^{n-2} - q)\,r_Q(m)\qquad(\pi \nmid m)$$
(`sum_latRep_neighbors_of_not_dvd`). *Proof.* Every $\vec x$ with $Q(\vec x) = m$ in some neighbour is $\frac1\pi\vec y$, $\vec y \in R^n$,
$Q(\vec y) = \pi^2m$. Count (×$(q-1)$) the nonzero isotropic $\bar{\vec v}$ with $\frac1\pi\vec y \in L(\bar{\vec v})$:
- $\bar{\vec y} \ne 0$: the points of the line $k\bar{\vec y}$, $q - 1$ of them;
- $\vec y = \pi\vec z$ (then $\bar{\vec z} \ne 0$ and $\bar Q(\bar{\vec z}) = \bar m \ne 0$): the isotropic $\bar{\vec v} \ne 0$ with $\bar B(\bar{\vec z}, \bar{\vec v}) = 0$,
  $q^{n-2} - 1$ of them (`card_perp_anisotropic`).
The numbers of such $\vec y$ are $r_Q(\pi^2m) - r_Q(m)$ and $r_Q(m)$.

Over $\mathbb Z$ this is the $p \nmid m$ case of `Siegel.Kneser.sum_latRep_neighbors_even`.
-/
import QuadFormsKB.Lattices.Neighbors

open Matrix

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

namespace QuadFormsKB.Lattices.Nbr

open Classical

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ}

variable (K) in
/-- **The representation numbers of a lattice** $L' \subset K^n$: $r_{L'}(m) = \#\{\vec x \in L' : Q(\vec x) = m\}$ (a `Nat.card`, so $0$
if infinite). Parameters: `Q` (the form over $R$, evaluated in $K$), `L` (the lattice), `m` (an element of $R$). -/
@[kb "eichler1952" "representation numbers of a lattice [unverified]"]
noncomputable def latRep (Q : QuadForm R n) (L : Submodule R (Fin n → K)) (m : R) : ℕ :=
  Nat.card {x : Fin n → K // x ∈ L ∧ qv K Q x = algebraMap R K m}

/-- **The representation number** $r_Q(m) = \#\{\vec y \in R^n : Q(\vec y) = m\}$. -/
noncomputable def repNum (Q : QuadForm R n) (m : R) : ℕ := Nat.card {y : Fin n → R // qv R Q y = m}

section Rep

variable {Q : QuadForm R n} (hfin : ∀ M : R, Set.Finite {y : Fin n → R | qv R Q y = M})
include hfin

/-- The solutions of $Q(\vec y) = M$ as a `Finset`. -/
noncomputable def repFinset (M : R) : Finset (Fin n → R) := (hfin M).toFinset

theorem mem_repFinset {M : R} {y : Fin n → R} : y ∈ repFinset hfin M ↔ qv R Q y = M := by
  simp [repFinset]

theorem card_repFinset (M : R) : (repFinset hfin M).card = repNum Q M := by
  unfold repFinset repNum
  show _ = Nat.card ({y | qv R Q y = M} : Set (Fin n → R))
  rw [Nat.card_eq_card_finite_toFinset (hfin M)]

/-- **$r_{R^n}(m) = r_Q(m)$.** -/
theorem latRep_stdLat (m : R) : latRep K Q (stdLat R K n) m = repNum Q m := by
  unfold latRep repNum
  refine Nat.card_congr
    { toFun := fun x => ⟨toR R x.1, by
        obtain ⟨⟨y, hy⟩, hq⟩ := x.2
        rw [hy, toR_cv]
        rw [hy, qv_cv] at hq; exact IsFractionRing.injective R K hq⟩
      invFun := fun y => ⟨cv K y.1, cv_mem_stdLat _, by rw [qv_cv, y.2]⟩
      left_inv := fun x => by
        obtain ⟨x, ⟨y, rfl⟩, -⟩ := x
        simp
      right_inv := fun y => by simp }

/-- **Solutions divisible by $c$:** $\#\{\vec y : Q(\vec y) = c^2M,\ c \mid \vec y\} = r_Q(M)$ ($\vec y = c\vec z$). -/
theorem card_filter_dvd {c : R} (hc : c ≠ 0) (M : R) :
    ((repFinset hfin (c ^ 2 * M)).filter fun y => ∀ i, c ∣ y i).card = repNum Q M := by
  classical
  rw [← card_repFinset hfin M]
  refine (Finset.card_nbij' (fun y => fun i => (if h : c ∣ y i then h.choose else 0)) (fun z => c • z)
    ?_ ?_ ?_ ?_)
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_repFinset] at hy
    simp only [Finset.mem_coe, mem_repFinset]
    have e : y = c • fun i => (if h : c ∣ y i then h.choose else 0) := by
      ext i; simp only [Pi.smul_apply, smul_eq_mul]; rw [dif_pos (hy.2 i)]; exact (hy.2 i).choose_spec
    have := hy.1
    rw [e, qv_smul] at this
    exact mul_left_cancel₀ (pow_ne_zero 2 hc) this
  · intro z hz
    simp only [Finset.mem_coe, mem_repFinset] at hz
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_repFinset]
    refine ⟨by rw [qv_smul, hz], fun i => ⟨z i, rfl⟩⟩
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hy
    ext i; simp only [Pi.smul_apply, smul_eq_mul]; rw [dif_pos (hy.2 i)]
    exact (hy.2 i).choose_spec.symm
  · intro z _
    ext i
    have h : c ∣ (c • z) i := ⟨z i, rfl⟩
    simp only [dif_pos h]
    exact mul_left_cancel₀ hc (h.choose_spec.symm.trans rfl)

variable {π : R} (hπ : Prime π)
include hπ

variable [(Ideal.span {π}).IsMaximal] [Fintype (Res π)] [DecidableEq (Res π)]

/-- $\#\{\vec y : Q(\vec y) = \pi^2m,\ \bar{\vec y} = 0\} = r_Q(m)$. -/
theorem card_filter_red_eq_zero (m : R) :
    ((repFinset hfin (π ^ 2 * m)).filter fun y => red π y = 0).card = repNum Q m := by
  rw [← card_filter_dvd hfin hπ.ne_zero m]
  congr 1; ext y; simp [red_eq_zero_iff]

/-- **$r_{L(\bar{\vec v})}(m)$ as a count of integral vectors:** $\#\{\vec y : Q(\vec y) = \pi^2m,\ \frac1\pi\vec y \in L'\}$, for any lattice
$L'$ with $\pi L' \subseteq R^n$. -/
theorem latRep_eq_card {L : Submodule R (Fin n → K)} (hL : ∀ x ∈ L, algebraMap R K π • x ∈ stdLat R K n)
    (m : R) :
    latRep K Q L m =
      ((repFinset hfin (π ^ 2 * m)).filter fun y => (algebraMap R K π)⁻¹ • cv K y ∈ L).card := by
  classical
  have h0 := πK_ne_zero (K := K) hπ
  unfold latRep
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun x => ⟨toR R ((algebraMap R K π) • x.1), by
        obtain ⟨hx, hq⟩ := x.2
        obtain ⟨y, hy⟩ := hL _ hx
        rw [Finset.mem_filter, mem_repFinset, hy, toR_cv, ← hy, smul_smul, inv_mul_cancel₀ h0, one_smul]
        refine ⟨?_, hx⟩
        apply IsFractionRing.injective R K
        rw [← qv_cv, ← hy, qv_smul, hq, map_mul, map_pow]⟩
      invFun := fun y => ⟨(algebraMap R K π)⁻¹ • cv K y.1, by
        obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp y.2
        refine ⟨hy2, ?_⟩
        rw [qv_smul, qv_cv, (mem_repFinset hfin).mp hy1, map_mul, map_pow]
        field_simp⟩
      left_inv := fun x => by
        obtain ⟨x, hx, -⟩ := x
        obtain ⟨y, hy⟩ := hL _ hx
        simp only [Subtype.mk.injEq]
        rw [hy, toR_cv, ← hy, smul_smul, inv_mul_cancel₀ h0, one_smul]
      right_inv := fun y => by
        apply Subtype.ext
        show toR R ((algebraMap R K π) • ((algebraMap R K π)⁻¹ • cv K y.1)) = y.1
        rw [smul_smul, mul_inv_cancel₀ h0, one_smul, toR_cv] }

theorem nbOf_smul_mem (hdet : ¬ π ∣ Q.hessian.det) {vb : Fin n → Res π} (hvb : vb ∈ isoSet Q π) :
    ∀ x ∈ nbOf K Q π vb, algebraMap R K π • x ∈ stdLat R K n := by
  intro x hx
  obtain ⟨h1, h2⟩ := liftV_spec hπ hdet hvb
  exact (isNbr_nbLat hπ hdet h2 (by rw [h1]; exact (mem_isoSet.mp hvb).1)).smul_mem x hx

/-- **Neighbours containing $\frac1\pi\vec y$, $\bar{\vec y} \ne 0$:** $q - 1$ isotropic vectors (one line). -/
theorem card_mem_of_red_ne_zero (hdet : ¬ π ∣ Q.hessian.det) {m : R} {y : Fin n → R}
    (hy : qv R Q y = π ^ 2 * m) (hy0 : red π y ≠ 0) :
    ((isoSet Q π).filter fun vb => (algebraMap R K π)⁻¹ • cv K y ∈ nbOf K Q π vb).card =
      Fintype.card (Res π) - 1 := by
  rw [← card_line hy0]
  have hy2 : π ^ 2 ∣ qv R Q y := ⟨m, hy⟩
  have hqy : qv (Res π) Q (red π y) = 0 := by
    rw [qv_red, dvd_of_red]; exact (dvd_pow_self _ two_ne_zero).trans hy2
  congr 1
  ext vb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hv, hmem⟩
    obtain ⟨h1, h2⟩ := liftV_spec hπ hdet hv
    unfold nbOf at hmem
    rw [mem_nbLat_iff_of_red_ne_zero hπ h2 hy2 hy0, h1] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc0 : c ≠ 0 := by rintro rfl; exact hy0 (by rw [hc, zero_smul])
    exact ⟨(mem_isoSet.mp hv).1, c⁻¹, by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  · rintro ⟨hv0, c, rfl⟩
    have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
    have hv : c • red π y ∈ isoSet Q π := by
      rw [mem_isoSet, qv_smul, hqy, mul_zero]; exact ⟨hv0, rfl⟩
    refine ⟨hv, ?_⟩
    obtain ⟨h1, h2⟩ := liftV_spec hπ hdet hv
    unfold nbOf
    rw [mem_nbLat_iff_of_red_ne_zero hπ h2 hy2 hy0, h1]
    exact ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

/-- **Neighbours containing $\vec z \in R^n$:** the isotropic $\bar{\vec v} \ne 0$ with $\bar B(\bar{\vec z}, \bar{\vec v}) = 0$. -/
theorem card_mem_cv (hdet : ¬ π ∣ Q.hessian.det) (z : Fin n → R) :
    ((isoSet Q π).filter fun vb => cv K z ∈ nbOf K Q π vb).card =
      ((isoSet Q π).filter fun vb => bv (Res π) Q (red π z) vb = 0).card := by
  congr 1
  ext vb
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hv
  obtain ⟨h1, h2⟩ := liftV_spec hπ hdet hv
  unfold nbOf
  rw [cv_mem_nbLat_iff hπ h2, ← dvd_of_red, ← bv_red, h1]

/-- **The neighbour count of $\frac1\pi\vec y$ at $\pi \nmid m$** ($n$ even, $\operatorname{char}k \ne 2$, $\pi \nmid \det H$,
$Q(\vec y) = \pi^2m$): $(q - 1)$ if $\bar{\vec y} \ne 0$, and $q^{n-2} - 1$ if $\bar{\vec y} = 0$. -/
theorem card_mem_eq_of_not_dvd (hk : ringChar (Res π) ≠ 2) (hdet : ¬ π ∣ Q.hessian.det) (hn2 : 2 ≤ n)
    (hconst : ∀ c : Res π, c ≠ 0 → (Finset.univ.filter fun y => qv (Res π) Q y = c).card =
      (Finset.univ.filter fun y => qv (Res π) Q y = 1).card)
    {m : R} (hm : ¬ π ∣ m) {y : Fin n → R} (hy : qv R Q y = π ^ 2 * m) :
    (((isoSet Q π).filter fun vb => (algebraMap R K π)⁻¹ • cv K y ∈ nbOf K Q π vb).card : ℤ) =
      if red π y = 0 then (Fintype.card (Res π) : ℤ) ^ (n - 2) - 1
      else (Fintype.card (Res π) : ℤ) - 1 := by
  have hq1 : 1 ≤ Fintype.card (Res π) := Fintype.card_pos
  by_cases hy0 : red π y = 0
  · rw [if_pos hy0]
    obtain ⟨z, rfl⟩ := eq_smul_of_red_eq_zero hπ hy0
    have hz : qv R Q z = m := by
      have := hy; rw [qv_smul] at this; exact mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) this
    rw [cv_eq_inv_smul hπ, card_mem_cv (K := K) hfin hπ hdet z]
    have hqz : qv (Res π) Q (red π z) ≠ 0 := by
      rw [qv_red, hz]; exact fun h => hm ((dvd_of_red m).mp h)
    have hperp := card_perp_anisotropic hk (det_res_ne_zero hdet) hn2 hconst hqz
    have hK : ((isoSet Q π).filter fun vb => bv (Res π) Q (red π z) vb = 0).card + 1 =
        (Finset.univ.filter fun y => qv (Res π) Q y = 0 ∧ bv (Res π) Q (red π z) y = 0).card := by
      classical
      have : (Finset.univ.filter fun y => qv (Res π) Q y = 0 ∧ bv (Res π) Q (red π z) y = 0) =
          insert 0 ((isoSet Q π).filter fun vb => bv (Res π) Q (red π z) vb = 0) := by
        ext w; by_cases hw : w = 0
        · subst hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, true_or,
            iff_true]
          exact ⟨qv_zero, bv_zero_right _⟩
        · simp [isoSet, hw]
      rw [this, Finset.card_insert_of_notMem (by simp [isoSet])]
    rw [hperp] at hK
    have : (((isoSet Q π).filter fun vb => bv (Res π) Q (red π z) vb = 0).card : ℤ) =
        (Fintype.card (Res π) : ℤ) ^ (n - 2) - 1 := by
      have := congrArg (fun t : ℕ => (t : ℤ)) hK; push_cast at this; linarith
    exact this
  · rw [if_neg hy0, card_mem_of_red_ne_zero (K := K) hfin hπ hdet hy hy0]
    push_cast [Nat.cast_sub hq1]; ring

/-- **The neighbour relation at $\pi \nmid m$** ($n$ even, $n \ge 2$, $\operatorname{char}k \ne 2$, $\pi \nmid \det H$, `hconst` from
Table 1, finitely many representations): with $q = |k|$,
$$(q - 1)\sum_{L' \sim_\pi R^n} r_{L'}(m) = (q - 1)\,r_Q(\pi^2m) + (q^{n-2} - q)\,r_Q(m).$$ -/
@[kb "eichler1952" "Eichler commutation relation, coefficient level, π ∤ m (over a Dedekind domain) [unverified]"]
theorem sum_latRep_neighbors_of_not_dvd (hk : ringChar (Res π) ≠ 2) (hdet : ¬ π ∣ Q.hessian.det)
    (hn2 : 2 ≤ n)
    (hconst : ∀ c : Res π, c ≠ 0 → (Finset.univ.filter fun y => qv (Res π) Q y = c).card =
      (Finset.univ.filter fun y => qv (Res π) Q y = 1).card)
    {m : R} (hm : ¬ π ∣ m) :
    ((Fintype.card (Res π) : ℤ) - 1) * ∑ L ∈ neighbors K Q π, (latRep K Q L m : ℤ) =
      ((Fintype.card (Res π) : ℤ) - 1) * repNum Q (π ^ 2 * m) +
        ((Fintype.card (Res π) : ℤ) ^ (n - 2) - Fintype.card (Res π)) * repNum Q m := by
  classical
  have hq1 : 1 ≤ Fintype.card (Res π) := Fintype.card_pos
  have h1 := sum_neighbors (K := K) hπ hdet (Q := Q) (fun L => (latRep K Q L m : ℤ))
  rw [nsmul_eq_mul, Nat.cast_sub hq1, Nat.cast_one] at h1
  rw [h1]
  set S := repFinset hfin (π ^ 2 * m)
  have h2 : ∑ vb ∈ isoSet Q π, (latRep K Q (nbOf K Q π vb) m : ℤ) =
      ∑ y ∈ S, (((isoSet Q π).filter fun vb => (algebraMap R K π)⁻¹ • cv K y ∈ nbOf K Q π vb).card : ℤ) := by
    rw [Finset.sum_congr rfl fun vb hvb => by
      rw [latRep_eq_card hfin hπ (nbOf_smul_mem hfin hπ hdet hvb)]]
    simp_rw [Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  rw [h2, Finset.sum_congr rfl fun y hy =>
    card_mem_eq_of_not_dvd hfin hπ hk hdet hn2 hconst hm ((mem_repFinset hfin).mp hy)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_filter_red_eq_zero hfin hπ]
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun y => red π y = 0)
  rw [card_filter_red_eq_zero hfin hπ, card_repFinset] at hsplit
  have : ((S.filter fun y => ¬ red π y = 0).card : ℤ) = repNum Q (π ^ 2 * m) - repNum Q m := by
    have := congrArg (fun t : ℕ => (t : ℤ)) hsplit; push_cast at this; linarith
  simp only [nsmul_eq_mul]
  rw [this]
  ring

end Rep

end QuadFormsKB.Lattices.Nbr
