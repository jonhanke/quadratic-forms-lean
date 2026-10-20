/-
# Kneser neighbours over a Dedekind domain, part 2: $\mathfrak p$-neighbours of $R^n$

**Layer:** $R$ a domain with fraction field $K$ (in the application: $R = \mathcal O_F$, $K = F$), $Q$ a form over $R$ (`QuadForm R n`, the
Gram form of a free lattice), lattices are $R$-submodules of $K^n$, the base lattice is $L = R^n$ (`stdLat`). $\pi \in R$ is a
prime with finite residue field $k = R/\pi$ (`Res π`) of size $q$, and $\pi \nmid \det H$ ($H$ the Hessian): $L_\mathfrak p$ is
unimodular, $\mathfrak p = (\pi)$ is a good prime.

**Defines** (Kneser 1957, §1; AWS notes `hanke2011aws`, Def. 1.10.1, p. 22, for $R = \mathbb Z$) the **$\pi$-neighbours** of $L$
(`IsNbr`): lattices $L'$ with
$$[L : L \cap L'] = q,\qquad [L' : L \cap L'] = q,\qquad \pi L' \subseteq L,\qquad Q(L') \subseteq R;$$
and the explicit neighbour (`nbLat`)
$$L(\vec v) = L_{\vec v} + R\,\tfrac1\pi\vec v,\qquad L_{\vec v} = \{\vec y \in R^n : \pi \mid B(\vec y, \vec v)\},$$
for $\vec v \in R^n$, $\vec v \not\equiv 0 \pmod\pi$, $\pi^2 \mid Q(\vec v)$.

**Proves**, for $\pi \nmid \det H$:
- `isNbr_nbLat`: $L(\vec v)$ is a $\pi$-neighbour; `exists_eq_nbLat`: every $\pi$-neighbour is some $L(\vec v)$;
- `mem_nbLat_iff`: $\frac1\pi\vec y \in L(\vec v) \iff \vec y \equiv c\vec v \pmod\pi$ for some $c$ and $\pi^2 \mid B(\vec y, \vec v)$; so $L(\vec v)$
  depends only on the line $k\bar{\vec v}$ (`nbLat_eq_of_line`), and different lines give different neighbours (`line_eq_of_nbLat_eq`);
- `exists_lift`: every nonzero isotropic $\bar{\vec v} \in k^n$ lifts to $\vec v$ with $\pi^2 \mid Q(\vec v)$;
- `card_neighbors`: $(q - 1)\cdot\#\{\pi\text{-neighbours}\} = \#\{\bar{\vec v} \ne 0 : \bar Q(\bar{\vec v}) = 0\}$ (the isotropic lines of $L/\pi L$).

These generalize `Siegel/Neighbors.lean` ($R = \mathbb Z$) verbatim, with $p \mapsto \pi$, $\mathbb F_p \mapsto k$.
-/
import QuadFormsKB.Lattices.NeighborCount

open Matrix

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

namespace QuadFormsKB.Lattices.Nbr

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ}

/-! ### Integral vectors in $K^n$ -/

section Basic

variable (K) in
/-- The vector $\vec y \in R^n$ as a vector of $K^n$. -/
def cv (y : Fin n → R) : Fin n → K := fun i => algebraMap R K (y i)

@[simp] theorem cv_apply (y : Fin n → R) (i : Fin n) : cv K y i = algebraMap R K (y i) := rfl
theorem cv_add (y z : Fin n → R) : cv K (y + z) = cv K y + cv K z := by ext i; simp
theorem cv_smul (c : R) (y : Fin n → R) : cv K (c • y) = (algebraMap R K c) • cv K y := by ext i; simp
theorem cv_zero : cv (R := R) K (0 : Fin n → R) = 0 := by ext i; simp
theorem cv_sub (y z : Fin n → R) : cv K (y - z) = cv K y - cv K z := by ext i; simp
theorem cv_injective : Function.Injective (cv (R := R) K (n := n)) := fun y z h => by
  ext i; exact IsFractionRing.injective R K (congrFun h i)

variable (R K) in
/-- **The standard lattice** $L = R^n \subset K^n$. -/
def stdLat (n : ℕ) : Submodule R (Fin n → K) where
  carrier := {x | ∃ y : Fin n → R, x = cv K y}
  add_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩; exact ⟨y + z, (cv_add y z).symm⟩
  zero_mem' := ⟨0, cv_zero.symm⟩
  smul_mem' := by
    rintro c _ ⟨y, rfl⟩; refine ⟨c • y, ?_⟩; rw [cv_smul, algebra_compatible_smul K c]

theorem mem_stdLat {x : Fin n → K} : x ∈ stdLat R K n ↔ ∃ y : Fin n → R, x = cv K y := Iff.rfl

theorem cv_mem_stdLat (y : Fin n → R) : cv K y ∈ stdLat R K n := ⟨y, rfl⟩

variable (Q : QuadForm R n)

theorem qv_cv (y : Fin n → R) : qv K Q (cv K y) = algebraMap R K (qv R Q y) :=
  qv_map (S := R) (T := K) y

theorem bv_cv (y v : Fin n → R) : bv K Q (cv K y) (cv K v) = algebraMap R K (bv R Q y v) :=
  bv_map (S := R) (T := K) y v

theorem eval_smul' (c : R) (z : Fin n → R) : qv R Q (c • z) = c ^ 2 * qv R Q z := qv_smul z c

end Basic

/-! ### The explicit neighbour -/

variable (Q : QuadForm R n) (π : R)

/-- **The explicit $\pi$-neighbour** $L(\vec v) = L_{\vec v} + R\frac1\pi\vec v$, $L_{\vec v} = \{\vec y \in R^n : \pi \mid B(\vec y, \vec v)\}$ (Kneser
1957; AWS notes, §1.10.1, Thm. 1.10.2, p. 22): the vectors $\vec y + \frac c\pi\vec v$ with $\vec y \in R^n$, $\pi \mid B(\vec y, \vec v)$, $c \in R$.
A $\pi$-neighbour when $\vec v \not\equiv 0 \pmod \pi$ and $\pi^2 \mid Q(\vec v)$ (`isNbr_nbLat`). -/
@[kb "kneser1957" "§1, the neighbour L(v) [unverified]"]
def nbLat (v : Fin n → R) : Submodule R (Fin n → K) where
  carrier := {x | ∃ y : Fin n → R, ∃ c : R, π ∣ bv R Q y v ∧
    x = cv K y + (algebraMap R K c / algebraMap R K π) • cv K v}
  add_mem' := by
    rintro _ _ ⟨y, c, hy, rfl⟩ ⟨y', c', hy', rfl⟩
    refine ⟨y + y', c + c', by rw [bv_add_left]; exact dvd_add hy hy', ?_⟩
    rw [cv_add, map_add, add_div, add_smul]; abel
  zero_mem' := ⟨0, 0, by simp [bv], by simp [cv_zero]⟩
  smul_mem' := by
    rintro c _ ⟨y, d, hy, rfl⟩
    refine ⟨c • y, c * d, by rw [bv_smul_left]; exact dvd_mul_of_dvd_right hy c, ?_⟩
    rw [cv_smul, algebra_compatible_smul K c, smul_add, smul_smul, map_mul, mul_div_assoc]

section Lattice

variable {Q π}
variable (hπ : Prime π)
include hπ

omit [IsFractionRing R K] in
theorem πK_ne_zero [IsFractionRing R K] : algebraMap R K π ≠ 0 := by
  intro h; exact hπ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))

/-- Every element of $L(\vec v)$ is $\frac1\pi\vec y$ with $\vec y \in R^n$. -/
theorem exists_eq_of_mem_nbLat {v : Fin n → R} {x : Fin n → K} (hx : x ∈ nbLat (K := K) Q π v) :
    ∃ y : Fin n → R, x = (algebraMap R K π)⁻¹ • cv K y := by
  obtain ⟨y, c, -, rfl⟩ := hx
  refine ⟨π • y + c • v, ?_⟩
  have h0 := πK_ne_zero (K := K) hπ
  rw [cv_add, cv_smul, cv_smul, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ h0, one_smul, div_eq_mul_inv,
    mul_comm]

/-- **Membership in $L(\vec v)$** ($\pi^2 \mid Q(\vec v)$): $\frac1\pi\vec y \in L(\vec v)$ iff $\vec y \equiv c\vec v \pmod\pi$ for some
$c \in R$ and $\pi^2 \mid B(\vec y, \vec v)$. -/
theorem mem_nbLat_iff {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) (y : Fin n → R) :
    (algebraMap R K π)⁻¹ • cv K y ∈ nbLat (K := K) Q π v ↔
      (∃ c : R, ∃ z : Fin n → R, y = c • v + π • z) ∧ π ^ 2 ∣ bv R Q y v := by
  have h0 := πK_ne_zero (K := K) hπ
  constructor
  · rintro ⟨z, c, hz, he⟩
    have hy : y = c • v + π • z := by
      apply cv_injective (K := K)
      have := congrArg (fun w => (algebraMap R K π) • w) he
      simp only [smul_smul, smul_add, mul_inv_cancel₀ h0, one_smul] at this
      rw [this, cv_add, cv_smul, cv_smul, mul_div_cancel₀ _ h0]; abel
    refine ⟨⟨c, z, hy⟩, ?_⟩
    obtain ⟨e, he'⟩ := hz
    obtain ⟨d, hd⟩ := hv
    rw [hy, bv_add_left, bv_smul_left, bv_smul_left, bv_self, hd, he']
    exact ⟨2 * c * d + e, by ring⟩
  · rintro ⟨⟨c, z, hy⟩, hb⟩
    refine ⟨z, c, ?_, ?_⟩
    · obtain ⟨d, hd⟩ := hv
      rw [hy, bv_add_left, bv_smul_left, bv_smul_left, bv_self, hd] at hb
      obtain ⟨e, he⟩ := hb
      refine ⟨e - 2 * c * d, ?_⟩
      apply mul_left_cancel₀ hπ.ne_zero
      linear_combination he
    · rw [hy, cv_add, cv_smul, cv_smul, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ h0, one_smul,
        add_comm, div_eq_mul_inv, mul_comm (algebraMap R K c)]

/-- **Integrality of $L(\vec v)$** ($\pi^2 \mid Q(\vec v)$): $Q(\vec y + \frac c\pi\vec v) = Q(\vec y) + \frac c\pi B(\vec y, \vec v) + \frac{c^2}{\pi^2}Q(\vec v) \in R$. -/
theorem nbLat_integral {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) :
    ∀ x ∈ nbLat (K := K) Q π v, ∃ z : R, qv K Q x = algebraMap R K z := by
  rintro _ ⟨y, c, ⟨e, he⟩, rfl⟩
  obtain ⟨d, hd⟩ := hv
  have h0 := πK_ne_zero (K := K) hπ
  refine ⟨qv R Q y + c * e + c ^ 2 * d, ?_⟩
  rw [qv_add_smul, qv_cv, qv_cv, bv_cv, he, hd]
  simp only [map_add, map_mul, map_pow]
  field_simp

end Lattice

/-! ### Reduction mod $\pi$ -/

/-- **The residue ring** $k = R/\pi R$. -/
abbrev Res (π : R) : Type _ := R ⧸ Ideal.span {π}

/-- **The reduction of an integral vector mod $\pi$.** -/
def red (π : R) (y : Fin n → R) : Fin n → Res π := fun i => Ideal.Quotient.mk _ (y i)

section Red

variable {Q π}

theorem red_add (y z : Fin n → R) : red π (y + z) = red π y + red π z := by ext i; simp [red]
theorem red_smul (c : R) (y : Fin n → R) : red π (c • y) = (Ideal.Quotient.mk (Ideal.span {π}) c) • red π y := by
  ext i; simp [red]

theorem dvd_of_red (z : R) : Ideal.Quotient.mk (Ideal.span {π}) z = 0 ↔ π ∣ z := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem red_eq_zero_iff (y : Fin n → R) : red π y = 0 ↔ ∀ i, π ∣ y i := by
  simp only [funext_iff, red, Pi.zero_apply, dvd_of_red]

theorem qv_red (y : Fin n → R) : qv (Res π) Q (red π y) = Ideal.Quotient.mk _ (qv R Q y) :=
  qv_map (S := R) (T := Res π) y

theorem bv_red (y v : Fin n → R) :
    bv (Res π) Q (red π y) (red π v) = Ideal.Quotient.mk _ (bv R Q y v) :=
  bv_map (S := R) (T := Res π) y v

/-- $\vec y \equiv c\vec v \pmod\pi$ for some $c \in R$ iff $\bar{\vec y} \in k\bar{\vec v}$. -/
theorem exists_congr_iff (y v : Fin n → R) :
    (∃ c : R, ∃ z : Fin n → R, y = c • v + π • z) ↔ ∃ c : Res π, red π y = c • red π v := by
  constructor
  · rintro ⟨c, z, rfl⟩
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [red_add, red_smul, red_smul]
    simp [(dvd_of_red π).mpr (dvd_refl π)]
  · rintro ⟨c, hc⟩
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h : ∀ i, π ∣ y i - c' * v i := by
      intro i
      rw [← dvd_of_red]
      have := congrFun hc i
      simp only [red, Pi.smul_apply, smul_eq_mul] at this
      rw [map_sub, map_mul, this, sub_self]
    refine ⟨c', fun i => (h i).choose, ?_⟩
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← (h i).choose_spec]; ring

end Red

section Lattice2

variable {Q π}
variable (hπ : Prime π)
include hπ

/-- **Membership of $\frac1\pi\vec y$ for $\bar{\vec y} \ne 0$** ($\pi^2 \mid Q(\vec v)$, $\pi^2 \mid Q(\vec y)$): $\frac1\pi\vec y \in L(\vec v)$ iff
$\bar{\vec y} \in k\bar{\vec v}$ (the condition $\pi^2 \mid B(\vec y, \vec v)$ is then automatic). -/
theorem mem_nbLat_iff_of_red_ne_zero {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) {y : Fin n → R}
    (hy : π ^ 2 ∣ qv R Q y) (hy0 : red π y ≠ 0) :
    (algebraMap R K π)⁻¹ • cv K y ∈ nbLat (K := K) Q π v ↔ ∃ c : Res π, red π y = c • red π v := by
  rw [mem_nbLat_iff hπ hv, ← exists_congr_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨c, z, rfl⟩ := h
  have hc : ¬ π ∣ c := by
    intro hc
    apply hy0
    rw [red_add, red_smul, red_smul, (dvd_of_red (π := π) c).mpr hc, (dvd_of_red (π := π) π).mpr (dvd_refl π)]
    simp
  have e := qv_add_smul (S := R) (Q := Q) (c • v) z π
  simp only [qv_smul, bv_smul_left] at e
  obtain ⟨d, hd⟩ := hv
  obtain ⟨f, hf⟩ := hy
  have h1 : π ∣ c * bv R Q v z := by
    have : π ^ 2 * (f - c ^ 2 * d - qv R Q z) = π * (c * bv R Q v z) := by
      linear_combination -hf + e + c ^ 2 * hd
    have h2 : π * π ∣ π * (c * bv R Q v z) :=
      ⟨f - c ^ 2 * d - qv R Q z, by rw [← this]; ring⟩
    exact (mul_dvd_mul_iff_left hπ.ne_zero).mp h2
  have h2 : π ∣ bv R Q v z := (hπ.dvd_or_dvd h1).resolve_left hc
  obtain ⟨b, hb⟩ := h2
  rw [bv_add_left, bv_smul_left, bv_smul_left, bv_self, hd, bv_comm, hb]
  exact ⟨2 * c * d + b, by ring⟩

/-- **Membership of $\vec z \in R^n$** ($\pi^2 \mid Q(\vec v)$): $\vec z \in L(\vec v)$ iff $\pi \mid B(\vec z, \vec v)$. -/
theorem cv_mem_nbLat_iff {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) (z : Fin n → R) :
    cv K z ∈ nbLat (K := K) Q π v ↔ π ∣ bv R Q z v := by
  have h0 := πK_ne_zero (K := K) hπ
  have e : cv K z = (algebraMap R K π)⁻¹ • cv K (π • z) := by
    rw [cv_smul, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [e, mem_nbLat_iff hπ hv]
  constructor
  · rintro ⟨-, h⟩
    rw [bv_smul_left, sq] at h
    exact (mul_dvd_mul_iff_left hπ.ne_zero).mp h
  · intro h
    refine ⟨⟨0, z, by simp⟩, ?_⟩
    rw [bv_smul_left, sq]
    exact mul_dvd_mul_left _ h

theorem smul_cv_mem_nbLat {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) (z : Fin n → R) :
    cv K (π • z) ∈ nbLat (K := K) Q π v := by
  rw [cv_mem_nbLat_iff hπ hv, bv_smul_left]; exact dvd_mul_right _ _

end Lattice2

/-! ### Lines and neighbours -/

section Lines

variable {Q π}
variable (hπ : Prime π)
include hπ

theorem eq_smul_of_red_eq_zero {y : Fin n → R} (hy : red π y = 0) :
    ∃ z : Fin n → R, y = π • z := by
  have h := (red_eq_zero_iff y).mp hy
  refine ⟨fun i => (h i).choose, ?_⟩
  ext i; simp only [Pi.smul_apply, smul_eq_mul]; exact (h i).choose_spec

theorem cv_eq_inv_smul (z : Fin n → R) :
    (algebraMap R K π)⁻¹ • cv K (π • z) = cv K z := by
  rw [cv_smul, smul_smul, inv_mul_cancel₀ (πK_ne_zero (K := K) hπ), one_smul]

theorem qv_of_mem_nbLat {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) {y : Fin n → R}
    (hx : (algebraMap R K π)⁻¹ • cv K y ∈ nbLat (K := K) Q π v) : π ^ 2 ∣ qv R Q y := by
  obtain ⟨m, hm⟩ := nbLat_integral (K := K) hπ hv _ hx
  have h0 := πK_ne_zero (K := K) hπ
  rw [qv_smul, qv_cv] at hm
  refine ⟨m, IsFractionRing.injective R K ?_⟩
  rw [map_mul, map_pow]
  field_simp at hm
  linear_combination hm

/-- **$L(\vec v)$ depends only on the line $k\bar{\vec v}$:** if $\pi^2 \mid Q(\vec v), Q(\vec w)$ and $\bar{\vec w} = c\bar{\vec v}$ with
$c \ne 0$, then $L(\vec w) = L(\vec v)$. -/
theorem nbLat_eq_of_line {v w : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) (hw : π ^ 2 ∣ qv R Q w)
    {c : Res π} (hc : IsUnit c) (hwv : red π w = c • red π v) :
    nbLat (K := K) Q π w = nbLat (K := K) Q π v := by
  -- a symmetric statement, proved in one direction
  have key : ∀ {v w : Fin n → R}, π ^ 2 ∣ qv R Q v → π ^ 2 ∣ qv R Q w → ∀ {c : Res π}, IsUnit c →
      red π w = c • red π v → nbLat (K := K) Q π w ≤ nbLat (K := K) Q π v := by
    intro v w hv hw c hc hwv x hx
    obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
    have hy2 := qv_of_mem_nbLat hπ hw hx
    by_cases hy0 : red π y = 0
    · obtain ⟨z, rfl⟩ := eq_smul_of_red_eq_zero hπ hy0
      rw [cv_eq_inv_smul hπ] at hx ⊢
      rw [cv_mem_nbLat_iff hπ hw] at hx
      rw [cv_mem_nbLat_iff hπ hv, ← dvd_of_red, ← bv_red]
      rw [← dvd_of_red, ← bv_red, hwv, bv_smul_right] at hx
      exact (hc.mul_right_eq_zero).mp hx
    · rw [mem_nbLat_iff_of_red_ne_zero hπ hw hy2 hy0] at hx
      rw [mem_nbLat_iff_of_red_ne_zero hπ hv hy2 hy0]
      obtain ⟨d, hd⟩ := hx
      exact ⟨d * c, by rw [hd, hwv, smul_smul]⟩
  refine le_antisymm (key hv hw hc hwv) (key hw hv hc.unit⁻¹.isUnit ?_)
  rw [hwv, smul_smul]
  simp

/-- **Different lines give different neighbours:** if $L(\vec w) = L(\vec v)$ (with $\pi^2 \mid Q(\vec v), Q(\vec w)$, $\bar{\vec w} \ne 0$)
then $\bar{\vec w} \in k\bar{\vec v}$. -/
theorem line_eq_of_nbLat_eq {v w : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) (hw : π ^ 2 ∣ qv R Q w)
    (hw0 : red π w ≠ 0) (h : nbLat (K := K) Q π w = nbLat (K := K) Q π v) :
    ∃ c : Res π, red π w = c • red π v := by
  have hmem : (algebraMap R K π)⁻¹ • cv K w ∈ nbLat (K := K) Q π w := by
    rw [mem_nbLat_iff hπ hw]
    refine ⟨⟨1, 0, by simp⟩, ?_⟩
    rw [bv_self]; obtain ⟨d, hd⟩ := hw; exact ⟨2 * d, by rw [hd]; ring⟩
  rw [h, mem_nbLat_iff_of_red_ne_zero hπ hv hw hw0] at hmem
  exact hmem

theorem inv_smul_mem_nbLat {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) :
    (algebraMap R K π)⁻¹ • cv K v ∈ nbLat (K := K) Q π v := by
  rw [mem_nbLat_iff hπ hv]
  refine ⟨⟨1, 0, by simp⟩, ?_⟩
  rw [bv_self]; obtain ⟨d, hd⟩ := hv; exact ⟨2 * d, by rw [hd]; ring⟩

end Lines

/-! ### Indices -/

section Index

variable {Q π}

/-- **An index computed by a surjection onto $k$:** if $f : M \to k$ is a surjective homomorphism with kernel $H \cap M$, then
$[M : H \cap M] = |k|$. -/
theorem relIndex_eq_of_hom {G : Type*} [AddCommGroup G] (H M : AddSubgroup G) (f : M →+ Res π)
    (hf : Function.Surjective f) (hker : ∀ x : M, f x = 0 ↔ (x : G) ∈ H) :
    H.relIndex M = Nat.card (Res π) := by
  have e : H.addSubgroupOf M = f.ker := by
    ext x; rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hker]
  rw [AddSubgroup.relIndex, e, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    AddSubgroup.card_top]

variable (R) in
open Classical in
/-- The integral vector of a vector of $R^n \subset K^n$ (junk $0$ outside). -/
noncomputable def toR (x : Fin n → K) : Fin n → R :=
  if h : ∃ y : Fin n → R, x = cv K y then h.choose else 0

@[simp] theorem toR_cv (y : Fin n → R) : toR R (cv K y) = y := by
  have h : ∃ y' : Fin n → R, cv K y = cv K y' := ⟨y, rfl⟩
  unfold toR; rw [dif_pos h]; exact (cv_injective h.choose_spec).symm

theorem cv_toR {x : Fin n → K} (hx : x ∈ stdLat R K n) : cv K (toR R x) = x := by
  obtain ⟨y, rfl⟩ := hx; simp

/-- A lift $R^n \to$ of a vector of $k^n$. -/
noncomputable def liftRes (vb : Fin n → Res π) : Fin n → R := fun i => (Ideal.Quotient.mk_surjective (vb i)).choose

@[simp] theorem red_liftRes (vb : Fin n → Res π) : red π (liftRes vb) = vb := by
  ext i; exact (Ideal.Quotient.mk_surjective (vb i)).choose_spec

variable [(Ideal.span {π}).IsMaximal] [Fintype (Res π)] [DecidableEq (Res π)]

theorem det_res_ne_zero (hdet : ¬ π ∣ Q.hessian.det) :
    (Q.hessian.map (algebraMap R (Res π))).det ≠ 0 := by
  have e : (Q.hessian.map (algebraMap R (Res π))).det = algebraMap R (Res π) Q.hessian.det :=
    (RingHom.map_det _ _).symm
  rw [e]
  intro h; exact hdet ((dvd_of_red _).mp h)

/-- **$\vec v \not\equiv 0$ has a vector with $B(\vec z, \vec v) \equiv 1 \pmod\pi$** ($\pi \nmid \det H$). -/
theorem exists_bv_eq_one (hdet : ¬ π ∣ Q.hessian.det) {v : Fin n → R} (hv0 : red π v ≠ 0) :
    ∃ z : Fin n → R, Ideal.Quotient.mk (Ideal.span {π}) (bv R Q z v) = 1 := by
  have hc := card_bv_eq (k := Res π) (Q := Q) (det_res_ne_zero hdet) hv0 (1 : Res π)
  have hpos : 0 < (Finset.univ.filter fun y => bv (Res π) Q (red π v) y = 1).card := by
    rw [hc]; exact pow_pos Fintype.card_pos _
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hy
  replace hy := hy.2
  refine ⟨liftRes y, ?_⟩
  rw [← bv_red, red_liftRes, bv_comm, hy]

variable (hπ : Prime π)
include hπ

theorem relIndex_nbLat_std (hdet : ¬ π ∣ Q.hessian.det) {v : Fin n → R}
    (hv : π ^ 2 ∣ qv R Q v) (hv0 : red π v ≠ 0) :
    (nbLat (K := K) Q π v).toAddSubgroup.relIndex (stdLat R K n).toAddSubgroup = Nat.card (Res π) := by
  let f : (stdLat R K n).toAddSubgroup →+ Res π :=
    { toFun := fun x => Ideal.Quotient.mk _ (bv R Q (toR R (x : Fin n → K)) v)
      map_zero' := by
        have : toR R (0 : Fin n → K) = (0 : Fin n → R) := by rw [← cv_zero (R := R), toR_cv]
        simp [this, bv]
      map_add' := by
        rintro ⟨_, y, rfl⟩ ⟨_, z, rfl⟩
        simp only [AddSubgroup.coe_add]
        rw [← cv_add, toR_cv, toR_cv, toR_cv, bv_add_left, map_add] }
  refine relIndex_eq_of_hom _ _ f ?_ ?_
  · obtain ⟨z, hz⟩ := exists_bv_eq_one hdet hv0
    intro t
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨⟨cv K (t' • z), _, rfl⟩, ?_⟩
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toR_cv, bv_smul_left, map_mul, hz, mul_one]
  · rintro ⟨_, y, rfl⟩
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toR_cv, Submodule.mem_toAddSubgroup]
    rw [dvd_of_red, cv_mem_nbLat_iff hπ hv]

theorem relIndex_std_nbLat {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v) (hv0 : red π v ≠ 0) :
    (stdLat R K n).toAddSubgroup.relIndex (nbLat (K := K) Q π v).toAddSubgroup = Nat.card (Res π) := by
  have h0 := πK_ne_zero (K := K) hπ
  obtain ⟨i0, hi0⟩ : ∃ i, red π v i ≠ 0 := by
    by_contra h; push Not at h; exact hv0 (funext h)
  have hpx : ∀ x ∈ nbLat (K := K) Q π v, (algebraMap R K π) • x ∈ stdLat R K n := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
    refine ⟨y, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
  let f : (nbLat (K := K) Q π v).toAddSubgroup →+ Res π :=
    { toFun := fun x => Ideal.Quotient.mk _ (toR R ((algebraMap R K π) • (x : Fin n → K)) i0) * (red π v i0)⁻¹
      map_zero' := by
        have : toR R (0 : Fin n → K) = (0 : Fin n → R) := by rw [← cv_zero (R := R), toR_cv]
        simp [this]
      map_add' := by
        rintro ⟨x, hx⟩ ⟨x', hx'⟩
        simp only [AddSubgroup.coe_add]
        obtain ⟨y, hy⟩ := hpx x hx
        obtain ⟨y', hy'⟩ := hpx x' hx'
        rw [smul_add, hy, hy', ← cv_add, toR_cv, toR_cv, toR_cv]
        simp only [Pi.add_apply, map_add]; ring }
  have key : ∀ y : Fin n → R, toR R ((algebraMap R K π) • ((algebraMap R K π)⁻¹ • cv K y)) = y := by
    intro y
    rw [smul_smul, mul_inv_cancel₀ h0, one_smul, toR_cv]
  refine relIndex_eq_of_hom _ _ f ?_ ?_
  · have hmem := inv_smul_mem_nbLat (K := K) hπ hv
    intro t
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨⟨t' • ((algebraMap R K π)⁻¹ • cv K v), (nbLat (K := K) Q π v).smul_mem t' hmem⟩, ?_⟩
    have e : (algebraMap R K π) • (t' • ((algebraMap R K π)⁻¹ • cv K v)) = cv K (t' • v) := by
      rw [cv_smul, algebra_compatible_smul K t', smul_smul, smul_smul]
      congr 1
      field_simp
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [e, toR_cv, Pi.smul_apply, smul_eq_mul, map_mul]
    change _ * red π v i0 * (red π v i0)⁻¹ = _
    rw [mul_assoc, mul_inv_cancel₀ hi0, mul_one]
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Submodule.mem_toAddSubgroup]
    rw [key y]
    have hx' : (algebraMap R K π)⁻¹ • cv K y ∈ nbLat (K := K) Q π v := hx
    rw [mem_nbLat_iff hπ hv, exists_congr_iff] at hx'
    obtain ⟨⟨c, hc⟩, -⟩ := hx'
    have hyi : Ideal.Quotient.mk (Ideal.span {π}) (y i0) = c * red π v i0 := by
      have := congrFun hc i0; simpa [red] using this
    rw [hyi, mul_assoc, mul_inv_cancel₀ hi0, mul_one]
    constructor
    · intro hc0
      have hy0 : red π y = 0 := by rw [hc, hc0, zero_smul]
      obtain ⟨z, rfl⟩ := eq_smul_of_red_eq_zero hπ hy0
      rw [cv_eq_inv_smul hπ]; exact cv_mem_stdLat z
    · rintro ⟨w, hw⟩
      have hy : y = π • w := by
        apply cv_injective (K := K)
        rw [cv_smul, ← hw, smul_smul, mul_inv_cancel₀ h0, one_smul]
      have : red π y = 0 := by
        rw [hy, red_smul, (dvd_of_red (π := π) π).mpr (dvd_refl π), zero_smul]
      rw [hc] at this
      by_contra hc0
      exact hv0 (by
        have := congrArg (fun u => c⁻¹ • u) this
        simpa [smul_smul, inv_mul_cancel₀ hc0] using this)

end Index

/-! ### Neighbours -/

variable (K) in
/-- **$\pi$-neighbours of $L = R^n$** (Kneser 1957, §1; AWS notes, Def. 1.10.1, p. 22, for $R = \mathbb Z$): a lattice $L' \subset K^n$ with
$$[L : L \cap L'] = q,\qquad [L' : L \cap L'] = q,\qquad \pi L' \subseteq L,\qquad Q(L') \subseteq R,$$
$q = |R/\pi|$. Fields: `relIndex_std` ($[L : L \cap L'] = q$; Mathlib's `relIndex H M` is $[M : H \cap M]$), `relIndex_self`
($[L' : L \cap L'] = q$), `smul_mem` ($\pi L' \subseteq L$; automatic over $\mathbb Z$, where it follows from the index), `integral`
($Q(\vec x) \in R$ for $\vec x \in L'$). -/
@[kb "kneser1957" "§1, π-neighbours [unverified]"]
structure IsNbr (Q : QuadForm R n) (π : R) (L' : Submodule R (Fin n → K)) : Prop where
  relIndex_std : L'.toAddSubgroup.relIndex (stdLat R K n).toAddSubgroup = Nat.card (Res π)
  relIndex_self : (stdLat R K n).toAddSubgroup.relIndex L'.toAddSubgroup = Nat.card (Res π)
  smul_mem : ∀ x ∈ L', algebraMap R K π • x ∈ stdLat R K n
  integral : ∀ x ∈ L', ∃ z : R, qv K Q x = algebraMap R K z

section Nbr

variable {Q π}
variable [(Ideal.span {π}).IsMaximal] [Fintype (Res π)] [DecidableEq (Res π)]
variable (hπ : Prime π)
include hπ

/-- **$L(\vec v)$ is a $\pi$-neighbour of $R^n$** ($\pi \nmid \det H$, $\vec v \not\equiv 0$, $\pi^2 \mid Q(\vec v)$). -/
@[kb "kneser1957" "§1, L(v) is a neighbour [unverified]"]
theorem isNbr_nbLat (hdet : ¬ π ∣ Q.hessian.det) {v : Fin n → R}
    (hv : π ^ 2 ∣ qv R Q v) (hv0 : red π v ≠ 0) : IsNbr K Q π (nbLat (K := K) Q π v) := by
  refine ⟨relIndex_nbLat_std hπ hdet hv hv0, relIndex_std_nbLat hπ hv hv0, fun x hx => ?_,
    nbLat_integral hπ hv⟩
  obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
  refine ⟨y, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ (πK_ne_zero hπ), one_smul]

theorem one_lt_card_res : 1 < Nat.card (Res π) := by
  rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card

/-- **Every $\pi$-neighbour is explicit** (Kneser 1957; AWS notes, §1.10.1, Thm. 1.10.2, p. 22): if $\pi \nmid \det H$ and $L'$ is a
$\pi$-neighbour of $R^n$, then $L' = L(\vec v)$ for some $\vec v \in R^n$, $\vec v \not\equiv 0 \pmod\pi$, $\pi^2 \mid Q(\vec v)$
(namely $\vec v = \pi\vec w$ for any $\vec w \in L' \setminus R^n$). *Proof* as over $\mathbb Z$ (`Siegel.Kneser.exists_eq_nbLat`): integrality
gives $L \cap L' \subseteq L_{\vec v}$, equal by the index; then $L(\vec v) \subseteq L'$, equal by the index. -/
@[kb "kneser1957" "§1, every neighbour is some L(v) [unverified]"]
theorem exists_eq_nbLat (hdet : ¬ π ∣ Q.hessian.det) {L : Submodule R (Fin n → K)}
    (hL : IsNbr K Q π L) : ∃ v : Fin n → R, π ^ 2 ∣ qv R Q v ∧ red π v ≠ 0 ∧ L = nbLat (K := K) Q π v := by
  have h0 := πK_ne_zero (K := K) hπ
  have hq1 := one_lt_card_res (π := π) hπ
  set S := (stdLat R K n).toAddSubgroup
  set LA := L.toAddSubgroup
  obtain ⟨w, hwL, hwS⟩ : ∃ w ∈ L, w ∉ stdLat R K n := by
    by_contra h
    push Not at h
    have : S.relIndex LA = 1 := AddSubgroup.relIndex_eq_one.mpr fun x hx => h x hx
    have := hL.relIndex_self.symm.trans this
    omega
  obtain ⟨v, hv⟩ := hL.smul_mem w hwL
  have hw : w = (algebraMap R K π)⁻¹ • cv K v := by
    rw [← hv, smul_smul, inv_mul_cancel₀ h0, one_smul]
  obtain ⟨m, hm⟩ := hL.integral w hwL
  have hQv : qv R Q v = π ^ 2 * m := by
    have h := hm
    rw [hw, qv_smul, qv_cv] at h
    apply IsFractionRing.injective R K
    rw [map_mul, map_pow]
    field_simp at h
    linear_combination h
  have hv2 : π ^ 2 ∣ qv R Q v := ⟨m, hQv⟩
  have hv0 : red π v ≠ 0 := by
    intro h0'
    apply hwS
    obtain ⟨z, rfl⟩ := eq_smul_of_red_eq_zero hπ h0'
    rw [hw, cv_eq_inv_smul hπ]; exact cv_mem_stdLat z
  refine ⟨v, hv2, hv0, ?_⟩
  set N := nbLat (K := K) Q π v
  set NA := N.toAddSubgroup
  have hsub : LA ⊓ S ≤ NA ⊓ S := by
    rintro x ⟨hxL, z, rfl⟩
    refine ⟨?_, z, rfl⟩
    change cv K z ∈ N
    rw [cv_mem_nbLat_iff hπ hv2]
    obtain ⟨a, ha⟩ := hL.integral _ (L.add_mem hxL hwL)
    obtain ⟨b, hb⟩ := hL.integral _ hxL
    have hpol := qv_add_smul (S := K) (Q := Q) (cv K z) w 1
    rw [one_smul, one_mul, one_pow, one_mul, ha, hb, hm] at hpol
    have hB : bv K Q (cv K z) (cv K v) = algebraMap R K (π * (a - b - m)) := by
      rw [← hv, bv_smul_right, map_mul, map_sub, map_sub]
      linear_combination (-(algebraMap R K π)) * hpol
    rw [bv_cv] at hB
    exact ⟨a - b - m, IsFractionRing.injective R K hB⟩
  have hNstd := relIndex_nbLat_std (K := K) hπ hdet hv2 hv0
  have hstdN := relIndex_std_nbLat (K := K) hπ hv2 hv0
  have hsub' : NA ⊓ S ≤ LA ⊓ S := by
    have h1 := AddSubgroup.relIndex_mul_relIndex (LA ⊓ S) (NA ⊓ S) S hsub inf_le_right
    rw [AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_right, hNstd, hL.relIndex_std] at h1
    have : (LA ⊓ S).relIndex (NA ⊓ S) = 1 := (Nat.mul_eq_right (by omega)).mp h1
    exact AddSubgroup.relIndex_eq_one.mp this |>.trans inf_le_left |> fun h => le_inf h inf_le_right
  have hNL : NA ≤ LA := by
    rintro _ ⟨z, c, hz, rfl⟩
    have hzL : cv K z ∈ L := (hsub' ⟨(cv_mem_nbLat_iff hπ hv2 z).mpr hz, z, rfl⟩).1
    have : (algebraMap R K c / algebraMap R K π) • cv K v = c • w := by
      rw [hw, algebra_compatible_smul K c, smul_smul, div_eq_mul_inv]
    change cv K z + (algebraMap R K c / algebraMap R K π) • cv K v ∈ L
    rw [this]
    exact L.add_mem hzL (L.smul_mem c hwL)
  have hLN : LA ≤ NA := by
    have h1 := AddSubgroup.relIndex_mul_relIndex (S ⊓ NA) NA LA inf_le_right hNL
    have e : S ⊓ NA = S ⊓ LA := by
      rw [inf_comm, inf_comm S LA]; exact le_antisymm hsub' hsub
    rw [AddSubgroup.inf_relIndex_right, hstdN, e, AddSubgroup.inf_relIndex_right, hL.relIndex_self] at h1
    have : NA.relIndex LA = 1 := (Nat.mul_eq_left (by omega)).mp h1
    exact AddSubgroup.relIndex_eq_one.mp this
  exact le_antisymm (fun x hx => hLN hx) (fun x hx => hNL hx)

/-- **Lifting isotropic vectors** ($\pi \nmid \det H$): every $\bar{\vec v} \in k^n \setminus 0$ with $\bar Q(\bar{\vec v}) = 0$ has a lift
$\vec v \in R^n$ with $\pi^2 \mid Q(\vec v)$ (correct an arbitrary lift by $\pi\vec w$, using that $B(\vec v, \cdot)$ is onto mod $\pi$). -/
theorem exists_lift (hdet : ¬ π ∣ Q.hessian.det) {vb : Fin n → Res π} (hv0 : vb ≠ 0)
    (hq : qv (Res π) Q vb = 0) : ∃ v : Fin n → R, red π v = vb ∧ π ^ 2 ∣ qv R Q v := by
  set v0 : Fin n → R := liftRes vb
  have hred : red π v0 = vb := red_liftRes vb
  have hq0 : π ∣ qv R Q v0 := by rw [← dvd_of_red, ← qv_red, hred, hq]
  obtain ⟨c, hc⟩ := hq0
  obtain ⟨z, hz⟩ := exists_bv_eq_one (Q := Q) hdet (by rw [hred]; exact hv0)
  refine ⟨v0 + π • ((-c) • z), ?_, ?_⟩
  · rw [red_add, red_smul, (dvd_of_red (π := π) π).mpr (dvd_refl π), zero_smul, add_zero, hred]
  · rw [qv_add_smul, hc, bv_comm, bv_smul_left, qv_smul]
    have : π ∣ c + (-c) * bv R Q z v0 := by
      rw [← dvd_of_red, map_add, map_mul, hz]; simp
    obtain ⟨d, hd⟩ := this
    refine ⟨d + c ^ 2 * qv R Q z, ?_⟩
    linear_combination π * hd

end Nbr

/-! ### The neighbours as a finite set, indexed by isotropic lines -/

section Count

variable {Q π}
variable [(Ideal.span {π}).IsMaximal] [Fintype (Res π)] [DecidableEq (Res π)]

variable (Q π) in
/-- **The nonzero isotropic vectors of $L/\pi L$:** $\{\bar{\vec v} \in k^n : \bar{\vec v} \ne 0,\ \bar Q(\bar{\vec v}) = 0\}$. -/
def isoSet : Finset (Fin n → Res π) :=
  Finset.univ.filter fun y => y ≠ 0 ∧ qv (Res π) Q y = 0

variable (Q π) in
open Classical in
/-- A lift $\vec v \in R^n$ of $\bar{\vec v}$ with $\pi^2 \mid Q(\vec v)$ (`exists_lift`; junk $0$ if there is none). -/
noncomputable def liftV (vb : Fin n → Res π) : Fin n → R :=
  if h : ∃ v : Fin n → R, red π v = vb ∧ π ^ 2 ∣ qv R Q v then h.choose else 0

variable (K Q π) in
/-- **The neighbour of an isotropic line:** $L(\bar{\vec v}) = L(\vec v)$ for a lift $\vec v$ with $\pi^2 \mid Q(\vec v)$. -/
noncomputable def nbOf (vb : Fin n → Res π) : Submodule R (Fin n → K) := nbLat Q π (liftV Q π vb)

variable (K Q π) in
open Classical in
/-- **The $\pi$-neighbours of $R^n$** as a finite set (`mem_neighbors_iff`): the image of `isoSet` under `nbOf`. -/
noncomputable def neighbors : Finset (Submodule R (Fin n → K)) := (isoSet Q π).image (nbOf K Q π)

theorem mem_isoSet {vb : Fin n → Res π} : vb ∈ isoSet Q π ↔ vb ≠ 0 ∧ qv (Res π) Q vb = 0 := by
  simp [isoSet]

variable (hπ : Prime π)
include hπ

theorem liftV_spec (hdet : ¬ π ∣ Q.hessian.det) {vb : Fin n → Res π} (hvb : vb ∈ isoSet Q π) :
    red π (liftV Q π vb) = vb ∧ π ^ 2 ∣ qv R Q (liftV Q π vb) := by
  rw [mem_isoSet] at hvb
  have h := exists_lift hπ hdet hvb.1 hvb.2 (Q := Q)
  unfold liftV
  rw [dif_pos h]
  exact h.choose_spec

theorem isUnit_res_of_ne_zero {c : Res π} (hc : c ≠ 0) : IsUnit c := hc.isUnit

theorem nbOf_eq_nbLat (hdet : ¬ π ∣ Q.hessian.det) {v : Fin n → R} (hv : π ^ 2 ∣ qv R Q v)
    (hv0 : red π v ≠ 0) : nbOf K Q π (red π v) = nbLat Q π v := by
  have hmem : red π v ∈ isoSet Q π := by
    rw [mem_isoSet, qv_red, dvd_of_red]
    exact ⟨hv0, (dvd_pow_self _ two_ne_zero).trans hv⟩
  obtain ⟨h1, h2⟩ := liftV_spec hπ hdet hmem
  exact nbLat_eq_of_line hπ hv h2 isUnit_one (by rw [h1, one_smul])

/-- **The $\pi$-neighbours of $R^n$** ($\pi \nmid \det H$): `neighbors K Q π` is exactly the set of $\pi$-neighbours. -/
@[kb "kneser1957" "§1, the neighbours ↔ isotropic lines [unverified]"]
theorem mem_neighbors_iff (hdet : ¬ π ∣ Q.hessian.det) {L : Submodule R (Fin n → K)} :
    L ∈ neighbors K Q π ↔ IsNbr K Q π L := by
  classical
  unfold neighbors
  rw [Finset.mem_image]
  constructor
  · rintro ⟨vb, hvb, rfl⟩
    obtain ⟨h1, h2⟩ := liftV_spec hπ hdet hvb
    exact isNbr_nbLat hπ hdet h2 (by rw [h1]; exact (mem_isoSet.mp hvb).1)
  · intro hL
    obtain ⟨v, hv, hv0, rfl⟩ := exists_eq_nbLat hπ hdet hL
    refine ⟨red π v, ?_, nbOf_eq_nbLat hπ hdet hv hv0⟩
    rw [mem_isoSet, qv_red, dvd_of_red]
    exact ⟨hv0, (dvd_pow_self _ two_ne_zero).trans hv⟩

/-- **Same neighbour iff same line:** for $\bar{\vec v}, \bar{\vec w} \in$ `isoSet`, $L(\bar{\vec w}) = L(\bar{\vec v})$ iff
$\bar{\vec w} = c\bar{\vec v}$ for some $c \in k$. -/
theorem nbOf_eq_iff (hdet : ¬ π ∣ Q.hessian.det) {vb wb : Fin n → Res π} (hv : vb ∈ isoSet Q π)
    (hw : wb ∈ isoSet Q π) : nbOf K Q π wb = nbOf K Q π vb ↔ ∃ c : Res π, wb = c • vb := by
  obtain ⟨hv1, hv2⟩ := liftV_spec hπ hdet hv
  obtain ⟨hw1, hw2⟩ := liftV_spec hπ hdet hw
  constructor
  · intro h
    have := line_eq_of_nbLat_eq (K := K) hπ hv2 hw2 (by rw [hw1]; exact (mem_isoSet.mp hw).1) h
    rwa [hw1, hv1] at this
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl; exact (mem_isoSet.mp hw).1 (by rw [hc, zero_smul])
    exact nbLat_eq_of_line hπ hv2 hw2 hc0.isUnit (by rw [hw1, hv1, hc])

omit hπ in
/-- **The points of a line:** for $\vec u \ne 0$, $\#\{\vec w \ne 0 : \vec w \in k\vec u\} = q - 1$. -/
theorem card_line {u : Fin n → Res π} (hu : u ≠ 0) :
    (Finset.univ.filter fun w : Fin n → Res π => w ≠ 0 ∧ ∃ c : Res π, w = c • u).card =
      Fintype.card (Res π) - 1 := by
  classical
  have e : (Finset.univ.filter fun w : Fin n → Res π => w ≠ 0 ∧ ∃ c : Res π, w = c • u) =
      (Finset.univ.erase (0 : Res π)).image (fun c => c • u) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨hw, c, rfl⟩
      exact ⟨c, ⟨fun h => hw (by rw [h, zero_smul]), trivial⟩, rfl⟩
    · rintro ⟨c, ⟨hc, -⟩, rfl⟩
      exact ⟨smul_ne_zero hc hu, c, rfl⟩
  rw [e, Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  intro c _ d _ h
  exact smul_left_injective _ hu h

/-- **Each neighbour comes from $q - 1$ isotropic vectors** (the nonzero points of its line). -/
theorem card_fibre_nbOf (hdet : ¬ π ∣ Q.hessian.det) {vb : Fin n → Res π} (hv : vb ∈ isoSet Q π) :
    ((isoSet Q π).filter fun wb => nbOf K Q π wb = nbOf K Q π vb).card = Fintype.card (Res π) - 1 := by
  rw [← card_line (mem_isoSet.mp hv).1]
  congr 1
  ext wb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨(mem_isoSet.mp hw).1, (nbOf_eq_iff hπ hdet hv hw).mp h⟩
  · rintro ⟨hw0, c, rfl⟩
    have hw : c • vb ∈ isoSet Q π := by
      rw [mem_isoSet, qv_smul, (mem_isoSet.mp hv).2, mul_zero]; exact ⟨hw0, rfl⟩
    exact ⟨hw, (nbOf_eq_iff hπ hdet hv hw).mpr ⟨c, rfl⟩⟩

/-- **Sums over neighbours as sums over isotropic vectors:** $(q-1)\sum_{L'} f(L') = \sum_{\bar{\vec v}} f(L(\bar{\vec v}))$. -/
theorem sum_neighbors (hdet : ¬ π ∣ Q.hessian.det) {M : Type*} [AddCommMonoid M]
    (f : Submodule R (Fin n → K) → M) :
    (Fintype.card (Res π) - 1) • ∑ L ∈ neighbors K Q π, f L = ∑ vb ∈ isoSet Q π, f (nbOf K Q π vb) := by
  classical
  unfold neighbors
  rw [Finset.smul_sum]
  refine Finset.sum_image' _ fun vb hv => ?_
  rw [Finset.sum_congr rfl fun wb hw => by rw [(Finset.mem_filter.mp hw).2], Finset.sum_const,
    card_fibre_nbOf hπ hdet hv]

/-- **The number of $\pi$-neighbours** (Kneser 1957; AWS Thm. 1.10.4, p. 23): $(q - 1)\cdot\#\{L'\} = \#\{\bar{\vec v} \ne 0 : \bar Q(\bar{\vec v}) = 0\}$. -/
@[kb "kneser1957" "§1, number of neighbours = isotropic lines [unverified]"]
theorem card_neighbors (hdet : ¬ π ∣ Q.hessian.det) :
    (Fintype.card (Res π) - 1) * (neighbors K Q π).card = (isoSet Q π).card := by
  have := sum_neighbors (K := K) hπ hdet (Q := Q) (fun _ => (1 : ℕ))
  simpa using this

omit hπ in
theorem card_isoSet : (isoSet Q π).card + 1 = (Finset.univ.filter fun y => qv (Res π) Q y = 0).card := by
  classical
  have : (Finset.univ.filter fun y => qv (Res π) Q y = 0) = insert 0 (isoSet Q π) := by
    ext y; by_cases hy : y = 0 <;> simp [isoSet, hy, qv_zero]
  rw [this, Finset.card_insert_of_notMem (by simp [isoSet])]

end Count

end QuadFormsKB.Lattices.Nbr
