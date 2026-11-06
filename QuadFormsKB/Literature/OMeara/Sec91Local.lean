/-
# O'Meara §91: spinor norms and values on lattices over local fields of dimension $\ge 3$ (91:6, 91:7, 91:8, 91:3 remarks)

**Setting** (as in `Sec63C.lean` and `Sec91Spinor.lean`). The local field is a completion
$K = F_\mathfrak p$ of a number field $F$ at a finite place $\mathfrak p$ (`v.adicCompletion F`), with ring of integers
$R = \mathfrak o$ (`v.adicCompletionIntegers F`, a Henselian discrete valuation ring with fraction field $K$,
$2 \in K^\times$). The proofs are written for an abstract pair $(R, K)$: $R$ a (Henselian) discrete valuation ring
with fraction field $K$ of characteristic $0$ such that $K$ satisfies the Hilbert-symbol axioms
`PadicClass.LocalHilbertField` (`HasseIsoNF.localHilbertField_adicCompletion` shows they hold for $F_\mathfrak p$, dyadic
places included), and the number-field statements are the specializations at the end. Regular quadratic spaces
$(V, Q)$ over $K$ are finite-dimensional with `(QuadraticMap.associated Q).Nondegenerate`; lattices are
`Submodule R V`; spinor norms are expressed through `HasSpinorNorm` (`Sec92Spinor.lean`) and `spinorNormHom`
(`Sec55.lean`). Helper declarations carry the prefix `loc91_`.

**Proves**
* `loc91_ternary` (the representation criterion behind 91:6 and 91:3): a regular ternary space $V$ over a local
  field represents every $\alpha \in K^\times$ outside the square class $-dV$, i.e. with $\alpha\cdot(-dV)$ not a square
  (63:21 for the diagonal form, transported to $V$ by an orthogonal basis); `loc91_universal`: a regular space of
  dimension $\ge 4$ is universal (63:18);
* `spinorNormHom_surjective_of_three_le` (**91:6**, p. 242): $\theta(O^+(V)) = K^\times$ for $\dim V \ge 3$;
* `Q_image_eq_of_four_le` and `Q_image_ternary` (**91:3**, remarks, p. 241): for an $\mathfrak a$-maximal lattice $L$,
  $Q(L) = \mathfrak a$ if $\dim V \ge 4$, and for $\dim V = 3$ and $0 \ne \beta \in \mathfrak a$ either
  $Q(L) \supseteq \beta\mathfrak u$ or $Q(L) \supseteq \pi\beta\mathfrak u$;
* `exists_hasSpinorNorm_of_isMaximal` (**91:8**, p. 243): $\theta(O^+(L)) \supseteq \mathfrak u$ for a maximal lattice
  $L$ on $V$ with $\dim V \ge 3$ (the isotropic case is `exists_hasSpinorNorm_of_isMaximal_isotropic`; the anisotropic
  case is 91:5 and 91:6, `exists_hasSpinorNorm_of_isMaximal_anisotropic`);
* `exists_lattice_spinorNorm_eq_top` (**91:7**, pp. 242-243): some lattice $L$ on $V$ has $\theta(O^+(L)) = K^\times$.
-/
import QuadFormsKB.Literature.OMeara.Sec93E
import QuadFormsKB.Literature.OMeara.Sec91Spinor
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Literature.Cassels.Ch4.Invariants
import QuadFormsKB.Tamagawa.QuatOrderGlobal
import QuadFormsKB.Literature.OMeara.Sec82Max
import QuadFormsKB.Literature.OMeara.Sec91Max3
import QuadFormsKB.Literature.OMeara.Sec55

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Local

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- A uniformizer times a unit of $R$ is never a square in $K$ (so the valuation of a uniformizer is odd). -/
theorem loc91_not_isSquare_irred_mul_unit {π e : R} (hπ : Irreducible π) (he : IsUnit e) :
    ¬ IsSquare (algebraMap R K π * algebraMap R K e) := by
  rintro ⟨r, hr⟩
  have hinj := IsFractionRing.injective R K
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmax : maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  rcases ValuationRing.isInteger_or_isInteger R r with ⟨s, hs⟩ | ⟨s, hs⟩
  · have h1 : π * e = s * s := hinj (by rw [map_mul, map_mul, hs, ← hr])
    have hsn : ¬ IsUnit s := fun hu =>
      hπ.not_isUnit (isUnit_of_mul_isUnit_left (h1 ▸ hu.mul hu))
    have hsm : s ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact hsn
    rw [hmax, Ideal.mem_span_singleton'] at hsm
    obtain ⟨t, ht⟩ := hsm
    have h2 : π * e = π * (t * t * π) := by rw [h1, ← ht]; ring
    have h3 : e = t * t * π := mul_left_cancel₀ hπ0 h2
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_right (h3 ▸ he))
  · have hr0 : r ≠ 0 := by
      rintro rfl
      have : algebraMap R K (π * e) = 0 := by rw [map_mul]; simpa using hr
      exact mul_ne_zero hπ0 he.ne_zero (hinj (by simpa using this))
    have h1 : s * s * (π * e) = 1 := hinj (by
      rw [map_mul, map_mul, map_mul, hs, map_one, hr]
      field_simp)
    exact hπ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨s * s * e, by rw [← h1]; ring⟩)

/-- If $xm$ and $ym$ are squares ($m \ne 0$), so is $xy$. -/
theorem loc91_isSquare_mul {x y m : K} (hm : m ≠ 0) (hx : IsSquare (x * m)) (hy : IsSquare (y * m)) :
    IsSquare (x * y) := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  refine ⟨r * s / m, ?_⟩
  field_simp
  linear_combination (y * m) * hr + (r * r) * hs

include R in
/-- A local field has three square classes $1$, $p$, $w$, pairwise distinct (here $p$ is a uniformizer and $w$
is $-1$ or an element with Hilbert symbol $(p, w) = -1$). -/
theorem loc91_exists_three_classes (hK : LocalHilbertField K) :
    ∃ p w : K, p ≠ 0 ∧ w ≠ 0 ∧ ¬ IsSquare p ∧ ¬ IsSquare w ∧ ¬ IsSquare (p * w) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj := IsFractionRing.injective R K
  have hp0 : algebraMap R K π ≠ 0 := fun h => hπ.ne_zero (hinj (by simpa using h))
  have hp : ¬ IsSquare (algebraMap R K π) := by
    simpa using loc91_not_isSquare_irred_mul_unit (K := K) hπ isUnit_one
  have hpm : ¬ IsSquare (-algebraMap R K π) := by
    have := loc91_not_isSquare_irred_mul_unit (K := K) hπ (isUnit_one.neg)
    simpa using this
  set p : K := algebraMap R K π with hpdef
  by_cases h : hilbertSymbol K p (-1) = -1
  · refine ⟨p, -1, hp0, by norm_num, hp, ?_, by simpa using hpm⟩
    intro hsq
    have := hs_of_isSquare p (-1) (by norm_num) hsq
    rw [this] at h
    norm_num at h
  · have h1 : hilbertSymbol K p (-1) = 1 := (hs_pm _ _).resolve_right h
    obtain ⟨z, hz0, hz⟩ := hK.exists_neg_one p hp0 hp
    refine ⟨p, z, hp0, hz0, hp, ?_, ?_⟩
    · intro hsq
      rw [hs_of_isSquare p z hz0 hsq] at hz
      norm_num at hz
    · intro hsq
      have := hs_of_isSquare p (p * z) (mul_ne_zero hp0 hz0) hsq
      rw [hK.mul_right hp0 hp0 hz0, hK.self hp0, h1, hz] at this
      norm_num at this

include R in
/-- Two square classes never cover $K^\times$: for $m, m' \ne 0$ some $a$ has $am$ and $am'$ both non-squares. -/
theorem loc91_exists_avoid (hK : LocalHilbertField K) {m m' : K} (hm : m ≠ 0) (hm' : m' ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ¬ IsSquare (a * m) ∧ ¬ IsSquare (a * m') := by
  obtain ⟨p, w, hp0, hw0, hp, hw, hpw⟩ := loc91_exists_three_classes (R := R) hK
  by_contra hcon
  have key : ∀ a : K, a ≠ 0 → IsSquare (a * m) ∨ IsSquare (a * m') := by
    intro a ha
    by_contra h'
    push Not at h'
    exact hcon ⟨a, ha, h'.1, h'.2⟩
  have k1 := key 1 one_ne_zero
  have kp := key p hp0
  have kw := key w hw0
  have sq1 := fun {x y m : K} (hm : m ≠ 0) (hx : IsSquare (x * m)) (hy : IsSquare (y * m)) =>
    loc91_isSquare_mul hm hx hy
  rcases k1 with a | a <;> rcases kp with b | b <;> rcases kw with c | c
  · exact hp (by simpa using sq1 hm a b)
  · exact hp (by simpa using sq1 hm a b)
  · exact hw (by simpa using sq1 hm a c)
  · exact hpw (sq1 hm' b c)
  · exact hpw (sq1 hm b c)
  · exact hw (by simpa using sq1 hm' a c)
  · exact hp (by simpa using sq1 hm' a b)
  · exact hp (by simpa using sq1 hm' a b)

/-- **Orthogonal basis.** A regular space of dimension $n$ over $K$ is isometric to a diagonal form
$\langle w_0, \dots, w_{n-1}\rangle$ with all $w_i \ne 0$; so $V$ represents $x$ iff the diagonal form does. -/
theorem loc91_exists_weights (hV : (QuadraticMap.associated Q).Nondegenerate) :
    ∃ (n : ℕ) (w : Fin n → K), n = finrank K V ∧ (∀ i, w i ≠ 0) ∧
      ∀ x : K, (∃ y : V, Q y = x) ↔ (QuadForm.diag w).RepresentsIn K x := by
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hV.1
  refine ⟨finrank K V, fun i => (w i : K), rfl, fun i => (w i).ne_zero, fun x => ?_⟩
  have hev : ∀ z : Fin (finrank K V) → K, (QuadForm.diag fun i => (w i : K)).evalIn K z =
      QuadraticMap.weightedSumSquares K w z := by
    intro z
    rw [QuadForm.evalIn_diag, QuadraticMap.weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Units.smul_def, _root_.sq]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    rw [hev, e.map_app]
    rfl
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    have h1 := e.map_app (e.symm z)
    have h2 : e (e.symm z) = z := by simp
    rw [h2] at h1
    rw [← h1, ← hev]
    exact hz

/-- **63:18**: a regular quadratic space of dimension $\ge 4$ over a local field is universal. -/
theorem loc91_universal (hK : LocalHilbertField K) (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h4 : 4 ≤ finrank K V) (x : K) : ∃ y : V, Q y = x := by
  obtain ⟨n, w, hn, hw, hrep⟩ := loc91_exists_weights Q hV
  exact (hrep x).mpr (represents_of_four_le hK hw (hn ▸ h4) x)

/-- **The ternary case of 63:21 / 63:18**: a regular ternary space over a local field represents every
$x \in K^\times$ outside the square class $m K^{\times 2}$, where $m = -dV$ (here $m = -w_0w_1w_2$ for an orthogonal
basis with $Q(e_i) = w_i$; the class is $-dV$ since the discriminant is the class of $w_0w_1w_2$). -/
theorem loc91_ternary (hK : LocalHilbertField K) (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : finrank K V = 3) :
    ∃ m : K, m ≠ 0 ∧ ∀ x : K, x ≠ 0 → ¬ IsSquare (x * m) → ∃ y : V, Q y = x := by
  obtain ⟨n, w, hn, hw, hrep⟩ := loc91_exists_weights Q hV
  have hn3 : n = 3 := hn.trans h3
  subst hn3
  have hw3 : w = ![w 0, w 1, w 2] := by ext i; fin_cases i <;> rfl
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  refine ⟨-(w 0 * w 1 * w 2), neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h0 h1) h2), fun x hx hsq => ?_⟩
  refine (hrep x).mpr ?_
  rw [hw3]
  refine (represents_three_iff hK h0 h1 h2 hx).mpr ?_
  rintro ⟨t, -, ht⟩
  exfalso
  apply hsq
  refine ⟨t * -(w 0 * w 1 * w 2), ?_⟩
  rw [ht]; ring

include R in
/-- **Two values with a given product**: on a regular space of dimension $\ge 3$ over a local field, every
$c \in K^\times$ is $Q(x)Q(y)$ with $Q(x), Q(y) \ne 0$. -/
theorem loc91_exists_two_values (hK : LocalHilbertField K) (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank K V) {c : K} (hc : c ≠ 0) :
    ∃ x y : V, Q x ≠ 0 ∧ Q y ≠ 0 ∧ Q x * Q y = c := by
  rcases (show finrank K V = 3 ∨ 4 ≤ finrank K V by omega) with h | h
  · obtain ⟨m, hm, hrep⟩ := loc91_ternary Q hK hV h
    obtain ⟨a, ha, h1, h2⟩ := loc91_exists_avoid (R := R) hK hm (mul_ne_zero hc hm)
    obtain ⟨x, hx⟩ := hrep a ha h1
    have hca : c / a ≠ 0 := div_ne_zero hc ha
    have hns : ¬ IsSquare (c / a * m) := by
      rintro ⟨r, hr⟩
      apply h2
      refine ⟨a * r, ?_⟩
      calc a * (c * m) = a * a * (c / a * m) := by field_simp
        _ = a * r * (a * r) := by rw [hr]; ring
    obtain ⟨y, hy⟩ := hrep (c / a) hca hns
    refine ⟨x, y, by rw [hx]; exact ha, by rw [hy]; exact hca, ?_⟩
    rw [hx, hy]; field_simp
  · obtain ⟨x, hx⟩ := loc91_universal Q hK hV h 1
    obtain ⟨y, hy⟩ := loc91_universal Q hK hV h c
    exact ⟨x, y, by rw [hx]; exact one_ne_zero, by rw [hy]; exact hc, by rw [hx, hy, one_mul]⟩

include R in
/-- **The core of 91:6**: on a regular space of dimension $\ge 3$ over a local field every $c \in K^\times$ is a
spinor norm of a rotation: $c = \theta(\tau_x\tau_y)$ with $Q(x)Q(y) = c$. -/
theorem loc91_exists_hasSpinorNorm (hK : LocalHilbertField K)
    (hV : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank K V) {c : K} (hc : c ≠ 0) :
    ∃ σ ∈ orthPlus Q, HasSpinorNorm Q σ c := by
  obtain ⟨x, y, hx, hy, hxy⟩ := loc91_exists_two_values (R := R) Q hK hV h3 hc
  refine ⟨_, symmetry_mul_mem_orthPlus Q hx hy, ?_⟩
  have := hasSpinorNorm_symmetry_mul Q hx hy
  rwa [hxy] at this

include R in
/-- **91:6, abstract form**: $\theta(O^+(V)) = K^\times$ for a regular space of dimension $\ge 3$ over a local
field. -/
theorem loc91_spinorNormHom_surjective (hK : LocalHilbertField K)
    (hV : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank K V) :
    Function.Surjective (spinorNormHom Q hV) := by
  intro g
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom 2 : Kˣ →* Kˣ).range) g
  obtain ⟨σ, hσ, hs⟩ := loc91_exists_hasSpinorNorm (R := R) Q hK hV h3 u.ne_zero
  refine ⟨⟨σ, hσ⟩, ?_⟩
  rw [spinorNormHom_apply Q hV hs, Sp55.sqClassOf_of_ne_zero' u.ne_zero]
  have e : Units.mk0 (u : K) u.ne_zero = u := Units.ext rfl
  rw [e]
  rfl

end Local

section Classes

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Square classes of a local field**: every $c \in K^\times$ is $\varepsilon s^2$ or $\pi\varepsilon s^2$ with
$\varepsilon \in R^\times$, $s \in K^\times$ and $\pi$ an irreducible element (write the numerator times the
denominator of $c$ as $\varepsilon\pi^n$). -/
theorem loc91_exists_unit_mul_sq {π : R} (hπ : Irreducible π) {c : K} (hc : c ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ ε : R, IsUnit ε ∧
      (c = algebraMap R K ε * s ^ 2 ∨ c = algebraMap R K π * algebraMap R K ε * s ^ 2) := by
  have hinj := IsFractionRing.injective R K
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hc
    rw [← hab]
    simp
  have hπK : algebraMap R K π ≠ 0 := fun h => hπ.ne_zero (hinj (by simpa using h))
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (mul_ne_zero ha0 hb0) hπ
  have hK : algebraMap R K a * algebraMap R K b = algebraMap R K u * algebraMap R K π ^ n := by
    rw [← map_mul, hn, map_mul, map_pow]
  have hc' : c = algebraMap R K a * algebraMap R K b / algebraMap R K b ^ 2 := by
    rw [← hab]
    field_simp
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · refine ⟨algebraMap R K π ^ k / algebraMap R K b, div_ne_zero (pow_ne_zero _ hπK) hbK, u, u.isUnit,
      Or.inl ?_⟩
    rw [hc', hK]
    field_simp
    ring
  · refine ⟨algebraMap R K π ^ k / algebraMap R K b, div_ne_zero (pow_ne_zero _ hπK) hbK, u, u.isUnit,
      Or.inr ?_⟩
    rw [hc', hK]
    field_simp
    ring

end Classes

section Max

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {K : Type*} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- **91:3, remark for $\dim V \ge 4$** (O'Meara 1963, p. 241): $Q(L) = \mathfrak a$ for an $\mathfrak a$-maximal lattice
$L$ on a regular space of dimension $\ge 4$ over a local field, since $V$ is universal (63:18) and $Q(L) = Q(V)\cap\mathfrak a$
(91:3). -/
theorem loc91_Q_image_eq_of_four_le (hK : LocalHilbertField K)
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R K} {L : Submodule R V}
    (hL : IsMaximal Q a L) (h4 : 4 ≤ finrank K V) : Q '' (L : Set V) = (a : Set K) := by
  rw [Q_image_eq_of_isMaximal Q hV hL]
  have : Set.range Q = Set.univ :=
    Set.eq_univ_of_forall fun x => loc91_universal Q hK hV h4 x
  rw [this, Set.univ_inter]

/-- **91:3, remark for $\dim V = 3$** (O'Meara 1963, p. 241): $V$ represents every class outside $-dV$, so for
$0 \ne \beta \in \mathfrak a$ either $Q(L) \supseteq \beta\mathfrak u$ or $Q(L) \supseteq \pi\beta\mathfrak u$. (If the
class $-dV$ is a unit class, the elements $\beta u$ with $\beta$ of even valuation are represented, and $\pi\beta u$
otherwise; and dually.) -/
theorem loc91_Q_image_ternary (hK : LocalHilbertField K)
    (hV : (QuadraticMap.associated Q).Nondegenerate) (h3 : finrank K V = 3) {a : Submodule R K}
    {L : Submodule R V} (hL : IsMaximal Q a L) {π : R} (hπ : Irreducible π) {β : K} (hβa : β ∈ a)
    (hβ : β ≠ 0) :
    (∀ u : R, IsUnit u → β * algebraMap R K u ∈ Q '' (L : Set V)) ∨
      (∀ u : R, IsUnit u → algebraMap R K π * β * algebraMap R K u ∈ Q '' (L : Set V)) := by
  obtain ⟨m, hm, hrep⟩ := loc91_ternary Q hK hV h3
  have himg := Q_image_eq_of_isMaximal Q hV hL
  have hinj := IsFractionRing.injective R K
  have hne : ∀ u : R, IsUnit u → algebraMap R K u ≠ 0 := fun u hu h =>
    hu.ne_zero (hinj (by simpa using h))
  have hπ0 : algebraMap R K π ≠ 0 := fun h => hπ.ne_zero (hinj (by simpa using h))
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨u1, hu1, h1⟩, ⟨u2, hu2, h2⟩⟩ := hcon
  have hmem1 : β * algebraMap R K u1 ∈ a := by
    have := a.smul_mem u1 hβa
    rwa [Algebra.smul_def, mul_comm] at this
  have hmem2 : algebraMap R K π * β * algebraMap R K u2 ∈ a := by
    have := a.smul_mem (π * u2) hβa
    rw [Algebra.smul_def, map_mul] at this
    convert this using 1
    ring
  have sq1 : IsSquare (β * algebraMap R K u1 * m) := by
    by_contra hns
    apply h1
    rw [himg]
    exact ⟨hrep _ (mul_ne_zero hβ (hne u1 hu1)) hns, hmem1⟩
  have sq2 : IsSquare (algebraMap R K π * β * algebraMap R K u2 * m) := by
    by_contra hns
    apply h2
    rw [himg]
    exact ⟨hrep _ (mul_ne_zero (mul_ne_zero hπ0 hβ) (hne u2 hu2)) hns, hmem2⟩
  obtain ⟨r, hr⟩ := loc91_isSquare_mul hm sq1 sq2
  refine loc91_not_isSquare_irred_mul_unit (K := K) hπ (hu1.mul hu2) ⟨r / β, ?_⟩
  rw [map_mul]
  field_simp
  linear_combination hr

/-- **The criterion of §91B for a vector of $L$**: if $u \in L$, $Q(u) \ne 0$ and
$2B(L, u) \subseteq Q(u)\mathfrak o$, then $\tau_u \in O(L)$. -/
theorem loc91_symmetry_mem_orthLat {L : Submodule R V} {u : V} (hu : Q u ≠ 0) (huL : u ∈ L)
    (h : ∀ l ∈ L, 2 * bil Q l u ∈ R ∙ Q u) : symmetry Q u hu ∈ orthLat Q L := by
  refine symmetry_mem_orthLat_of_le Q hu fun x hx => ?_
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (h x hx)
  rw [symmetry_apply]
  have : (2 * bil Q x u / Q u) • u = r • u := by
    rw [← algebraMap_smul K r u]
    congr 1
    rw [← hr, Algebra.smul_def]
    field_simp
  rw [this]
  exact L.sub_mem hx (L.smul_mem r huL)

/-- The $R$-submodule $\{l : B(l, u) \in c R\}$. -/
def loc91_bilSub (u : V) (c : K) : Submodule R V where
  carrier := {l | bil Q l u ∈ R ∙ c}
  add_mem' := by
    intro a b ha hb
    show bil Q (a + b) u ∈ R ∙ c
    rw [bil_add_left]
    exact add_mem ha hb
  zero_mem' := by
    show bil Q 0 u ∈ R ∙ c
    simp [bil]
  smul_mem' := by
    intro r l hl
    show bil Q (r • l) u ∈ R ∙ c
    rw [bil_rsmul_left, ← Algebra.smul_def]
    exact (R ∙ c).smul_mem r hl

/-- **A vector orthogonal to a hyperbolic pair with non-zero norm** (dimension $\ge 3$): if $x, y$ are isotropic with
$B(x, y) = 1$ in a regular space of dimension $\ge 3$ there is $z$ with $Q(z) \ne 0$, $B(z, x) = B(z, y) = 0$. -/
theorem loc91_exists_orth_vec (hV : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank K V)
    {x y : V} (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = 1) :
    ∃ z : V, Q z ≠ 0 ∧ bil Q z x = 0 ∧ bil Q z y = 0 := by
  by_contra hcon
  have hcon' : ∀ z : V, bil Q z x = 0 → bil Q z y = 0 → Q z = 0 := by
    intro z h1 h2
    by_contra h
    exact hcon ⟨z, h, h1, h2⟩
  have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
  obtain ⟨pr, hpr⟩ : ∃ pr : V → V, ∀ v, pr v = v - bil Q v y • x - bil Q v x • y := ⟨_, fun _ => rfl⟩
  have hprx : ∀ v, bil Q (pr v) x = 0 := by
    intro v
    simp only [hpr, bil_sub_left, bil_smul_left, bil_self, hQx, hyx]
    ring
  have hpry : ∀ v, bil Q (pr v) y = 0 := by
    intro v
    simp only [hpr, bil_sub_left, bil_smul_left, bil_self, hQy, hxy]
    ring
  obtain ⟨v1, hv1⟩ : ∃ v1 : V, v1 ∉ span K (Set.range ![x, y]) := by
    by_contra h
    push Not at h
    have htop : span K (Set.range ![x, y]) = ⊤ := eq_top_iff.mpr fun v _ => h v
    have h1 := finrank_range_le_card (R := K) ![x, y]
    rw [Set.finrank, htop, finrank_top] at h1
    simp at h1
    omega
  have hw0 : pr v1 ≠ 0 := by
    intro h
    apply hv1
    have e : v1 = bil Q v1 y • x + bil Q v1 x • y := by
      have := hpr v1
      rw [h] at this
      rw [eq_comm, sub_sub, sub_eq_zero] at this
      exact this
    rw [e]
    exact add_mem (smul_mem _ _ (subset_span ⟨0, rfl⟩)) (smul_mem _ _ (subset_span ⟨1, rfl⟩))
  apply hw0
  refine hV.1 (pr v1) fun v => ?_
  show bil Q (pr v1) v = 0
  have hdec : v = pr v + bil Q v y • x + bil Q v x • y := by rw [hpr]; abel
  have hQ1 : Q (pr v1) = 0 := hcon' _ (hprx v1) (hpry v1)
  have hQ2 : Q (pr v) = 0 := hcon' _ (hprx v) (hpry v)
  have hQ3 : Q (pr v1 + pr v) = 0 :=
    hcon' _ (by rw [bil_add_left, hprx, hprx, add_zero]) (by rw [bil_add_left, hpry, hpry, add_zero])
  have hb : bil Q (pr v1) (pr v) = 0 := by
    have h := Q_add Q (pr v1) (pr v)
    rw [hQ3, hQ1, hQ2] at h
    have h' : (2 : K) * bil Q (pr v1) (pr v) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left two_ne_zero
  have e := congrArg (bil Q (pr v1)) hdec
  rw [e, bil_add_right, bil_add_right, bil_smul_right, bil_smul_right, hb, hprx, hpry]
  ring

/-- **91:8, abstract form** (O'Meara 1963, p. 243): if $L$ is an $\mathfrak a$-maximal lattice on a regular space of
dimension $\ge 3$ over a local field, every unit $\varepsilon$ is the spinor norm of a rotation in $O^+(L)$. The
isotropic case is `exists_hasSpinorNorm_of_isMaximal_isotropic`; on an anisotropic space $O(L) = O(V)$ (91:5), so
this is 91:6. -/
theorem loc91_exists_hasSpinorNorm_of_isMaximal (hK : LocalHilbertField K)
    (hV : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank K V) {a : Submodule R K}
    {L : Submodule R V} (hL : IsMaximal Q a L) {ε : R} (hε : IsUnit ε) :
    ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ (algebraMap R K ε) := by
  by_cases hiso : ∃ w : V, w ≠ 0 ∧ Q w = 0
  · obtain ⟨w, hw0, hQw⟩ := hiso
    exact exists_hasSpinorNorm_of_isMaximal_isotropic Q hV hL hw0 hQw hε
  · push Not at hiso
    have haniso : Q.Anisotropic := fun x hx => by_contra fun hne => hiso x hne hx
    have hεK : algebraMap R K ε ≠ 0 := fun h => hε.ne_zero
      ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
    obtain ⟨σ, hσ, hs⟩ := loc91_exists_hasSpinorNorm (R := R) Q hK hV h3 hεK
    refine ⟨σ, ⟨?_, hσ⟩, hs⟩
    rw [orthLat_eq_orth_of_isMaximal Q haniso hL]
    exact hσ.1

/-- **91:7, isotropic case**: if $V$ is isotropic and regular of dimension $\ge 3$, the lattice
$L = \mathfrak o x + \mathfrak o y' + \mathfrak o z + \sum_j \mathfrak o\,p_j$, where $x, y$ is a hyperbolic pair,
$y' = \kappa y$, $z \perp \{x, y\}$ with $Q(z) \ne 0$, $2\kappa Q(z) = \pi$ and $p_j$ are the projections of a basis to
$\{x, y, z\}^\perp$, has $\theta(O^+(L)) = K^\times$: the units come from $\tau_{x + \varepsilon y'}\tau_{x + y'}$
(spinor norm $\varepsilon(2\kappa)^2$) and the classes $\pi\varepsilon$ from $\tau_{x + \varepsilon y'}\tau_z$
(spinor norm $\pi\varepsilon$). (Rescaling the hyperbolic pair replaces O'Meara's rescaling of the form.) -/
theorem loc91_exists_lattice_isotropic (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank K V) {x : V} (hx0 : x ≠ 0) (hQx : Q x = 0) :
    ∃ L : Submodule R V, L.IsLattice K ∧
      ∀ c : K, c ≠ 0 → ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ c := by
  classical
  obtain ⟨y, hQy, hxy⟩ := exists_hyperbolic_pair Q hV hx0 hQx
  obtain ⟨z, hQz, hzx, hzy⟩ := loc91_exists_orth_vec Q hV h3 hQx hQy hxy
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj := IsFractionRing.injective R K
  have hp0 : algebraMap R K π ≠ 0 := fun h => hπ.ne_zero (hinj (by simpa using h))
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨κ, hκ0, hκq⟩ : ∃ κ : K, κ ≠ 0 ∧ 2 * κ * Q z = algebraMap R K π :=
    ⟨algebraMap R K π / (2 * Q z), div_ne_zero hp0 (mul_ne_zero h2 hQz), by field_simp⟩
  obtain ⟨y', hy'⟩ : ∃ y' : V, y' = κ • y := ⟨_, rfl⟩
  have hQy' : Q y' = 0 := by rw [hy', Q_smul, hQy, mul_zero]
  have hxy' : bil Q x y' = κ := by rw [hy', bil_smul_right, hxy, mul_one]
  have hy'x : bil Q y' x = κ := by rw [bil_comm]; exact hxy'
  have hzy' : bil Q z y' = 0 := by rw [hy', bil_smul_right, hzy, mul_zero]
  have hy'z : bil Q y' z = 0 := by rw [bil_comm]; exact hzy'
  have hxz : bil Q x z = 0 := by rw [bil_comm]; exact hzx
  have hyz : bil Q y z = 0 := by rw [bil_comm]; exact hzy
  have hyx : bil Q y x = 1 := by rw [bil_comm]; exact hxy
  -- the projection onto `{x, y, z}^⊥`
  obtain ⟨pr, hpr⟩ : ∃ pr : V → V,
      ∀ v, pr v = v - bil Q v y • x - bil Q v x • y - (bil Q v z / Q z) • z := ⟨_, fun _ => rfl⟩
  have hprx : ∀ v, bil Q (pr v) x = 0 := by
    intro v
    simp only [hpr, bil_sub_left, bil_smul_left, bil_self, hQx, hyx, hzx]
    ring
  have hpry : ∀ v, bil Q (pr v) y = 0 := by
    intro v
    simp only [hpr, bil_sub_left, bil_smul_left, bil_self, hQy, hxy, hzy]
    ring
  have hprz : ∀ v, bil Q (pr v) z = 0 := by
    intro v
    simp only [hpr, bil_sub_left, bil_smul_left, bil_self, hxz, hyz]
    rw [div_mul_cancel₀ _ hQz]
    ring
  let b := Module.finBasis K V
  obtain ⟨L, hL⟩ : ∃ L : Submodule R V,
      L = span R (insert x (insert y' (insert z (Set.range fun j => pr (b j))))) := ⟨_, rfl⟩
  have hxL : x ∈ L := by rw [hL]; exact subset_span (Set.mem_insert _ _)
  have hy'L : y' ∈ L := by
    rw [hL]; exact subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hzL : z ∈ L := by
    rw [hL]
    exact subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hprL : ∀ j, pr (b j) ∈ L := by
    intro j
    rw [hL]
    exact subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ ⟨j, rfl⟩)))
  have gens_ok : ∀ g ∈ (insert x (insert y' (insert z (Set.range fun j => pr (b j)))) : Set V),
      bil Q g x ∈ R ∙ κ ∧ bil Q g y' ∈ R ∙ κ ∧ bil Q g ((2 : K) • z) ∈ R ∙ Q z := by
    intro g hg
    rcases hg with rfl | rfl | rfl | ⟨j, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [bil_self, hQx]; exact zero_mem _
      · rw [hxy']; exact mem_span_singleton_self κ
      · rw [bil_smul_right, hxz, mul_zero]; exact zero_mem _
    · refine ⟨?_, ?_, ?_⟩
      · rw [hy'x]; exact mem_span_singleton_self κ
      · rw [bil_self, hQy']; exact zero_mem _
      · rw [bil_smul_right, hy'z, mul_zero]; exact zero_mem _
    · refine ⟨?_, ?_, ?_⟩
      · rw [hzx]; exact zero_mem _
      · rw [hzy']; exact zero_mem _
      · rw [bil_smul_right, bil_self]
        exact mem_span_singleton.mpr ⟨2, by rw [Algebra.smul_def, map_ofNat]⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hprx]; exact zero_mem _
      · rw [hy', bil_smul_right, hpry, mul_zero]; exact zero_mem _
      · rw [bil_smul_right, hprz, mul_zero]; exact zero_mem _
  have hLprop : ∀ l ∈ L, bil Q l x ∈ R ∙ κ ∧ bil Q l y' ∈ R ∙ κ ∧
      bil Q l ((2 : K) • z) ∈ R ∙ Q z := by
    intro l hl
    have hle : L ≤ loc91_bilSub Q x κ ⊓ loc91_bilSub Q y' κ ⊓ loc91_bilSub Q ((2 : K) • z) (Q z) := by
      rw [hL, span_le]
      intro g hg
      simp only [SetLike.mem_coe, Submodule.mem_inf]
      exact ⟨⟨(gens_ok g hg).1, (gens_ok g hg).2.1⟩, (gens_ok g hg).2.2⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := Submodule.mem_inf.mp (hle hl) |>.imp_left Submodule.mem_inf.mp
    exact ⟨h1, h2, h3⟩
  -- `L` is a lattice
  have hlat : L.IsLattice K := by
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact fg_span (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
        (Set.finite_range _))))
    · rw [eq_top_iff, ← b.span_eq, span_le]
      rintro _ ⟨j, rfl⟩
      have hx' : x ∈ span K (L : Set V) := subset_span hxL
      have hy : y ∈ span K (L : Set V) := by
        have e : y = κ⁻¹ • y' := by rw [hy', smul_smul, inv_mul_cancel₀ hκ0, one_smul]
        rw [e]
        exact smul_mem _ _ (subset_span hy'L)
      have hz' : z ∈ span K (L : Set V) := subset_span hzL
      have hp' : pr (b j) ∈ span K (L : Set V) := subset_span (hprL j)
      have e : b j = pr (b j) + bil Q (b j) y • x + bil Q (b j) x • y +
          (bil Q (b j) z / Q z) • z := by
        rw [hpr]; abel
      rw [SetLike.mem_coe, e]
      exact add_mem (add_mem (add_mem hp' (smul_mem _ _ hx')) (smul_mem _ _ hy)) (smul_mem _ _ hz')
  -- the symmetries
  have hQu : ∀ t : R, Q (x + t • y') = 2 * algebraMap R K t * κ := by
    intro t
    rw [Q_add, Q_rsmul, hQx, hQy', bil_rsmul_right, hxy']
    ring
  have hmem : ∀ t : R, IsUnit t →
      ∃ h : Q (x + t • y') ≠ 0, symmetry Q (x + t • y') h ∈ orthLat Q L := by
    intro t ht
    have htF : algebraMap R K t ≠ 0 := fun h => ht.ne_zero (hinj (by simpa using h))
    have h0 : Q (x + t • y') ≠ 0 := by
      rw [hQu]; exact mul_ne_zero (mul_ne_zero h2 htF) hκ0
    refine ⟨h0, loc91_symmetry_mem_orthLat Q h0 (L.add_mem hxL (L.smul_mem t hy'L)) fun l hl => ?_⟩
    obtain ⟨h1, h2', -⟩ := hLprop l hl
    obtain ⟨r1, hr1⟩ := mem_span_singleton.mp h1
    obtain ⟨r2, hr2⟩ := mem_span_singleton.mp h2'
    obtain ⟨u, hu⟩ := ht
    have hinv : algebraMap R K (↑u⁻¹ : R) * algebraMap R K t = 1 := by
      rw [← hu, ← map_mul, Units.inv_mul, map_one]
    refine mem_span_singleton.mpr ⟨(r1 + t * r2) * ↑u⁻¹, ?_⟩
    rw [hQu, bil_add_right, bil_rsmul_right, ← hr1, ← hr2]
    simp only [Algebra.smul_def, map_mul, map_add]
    linear_combination
      (2 * (algebraMap R K r1 + algebraMap R K t * algebraMap R K r2) * κ) * hinv
  have hτz : symmetry Q z hQz ∈ orthLat Q L :=
    loc91_symmetry_mem_orthLat Q hQz hzL fun l hl => by
      have := (hLprop l hl).2.2
      rwa [bil_smul_right] at this
  refine ⟨L, hlat, fun c hc => ?_⟩
  obtain ⟨s, hs0, ε, hε, hcase⟩ := loc91_exists_unit_mul_sq (R := R) hπ hc
  obtain ⟨h1, hτ1⟩ := hmem ε hε
  rcases hcase with hcase | hcase
  · obtain ⟨h1', hτ1'⟩ := hmem 1 isUnit_one
    refine ⟨symmetry Q _ h1 * symmetry Q _ h1', ⟨(orthLat Q L).mul_mem hτ1 hτ1',
      symmetry_mul_mem_orthPlus Q h1 h1'⟩, ?_⟩
    refine HasSpinorNorm.of_eq_mul_sq Q (hasSpinorNorm_symmetry_mul Q h1 h1')
      (s := s / (2 * κ)) (div_ne_zero hs0 (mul_ne_zero h2 hκ0)) ?_
    rw [hQu, hQu, hcase, map_one]
    field_simp
  · refine ⟨symmetry Q _ h1 * symmetry Q z hQz, ⟨(orthLat Q L).mul_mem hτ1 hτz,
      symmetry_mul_mem_orthPlus Q h1 hQz⟩, ?_⟩
    refine HasSpinorNorm.of_eq_mul_sq Q (hasSpinorNorm_symmetry_mul Q h1 hQz) (s := s) hs0 ?_
    rw [hQu, hcase]
    linear_combination (-(algebraMap R K ε * s ^ 2)) * hκq

/-- **Proposition 91:7** (O'Meara 1963, pp. 242-243), abstract form: for a regular space $V$ over a local field with
$\dim V \ge 3$ there is a lattice $L$ on $V$ with $\theta(O^+(L)) = K^\times$. (Anisotropic case: a maximal lattice,
91:5 and 91:6; isotropic case: `loc91_exists_lattice_isotropic`.) -/
theorem loc91_exists_lattice (hK : LocalHilbertField K)
    (hV : (QuadraticMap.associated Q).Nondegenerate) (h3 : 3 ≤ finrank K V) :
    ∃ L : Submodule R V, L.IsLattice K ∧
      ∀ c : K, c ≠ 0 → ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ c := by
  by_cases hiso : ∃ w : V, w ≠ 0 ∧ Q w = 0
  · obtain ⟨w, hw0, hQw⟩ := hiso
    exact loc91_exists_lattice_isotropic Q hV h3 hw0 hQw
  · push Not at hiso
    have haniso : Q.Anisotropic := fun x hx => by_contra fun hne => hiso x hne hx
    obtain ⟨L, hL⟩ := exists_isMaximal Q hV (a := R ∙ (1 : K)) (fg_span_singleton _)
      (by simp)
    refine ⟨L, hL.1, fun c hc => ?_⟩
    obtain ⟨σ, hσ, hs⟩ := loc91_exists_hasSpinorNorm (R := R) Q hK hV h3 hc
    refine ⟨σ, ⟨?_, hσ⟩, hs⟩
    rw [orthLat_eq_orth_of_isMaximal Q haniso hL]
    exact hσ.1

end Max

/-! ### The statements for completions of number fields -/

section NumberFieldCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion F) V]
  [FiniteDimensional (v.adicCompletion F) V]
variable (Q : QuadraticForm (v.adicCompletion F) V)

/-- **Proposition 91:6** (O'Meara 1963, p. 242): for a regular quadratic space $V$ over a local field
$F_\mathfrak p$ with $\dim V \ge 3$, $\theta(O^+(V)) = \dot F$: the spinor norm
$\theta : O^+(V) \to F_\mathfrak p^\times/F_\mathfrak p^{\times 2}$ is surjective. (Dimension $\ge 4$: $V$ is universal,
63:18, so a symmetry with any prescribed spinor norm exists; dimension $3$: $V$ represents every class other than
$-dV$ and every class is a product of two such classes. Both through `loc91_exists_two_values`.) -/
@[kb "omeara1963" "§91B, 91:6, p. 242"]
theorem spinorNormHom_surjective_of_three_le (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank (v.adicCompletion F) V) : Function.Surjective (spinorNormHom Q hV) :=
  loc91_spinorNormHom_surjective (R := v.adicCompletionIntegers F) Q
    (HasseIsoNF.localHilbertField_adicCompletion v) hV h3

variable [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **91:3, remark for $\dim V \ge 4$** (O'Meara 1963, p. 241): if $L$ is an $\mathfrak a$-maximal lattice on a regular
space $V$ over a local field with $\dim V \ge 4$ then $Q(L) = \mathfrak a$ (as $V$ is universal, 63:18, and
$Q(L) = Q(V) \cap \mathfrak a$ by 91:3). -/
@[kb "omeara1963" "§91A, 91:3, p. 241 (dim V ≥ 4: Q(L) = a)"]
theorem Q_image_eq_of_four_le (hV : (QuadraticMap.associated Q).Nondegenerate)
    {a : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F)}
    {L : Submodule (v.adicCompletionIntegers F) V} (hL : IsMaximal Q a L)
    (h4 : 4 ≤ finrank (v.adicCompletion F) V) : Q '' (L : Set V) = (a : Set (v.adicCompletion F)) :=
  loc91_Q_image_eq_of_four_le Q (HasseIsoNF.localHilbertField_adicCompletion v) hV hL h4

/-- **91:3, remark for $\dim V = 3$** (O'Meara 1963, p. 241): $V$ represents either all units or all prime elements
(up to the excluded square class $-dV$), hence for any $0 \ne \beta \in \mathfrak a$ either $Q(L) \supseteq \beta\mathfrak u$
or $Q(L) \supseteq \pi\beta\mathfrak u$, for an irreducible element $\pi$ of $\mathfrak o$. -/
@[kb "omeara1963" "§91A, 91:3, p. 241 (dim V = 3: Q(L) ⊇ βu or πβu)"]
theorem Q_image_ternary (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : finrank (v.adicCompletion F) V = 3)
    {a : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F)}
    {L : Submodule (v.adicCompletionIntegers F) V} (hL : IsMaximal Q a L)
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π) {β : v.adicCompletion F} (hβa : β ∈ a)
    (hβ : β ≠ 0) :
    (∀ u : v.adicCompletionIntegers F, IsUnit u →
        β * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) u ∈ Q '' (L : Set V)) ∨
      (∀ u : v.adicCompletionIntegers F, IsUnit u →
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) π * β *
          algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) u ∈ Q '' (L : Set V)) :=
  loc91_Q_image_ternary Q (HasseIsoNF.localHilbertField_adicCompletion v) hV h3 hL hπ hβa hβ

/-- **Proposition 91:8** (O'Meara 1963, p. 243): if $L$ is a maximal lattice on a regular quadratic space $V$ over a
local field with $\dim V \ge 3$, then $\theta(O^+(L)) \supseteq \mathfrak u$: every unit $\varepsilon$ of $\mathfrak o$ is
the spinor norm of some $\sigma \in O^+(L)$. The isotropic case is
`exists_hasSpinorNorm_of_isMaximal_isotropic`; the anisotropic case is 91:5 and 91:6 (see the docstring of
`exists_hasSpinorNorm_of_isMaximal_anisotropic`). -/
@[kb "omeara1963" "§91B, 91:8, p. 243"]
theorem exists_hasSpinorNorm_of_isMaximal (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank (v.adicCompletion F) V)
    {a : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F)}
    {L : Submodule (v.adicCompletionIntegers F) V} (hL : IsMaximal Q a L)
    {ε : v.adicCompletionIntegers F} (hε : IsUnit ε) :
    ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ε) :=
  loc91_exists_hasSpinorNorm_of_isMaximal Q (HasseIsoNF.localHilbertField_adicCompletion v) hV h3 hL hε

/-- **Proposition 91:8, anisotropic case** (O'Meara 1963, p. 243): on an anisotropic regular space of dimension
$\ge 3$ over a local field, a maximal lattice $L$ has $O^+(L) = O^+(V)$ (91:5, as $O(L) = O(V)$), so
$\theta(O^+(L)) = \theta(O^+(V)) = \dot F$ by 91:6; in particular every unit is a spinor norm of $O^+(L)$. -/
@[kb "omeara1963" "§91B, 91:8, p. 243 (anisotropic case: O⁺(L) = O⁺(V))"]
theorem exists_hasSpinorNorm_of_isMaximal_anisotropic (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank (v.adicCompletion F) V) (haniso : Q.Anisotropic)
    {a : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F)}
    {L : Submodule (v.adicCompletionIntegers F) V} (hL : IsMaximal Q a L) :
    orthLatPlus Q L = orthPlus Q ∧ ∀ c : v.adicCompletion F, c ≠ 0 →
      ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ c := by
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  have hLV : orthLatPlus Q L = orthPlus Q := by
    unfold orthLatPlus
    rw [orthLat_eq_orth_of_isMaximal Q haniso hL]
    exact inf_eq_right.mpr fun σ hσ => hσ.1
  refine ⟨hLV, fun c hc => ?_⟩
  obtain ⟨σ, hσ, hs⟩ := loc91_exists_hasSpinorNorm (R := v.adicCompletionIntegers F) Q hK hV h3 hc
  exact ⟨σ, hLV ▸ hσ, hs⟩

/-- **Proposition 91:7** (O'Meara 1963, pp. 242-243): for a regular quadratic space $V$ over a local field with
$\dim V \ge 3$ there is a lattice $L$ on $V$ with $\theta(O^+(L)) = \dot F$: every $c \in F_\mathfrak p^\times$ is the
spinor norm of some $\sigma \in O^+(L)$. -/
@[kb "omeara1963" "§91B, 91:7, pp. 242–243"]
theorem exists_lattice_spinorNorm_eq_top (hV : (QuadraticMap.associated Q).Nondegenerate)
    (h3 : 3 ≤ finrank (v.adicCompletion F) V) :
    ∃ L : Submodule (v.adicCompletionIntegers F) V, L.IsLattice (v.adicCompletion F) ∧
      ∀ c : v.adicCompletion F, c ≠ 0 → ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ c :=
  loc91_exists_lattice Q (HasseIsoNF.localHilbertField_adicCompletion v) hV h3

end NumberFieldCompletion

end QuadFormsKB.OMeara
