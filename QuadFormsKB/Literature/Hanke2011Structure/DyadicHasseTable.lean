/-
# Hanke 2011, Lemma 7.2 for $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb Q_2$: the dyadic table

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Lemma 7.2, pp. 27–29 (second table and Case 2 of the proof).

**The statement.** Let $G_2$ run over the primitive local genera of $\mathbb Z_2$-valued binary quadratic forms with
fixed Hessian determinant $\det_H(G_2)$. The second table of Lemma 7.2 gives, for each partial local genus symbol
(Definition 5.1, Lemma 7.1: $(\bar 2), (2), (1,1), (1;1), (1::1)$), the number of genera with $c_2 = 1$ and with
$c_2 = -1$:

| symbol | $\det_H$ | $c_2 = 1$ | $c_2 = -1$ | condition |
|---|---|---|---|---|
| $(\bar 2)$ | $u$ | 0 | 0 | $u \equiv 1 \bmod 4$ |
| $(\bar 2)$ | $u$ | 0 (*erratum:* 1) | 1 (*erratum:* 0) | $u \equiv 3 \bmod 4$ |
| $(2)$ | $u$ | 1 | 1 | $u \equiv 1 \bmod 4$ |
| $(2)$ | $u$ | 1 | 0 | $u \equiv 3 \bmod 4$ |
| $(1,1)$ | – | 1 | 1 | – |
| $(1;1)$ | $u$ | 1 | 1 | $u \equiv 1 \bmod 4$ |
| $(1;1)$ | $u$ | 2 | 0 | $u \equiv 3 \bmod 4$ |
| $(1::1)$ | $u2^\nu$ | 2 | 2 | $\nu$ odd or $u \equiv 1 \bmod 4$ |
| $(1::1)$ | $u2^\nu$ | 4 | 0 | $\nu$ even and $u \equiv 3 \bmod 4$ |

**Reading of the table.** For a primitive binary form $Q = ax^2 + bxy + cy^2$ over $\mathbb Z_2$ with Hessian
$H = \begin{pmatrix}2a & b\\ b & 2c\end{pmatrix}$, the partial symbol is fixed by $\nu = \mathrm{ord}_2(\det_H Q)$: $b$ odd
gives $(\bar 2)$ and $\nu = 0$; otherwise $Q \cong ux^2 + 2^{\mu}u'y^2$ with $u, u'$ units (`Composition.exists_diagForm`),
$\det_H = 2^{\mu+2}uu'$, and $\mu = 0, 1, 2, \ge 3$ is $(2), (1,1), (1;1), (1::1)$ (Remark 5.2: ";" separates scales
differing by $4$, "::" separates trains). So the column $\det_H$ fixes the unit part $u$ of $\det_H = 2^{\nu}u$, with
$\nu = 0, 2, 3, 4$ for the first four symbols and $\nu \ge 5$ for $(1::1)$; $\nu = 1$ never occurs (Remark 2.11,
`remark_2_11_even_dyadic`). Since the paper's $\nu$ in the last row is $\mathrm{ord}_2(\det_H)$ and $\mu = \nu - 2$, the
parity conditions are the same for both.

**Formalization.** The genera are Cassels' $\mathbb Z_2$-classes `Composition.LocalClasses 2 D` of primitive
$\mathbb Z_2$-forms of discriminant $D = b^2 - 4ac = -\det_H$ (with $\det_H$ fixed as an element, not only as a squareclass:
every form whose $\det_H$ lies in the squareclass of $s$ is $\mathbb Z_2$-equivalent to one with $\det_H = s$, by scaling a
variable by a unit). Every squareclass of $\mathbb Q_2^\times$ has a representative $s = 2^\nu u$ with $u \in \mathbb Z$ odd, so
we take $s \in \mathbb Z$. The Hasse invariant is Serre's $c_2 = \prod_{i<j}(a_i,a_j)_2$ of a diagonalization over $\mathbb Q_2$
(`Composition.hasseC`), the convention of the paper's proofs ($c_{\mathfrak p}(u_1x^2 + \pi^\nu u_2y^2) = (u_1, \pi^\nu u_2)_{\mathfrak p}$
in Case 1, $c_{\mathfrak p}(uQ) = (ua, u2^\nu b)_{\mathfrak p}$ in Case 2). `hasseCount 2 D ε` is the number of classes with
$c_2 = \varepsilon$.

**Proof.** A form representing a unit $w$ has $c_2 = (w, D)_2$ (`Composition.hasseC_eq_of_represents`), so $c_2$ is a
function of the set of residues mod $8$ of the unit values, Cassels' complete invariant `Composition.Phi` (the proof of
`Composition.card_two_even`); with the $2$-adic Hilbert symbol formula (`HilbertLocal.hilbertSymbol_two_formula`) the
count becomes a finite computation over $\mathbb Z/8$ (`countTable`, checked by `decide`).

*Erratum.* Row $(\bar 2)$, $u \equiv 3 \bmod 4$: the unique genus
(for each such $u$; e.g. $x^2 + xy + y^2$ for $u \equiv 3$, $xy$ for $u \equiv 7 \bmod 8$) represents $1$, so
$c_2 = (1, -u)_2 = 1$; the table and the proof ("both with $c_{\mathfrak p} = -1$") print $c_2 = -1$
(`lemma_7_2_dyadic_bar_two`). Every other row is confirmed as printed. (In the other common convention
$\prod_{i \le j}(a_i,a_j)$ the row $(\bar 2)$ would be right but the rows $(2)$, $u \equiv 3$, $(1;1)$ and $(1::1)$,
$u \equiv 3$, would be wrong; the paper's proofs use Serre's.)

**Proves** (all unconditional): `lemma_7_2_dyadic_bar_two`, `lemma_7_2_dyadic_bar_two_one_mod_four`,
`lemma_7_2_dyadic_two`, `lemma_7_2_dyadic_one_one`, `lemma_7_2_dyadic_one_semi_one`, `lemma_7_2_dyadic_one_colon_one`.
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicExistence
import QuadFormsKB.Literature.Cassels.Ch14.ExistenceImage

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Composition QuadFormsKB.Siegel QuadFormsKB.HilbertLocal

noncomputable section

/-! ### The Hasse invariant of a $\mathbb Z_2$-class -/

theorem map_eval_padic {p : ℕ} [Fact p.Prime] (Q : QuadForm ℤ_[p] 2) (x : Fin 2 → ℤ_[p]) :
    (Q.map PadicInt.Coe.ringHom).eval (fun i => ((x i : ℤ_[p]) : ℚ_[p])) = ((Q.eval x : ℤ_[p]) : ℚ_[p]) := by
  show (Q.map PadicInt.Coe.ringHom).evalIn ℚ_[p] _ = PadicInt.Coe.ringHom (Q.evalIn ℤ_[p] x)
  unfold QuadForm.evalIn
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp only [Algebra.algebraMap_self, RingHom.id_apply, QuadForm.map, Matrix.map_apply, map_mul]; rfl
  · simp

/-- The Hasse invariant over $\mathbb Q_p$ of a primitive $\mathbb Z_p$-form of discriminant $D \ne 0$ is $(w, D)_p$ for
every unit $w$ it represents over $\mathbb Z_p$. -/
theorem hasseC_eq_of_unit_value {p : ℕ} [Fact p.Prime] {D : ℤ} (hD : D ≠ 0) (F : LocalPrimForm p D) {v : Fin 2 → ℤ_[p]} :
    hasseC (F.1.map PadicInt.Coe.ringHom) = hilbertSymbol ℚ_[p] ((F.1.eval v : ℤ_[p]) : ℚ_[p]) (D : ℚ_[p]) ∨
      F.1.eval v = 0 := by
  by_cases h0 : F.1.eval v = 0
  · exact Or.inr h0
  left
  have hDp : (D : ℚ_[p]) ≠ 0 := by exact_mod_cast hD
  have hg : -(F.1.map PadicInt.Coe.ringHom).hessian.det = (D : ℚ_[p]) := by
    have h := F.2.2
    rw [Siegel.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_neg, h]
    simp
  refine hasseC_eq_of_represents p hDp hg (by rwa [Ne, PadicInt.coe_eq_zero]) ⟨fun i => ((v i : ℤ_[p]) : ℚ_[p]), ?_⟩
  simpa [QuadForm.evalIn] using map_eval_padic F.1 v

/-- A class has one Hasse invariant: $\mathbb Z_p$-equivalent forms have the same $c_p$. -/
theorem hasseC_eq_of_isometricGL {p : ℕ} [Fact p.Prime] {D : ℤ} {F G : LocalPrimForm p D} (h : IsometricGL F.1 G.1) :
    hasseC (F.1.map PadicInt.Coe.ringHom) = hasseC (G.1.map PadicInt.Coe.ringHom) := by
  by_cases hD : D = 0
  · subst hD
    have hdeg : ∀ H : LocalPrimForm p 0, ¬ (H.1.map PadicInt.Coe.ringHom).Nondegenerate := by
      intro H
      obtain ⟨g, _, hgd⟩ := H
      intro hH
      apply hH
      show (g.map PadicInt.Coe.ringHom).hessian.det = 0
      rw [Siegel.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [Int.cast_zero, neg_eq_zero] at hgd
      rw [hgd, map_zero]
    unfold hasseC
    simp [hdeg F, hdeg G]
  obtain ⟨v, hv⟩ := exists_unit_value G.2.1
  obtain ⟨g, hg⟩ := h
  have hFv : F.1.eval (g.val.mulVec v) = G.1.eval v := hg v
  rcases hasseC_eq_of_unit_value hD G (v := v) with hG | hG
  · rcases hasseC_eq_of_unit_value hD F (v := g.val.mulVec v) with hF | hF
    · rw [hF, hG, hFv]
    · exact absurd (hFv ▸ hF) hv.ne_zero
  · exact absurd hG hv.ne_zero

/-- **The Hasse invariant $c_p$ of a $\mathbb Z_p$-class** (Serre's convention, computed over $\mathbb Q_p$). -/
def hasseClass {p : ℕ} [Fact p.Prime] {D : ℤ} : LocalClasses p D → ℤ :=
  Quotient.lift (s := localSetoid p D) (fun F => hasseC (F.1.map PadicInt.Coe.ringHom))
    (fun _ _ h => hasseC_eq_of_isometricGL h)

/-- **The number of primitive local genera with $\det_H = -D$ and $c_p = \varepsilon$** at $p$ (Hanke 2011, Lemma 7.2): the $\mathbb Z_p$-classes of primitive
binary forms of discriminant $D$ with Hasse invariant $\varepsilon$. -/
def hasseCount (p : ℕ) [Fact p.Prime] (D : ℤ) (ε : ℤ) : ℕ := Nat.card {G : LocalClasses p D // hasseClass G = ε}

/-! ### The finite computation -/

/-- The value $(w, 2^\alpha v)_2$ for units $w, v$ with residues $a, \bar v$ mod $8$ (`hilbertSymbol_two_formula`). -/
def hval (α : ℕ) (vb a : R8) : ℤ := (-1) ^ (twoEps a * twoEps vb + α * twoOmega a)

/-- The classes with given Hasse invariant, counted through Cassels' invariant `Phi` (the residues mod $8$ of the unit
values; for $D = 4d$ the possible values are `Tset (d mod 8)`). -/
def countTable (m : R8) (α : ℕ) (vb : R8) (ε : ℤ) : ℕ :=
  ((Tset m).filter fun S => ∃ a ∈ S, hval α vb a = ε).card

theorem hval_mod_two (α : ℕ) (vb a : R8) : hval α vb a = hval (α % 2) vb a := by
  unfold hval
  rw [← Nat.mod_add_div α 2]
  simp only [Nat.add_mul_mod_self_left, Nat.mod_mod]
  rw [add_mul, ← add_assoc, pow_add, mul_assoc 2, pow_mul, neg_one_sq, one_pow, mul_one]

theorem countTable_mod_two (m : R8) (α : ℕ) (vb : R8) (ε : ℤ) :
    countTable m α vb ε = countTable m (α % 2) vb ε := by
  unfold countTable
  simp_rw [hval_mod_two α]

/-! ### Counting through Cassels' invariant -/

/-- $(w, 2^\alpha v)_2$ for $\mathbb Z_2$-units $w, v$ is `hval α (v mod 8) (w mod 8)`. -/
theorem hilbert_eq_hval {α : ℕ} (v : ℤ_[2]ˣ) {w : ℤ_[2]} (hw : IsUnit w) :
    hilbertSymbol ℚ_[2] (w : ℚ_[2]) ((2 : ℚ_[2]) ^ α * ((v : ℤ_[2]) : ℚ_[2])) = hval α (pi8 v) (pi8 w) := by
  have h := hilbertSymbol_two_formula 0 α hw.unit v
  simp only [pow_zero, one_mul, IsUnit.unit_spec, zero_mul, add_zero] at h
  rw [h, hval]

/-- **The count of classes with $c_2 = \varepsilon$ for $D = 4d = 2^\alpha v$** ($v$ a unit) is the finite count
`countTable (d mod 8) α (v mod 8) ε`. -/
theorem hasseCount_eq_countTable {d : ℤ} (hd : d ≠ 0) {α : ℕ} (v : ℤ_[2]ˣ)
    (hDv : ((4 * d : ℤ) : ℚ_[2]) = (2 : ℚ_[2]) ^ α * ((v : ℤ_[2]) : ℚ_[2])) (ε : ℤ) :
    hasseCount 2 (4 * d) ε = countTable (d : R8) α (pi8 v) ε := by
  classical
  have hD0 : (4 * d : ℤ) ≠ 0 := by omega
  have hD : ((4 * d : ℤ) : ℤ_[2]) = 4 * (d : ℤ_[2]) := by push_cast; ring
  have hp : Prime (2 : ℤ_[2]) := by simpa using PadicInt.prime_p (p := 2)
  have hhalf := half_of_two_dvd hp (D := ((4 * d : ℤ) : ℤ_[2])) ⟨2 * (d : ℤ_[2]), by rw [hD]; ring⟩
  let PhiC : LocalClasses 2 (4 * d) → Finset R8 :=
    Quotient.lift (s := localSetoid 2 (4 * d)) (fun F => Phi F.1) (fun F G h => Phi_iso h)
  have PhiC_mk : ∀ F : LocalPrimForm 2 (4 * d), PhiC (Quotient.mk _ F) = Phi F.1 := fun F => rfl
  -- `PhiC` is injective (Cassels' proof of Lemma 3.3, `card_two_even`)
  have inj : Function.Injective PhiC := by
    intro a b hab
    induction a using localClasses_ind with | _ F => ?_
    induction b using localClasses_ind with | _ G => ?_
    rw [PhiC_mk, PhiC_mk] at hab
    obtain ⟨u, e, hu, h, hF⟩ := exists_diagForm hhalf F
    obtain ⟨u', e', hu', h', hG⟩ := exists_diagForm hhalf G
    have hF' : IsometricGL F.1 (bq u 0 e) := hF
    have hG' : IsometricGL G.1 (bq u' 0 e') := hG
    have h1 : Phi (bq u 0 e) = Phi (bq u' 0 e') := by
      rw [← Phi_iso hF', ← Phi_iso hG']; exact hab
    have hmem : pi8 u ∈ Phi (bq u 0 e) := by
      rw [mem_Phi, mem_Uset_bq]
      exact ⟨(isUnit_iff_oddRes _).mp hu, 1, 0, by simp⟩
    rw [h1, mem_Phi, mem_Uset_bq] at hmem
    obtain ⟨_, s, t, hst⟩ := hmem
    obtain ⟨s', rfl⟩ := pi8_surj s
    obtain ⟨t', rfl⟩ := pi8_surj t
    have hw : pi8 (u' * s' ^ 2 + e' * t' ^ 2) = pi8 u := by simpa using hst
    have hwU : IsUnit (u' * s' ^ 2 + e' * t' ^ 2) :=
      (isUnit_iff_oddRes _).mpr (by rw [hw]; exact (isUnit_iff_oddRes _).mp hu)
    have key : IsometricGL (bq u' 0 e') (bq u 0 e) :=
      diag_equiv_of_mod8 hhalf hu h' h hwU rfl hw
    exact localClasses_sound (hF'.trans (key.symm.trans hG'.symm))
  set m : R8 := pi8 (d : ℤ_[2]) with hm
  -- its range is `Tset m`
  have hrange : Set.range PhiC = ↑(Tset m) := by
    ext S
    simp only [Set.mem_range, Finset.mem_coe, Tset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨q, rfl⟩
      induction q using localClasses_ind with | _ F => ?_
      obtain ⟨u, e, hu, h, hF⟩ := exists_diagForm hhalf F
      have hF' : IsometricGL F.1 (bq u 0 e) := hF
      have hodd : OddRes (pi8 u) := (isUnit_iff_oddRes _).mp hu
      have hue : u * e = -(d : ℤ_[2]) := by
        rw [hD] at h
        exact mul_left_cancel₀ (four_ne_zero_padic (p := 2)) (by linear_combination (-1 : ℤ_[2]) * h)
      have hm' : pi8 u * pi8 e = -m := by
        rw [← map_mul, hue, map_neg]
      have haa := oddRes_mul_self _ hodd
      have hπ : pi8 e = -m * pi8 u := by
        linear_combination (-pi8 e) * haa + pi8 u * hm'
      refine ⟨pi8 u, hodd, ?_⟩
      rw [PhiC_mk, Phi_iso hF', Phi_bq, hπ]
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨u, rfl⟩ := pi8_surj a
      have hu : IsUnit u := (isUnit_iff_oddRes _).mpr ha
      obtain ⟨ui, hui⟩ := hu.exists_right_inv
      have h : -4 * u * (-(d : ℤ_[2]) * ui) = ((4 * d : ℤ) : ℤ_[2]) := by
        rw [hD]; linear_combination (4 * (d : ℤ_[2])) * hui
      refine ⟨Quotient.mk _ (diagForm u (-(d : ℤ_[2]) * ui) hu h), ?_⟩
      rw [PhiC_mk]
      show Phi (bq u 0 (-(d : ℤ_[2]) * ui)) = _
      rw [Phi_bq]
      have haa := oddRes_mul_self _ ha
      have hui' : pi8 u * pi8 ui = 1 := by rw [← map_mul, hui, map_one]
      have : pi8 (-(d : ℤ_[2]) * ui) = -m * pi8 u := by
        have hpu : pi8 ui = pi8 u := by linear_combination (-pi8 ui) * haa + pi8 u * hui'
        rw [map_mul, map_neg, hpu, hm]
      rw [this]
  -- the Hasse invariant of a class, read off `PhiC`
  set Q : Finset R8 → Prop := fun S => ∃ a ∈ S, hval α (pi8 v) a = ε with hQ
  have hhasse : ∀ G : LocalClasses 2 (4 * d), hasseClass G = ε ↔ Q (PhiC G) := by
    intro G
    induction G using localClasses_ind with | _ F => ?_
    have hval_of : ∀ x : Fin 2 → ℤ_[2], IsUnit (F.1.eval x) →
        hasseClass (Quotient.mk _ F) = hval α (pi8 v) (pi8 (F.1.eval x)) := by
      intro x hx
      show hasseC (F.1.map PadicInt.Coe.ringHom) = _
      rcases hasseC_eq_of_unit_value hD0 F (v := x) with h | h
      · rw [h, hDv, hilbert_eq_hval v hx]
      · exact absurd h hx.ne_zero
    rw [PhiC_mk]
    constructor
    · intro hc
      obtain ⟨x, hx⟩ := exists_unit_value F.2.1
      exact ⟨pi8 (F.1.eval x), mem_Phi.mpr ⟨x, hx, rfl⟩, by rw [← hval_of x hx, hc]⟩
    · rintro ⟨a, ha, hae⟩
      obtain ⟨x, hx, rfl⟩ := mem_Phi.mp ha
      rw [hval_of x hx, hae]
  have hm8 : m = (d : R8) := by simp [hm]
  rw [← hm8]
  unfold hasseCount countTable
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun G => ⟨PhiC G.1, ?_⟩) ⟨?_, ?_⟩)
  · rw [Finset.mem_filter, ← Finset.mem_coe, ← hrange]
    exact ⟨⟨G.1, rfl⟩, (hhasse G.1).mp G.2⟩
  · intro G G' h
    exact Subtype.ext (inj (congrArg Subtype.val h))
  · rintro ⟨S, hS⟩
    rw [Finset.mem_filter, ← Finset.mem_coe, ← hrange] at hS
    obtain ⟨⟨G, rfl⟩, hq⟩ := hS
    exact ⟨⟨G, (hhasse G).mpr hq⟩, rfl⟩

/-- The count for $\det_H = 2^\nu u$, $\nu \ge 2$, $u$ odd, as a finite computation over $\mathbb Z/8$. -/
theorem hasseCount_pow_two (ν : ℕ) (hν : 2 ≤ ν) {u : ℤ} (hu : Odd u) (ε : ℤ) :
    hasseCount 2 (-(2 ^ ν * u)) ε = countTable ((-(2 ^ (ν - 2) * u) : ℤ) : R8) (ν % 2) ((-u : ℤ) : R8) ε := by
  have hu2 : ¬ ((2 : ℕ) : ℤ) ∣ -u := by
    rw [Int.dvd_neg]; exact_mod_cast (Int.not_even_iff_odd.mpr hu ∘ even_iff_two_dvd.mpr)
  set v : ℤ_[2]ˣ := (isUnit_intCast_of_not_dvd 2 hu2).unit with hv
  have hD : -(2 ^ ν * u) = 4 * (-(2 ^ (ν - 2) * u)) := by
    obtain ⟨k, rfl⟩ : ∃ k, ν = k + 2 := ⟨ν - 2, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have hd : -(2 ^ (ν - 2) * u) ≠ 0 := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ two_ne_zero) this)
  rw [hD, hasseCount_eq_countTable hd (α := ν) v ?_ ε, countTable_mod_two]
  · congr 2
    simp [hv]
  · rw [← hD, hv, IsUnit.unit_spec]; push_cast; ring

/-! ### The finite tables (checked by `decide`) -/

/-- Rows $(2)$: $\det_H = 4u$, i.e. $d = -u$, $\alpha = 2$. -/
theorem table_two : ∀ ub : R8, OddRes ub →
    (ub.val % 4 = 1 → countTable (-ub) 0 (-ub) 1 = 1 ∧ countTable (-ub) 0 (-ub) (-1) = 1) ∧
    (ub.val % 4 = 3 → countTable (-ub) 0 (-ub) 1 = 1 ∧ countTable (-ub) 0 (-ub) (-1) = 0) := by
  decide

/-- Row $(1,1)$: $\det_H = 8u$, i.e. $d = -2u$, $\alpha = 3$. -/
theorem table_one_one : ∀ ub : R8, OddRes ub →
    countTable (-(2 * ub)) 1 (-ub) 1 = 1 ∧ countTable (-(2 * ub)) 1 (-ub) (-1) = 1 := by
  decide

/-- Rows $(1;1)$: $\det_H = 16u$, i.e. $d = -4u$, $\alpha = 4$. -/
theorem table_one_semi_one : ∀ ub : R8, OddRes ub →
    (ub.val % 4 = 1 → countTable (-(4 * ub)) 0 (-ub) 1 = 1 ∧ countTable (-(4 * ub)) 0 (-ub) (-1) = 1) ∧
    (ub.val % 4 = 3 → countTable (-(4 * ub)) 0 (-ub) 1 = 2 ∧ countTable (-(4 * ub)) 0 (-ub) (-1) = 0) := by
  decide

/-- Rows $(1::1)$: $\det_H = 2^\nu u$, $\nu \ge 5$, i.e. $8 \mid d$, $\alpha = \nu$. -/
theorem table_one_colon_one : ∀ a : Fin 2, ∀ ub : R8, OddRes ub →
    ((a.val = 1 ∨ ub.val % 4 = 1) → countTable 0 a.val (-ub) 1 = 2 ∧ countTable 0 a.val (-ub) (-1) = 2) ∧
    ((a.val = 0 ∧ ub.val % 4 = 3) → countTable 0 a.val (-ub) 1 = 4 ∧ countTable 0 a.val (-ub) (-1) = 0) := by
  decide

/-! ### Lemma 7.2, $F_{\mathfrak p} = \mathbb Q_2$ -/

theorem oddRes_intCast {u : ℤ} (hu : Odd u) : OddRes (u : R8) := by
  have hu2 : ¬ ((2 : ℕ) : ℤ) ∣ u := by exact_mod_cast (Int.not_even_iff_odd.mpr hu ∘ even_iff_two_dvd.mpr)
  have h := (isUnit_iff_oddRes _).mp (isUnit_intCast_of_not_dvd 2 hu2)
  rwa [map_intCast] at h

theorem val_intCast_mod_four (u : ℤ) :
    (u % 4 = 1 ↔ (u : R8).val % 4 = 1) ∧ (u % 4 = 3 ↔ (u : R8).val % 4 = 3) := by
  have h := ZMod.val_intCast (n := 2 ^ 3) u
  have h8 : ((2 ^ 3 : ℕ) : ℤ) = 8 := by norm_num
  rw [h8] at h
  constructor <;> omega

theorem hasseCount_of_isEmpty {D : ℤ} (h : IsEmpty (LocalPrimForm 2 D)) (ε : ℤ) : hasseCount 2 D ε = 0 := by
  unfold hasseCount
  have : IsEmpty (LocalClasses 2 D) := ⟨fun G => by
    induction G using localClasses_ind with | _ F => exact h.false F⟩
  simp

/-- **Lemma 7.2, $(\bar 2)$, $u \equiv 1 \bmod 4$** (Hanke 2011, p. 28): no primitive binary $\mathbb Z_2$-form has
$\det_H = u$ (indeed $\det_H \equiv 0, -1 \bmod 4$ always, `hessian_det_mod_four`). -/
@[kb "hanke2011structure" "Lemma 7.2, p. 28 (F_p = Q_2, symbol (2̄), u ≡ 1 mod 4)"]
theorem lemma_7_2_dyadic_bar_two_one_mod_four {u : ℤ} (hu : u % 4 = 1) :
    hasseCount 2 (-u) 1 = 0 ∧ hasseCount 2 (-u) (-1) = 0 := by
  have hE : IsEmpty (LocalPrimForm 2 (-u)) := by
    refine ⟨fun F => ?_⟩
    have hdet : F.1.hessian.det = (u : ℤ_[2]) := by
      have h := F.2.2; push_cast at h; linear_combination -h
    obtain ⟨k, hk⟩ : ∃ k, u = 4 * k + 1 := ⟨u / 4, by omega⟩
    have h4 : ∀ x : ℤ_[2], (4 : ℤ_[2]) ∣ x → PadicInt.toZModPow 2 x = 0 := by
      rintro x ⟨c, rfl⟩
      rw [map_mul, map_ofNat]
      have : (4 : ZMod (2 ^ 2)) = 0 := by decide
      rw [this, zero_mul]
    have hu' : PadicInt.toZModPow 2 (u : ℤ_[2]) = 1 := by
      rw [map_intCast, hk]; push_cast
      have : (4 : ZMod (2 ^ 2)) = 0 := by decide
      rw [this]; ring
    rcases hessian_det_mod_four 1 F.1.hessian ⟨F.1.coeff, rfl⟩ (by simp) with h | h
    · have := h4 _ h; rw [hdet, hu'] at this; exact absurd this (by decide)
    · have := h4 _ h; rw [map_sub, hdet, hu'] at this; simp at this
      exact absurd this (by decide)
  exact ⟨hasseCount_of_isEmpty hE 1, hasseCount_of_isEmpty hE (-1)⟩

/-- **Lemma 7.2, $(\bar 2)$, $u \equiv 3 \bmod 4$, corrected** (Hanke 2011, pp. 28; *erratum*): for $\det_H = u$ there is exactly one genus, and it has $c_2 = +1$ (it represents
$1$, so $c_2 = (1, -u)_2 = 1$); the paper prints $c_2 = -1$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 28 (F_p = Q_2, symbol (2̄), u ≡ 3 mod 4; erratum)"]
theorem lemma_7_2_dyadic_bar_two {u : ℤ} (hu : u % 4 = 3) :
    hasseCount 2 (-u) 1 = 1 ∧ hasseCount 2 (-u) (-1) = 0 := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, -u = 4 * q + 1 := ⟨(-u) / 4, by omega⟩
  have hD0 : (-u : ℤ) ≠ 0 := by omega
  have hall : ∀ G : LocalClasses 2 (-u), hasseClass G = 1 := by
    intro G
    induction G using localClasses_ind with | _ F => ?_
    have hiso := odd_normal (q := q) (exists_unit_value F.2.1) (by rw [← neg_det_eq_disc2, F.2.2, hq]; push_cast; ring)
    obtain ⟨g, hg⟩ := hiso
    have h1 : F.1.eval (g.val.mulVec ![1, 0]) = 1 := by rw [hg, bq_eval]; ring
    show hasseC (F.1.map PadicInt.Coe.ringHom) = 1
    rcases hasseC_eq_of_unit_value hD0 F (v := g.val.mulVec ![1, 0]) with h | h
    · rw [h, h1]; push_cast; rw [hilbertSymbol_comm, hilbertSymbol_one_right]
    · rw [h1] at h; exact absurd h one_ne_zero
  have hcard : Nat.card (LocalClasses 2 (-u)) = 1 := card_two_odd (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · unfold hasseCount
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  · unfold hasseCount
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun G => by have := G.2; rw [hall] at this; exact absurd this (by decide)⟩

/-- The printed row $(\bar 2)$, $u \equiv 3 \bmod 4$ ("$c_2 = 1$: $0$, $c_2 = -1$: $1$") is false, e.g. for $u = 3$
($x^2 + xy + y^2$). -/
@[kb "hanke2011structure" "Lemma 7.2, p. 28 (F_p = Q_2, symbol (2̄): printed row false)"]
theorem lemma_7_2_dyadic_bar_two_printed_false : ¬ (hasseCount 2 (-3) 1 = 0 ∧ hasseCount 2 (-3) (-1) = 1) := by
  rintro ⟨h, -⟩
  rw [(lemma_7_2_dyadic_bar_two (u := 3) (by norm_num)).1] at h
  exact absurd h one_ne_zero

/-- **Lemma 7.2, symbol $(2)$** (Hanke 2011, p. 28): $\det_H = 4u$, $u$ odd: two genera, $c_2 = \pm 1$, if
$u \equiv 1 \bmod 4$; one genus, $c_2 = 1$, if $u \equiv 3 \bmod 4$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 28 (F_p = Q_2, symbol (2))"]
theorem lemma_7_2_dyadic_two {u : ℤ} (hu : Odd u) :
    (u % 4 = 1 → hasseCount 2 (-(2 ^ 2 * u)) 1 = 1 ∧ hasseCount 2 (-(2 ^ 2 * u)) (-1) = 1) ∧
    (u % 4 = 3 → hasseCount 2 (-(2 ^ 2 * u)) 1 = 1 ∧ hasseCount 2 (-(2 ^ 2 * u)) (-1) = 0) := by
  have hc : ∀ ε, hasseCount 2 (-(2 ^ 2 * u)) ε = countTable (-(u : R8)) 0 (-(u : R8)) ε := fun ε => by
    rw [hasseCount_pow_two 2 le_rfl hu]; push_cast; norm_num
  simp only [hc, (val_intCast_mod_four u).1, (val_intCast_mod_four u).2]
  exact table_two _ (oddRes_intCast hu)

/-- **Lemma 7.2, symbol $(1,1)$** (Hanke 2011, p. 28): $\det_H = 8u$, $u$ odd: two genera, $c_2 = \pm 1$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 28 (F_p = Q_2, symbol (1,1))"]
theorem lemma_7_2_dyadic_one_one {u : ℤ} (hu : Odd u) :
    hasseCount 2 (-(2 ^ 3 * u)) 1 = 1 ∧ hasseCount 2 (-(2 ^ 3 * u)) (-1) = 1 := by
  have hc : ∀ ε, hasseCount 2 (-(2 ^ 3 * u)) ε = countTable (-(2 * (u : R8))) 1 (-(u : R8)) ε := fun ε => by
    rw [hasseCount_pow_two 3 (by norm_num) hu]; push_cast; norm_num
  simp only [hc]
  exact table_one_one _ (oddRes_intCast hu)

/-- **Lemma 7.2, symbol $(1;1)$** (Hanke 2011, p. 28): $\det_H = 16u$, $u$ odd: two genera, $c_2 = \pm 1$, if
$u \equiv 1 \bmod 4$; two genera, both $c_2 = 1$, if $u \equiv 3 \bmod 4$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 28 (F_p = Q_2, symbol (1;1))"]
theorem lemma_7_2_dyadic_one_semi_one {u : ℤ} (hu : Odd u) :
    (u % 4 = 1 → hasseCount 2 (-(2 ^ 4 * u)) 1 = 1 ∧ hasseCount 2 (-(2 ^ 4 * u)) (-1) = 1) ∧
    (u % 4 = 3 → hasseCount 2 (-(2 ^ 4 * u)) 1 = 2 ∧ hasseCount 2 (-(2 ^ 4 * u)) (-1) = 0) := by
  have hc : ∀ ε, hasseCount 2 (-(2 ^ 4 * u)) ε = countTable (-(4 * (u : R8))) 0 (-(u : R8)) ε := fun ε => by
    rw [hasseCount_pow_two 4 (by norm_num) hu]; push_cast; norm_num
  simp only [hc, (val_intCast_mod_four u).1, (val_intCast_mod_four u).2]
  exact table_one_semi_one _ (oddRes_intCast hu)

/-- **Lemma 7.2, symbol $(1::1)$** (Hanke 2011, p. 28): $\det_H = 2^\nu u$, $\nu \ge 5$, $u$ odd: four genera; two with
each $c_2 = \pm 1$ if $\nu$ is odd or $u \equiv 1 \bmod 4$, all four with $c_2 = 1$ if $\nu$ is even and
$u \equiv 3 \bmod 4$. -/
@[kb "hanke2011structure" "Lemma 7.2, p. 28 (F_p = Q_2, symbol (1::1))"]
theorem lemma_7_2_dyadic_one_colon_one {ν : ℕ} (hν : 5 ≤ ν) {u : ℤ} (hu : Odd u) :
    ((Odd ν ∨ u % 4 = 1) → hasseCount 2 (-(2 ^ ν * u)) 1 = 2 ∧ hasseCount 2 (-(2 ^ ν * u)) (-1) = 2) ∧
    ((Even ν ∧ u % 4 = 3) → hasseCount 2 (-(2 ^ ν * u)) 1 = 4 ∧ hasseCount 2 (-(2 ^ ν * u)) (-1) = 0) := by
  have h0 : ((-(2 ^ (ν - 2) * u) : ℤ) : R8) = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, ν = k + 5 := ⟨ν - 5, by omega⟩
    rw [show k + 5 - 2 = k + 3 by omega]
    push_cast
    rw [pow_add, show (2 : R8) ^ 3 = 0 by decide, mul_zero, zero_mul, neg_zero]
  have hc : ∀ ε, hasseCount 2 (-(2 ^ ν * u)) ε = countTable 0 (ν % 2) (-(u : R8)) ε := fun ε => by
    rw [hasseCount_pow_two ν (by omega) hu, h0]; push_cast; rfl
  have ht := table_one_colon_one ⟨ν % 2, Nat.mod_lt _ (by norm_num)⟩ _ (oddRes_intCast hu)
  simp only [hc, (val_intCast_mod_four u).1, (val_intCast_mod_four u).2]
  simp only [← Nat.odd_iff, ← Nat.even_iff] at ht
  exact ht

end

end QuadFormsKB.Hanke2011Structure
