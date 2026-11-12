/-
# Chenevier–Lannes, Chapters 1 and 2: even unimodular lattices and the class sets $X_n$

Source: G. Chenevier and J. Lannes, *Automorphic Forms and Even Unimodular Lattices: Kneser Neighbors of Niemeier
Lattices*, Ergebnisse der Mathematik 69, Springer, 2019 (`chenevierlannes2019`). **Page numbers are the printed pages of
the book.**

**Layer and dictionary.** The book's even unimodular lattice $L \subset \mathbb{R}^n$ (covolume $1$, $x \cdot x \in 2\mathbb{Z}$,
§1.1, p. 1) is recorded, as everywhere in this library, by its integral form $Q$ (`QuadForm ℤ n`) in a basis of $L$:
$$Q(\vec{x}) = q_L(\vec{x}) = \tfrac12\,\vec{x} \cdot \vec{x}, \qquad H = \text{Hessian of } Q = \text{Gram matrix of } L.$$
So the book's $q_L$ is exactly `Q.eval`, its inner product $x \cdot y$ is $\vec{x}^{\mathsf T}H\vec{y}$, and
- $L$ is **even** automatically ($x \cdot x = 2Q(x)$);
- $L$ is **unimodular** iff $\det H = 1$ (covolume $\sqrt{\det H}$);
- $L \subset \mathbb{R}^n$ (Euclidean) means $Q$ is positive definite.
The isomorphism classes of lattices are the $\mathrm{GL}_n(\mathbb{Z})$-classes of forms (`QClass n`), and the book's
$X_n$ is `classSet n`. The book's $O(L)$ is `Aut Q` (a subgroup of $\mathrm{GL}_n(\mathbb{Z})$, improper elements included).

**Defines** `IsEvenUnimodular`, `classSet` ($X_n$), `rootSet` ($R(L)$), `IsNiemeier`, `coxeterNumber` ($h(L)$),
`IsLeechType` (a Niemeier lattice without roots), the dimension `cn n p` of the quadric $C_L(\mathbb{F}_p)$ (as a
number: $c_n(p)$).

**Proves** (all unconditional):
- `eight_dvd_of_isEvenUnimodular` (§1.1, p. 1; Scholium 2.2.2 (b), p. 29): $8 \mid n$;
- `sameGenus_of_isEvenUnimodular`: any two even unimodular lattices of the same dimension are in the same genus
  (the book's Scholium 2.2.5 (b) / Proposition 2.2.6 together with the real place, pp. 31–32; here through
  Conway–Sloane's Lemma 2, `ConwaySloane.Mass.sameGenus_of_discIso`);
- `classSet_eq_genusClasses`, `classSet_finite` (§1.1, p. 1: $X_n$ is finite);
- `isEvenUnimodular_repE8`, `classSet_nonempty_iff` (§1.1, p. 1: $X_n \ne \emptyset \iff 8 \mid n$).
-/
import QuadFormsKB.Siegel.EvenUnimodularRank
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmasHold
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicBase
import QuadFormsKB.Literature.OMeara.Sec106Rank13Forms
import QuadFormsKB.Literature.Cassels.AppA.Watson
import QuadFormsKB.Literature.Hanke2011Structure.DyadicExistence

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Even unimodular lattices and the class set $X_n$ -/

/-- **An even unimodular lattice of dimension $n$** (Chenevier–Lannes, §1.1, p. 1, and §2.2, Definition after
Scholium 2.2.5, p. 32), recorded by its integral form $Q = q_L$ in a basis: $Q$ is positive definite (`posDef`, the
lattice lies in Euclidean $\mathbb{R}^n$) and its Hessian (the Gram matrix $x \cdot y$) has determinant $1$ (`det_one`,
covolume $1$). Evenness ($x \cdot x \in 2\mathbb{Z}$) is automatic for an integral form, since $x \cdot x = 2Q(x)$. -/
@[kb "chenevierlannes2019" "§1.1, p. 1; §2.2, p. 32"]
structure IsEvenUnimodular (Q : QuadForm ℤ n) : Prop where
  /-- $Q(\vec{x}) > 0$ for every nonzero $\vec{x} \in \mathbb{Z}^n$. -/
  posDef : IntQF.PosDef Q
  /-- The Gram matrix $H$ has determinant $1$. -/
  det_one : Q.hessian.det = 1

/-- **The set $X_n$** of isomorphism classes of even unimodular lattices of dimension $n$ (Chenevier–Lannes, §1.1,
p. 1): the $\mathrm{GL}_n(\mathbb{Z})$-classes of the forms satisfying `IsEvenUnimodular`. -/
@[kb "chenevierlannes2019" "§1.1, p. 1 (the set X_n)"]
def classSet (n : ℕ) : Set (QClass n) := {c | ∃ Q : QuadForm ℤ n, IsEvenUnimodular Q ∧ classOf Q = c}

/-- Being even unimodular is a class invariant. -/
theorem IsEvenUnimodular.of_intEquiv {Q Q' : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (h : IntEquiv Q Q') :
    IsEvenUnimodular Q' :=
  ⟨(h.sameGenus).posDef hQ.posDef, by rw [← (h.sameGenus).det_hessian_eq hQ.posDef]; exact hQ.det_one⟩

theorem mem_classSet_classOf {Q : QuadForm ℤ n} : classOf Q ∈ classSet n ↔ IsEvenUnimodular Q := by
  constructor
  · rintro ⟨Q', hQ', he⟩
    exact hQ'.of_intEquiv (classOf_eq_classOf_iff.mp he)
  · exact fun h => ⟨Q, h, rfl⟩

/-- **The dimension of an even unimodular lattice is divisible by $8$** (Chenevier–Lannes, §1.1, p. 1; Scholium 2.2.2 (b),
p. 29: the signature of a $q$-module over $\mathbb{Z}$ is divisible by $8$). Proved here by Serre's theta-series argument
(`Siegel.eight_dvd_of_posDef_det_one`). -/
@[kb "chenevierlannes2019" "§1.1, p. 1; Scholium 2.2.2 (b), p. 29 (positive definite case)"]
theorem eight_dvd_of_isEvenUnimodular {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) : 8 ∣ n :=
  eight_dvd_of_posDef_det_one hQ.posDef hQ.det_one

/-! ### One genus -/

theorem hessian_isSymm (Q : QuadForm ℤ n) : Q.hessian.IsSymm := by
  unfold QuadForm.hessian Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem hessian_evenDiag (Q : QuadForm ℤ n) : ConwaySloane.Mass.EvenGram Q.hessian := fun i => by
  unfold QuadForm.hessian
  simp only [Matrix.add_apply, Matrix.transpose_apply]
  exact ⟨Q.coeff i i, rfl⟩

/-- $\vec{x}^{\mathsf T}H\vec{x} = 2Q(\vec{x})$ over $\mathbb{Q}$, so $H$ is a positive definite Gram matrix. -/
theorem posDefGram_hessian {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) :
    ConwaySloane.Mass.PosDefGram Q.hessian := by
  refine ⟨(hessian_isSymm Q).eq, fun x hx => ?_⟩
  set d : ℕ := ∏ i, (x i).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun i _ => (x i).den_pos
  have hy : ∀ i, ∃ z : ℤ, (z : ℚ) = (d : ℚ) * x i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun i => (x i).den) (Finset.mem_univ i)
    refine ⟨(x i).num * k, ?_⟩
    have h1 : (x i) * ((x i).den : ℚ) = (x i).num := Rat.mul_den_eq_num (x i)
    have h2 : (d : ℚ) = ((x i).den : ℚ) * (k : ℚ) := by exact_mod_cast hk
    rw [h2]; push_cast
    rw [← h1]; ring
  choose y hy using hy
  have hyx : (fun i => (y i : ℚ)) = (d : ℚ) • x := by
    funext i; simp [hy i]
  have hy0 : y ≠ 0 := by
    intro h
    apply hx
    have : (d : ℚ) • x = 0 := by rw [← hyx, h]; funext i; simp
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h (by exact_mod_cast hdpos.ne')
    · exact h
  have hpos : 0 < Q.eval y := hQ y hy0
  have h2 := LocalDensity.two_mul_eval_eq_hessian Q y
  have e : (fun i => (y i : ℚ)) ⬝ᵥ (ConwaySloane.Mass.gramQ Q.hessian *ᵥ fun i => (y i : ℚ)) =
      ((y ⬝ᵥ (Q.hessian *ᵥ y) : ℤ) : ℚ) := by
    simp [ConwaySloane.Mass.gramQ, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hyx, mulVec_smul, smul_dotProduct, dotProduct_smul, ← h2] at e
  have hq : (0 : ℚ) < (d : ℚ) ^ 2 := by positivity
  have hq2 : (0 : ℚ) < ((2 * Q.eval y : ℤ) : ℚ) := by exact_mod_cast (by omega : (0 : ℤ) < 2 * Q.eval y)
  rw [← e] at hq2
  simp only [smul_eq_mul] at hq2
  have : (d : ℚ) * ((d : ℚ) * (x ⬝ᵥ (ConwaySloane.Mass.gramQ Q.hessian *ᵥ x))) =
      (d : ℚ) ^ 2 * (x ⬝ᵥ (ConwaySloane.Mass.gramQ Q.hessian *ᵥ x)) := by ring
  rw [this] at hq2
  exact pos_of_mul_pos_right hq2 hq.le

/-- $x^{\mathsf T}Hx$ as an integral form is $2Q$. -/
theorem ofMatrixZ_hessian (Q : QuadForm ℤ n) : LocalDensity.ofMatrixZ Q.hessian = (2 : ℤ) • Q := by
  ext i j
  simp only [LocalDensity.ofMatrixZ, QuadForm.hessian, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have := Q.upper (show i < j from h)
    simp [h, this]
    ring
  · simp; ring
  · have h1 : Q.coeff i j = 0 := Q.upper h
    simp [h.not_gt, h.ne', h1]

/-- Cancelling the factor $2$: $2Q \sim 2Q'$ in the genus sense implies $Q \sim Q'$. -/
theorem sameGenus_of_two_smul {Q Q' : QuadForm ℤ n} (h : SameGenus ((2 : ℤ) • Q) ((2 : ℤ) • Q')) :
    SameGenus Q Q' := by
  have key : ∀ {K : Type} [CommRing K] [IsDomain K] [CharZero K] (f : ℤ →+* K),
      IsometricGL (((2 : ℤ) • Q).map f) (((2 : ℤ) • Q').map f) → IsometricGL (Q.map f) (Q'.map f) := by
    intro K _ _ _ f ⟨g, hg⟩
    refine ⟨g, fun x => ?_⟩
    have h1 := hg x
    have ev : ∀ (P : QuadForm ℤ n) (y : Fin n → K), (((2 : ℤ) • P).map f).eval y = 2 * (P.map f).eval y := by
      intro P y
      rw [ConwaySloane.Mass.Two.Base.map_smul']
      simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
        QuadForm.eval, Algebra.algebraMap_self, RingHom.id_apply, map_ofNat]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [ev, ev] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  exact ⟨fun p _ => key _ (h.1 p), key _ h.2⟩

/-- **All even unimodular lattices of dimension $n$ lie in one genus** (Chenevier–Lannes, §2.2, Scholium 2.2.5 (b) and
Proposition 2.2.6, pp. 31–32: over every $\mathbb{Z}_p$ an even unimodular lattice is hyperbolic, so its isomorphism class
depends only on the dimension; over $\mathbb{R}$ both are positive definite). Proved through Conway–Sloane's genus
criterion (`ConwaySloane.Mass.sameGenus_of_discIso`): both Gram matrices are even (type II) with trivial discriminant
group. Unconditional. -/
@[kb "chenevierlannes2019" "Scholium 2.2.5 (b) and Prop. 2.2.6, pp. 31–32 (positive definite case)"]
theorem sameGenus_of_isEvenUnimodular {Q Q' : QuadForm ℤ n} (hQ : IsEvenUnimodular Q)
    (hQ' : IsEvenUnimodular Q') : SameGenus Q Q' := by
  have hA := posDefGram_hessian hQ.posDef
  have hB := posDefGram_hessian hQ'.posDef
  have ht : ConwaySloane.Mass.gramType Q.hessian = ConwaySloane.Mass.gramType Q'.hessian := by
    unfold ConwaySloane.Mass.gramType
    simp [hessian_evenDiag]
  have hi := Lattices.discIso_one_of_det_one (hessian_isSymm Q).eq (hessian_isSymm Q').eq hQ.det_one hQ'.det_one
  have := (ConwaySloane.Mass.lemma4 hA hB).mpr ⟨ht, hi⟩
  rw [ofMatrixZ_hessian, ofMatrixZ_hessian] at this
  exact sameGenus_of_two_smul this

/-- **$X_n$ is the genus of any one of its members** (consequence of `sameGenus_of_isEvenUnimodular`). -/
theorem classSet_eq_genusClasses {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) : classSet n = genusClasses Q := by
  ext c
  constructor
  · rintro ⟨Q', hQ', rfl⟩
    exact classOf_mem_genusClasses_iff.mpr (sameGenus_of_isEvenUnimodular hQ hQ')
  · rintro ⟨Q', rfl, hg⟩
    exact ⟨Q', ⟨hg.posDef hQ.posDef, by rw [← hg.det_hessian_eq hQ.posDef]; exact hQ.det_one⟩, rfl⟩

/-- **$X_n$ is finite** (Chenevier–Lannes, §1.1, p. 1). Unconditional: $X_n$ is one genus
(`classSet_eq_genusClasses`) and a genus of positive definite forms has finitely many classes (`Siegel.genusFinite`,
Hermite reduction). -/
@[kb "chenevierlannes2019" "§1.1, p. 1 (X_n is finite)"]
theorem classSet_finite (n : ℕ) : (classSet n).Finite := by
  by_cases h : ∃ Q : QuadForm ℤ n, IsEvenUnimodular Q
  · obtain ⟨Q, hQ⟩ := h
    rw [classSet_eq_genusClasses hQ]
    exact (genusFinite hQ.posDef).finite_classes
  · push Not at h
    convert Set.finite_empty
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨Q, hQ, -⟩
    exact h Q hQ

/-! ### Existence: $E_8^{\oplus r}$ -/

/-- **$E_8^{\oplus r}$ is even unimodular** (`DefiniteForms.repE8 r`, $r$ copies of $E_8$, dimension $8r$). -/
theorem isEvenUnimodular_repE8 (r : ℕ) : IsEvenUnimodular (DefiniteForms.repE8 r) := by
  induction r with
  | zero =>
    refine ⟨fun x hx => absurd (funext fun i => absurd i.2 (by simp)) hx, ?_⟩
    simp
  | succ r ih =>
    refine ⟨DefiniteForms.posDef_orthSum ih.posDef e8_posDef, ?_⟩
    show (QuadForm.orthSum (DefiniteForms.repE8 r) e8).hessian.det = 1
    rw [Hanke2011Structure.hessian_orthSum_det, ih.det_one, e8_det, one_mul]

/-- **$X_n$ is nonempty iff $8 \mid n$** (Chenevier–Lannes, §1.1, p. 1). Unconditional: necessity is
`eight_dvd_of_isEvenUnimodular`, and for $n = 8r$ the lattice $E_8^{\oplus r}$ is even unimodular. The book also mentions
$E_n = D_n^+$; the witness here is $E_8^{\oplus r}$. -/
@[kb "chenevierlannes2019" "§1.1, p. 1 (X_n is nonempty iff 8 divides n)"]
theorem classSet_nonempty_iff : (classSet n).Nonempty ↔ 8 ∣ n := by
  constructor
  · rintro ⟨c, Q, hQ, -⟩
    exact eight_dvd_of_isEvenUnimodular hQ
  · rintro ⟨r, rfl⟩
    exact ⟨_, DefiniteForms.repE8 r, isEvenUnimodular_repE8 r, rfl⟩

/-! ### Roots, Niemeier lattices, Coxeter numbers -/

/-- **The root system $R(L)$** (Chenevier–Lannes, §1.1, p. 2, and §2.3, p. 34): the vectors $x \in L$ with $x \cdot x = 2$,
i.e. $Q(\vec{x}) = 1$. (The book's claim that $R(L)$ is a root system of type ADE is not formalized; `rootSet` is the set.) -/
@[kb "chenevierlannes2019" "§1.1, p. 2; §2.3, p. 34 (R(L))"]
def rootSet (Q : QuadForm ℤ n) : Set (Fin n → ℤ) := {x | Q.eval x = 1}

/-- **A Niemeier lattice** (Chenevier–Lannes, §1.1, p. 2): an even unimodular lattice of dimension $24$. -/
@[kb "chenevierlannes2019" "§1.1, p. 2 (Niemeier lattices)"]
def IsNiemeier (Q : QuadForm ℤ 24) : Prop := IsEvenUnimodular Q

/-- **The Coxeter number $h(L)$** of an even unimodular lattice $L$ of dimension $n \in \{8, 16, 24\}$ with roots
(Chenevier–Lannes, Proposition-Definition 2.3.3, p. 35): defined here by the book's formula (c) there,
$$|R(L)| = n \cdot h(L), \qquad h(L) := |R(L)| / n.$$
*Deviation:* the book defines $h(L)$ as the common Coxeter number of the irreducible components of the ADE root system
$R(L)$ (parts (a), (b) of Proposition-Definition 2.3.3, Venkov), and proves (c). Root systems are not used here, so (c) is
taken as the definition; for $n = 24$ it gives the numbers $h(R)$ of Table 1.1 (p. 2). A rational number, so that no
divisibility is presupposed; $0$ for a lattice without roots. -/
@[kb "chenevierlannes2019" "Prop.-Def. 2.3.3 (c), p. 35; Table 1.1, p. 2"]
noncomputable def coxeterNumber (Q : QuadForm ℤ n) : ℚ := (repNum Q 1 : ℚ) / n

/-- **A lattice of Leech type**: a Niemeier lattice with no roots. By Conway's theorem (Chenevier–Lannes,
Theorem 2.3.16, p. 43; stated as `ConwayLeechUnique` in `Classification.lean`) these form one class, the Leech lattice. -/
@[kb "chenevierlannes2019" "§1.1, p. 2; Thm. 2.3.16, p. 43 (the Leech lattice)"]
def IsLeechType (Q : QuadForm ℤ 24) : Prop := IsNiemeier Q ∧ rootSet Q = ∅

/-! ### The number $c_n(p)$ -/

/-- **The number $c_n(p) = |C_L(\mathbb{F}_p)|$** of isotropic lines of $L/pL$ for an even unimodular $L$ of dimension
$n$ (Chenevier–Lannes, §1.2, p. 3, and Proposition-Definition 3.2.1, pp. 55–56):
$$c_n(p) = \sum_{m=0}^{n-2} p^m + p^{n/2 - 1}.$$
Defined by the formula (for every $n \ge 2$ and natural $p$); `Neighbors.lean` proves that it counts the $p$-neighbours. -/
@[kb "chenevierlannes2019" "§1.2, p. 3; Prop.-Def. 3.2.1, pp. 55–56 (c_n(p))"]
def cn (n p : ℕ) : ℕ := (∑ m ∈ Finset.range (n - 1), p ^ m) + p ^ (n / 2 - 1)

end QuadFormsKB.ChenevierLannes
