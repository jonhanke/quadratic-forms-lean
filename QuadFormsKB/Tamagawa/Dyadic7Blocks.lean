/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7LocalOne
import QuadFormsKB.Literature.ConwaySloane.Mass.Formula
import QuadFormsKB.Literature.ConwaySloane.Theorem11
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassification

/-!
# Paper 7 at $p = 2$: block decompositions of ternary Hessians and the combinatorial form of Table 5.3

This file sets up the reduction of `Dyadic7.DyadicTernaryLocalMassTable` (Hanke 2011, Thm. 4.12 and Table 5.3) to
Conway–Sloane's 2-adic genus symbols.

**Setting.** A primitive $\mathbb Z_2$-valued ternary quadratic form $Q$ is described by its *Hessian* matrix
$H = (\partial^2 Q/\partial x_i\partial x_j)$, the Gram matrix of the bilinear form $B(x,y) = Q(x+y) - Q(x) - Q(y)$. It is an
integral symmetric matrix with even diagonal. By Cassels (Ch. 8, Lemma 4.1) and Conway–Sloane (*Sphere Packings, Lattices and Groups* Ch. 15, §7.3–7.4)
$H$ is $\mathbb Z_2$-equivalent to an orthogonal sum of blocks (`Cassels.DyBlock`) $2^e u x^2$ ($u \in \{1,3,5,7\}$),
$2^e\cdot 2xy$, $2^e(2x^2+2xy+2y^2)$, $e \ge 0$; evenness of $H$ means that no block $2^0 u x^2$ occurs.

**Defines.**
* `hessZ n D`: the integer matrix of the block decomposition `D` (`ConwaySloane.dyMatInt`), as a matrix on `Fin n`;
  `formZ n D`: the integer quadratic form whose Hessian matrix is `hessZ n D` (when its diagonal is even);
  `genusOf v n D`: its local genus at a place $v$ of $\mathbb Q$.
* `IsAdm h u D`: `D` is a block decomposition of a primitive ternary Hessian with $\det H = 2^h w$, $w \equiv u \pmod 8$.
  `admSet h u`: the finite set of such lists with exponents $\le h$ (every admissible list has its exponents $\le h$).
* `hasseQ D`: the Hasse invariant $\prod_{i<j}(a_i,a_j)_2$ of the diagonal form $\langle a_i\rangle$ over $\mathbb Q_2$
  obtained from the blocks of $Q = \tfrac12 H$, computed by the explicit formula for the 2-adic Hilbert symbol.
* `massWt h u D`: $4^{1-h}\, m_2(D)/m_2(D_0(u))$, with $m_2$ Conway–Sloane's 2-mass of the symbol (`pMassTwo`) and $D_0(u)$
  the decomposition $2xy \perp 2(-u)z^2$ of Hessian determinant $2u$ (`baseList u`, row $h = 1$).
* `classCount h u D`: the number of lists in `admSet h u` whose symbol is related to that of `D` by Conway–Sloane's
  moves (sign walking, oddity fusion), i.e. (Theorem 10) the number of lists giving the same $\mathbb Z_2$-class.
* `TernaryDyadicMassCount`: the **named statement** that the class-weighted sums of `massWt` (and of `hasseQ * massWt`)
  over `admSet h u` are the entries of Table 5.3. It is a statement about finitely many explicit block lists for each
  $h$; it involves no forms, genera or densities.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal

noncomputable section

/-! ### The form of a block decomposition -/

/-- The block `b` is $2^0 u x^2$ (an odd diagonal entry of the Hessian). -/
def IsOddUnimodBlock : DyBlock → Prop
  | .sq e _ => e = 0
  | _ => False

/-- The integer matrix of the block decomposition `D` (`dyMatInt D`), on `Fin n` when `dyDim D = n` (the identity
matrix otherwise; only the case `dyDim D = n` is used). -/
def hessZ (n : ℕ) (D : List DyBlock) : Matrix (Fin n) (Fin n) ℤ :=
  if h : dyDim D = n then (dyMatInt D).submatrix (Fin.cast h.symm) (Fin.cast h.symm) else 1

/-- The integer quadratic form $Q_D$ with coefficients $c_{ii} = H_{ii}/2$ and $c_{ij} = H_{ij}$ ($i < j$), $H$ =
`hessZ n D`: its Hessian matrix is $H$ when the diagonal of $H$ is even (`hessian_formZ`). -/
def formZ (n : ℕ) (D : List DyBlock) : QuadForm ℤ n :=
  QuadForm.ofUpper fun i j => if i = j then hessZ n D i i / 2 else hessZ n D i j

/-- The local genus at the place $v$ of $\mathbb Q$ of the form $Q_D$ (`formZ n D`), viewed over $\mathbb Z_v$. -/
def genusOf (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (D : List DyBlock) : LocGenus v n :=
  LocGenus.mk ((formZ n D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ)))

/-! ### Admissible block lists -/

/-- The units of Cassels' blocks $2^e u x^2$. -/
def sqUnits : Finset ℤ := {1, 3, 5, 7}

/-- The blocks with exponents $0 \le e \le h$. -/
def alphabet (h : ℕ) : Finset DyBlock := by
  classical
  exact ((range (h + 1)) ×ˢ sqUnits).image (fun p => DyBlock.sq (p.1 : ℤ) p.2) ∪
    (range (h + 1)).image (fun e => DyBlock.hyp (e : ℤ)) ∪ (range (h + 1)).image (fun e => DyBlock.ell (e : ℤ))

/-- The lists of one, two or three blocks with exponents $\le h$. -/
def lists3 (h : ℕ) : Finset (List DyBlock) := by
  classical
  exact (alphabet h).image (fun a => [a]) ∪ (alphabet h ×ˢ alphabet h).image (fun p => [p.1, p.2]) ∪
    (alphabet h ×ˢ alphabet h ×ˢ alphabet h).image (fun p => [p.1, p.2.1, p.2.2])

/-- The form $Q_D$ is primitive: some coefficient of $Q_D$ (`formZ`) is odd. (Equivalently: some block has exponent $0$,
or some block $2^1 u x^2$ occurs; for the 2-adic symbol of $H$: the constituent of scale $1$ is nonzero or the one of
scale $2$ has type I.) -/
def IsPrimBlocks (D : List DyBlock) : Prop :=
  ∃ i j : Fin (dyDim D), ¬ (2 : ℤ) ∣ (formZ (dyDim D) D).coeff i j

/-- **Admissible block lists** for Hessian valuation $h$ and unit class $u$: valid blocks with exponents $\ge 0$,
three variables, even Hessian (no block $2^0 u x^2$), primitive, $\det H = 2^h\cdot w$ with $w$ = `unitProd D`
$\equiv u \pmod 8$ (`det_dyMatInt`). -/
def IsAdm (h : ℕ) (u : ℤ) (D : List DyBlock) : Prop :=
  (∀ b ∈ D, b.Valid) ∧ (∀ b ∈ D, 0 ≤ blockExp b) ∧ dyDim D = 3 ∧ (∀ b ∈ D, ¬ IsOddUnimodBlock b) ∧
    IsPrimBlocks D ∧ valSum D = h ∧ unitProd D % 8 = u % 8

/-- The finite set of admissible block lists with exponents $\le h$. -/
def admSet (h : ℕ) (u : ℤ) : Finset (List DyBlock) := by
  classical
  exact (lists3 h).filter (IsAdm h u)

/-- **The base decomposition** $D_0(u) = 2xy \perp 2(-u)z^2$ (Hessian $\begin{pmatrix}0&1\\1&0\end{pmatrix}\perp(2c)$,
$c \equiv -u \pmod 8$, determinant $-2c \equiv 2u$): the unique genus of Hessian valuation $1$ and unit class $u$
(row $h = 1$ of Table 5.3, `Dyadic7LocalOne.lean`). -/
def baseList (u : ℤ) : List DyBlock := [DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)]

/-! ### Hasse invariants -/

/-- Entries $(\alpha, u)$, standing for $2^\alpha u$ up to squares, of a diagonalization over $\mathbb Q_2$ of the part of
$Q = \tfrac12 H$ coming from one block:
$2^{e-1}u x^2 \sim \langle 2^{e+1}u\rangle$, $2^e xy \sim \langle 2^e, -2^e\rangle$,
$2^e(x^2+xy+y^2) \sim \langle 2^e, 3\cdot 2^e\rangle$. -/
def blockDiag : DyBlock → List (ℕ × ZMod 8)
  | .sq e u => [(e.toNat + 1, (u : ZMod 8))]
  | .hyp e => [(e.toNat, 1), (e.toNat, -1)]
  | .ell e => [(e.toNat, 1), (e.toNat, 3)]

/-- The 2-adic Hilbert symbol $(2^\alpha u, 2^\beta v)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\omega(v) + \beta\omega(u)}$ on
pairs $(\alpha, u \bmod 8)$ (`hilbertSymbol_two_formula`). -/
def hilb2 (a b : ℕ × ZMod 8) : ℤ :=
  (-1) ^ (twoEps a.2 * twoEps b.2 + a.1 * twoOmega b.2 + b.1 * twoOmega a.2)

/-- $\prod_{i<j} (a_i, a_j)_2$ for a list of entries. -/
def hasseList : List (ℕ × ZMod 8) → ℤ
  | [] => 1
  | a :: l => (l.map (hilb2 a)).prod * hasseList l

/-- **The Hasse invariant of the block decomposition** $D$: $c_2(Q_D) = \prod_{i<j}(a_i, a_j)_2$ for the diagonalization
of $Q_D = \tfrac12 H$ given by `blockDiag` (Serre's convention, as `LocGenus.hasse`). -/
def hasseQ (D : List DyBlock) : ℤ := hasseList (D.flatMap blockDiag)

/-! ### Mass weights and class counts -/

/-- **The weight of a block decomposition** $D$ at Hessian valuation $h$ and unit class $u$:
$$4^{1-h}\,\frac{m_2(D)}{m_2(D_0(u))},$$
$m_2$ = `pMassTwo` of the 2-adic symbol (Conway–Sloane 1988, (3)). With $\beta(G) = 2^{2h-7}/m_2$ (Hanke's density
of a genus of Hessian valuation $h$), this is $\beta(G_0)/\beta(G)$. -/
def massWt (h : ℕ) (u : ℤ) (D : List DyBlock) : ℝ :=
  (1 / 4 : ℝ) ^ (h - 1) * pMassTwo (blockSymbol D) (h + 1) / pMassTwo (blockSymbol (baseList u)) 2

/-- **The class count**: the number of admissible lists whose 2-adic symbol is related to that of `D` by
sign walking and oddity fusion (`ConwaySloane.MoveEquiv`), i.e. the number of lists of `admSet h u` in the
$\mathbb Z_2$-class of $D$ (Theorem 10, `zpEquiv_iff_moveEquiv`). -/
def classCount (h : ℕ) (u : ℤ) (D : List DyBlock) : ℕ := by
  classical
  exact ((admSet h u).filter fun D' => MoveEquiv (blockSymbol D) (blockSymbol D')).card

/-- **Named statement (Hanke 2011, Thm. 4.12 and Tables 5.1–5.3, the 2-adic case analysis):** the class-weighted sums of
the mass weights over the admissible ternary block decompositions are the entries of Table 5.3. For every Hessian
valuation $h \ge 1$ and unit $u \in \{1,3,5,7\}$:

* `A_eq`: $\displaystyle\sum_{D \in \mathrm{adm}(h,u)} \frac{\mathrm{massWt}(D)}{\mathrm{classCount}(D)} = $ `dyadicA h`;
* `B_eq`: $\displaystyle\sum_{D \in \mathrm{adm}(h,u)} \frac{c_2(D)\,\mathrm{massWt}(D)}{\mathrm{classCount}(D)} =
  c_2(D_0(u))\cdot\frac14$ `dyadicBmag h`.

Each sum is a sum over the $\mathbb Z_2$-classes of the admissible decompositions (each class is counted once). This is the
combinatorial content of Theorem 4.12 (Hanke's enumeration of the decorations of the 20 partial local genus symbols with
their Hasse invariants and 2-masses); it is a finite statement about explicit lists for each $h$, and involves no forms,
genera or local densities. *Status.* Proved: `Dyadic7.ternaryDyadicMassCount_holds` (`Dyadic7CountMain.lean`);
also checked by a computer calculation (outside Lean) for $h \le 12$ and all $u$. -/
@[kb "hanke2011ternary" "Thm. 4.12 and Tables 5.1–5.3, pp. 15–22 (the 2-adic case analysis)"]
structure TernaryDyadicMassCount : Prop where
  /-- $\sum_D \mathrm{massWt}/\mathrm{classCount} = $ `dyadicA h`. -/
  A_eq : ∀ h : ℕ, 1 ≤ h → ∀ u ∈ sqUnits,
    ∑ D ∈ admSet h u, massWt h u D / (classCount h u D : ℝ) = ((dyadicA h : ℚ) : ℝ)
  /-- $\sum_D c_2(D)\,\mathrm{massWt}/\mathrm{classCount} = c_2(D_0(u))\cdot$ `dyadicBmag h` $/\,4$. -/
  B_eq : ∀ h : ℕ, 1 ≤ h → ∀ u ∈ sqUnits,
    ∑ D ∈ admSet h u, (hasseQ D : ℝ) * massWt h u D / (classCount h u D : ℝ) =
      (hasseQ (baseList u) : ℝ) * ((dyadicBmag h : ℚ) : ℝ) / 4

/-! ### Basic lemmas: the Hessian of $Q_D$ -/

theorem orthSumMat_diag {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin b) (Fin b) R) (P : R → Prop) (hA : ∀ k, P (A k k)) (hB : ∀ k, P (B k k))
    (i : Fin (a + b)) : P (orthSumMat A B i i) := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [orthSumMat, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁]
    exact hA k
  · simp only [orthSumMat, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂]
    exact hB k

theorem even_blockMatInt_diag (b : DyBlock) (hb : 0 ≤ blockExp b) (hev : ¬ IsOddUnimodBlock b)
    (k : Fin b.dim) : Even (blockMatInt b k k) := by
  cases b with
  | sq e u =>
    have he : e ≠ 0 := hev
    change Fin 1 at k
    fin_cases k
    have hpos : 0 < e.toNat := by simp only [blockExp] at hb; omega
    change Even ((!![2 ^ e.toNat * u] : Matrix (Fin 1) (Fin 1) ℤ) 0 0)
    simp only [of_apply, cons_val', cons_val_fin_one, empty_val']
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hpos
    rw [hm, pow_succ]
    exact ⟨2 ^ m * u, by ring⟩
  | hyp e =>
    change Fin 2 at k
    fin_cases k
    · exact (⟨0, by ring⟩ : Even (0 : ℤ))
    · exact (⟨0, by ring⟩ : Even (0 : ℤ))
  | ell e =>
    change Fin 2 at k
    fin_cases k
    · exact (⟨2 ^ e.toNat, by ring⟩ : Even ((2 : ℤ) ^ (e.toNat + 1)))
    · exact (⟨2 ^ e.toNat, by ring⟩ : Even ((2 : ℤ) ^ (e.toNat + 1)))

theorem even_dyMatInt_diag : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b) →
    (∀ b ∈ D, ¬ IsOddUnimodBlock b) → ∀ i, Even (dyMatInt D i i)
  | [], _, _, i => i.elim0
  | b :: D, h0, hev, i => by
    show Even (orthSumMat (blockMatInt b) (dyMatInt D) i i)
    exact orthSumMat_diag _ _ Even
      (even_blockMatInt_diag b (h0 b (List.mem_cons_self ..)) (hev b (List.mem_cons_self ..)))
      (even_dyMatInt_diag D (fun c hc => h0 c (List.mem_cons_of_mem _ hc))
        (fun c hc => hev c (List.mem_cons_of_mem _ hc))) i

theorem hessZ_of {n : ℕ} {D : List DyBlock} (h : dyDim D = n) :
    hessZ n D = (dyMatInt D).submatrix (Fin.cast h.symm) (Fin.cast h.symm) := by
  unfold hessZ; rw [dite_eq_left h]

theorem hessZ_transpose {n : ℕ} {D : List DyBlock} (h : dyDim D = n) : (hessZ n D)ᵀ = hessZ n D := by
  rw [hessZ_of h, Matrix.transpose_submatrix, transpose_dyMatInt]

theorem even_hessZ_diag {n : ℕ} {D : List DyBlock} (h : dyDim D = n) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) (i : Fin n) : Even (hessZ n D i i) := by
  rw [hessZ_of h]
  exact even_dyMatInt_diag D h0 hev _

/-- A symmetric integer matrix with even diagonal is the Hessian matrix of the form with $c_{ii} = M_{ii}/2$,
$c_{ij} = M_{ij}$ ($i<j$). -/
theorem hessian_ofUpper_half {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : Mᵀ = M) (hev : ∀ i, Even (M i i)) :
    (QuadForm.ofUpper fun i j => if i = j then M i i / 2 else M i j).hessian = M := by
  ext i j
  simp only [QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.of_apply, Matrix.transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.le, not_le.2 h, h.ne]
  · obtain ⟨m, hm⟩ := hev i
    simp [hm]; omega
  · have hH' : M i j = M j i := by
      have := congrFun (congrFun hM j) i
      simpa [Matrix.transpose_apply] using this
    simp [h, h.le, not_le.2 h, h.ne', h.ne, hH']

theorem hessian_formZ {n : ℕ} {D : List DyBlock} (h : dyDim D = n) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) : (formZ n D).hessian = hessZ n D :=
  hessian_ofUpper_half _ (hessZ_transpose h) (even_hessZ_diag h h0 hev)

theorem det_hessZ {n : ℕ} {D : List DyBlock} (h : dyDim D = n) (h0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    (hessZ n D).det = 2 ^ valSum D * unitProd D := by
  rw [hessZ_of h]
  change ((dyMatInt D).submatrix (finCongr h.symm) (finCongr h.symm)).det = _
  rw [Matrix.det_submatrix_equiv_self (finCongr h.symm), det_dyMatInt D h0]

end

end QuadFormsKB.Dyadic7
