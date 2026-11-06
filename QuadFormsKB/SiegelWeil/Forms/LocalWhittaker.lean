/-
# Local Whittaker integrals of degree $r$ are forms-by-forms local densities
**Layer:** local, non-archimedean. Every finite place $v$ of a number field $F$, **dyadic places included**.

**Setting.** $V_v = \langle a_0, \dots, a_{n-1}\rangle$ over $F_v$, $a_i \in \mathcal O_v\setminus\{0\}$, $n = 2m$ (0-based indices); the degree
$r$; $L_v = \mathcal O_v^n$ and $\Phi_v = \mathbf 1_{L_v^r} = \mathbf 1_{M_{n\times r}(\mathcal O_v)}$ (`oneSG`); $f_v(g) = (\omega_v(g)\Phi_v)(0)$ the
section of `SiegelWeil/Forms/Sections.lean` for the Weil representation of $\mathrm{Sp}_{2r}(F_v)$ (`secRV`).

**Coordinates on $\mathrm{Sym}_r(F_v)$.** A symmetric matrix $B$ is given by its entries $u_{ij} = B_{ij}$, $i \le j$ (`SymIdx r`,
`symOf`), and $dB = \prod_{i\le j}du_{ij}$ with the self-dual measure $du$ on $F_v$ for $\psi_v$ (`muSym`; $\operatorname{vol}(\mathcal O_v) =
N(\mathfrak d_v)^{-1/2}$). A quadratic form $T = \sum_{i\le j}t_{ij}y_iy_j$ in $r$ variables (the repository's `QuadForm` convention, no
halving) pairs with $B$ by
$$\operatorname{tr}(T_GB) = \sum_{i\le j}t_{ij}u_{ij},\qquad T_G = \tfrac12H_T\ \text{the Gram matrix},$$
and $\operatorname{tr}(B\,Q[X]) = \sum_{i\le j}u_{ij}\,(Q\circ X)_{ij}$ (`trace_symOf_QX`), where $Q\circ X$ is the form of the columns of $X$
(`QuadForm.compMat`: $Q(X_i)$ on the diagonal, $B_Q(X_i, X_j)$ above it).

**The local Whittaker integral** $W_{T,v} = \int_{\mathrm{Sym}_r(F_v)}f_v(w\,n(B))\,\psi_v(-\operatorname{tr}(T_GB))\,dB$ is taken as the limit
of the integrals over $\mathrm{Sym}_r(\mathfrak p_v^{-k})$ (`whittakerTrR`, `whittakerR`): Siegel's local singular series. The limit is
attained (`whittakerTrR_eventually_eq`).

**Results.**
* `whittakerTrR_eq` (**the identity before the limit**): for every $k \ge d_v$ and every $T$ with coefficients in $\mathcal O_v$, with
  $j = k - d_v$ and $R = r(r+1)/2$,
  $$\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}f_v(wn(B))\psi_v(-\operatorname{tr}(T_GB))\,dB
    = \gamma_V^{\,r}c_B^{\,r}\operatorname{vol}(\mathcal O_v)^{nr - R}\,\frac{A_{\mathfrak p^j}(Q, T)}{q^{j(nr - R)}},$$
  $A_{\mathfrak p^j}(Q, T)$ = `DVR.repCountForm` (solutions of $Q\circ X = T$ mod $\mathfrak p_v^j$, as quadratic forms).
  *Proof* (Siegel; Weil 1965): the big cell (`secRV_spW_spN`), Fubini, the $u_{ij}$-integrals
  $\int_{\mathfrak p^{-k}}\psi_v(u\,y)\,du = \operatorname{vol}(\mathfrak p^{-k})\mathbf 1[y \in \mathfrak p^{k-d_v}]$, the volume of the congruence set
  (`muG_congSetR`: a disjoint union of cosets of $M_{n\times r}(\mathfrak p_v^j)$ over the solutions mod $\mathfrak p_v^j$), and
  $\operatorname{vol}(\mathfrak p^{-k})^R\operatorname{vol}(\mathfrak p^j)^{nr} = \operatorname{vol}(\mathcal O_v)^{nr-R}q^{-j(nr-R)}$.
* **`whittakerR_eq_localDensityForm`** (**Whittaker = forms-by-forms local density**, every finite place, dyadic included): for $T$
  nondegenerate with coefficients in $\mathcal O_v$ and $r \le n$,
  $$W_{T,v}(\mathbf 1_{L_v^r}) = \gamma_V^{\,r}\cdot\prod_{i<n}|2a_i|_v^{r/2}\cdot N(\mathfrak d_v)^{-(nr - r(r+1)/2)/2}\cdot\beta_v(Q, T),$$
  $\beta_v(Q, T) = \lim_jA_{\mathfrak p^j}(Q, T)/q^{j(nr - r(r+1)/2)}$ = `DVR.localDensityForm`. Over $\mathcal O_F$:
  `whittakerR_eq_NF_localDensityForm` with `NF.localDensityForm` of $\sum_ib_ix_i^2$, $b_i \in \mathcal O_F$. At a good place
  ($d_v = 0$, $v \nmid 2$, $a_i$ units) $W_{T,v} = \beta_v(Q, T)$ (`whittakerR_eq_localDensityForm_of_good`).
* `whittakerR_eq_zero_of_not_int`: $W_{T,v} = 0$ if some coefficient of $T$ is not in $\mathcal O_v$.

For $r = 1$, $T = \langle t\rangle$ this is `whittakerV_eq_localDensity` (`SiegelWeil/LocalWhittaker.lean`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), §§ 1–3 (densities as limits of
counts) [unverified]; Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), Ch. II
[unverified]; Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 ($W_{T,v}(e, s_0, \Phi_v)$) [unverified];
Kudla–Rallis, J. reine angew. Math. 387 (1988), §4 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.Sections
import QuadFormsKB.SiegelWeil.LocalWhittaker
import QuadFormsKB.LocalDensity.FormDensityStab
import QuadFormsKB.LocalDensity.NFFormDensity

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology Matrix
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### Coordinates on $\mathrm{Sym}_r$ -/

/-- The index set $\{(i, j) : i \le j\}$ of the coordinates $u_{ij}$ of a symmetric $r\times r$ matrix. -/
abbrev SymIdx (r : ℕ) := {p : Fin r × Fin r // p.1 ≤ p.2}

section SymCoord

variable {K : Type*} [CommRing K] {r : ℕ}

/-- **The symmetric matrix with upper entries $u$:** $B_{ij} = u_{ij}$ for $i \le j$ and $B_{ij} = u_{ji}$ for $i > j$. -/
def symOf (u : SymIdx r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => if h : i ≤ j then u ⟨(i, j), h⟩ else u ⟨(j, i), le_of_not_ge h⟩

lemma symOf_transpose (u : SymIdx r → K) : (symOf u)ᵀ = symOf u := by
  ext i j
  simp only [symOf, transpose_apply, of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dif_neg (not_le.mpr h), dif_pos h.le]
  · rfl
  · rw [dif_pos h.le, dif_neg (not_le.mpr h)]

/-- $\sum_{i,j}f(i,j) = \sum_{i \le j}\big(f(i,j) + [i < j]f(j,i)\big)$, the sum over the coordinates of $\mathrm{Sym}_r$. -/
lemma sum_eq_sum_symIdx {M : Type*} [AddCommMonoid M] (f : Fin r → Fin r → M) :
    ∑ i, ∑ j, f i j = ∑ p : SymIdx r, (f p.1.1 p.1.2 + if p.1.1 = p.1.2 then 0 else f p.1.2 p.1.1) := by
  classical
  have hsplit : ∀ i j, f i j = (if i ≤ j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases le_or_gt i j with h | h
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · rw [if_neg (not_le.mpr h), if_pos h, zero_add]
  have h1 : ∑ i, ∑ j, f i j = ∑ i, ∑ j, ((if i ≤ j then f i j else 0) + (if i < j then f j i else 0)) := by
    simp_rw [Finset.sum_add_distrib]
    conv_lhs => enter [2, i, 2, j]; rw [hsplit i j]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
  rw [h1]
  have h2 : ∀ i j, ((if i ≤ j then f i j else 0) + (if i < j then f j i else 0)) =
      if i ≤ j then (f i j + if i = j then 0 else f j i) else 0 := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h.le, if_pos h, if_pos h.le, if_neg h.ne]
    · simp
    · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le), if_neg (not_le.mpr h), add_zero]
  simp_rw [h2]
  rw [← Fintype.sum_prod_type' (f := fun i j => if i ≤ j then (f i j + if i = j then 0 else f j i) else 0),
    ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun q => by simp) (fun q : Fin r × Fin r =>
    f q.1 q.2 + if q.1 = q.2 then 0 else f q.2 q.1)).trans rfl

/-- **The pairing with a symmetric matrix:** for $S = {}^tS$,
$\operatorname{tr}(\operatorname{symOf}(u)\,S) = \sum_{i\le j}u_{ij}\,c_{ij}$ with $c_{ii} = S_{ii}$ and $c_{ij} = 2S_{ij}$ ($i < j$). -/
lemma trace_symOf_mul (u : SymIdx r → K) {S : Matrix (Fin r) (Fin r) K} (hS : Sᵀ = S) :
    trace (symOf u * S) = ∑ p : SymIdx r, u p * (if p.1.1 = p.1.2 then S p.1.1 p.1.2 else 2 * S p.1.1 p.1.2) := by
  have hS' : ∀ i j, S j i = S i j := fun i j => by rw [← transpose_apply S i j, hS]
  have e : trace (symOf u * S) = ∑ i, ∑ j, symOf u i j * S i j := by
    simp only [trace, diag, mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hS']
  rw [e, sum_eq_sum_symIdx]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := p
  dsimp only
  by_cases h : i = j
  · subst h; simp [symOf]
  · have hlt : i < j := lt_of_le_of_ne hij h
    rw [if_neg h, if_neg h]
    simp only [symOf, of_apply, dif_pos hij, dif_neg (not_le.mpr hlt)]
    rw [hS' i j]
    ring

/-- $\#\{(i, j) : i \le j < r\} = r(r+1)/2$. -/
lemma card_symIdx : Fintype.card (SymIdx r) = r * (r + 1) / 2 := by
  classical
  have e : SymIdx r ≃ Sym2 (Fin r) :=
    { toFun := fun p => s(p.1.1, p.1.2)
      invFun := Sym2.lift ⟨fun i j => ⟨(min i j, max i j), min_le_max⟩, fun i j => by
        simp only [Subtype.mk.injEq, Prod.mk.injEq]; exact ⟨min_comm i j, max_comm i j⟩⟩
      left_inv := fun p => by
        obtain ⟨⟨i, j⟩, h⟩ := p
        simp [min_eq_left h, max_eq_right h]
      right_inv := fun s => by
        induction s using Sym2.ind with
        | h i j =>
          simp only [Sym2.lift_mk]
          rcases le_total i j with h | h
          · simp [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, Sym2.eq_swap] }
  rw [Fintype.card_congr e, Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

end SymCoord

/-! ### The form $Q \circ X$ and the Gram matrix $Q[X]$ -/

section Comp

variable {K : Type*} [Field K] {m r : ℕ}

/-- The form $Q = \langle a_0, \dots, a_{n-1}\rangle$ over $K$, $n = 2m$. -/
def Qd (a : Fin (2 * m) → Kˣ) : QuadForm K (2 * m) := QuadForm.diag fun i => (a i : K)

lemma QX_transpose (a : Fin (2 * m) → Kˣ) (X : PtG m r K) : (QX a X)ᵀ = QX a X := by
  simp [QX, transpose_mul, Matrix.mul_assoc]

/-- **The coefficients of $Q \circ X$ are those of the Gram matrix $Q[X]$:** $(Q\circ X)_{ii} = Q[X]_{ii}$ and
$(Q\circ X)_{ij} = 2Q[X]_{ij}$ for $i < j$ ($\operatorname{char}K \ne 2$). -/
lemma compMat_coeff_eq (h2 : (2 : K) ≠ 0) (a : Fin (2 * m) → Kˣ) (X : PtG m r K) {i j : Fin r} (hij : i ≤ j) :
    ((Qd a).compMat X).coeff i j = if i = j then QX a X i j else 2 * QX a X i j := by
  have hH : ((Qd a).compMat X).hessian = 2 * QX a X := by
    have hd : (QuadForm.diag fun i => (a i : K)).hessian = diagonal fun i => 2 * (a i : K) := by
      unfold QuadForm.hessian QuadForm.diag
      simp only [diagonal_transpose, diagonal_add, two_mul]
    rw [QuadForm.hessian_compMat, Qd, hd]
    have : (diagonal fun i => 2 * (a i : K)) = (2 : Matrix (Fin (2 * m)) (Fin (2 * m)) K) *
        diagonal fun i => (a i : K) := by
      rw [show (2 : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = diagonal fun _ => 2 from rfl, diagonal_mul_diagonal]
    rw [this, QX]
    simp only [Matrix.mul_assoc]
    rw [show (2 : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = (2 : K) • (1 : Matrix _ _ K) by
      ext; simp [Matrix.ofNat_apply, Matrix.one_apply]]
    rw [show (2 : Matrix (Fin r) (Fin r) K) = (2 : K) • (1 : Matrix _ _ K) by
      ext; simp [Matrix.ofNat_apply, Matrix.one_apply]]
    simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
  have hent : ((Qd a).compMat X).coeff i j + ((Qd a).compMat X).coeff j i = 2 * QX a X i j := by
    have := congrFun (congrFun hH i) j
    simpa [QuadForm.hessian, Matrix.ofNat_apply, Matrix.mul_apply, Matrix.add_apply] using this
  rcases eq_or_lt_of_le hij with rfl | hlt
  · rw [if_pos rfl]
    have h' : 2 * ((Qd a).compMat X).coeff i i = 2 * QX a X i i := by rw [two_mul]; exact hent
    exact mul_left_cancel₀ h2 h'
  · rw [if_neg hlt.ne, ← hent, ((Qd a).compMat X).upper hlt, add_zero]

/-- **The pairing $\operatorname{tr}(B\,Q[X])$ in coordinates:** $\operatorname{tr}(\operatorname{symOf}(u)\,Q[X]) = \sum_{i\le j}u_{ij}(Q\circ X)_{ij}$. -/
lemma trace_symOf_QX (h2 : (2 : K) ≠ 0) (a : Fin (2 * m) → Kˣ) (u : SymIdx r → K) (X : PtG m r K) :
    trace (symOf u * QX a X) = ∑ p : SymIdx r, u p * ((Qd a).compMat X).coeff p.1.1 p.1.2 := by
  rw [trace_symOf_mul u (QX_transpose a X)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [compMat_coeff_eq h2 a X p.2]

end Comp

/-! ### The local setting -/

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {m r : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- **The measure $dB = \prod_{i\le j}du_{ij}$ on $\mathrm{Sym}_r(F_v)$** (self-dual $du$ for $\psi_v$). -/
def muSym (r : ℕ) : Measure (SymIdx r → Fv) := Measure.pi fun _ => selfDualV v

/-- The function $\mathbf 1_{M_{n\times r}(\mathcal O_v)} = \prod_{i,l}\mathbf 1_{\mathcal O_v}(X_{il})$ (the same as `Genus.oneVG`). -/
def oneG (m r : ℕ) : PtG m r Fv → ℂ := ptG fun _ _ => ballIndV v 0 0

/-- **The lattice function** $\Phi_v = \mathbf 1_{L_v^r} = \mathbf 1_{M_{n\times r}(\mathcal O_v)}$ as an element of $S(V_v^r)$. -/
@[kb "kudla1996" "§I.4 (the standard lattice function $\\varphi_v = \\mathbf 1_{L_v^n}$) [unverified]"]
def oneSG (m r : ℕ) : Sg (localDataV v) m r :=
  ⟨oneG v m r, ptG_mem_Sg fun _ _ => ballIndV_zero_mem_SBK v⟩

/-- **The function $u \mapsto f_v(w\,n(\operatorname{symOf}u))$** for the lattice section $f_v = f_{\mathbf 1_{L_v^r}}$. -/
def wfunR (u : SymIdx r → Fv) : ℂ := secRV v a (oneSG v m r) (spW * spN (symOf u) (symOf_transpose u))

/-- The truncation $\mathbf 1_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}(u) = \prod_{i\le j}\mathbf 1_{\mathfrak p_v^{-k}}(u_{ij})$. -/
def ballSym (k : ℕ) (u : SymIdx r → Fv) : ℂ := ∏ p, ballIndV v 0 (-(k : ℤ)) (u p)

/-- $\operatorname{tr}(T_GB) = \sum_{i\le j}t_{ij}u_{ij}$ for $B = \operatorname{symOf}(u)$ and $T = \sum_{i\le j}t_{ij}y_iy_j$. -/
def pairT (T : QuadForm Fv r) (u : SymIdx r → Fv) : Fv := ∑ p : SymIdx r, u p * T.coeff p.1.1 p.1.2

/-- **The truncated local Whittaker integral of degree $r$:**
$\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}f_v(w\,n(B))\,\psi_v(-\operatorname{tr}(T_GB))\,dB$, for a quadratic form $T$ in $r$ variables over
$F_v$ ($T_G = \tfrac12H_T$ its Gram matrix). -/
@[kb "weil1965" "Ch. II (the local factors of the Fourier coefficients of the Siegel Eisenstein series) [unverified]"]
def whittakerTrR (T : QuadForm Fv r) (k : ℕ) : ℂ :=
  ∫ u, ballSym v k u * (wfunR v a u * (psiV v (-pairT v T u) : ℂ)) ∂muSym v r

/-- **The local Whittaker integral of degree $r$:** $W_{T,v}(\mathbf 1_{L_v^r}) = \int_{\mathrm{Sym}_r(F_v)}f_v(wn(B))\psi_v(-\operatorname{tr}(T_GB))\,dB
= \lim_k\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}$ (`limUnder`; the limit is attained, `whittakerTrR_eventually_eq`). -/
@[kb "kudla2008" "§1 ($W_{T,v}(e, s_0, \\Phi_v)$) [unverified]; weil1965 Ch. II [unverified]"]
def whittakerR (T : QuadForm Fv r) : ℂ := limUnder atTop (whittakerTrR v a T)

/-! ### The congruence sets in $M_{n\times r}(\mathcal O_v)$ -/

/-- **The congruence set** $\{X \in M_{n\times r}(\mathcal O_v) : Q\circ X \equiv T \bmod \mathfrak p_v^j\}$ (coefficientwise, $i \le j$). -/
def congSetR (T : QuadForm Fv r) (j : ℕ) : Set (PtG m r Fv) :=
  {X | (∀ i l, Valued.v (X i l) ≤ 1) ∧
    ∀ p : SymIdx r, Valued.v (((Qd a).compMat X).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2) ≤ exp (-(j : ℤ))}

section Count

variable (j : ℕ)

/-- The lift of a residue matrix to $M_{n\times r}(\mathcal O_v)$. -/
def liftRG (Y : Matrix (Fin (2 * m)) (Fin r) (RQ v j)) : PtG m r Fv :=
  fun i l => ((Quotient.out (Y i l) : 𝔬) : Fv)

/-- The fiber of the reduction map over $Y$: the coset $\tilde Y + M_{n\times r}(\mathfrak p_v^j)$. -/
def fiberRG (Y : Matrix (Fin (2 * m)) (Fin r) (RQ v j)) : Set (PtG m r Fv) :=
  Set.univ.pi fun i => Set.univ.pi fun l => {z : Fv | Valued.v (z - liftRG v j Y i l) ≤ exp (-(j : ℤ))}

/-- The integral matrix of an $X$ with entries in $\mathcal O_v$. -/
def intMat (X : PtG m r Fv) (hX : ∀ i l, Valued.v (X i l) ≤ 1) : Matrix (Fin (2 * m)) (Fin r) 𝔬 :=
  fun i l => ⟨X i l, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hX i l)⟩

/-- The reduction $M_{n\times r}(\mathcal O_v) \to M_{n\times r}(\mathcal O_v/\mathfrak p_v^j)$. -/
def redRG (X : PtG m r Fv) (hX : ∀ i l, Valued.v (X i l) ≤ 1) : Matrix (Fin (2 * m)) (Fin r) (RQ v j) :=
  (intMat v X hX).map (Ideal.Quotient.mk _)

lemma valued_le_one_of_sub {x y : Fv} (hy : Valued.v y ≤ 1) (h : Valued.v (x - y) ≤ exp (-(j : ℤ))) :
    Valued.v x ≤ 1 := by
  have h1 : Valued.v (x - y) ≤ 1 := h.trans (by rw [← exp_zero, exp_le_exp]; omega)
  calc Valued.v x = Valued.v ((x - y) + y) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ 1 := max_le h1 hy

lemma mem_fiberRG_iff {Y : Matrix (Fin (2 * m)) (Fin r) (RQ v j)} {X : PtG m r Fv} :
    X ∈ fiberRG v j Y ↔ ∃ hX : ∀ i l, Valued.v (X i l) ≤ 1, redRG v j X hX = Y := by
  constructor
  · intro h
    have hX : ∀ i l, Valued.v (X i l) ≤ 1 := fun i l =>
      valued_le_one_of_sub v j (Quotient.out (Y i l)).2 (h i (Set.mem_univ _) l (Set.mem_univ _))
    refine ⟨hX, ?_⟩
    ext i l
    have := h i (Set.mem_univ _) l (Set.mem_univ _)
    simp only [redRG, Matrix.map_apply]
    rw [← Ideal.Quotient.mk_out (Y i l), valued_sub_le_iff_mk_eq]
    exact this
  · rintro ⟨hX, rfl⟩ i - l -
    show Valued.v (X i l - ((Quotient.out (redRG v j X hX i l) : 𝔬) : Fv)) ≤ _
    exact (valued_sub_le_iff_mk_eq v j (intMat v X hX i l) (Quotient.out (redRG v j X hX i l))).mp
      (by rw [Ideal.Quotient.mk_out]; rfl)

/-- The coefficient of $Q$ over $\mathcal O_v$ as a form over $F_v$. -/
lemma QO_map_coe (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) :
    (QO v a ha).map (algebraMap 𝔬 Fv) = Qd a := by
  ext i j
  simp only [QO, Qd, QuadForm.map, QuadForm.diag, Matrix.map_apply, diagonal_apply]
  split_ifs <;> simp [aO]

lemma compMat_coeff_coe (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (X : PtG m r Fv) (hX : ∀ i l, Valued.v (X i l) ≤ 1)
    (i l : Fin r) :
    ((((QO v a ha).compMat (intMat v X hX)).coeff i l : 𝔬) : Fv) = ((Qd a).compMat X).coeff i l := by
  have h := QuadForm.map_compMat (algebraMap 𝔬 Fv) (QO v a ha) (intMat v X hX)
  rw [QO_map_coe] at h
  have hX' : (intMat v X hX).map (algebraMap 𝔬 Fv) = X := by ext; rfl
  rw [hX'] at h
  rw [h]
  rfl

lemma compMat_red_eq_iff (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (T : QuadForm 𝔬 r) (X : PtG m r Fv)
    (hX : ∀ i l, Valued.v (X i l) ≤ 1) :
    ((QO v a ha).map (Ideal.Quotient.mk _)).compMat (redRG v j X hX) = T.map (Ideal.Quotient.mk _) ↔
      ∀ p : SymIdx r, Valued.v (((Qd a).compMat X).coeff p.1.1 p.1.2 -
        ((T.map (algebraMap 𝔬 Fv)).coeff p.1.1 p.1.2)) ≤ exp (-(j : ℤ)) := by
  rw [redRG, QuadForm.map_compMat]
  constructor
  · intro h p
    have := congrArg (fun S : QuadForm (RQ v j) r => S.coeff p.1.1 p.1.2) h
    simp only [QuadForm.map, Matrix.map_apply] at this
    rw [← compMat_coeff_coe v a ha X hX]
    exact (valued_sub_le_iff_mk_eq v j _ _).mp this
  · intro h
    refine QuadForm.ext_upper fun i l hil => ?_
    simp only [QuadForm.map, Matrix.map_apply]
    have := h ⟨(i, l), hil⟩
    rw [← compMat_coeff_coe v a ha X hX] at this
    exact (valued_sub_le_iff_mk_eq v j _ _).mpr this

open Classical in
lemma congSetR_eq_biUnion (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (T : QuadForm 𝔬 r) [Fintype (RQ v j)]
    [DecidableEq (RQ v j)] :
    congSetR v a (T.map (algebraMap 𝔬 Fv)) j = ⋃ Y ∈ (Finset.univ.filter fun Y : Matrix (Fin (2 * m)) (Fin r) (RQ v j) =>
      ((QO v a ha).map (Ideal.Quotient.mk _)).compMat Y = T.map (Ideal.Quotient.mk _)), fiberRG v j Y := by
  ext X
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · rintro ⟨hX, hQ⟩
    exact ⟨redRG v j X hX, (compMat_red_eq_iff v a j ha T X hX).mpr hQ, (mem_fiberRG_iff v j).mpr ⟨hX, rfl⟩⟩
  · rintro ⟨Y, hY, hXY⟩
    obtain ⟨hX, rfl⟩ := (mem_fiberRG_iff v j).mp hXY
    exact ⟨hX, (compMat_red_eq_iff v a j ha T X hX).mp hY⟩

lemma coset_eq (c : Fv) :
    {z : Fv | Valued.v (z - c) ≤ exp (-(j : ℤ))} = (fun z => z + -c) ⁻¹' (latticeV v j : Set Fv) := by
  ext z; simp [mem_latticeV, sub_eq_add_neg]

lemma measurableSet_fiberRG (Y : Matrix (Fin (2 * m)) (Fin r) (RQ v j)) : MeasurableSet (fiberRG v j Y) := by
  refine MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => ?_
  rw [coset_eq]
  exact (measurableSet_latticeV v j).preimage (measurable_add_const _)

lemma measure_fiberRG (Y : Matrix (Fin (2 * m)) (Fin r) (RQ v j)) :
    muG (localDataV v) m r (fiberRG v j Y) = selfDualV v (latticeV v j) ^ (2 * m * r) := by
  have : SigmaFinite (localDataV v).μ := (isOps_V v).sigmaFinite
  change (Measure.pi fun _ : Fin (2 * m) => Measure.pi fun _ : Fin r => (localDataV v).μ)
    (Set.univ.pi fun i => Set.univ.pi fun l => {z : Fv | Valued.v (z - liftRG v j Y i l) ≤ exp (-(j : ℤ))}) = _
  rw [Measure.pi_pi]
  have h1 : ∀ i, (Measure.pi fun _ : Fin r => (localDataV v).μ)
      (Set.univ.pi fun l => {z : Fv | Valued.v (z - liftRG v j Y i l) ≤ exp (-(j : ℤ))}) =
      selfDualV v (latticeV v j) ^ r := by
    intro i
    rw [Measure.pi_pi]
    have : ∀ l, (localDataV v).μ {z : Fv | Valued.v (z - liftRG v j Y i l) ≤ exp (-(j : ℤ))} =
        selfDualV v (latticeV v j) := fun l => by
      rw [coset_eq]; exact measure_preimage_add_right (selfDualV v) _ _
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm r]

lemma fiberRG_disjoint {Y Y' : Matrix (Fin (2 * m)) (Fin r) (RQ v j)} (h : Y ≠ Y') :
    Disjoint (fiberRG v j Y) (fiberRG v j Y') := by
  rw [Set.disjoint_left]
  intro X hX hX'
  obtain ⟨h1, rfl⟩ := (mem_fiberRG_iff v j).mp hX
  obtain ⟨h2, e⟩ := (mem_fiberRG_iff v j).mp hX'
  exact h e

/-- **The volume of a congruence set of matrices** (every finite place, dyadic included): for $j \ge 0$ and $T$ over $\mathcal O_v$,
$$\operatorname{vol}\{X \in M_{n\times r}(\mathcal O_v) : Q\circ X \equiv T \bmod \mathfrak p_v^j\} = A_{\mathfrak p^j}(Q, T)\cdot\operatorname{vol}(\mathfrak p_v^j)^{nr},$$
$A_{\mathfrak p^j}(Q, T)$ = `DVR.repCountForm` of $Q = \sum_ia_ix_i^2$ over $\mathcal O_v$ (uniformizer `NF.π v`). -/
@[kb "siegel1935" "§1 (densities as limits of volumes of congruence sets) [unverified]"]
theorem muG_congSetR (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (T : QuadForm 𝔬 r) :
    (muG (localDataV v) m r).real (congSetR v a (T.map (algebraMap 𝔬 Fv)) j) =
      (LocalDensity.DVR.repCountForm (QO v a ha) T (LocalDensity.NF.π v) j : ℝ) *
        (selfDualV v).real (latticeV v j) ^ (2 * m * r) := by
  classical
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) j
  haveI : Fintype (RQ v j) := Fintype.ofFinite _
  rw [congSetR_eq_biUnion v a j ha T, Measure.real, measure_biUnion_finset]
  · simp only [measure_fiberRG, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_natCast, Measure.real]
    congr 1
    rw [LocalDensity.DVR.repCountForm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro Y _ Y' _ h
    exact fiberRG_disjoint v j h
  · intro Y _; exact measurableSet_fiberRG v j Y

end Count

/-! ### The truncated Whittaker integral -/

lemma continuous_ballIndV_zero' (k : ℤ) : Continuous (ballIndV v 0 k) := continuous_ballIndV_zero v k

lemma continuous_oneVG : Continuous (oneG v m r) := by
  unfold oneG ptG
  exact continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun l _ =>
    (continuous_ballIndV_zero v 0).comp ((continuous_apply l).comp (continuous_apply i))

lemma integrable_oneVG : Integrable (oneG v m r) (muG (localDataV v) m r) := by
  have : SigmaFinite (localDataV v).μ := (isOps_V v).sigmaFinite
  unfold oneG ptG muG
  refine Integrable.fintype_prod (μ := fun _ => Measure.pi fun _ => (localDataV v).μ)
    (f := fun _ (x : Fin r → Fv) => ∏ l, ballIndV v 0 0 (x l)) fun i => ?_
  exact Integrable.fintype_prod (f := fun _ z => ballIndV v 0 0 z) fun l => integrable_ballIndV_zero v 0

lemma continuous_ballSym (k : ℕ) : Continuous (ballSym (r := r) v k) :=
  continuous_finsetProd _ fun p _ => (continuous_ballIndV_zero v _).comp (continuous_apply p)

lemma integrable_ballSym (k : ℕ) : Integrable (ballSym (r := r) v k) (muSym v r) := by
  unfold ballSym muSym
  exact Integrable.fintype_prod (f := fun _ z => ballIndV v 0 (-(k : ℤ)) z) fun p =>
    integrable_ballIndV_zero v _

lemma continuous_QX : Continuous fun X : PtG m r Fv => QX a X :=
  (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id

lemma continuous_compMat_coeff {i l : Fin r} (hil : i ≤ l) :
    Continuous fun X : PtG m r Fv => ((Qd a).compMat X).coeff i l := by
  have e : (fun X : PtG m r Fv => ((Qd a).compMat X).coeff i l) =
      fun X => if i = l then QX a X i l else 2 * QX a X i l := by
    funext X; exact compMat_coeff_eq two_ne_zero a X hil
  rw [e]
  split_ifs
  · exact (continuous_QX v a).matrix_elem i l
  · exact continuous_const.mul ((continuous_QX v a).matrix_elem i l)

lemma oneVG_eq_indicator (X : PtG m r Fv) :
    oneG v m r X = if ∀ i l, Valued.v (X i l) ≤ 1 then 1 else 0 := by
  classical
  unfold oneG ptG
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun l _ => by
      show ballIndV v 0 0 (X i l) = 1
      rw [ballIndV, Set.indicator_of_mem (by simpa using h i l)]
  · push Not at h
    obtain ⟨i, l, hil⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ l) (by
      show ballIndV v 0 0 (X i l) = 0
      rw [ballIndV, Set.indicator_of_notMem (by simpa using hil)]))

lemma ballIndV_eq_ite (j : ℤ) (y : Fv) :
    ballIndV v 0 j y = if Valued.v y ≤ exp (-j) then 1 else 0 := by
  unfold ballIndV
  split_ifs with h
  · exact Set.indicator_of_mem (by simpa using h) _
  · exact Set.indicator_of_notMem (by simpa using h) _

lemma oneVG_mul_prod_ballIndV (T : QuadForm Fv r) (j : ℕ) (X : PtG m r Fv) :
    oneG v m r X * ∏ p : SymIdx r, ballIndV v 0 (j : ℤ)
      (((Qd a).compMat X).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2) = (congSetR v a T j).indicator 1 X := by
  classical
  rw [oneVG_eq_indicator, Set.indicator_apply]
  simp only [ballIndV_eq_ite]
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  by_cases hA : ∀ i l, Valued.v (X i l) ≤ 1
  · by_cases hB : ∀ p : SymIdx r, Valued.v (((Qd a).compMat X).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2) ≤
      exp (-(j : ℤ))
    · rw [if_pos hA, if_pos (fun p _ => hB p), if_pos (show X ∈ congSetR v a T j from ⟨hA, hB⟩)]; simp
    · rw [if_pos hA, if_neg (fun h => hB fun p => h p (Finset.mem_univ p)),
        if_neg (show X ∉ congSetR v a T j from fun h => hB h.2)]; simp
  · rw [if_neg hA, if_neg (show X ∉ congSetR v a T j from fun h => hA h.1)]; simp

lemma isClosed_congSetR (T : QuadForm Fv r) (j : ℕ) : IsClosed (congSetR v a T j) := by
  have e : congSetR v a T j = (⋂ i, ⋂ l, (fun X : PtG m r Fv => X i l) ⁻¹' (latticeV v 0 : Set Fv)) ∩
      ⋂ p : SymIdx r, (fun X => ((Qd a).compMat X).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2) ⁻¹'
        (latticeV v j : Set Fv) := by
    ext X
    simp only [congSetR, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe, mem_latticeV, neg_zero, exp_zero]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun l =>
    (isCompact_latticeV v 0).isClosed.preimage ((continuous_apply l).comp (continuous_apply i))) ?_
  exact isClosed_iInter fun p => (isCompact_latticeV v j).isClosed.preimage
    ((continuous_compMat_coeff v a p.2).sub continuous_const)

/-- **The truncated Whittaker integral as a volume** (every $T$ over $F_v$, $k \ge d_v$, $j = k - d_v$):
$\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}f_v(wn(B))\psi_v(-\operatorname{tr}(T_GB))\,dB = \gamma_V^rc_B^r\operatorname{vol}(\mathfrak p_v^{-k})^{R}
\operatorname{vol}\{X \in M_{n\times r}(\mathcal O_v) : Q\circ X - T \in \mathfrak p_v^j\}$, $R = r(r+1)/2$. -/
theorem whittakerTrR_eq_vol (T : QuadForm Fv r) (k : ℕ) (hk : diffExp v ≤ k) :
    whittakerTrR v a T k = (localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r *
      (((selfDualV v).real (latticeV v (-(k : ℤ))) ^ Fintype.card (SymIdx r) : ℝ) *
        (((muG (localDataV v) m r).real (congSetR v a T (k - diffExp v)) : ℝ) : ℂ)) := by
  set j := k - diffExp v with hj
  set d := diffExp v
  set γc := (localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r
  have : SigmaFinite (localDataV v).μ := (isOps_V v).sigmaFinite
  have : SigmaFinite (selfDualV v) := (isOps_V v).sigmaFinite
  have : SFinite (muG (localDataV v) m r) :=
    (inferInstance : SFinite (Measure.pi fun _ : Fin (2 * m) => Measure.pi fun _ : Fin r => (localDataV v).μ))
  have : SFinite (muSym v r) := by unfold muSym; infer_instance
  -- the integrand
  set y : PtG m r Fv → SymIdx r → Fv := fun X p => ((Qd a).compMat X).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2
  have hW : ∀ u : SymIdx r → Fv, ballSym v k u * (wfunR v a u * (psiV v (-pairT v T u) : ℂ)) =
      γc * ∫ X, ballSym v k u * (oneG v m r X * (psiV v (∑ p, u p * y X p) : ℂ))
        ∂muG (localDataV v) m r := by
    intro u
    rw [wfunR, secRV_spW_spN]
    simp only [← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    have e : (psiV v (∑ p, u p * y X p) : ℂ) =
        ((localDataV v).ψ (trace (symOf u * QX a X)) : ℂ) * (psiV v (-pairT v T u) : ℂ) := by
      rw [trace_symOf_QX two_ne_zero a u X, show (localDataV v).ψ = psiV v from rfl, ← Circle.coe_mul,
        ← AddChar.map_add_eq_mul]
      congr 2
      simp only [y, pairT, mul_sub, Finset.sum_sub_distrib]
      ring
    dsimp only
    rw [e, show ((oneSG v m r : Sg (localDataV v) m r) : PtG m r Fv → ℂ) = oneG v m r from rfl]
    ring
  -- Fubini
  have hcontY : Continuous fun q : (SymIdx r → Fv) × PtG m r Fv => ∑ p, q.1 p * y q.2 p :=
    continuous_finsetSum _ fun p _ => ((continuous_apply p).comp continuous_fst).mul
      (((continuous_compMat_coeff v a p.2).sub continuous_const).comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (u : SymIdx r → Fv) (X : PtG m r Fv) =>
      ballSym v k u * (oneG v m r X * (psiV v (∑ p, u p * y X p) : ℂ)))
      ((muSym v r).prod (muG (localDataV v) m r)) := by
    refine Integrable.mono' ((integrable_ballSym v k).norm.mul_prod (integrable_oneVG v).norm) ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact ((continuous_ballSym v k).comp continuous_fst).mul (((continuous_oneVG v).comp continuous_snd).mul
        (continuous_subtype_val.comp ((continuous_psiV v).comp hcontY)))
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one]
      exact le_rfl
  have hfub : whittakerTrR v a T k = γc * ∫ X, oneG v m r X *
      ∫ u, ballSym v k u * (psiV v (∑ p, u p * y X p) : ℂ) ∂muSym v r ∂muG (localDataV v) m r := by
    rw [whittakerTrR, integral_congr_ae (Filter.Eventually.of_forall hW), integral_const_mul,
      integral_integral_swap hint]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    ring
  -- the `u`-integral factors over the coordinates
  have hb1 : ∀ z : Fv, ∫ b, ballIndV v 0 (-(k : ℤ)) b * (psiV v (b * z) : ℂ) ∂selfDualV v =
      ballIndV v 0 (j : ℤ) z * ((selfDualV v).real (latticeV v (-(k : ℤ))) : ℂ) := by
    intro z
    have := congrFun (fourierV_ballIndV_eq v 0 (-(k : ℤ))) z
    simp only [zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, neg_neg] at this
    rw [show ((k : ℤ) - d) = (j : ℤ) by omega] at this
    exact this
  have hb : ∀ z : SymIdx r → Fv, ∫ u, ballSym v k u * (psiV v (∑ p, u p * z p) : ℂ) ∂muSym v r =
      (∏ p, ballIndV v 0 (j : ℤ) (z p)) * ((selfDualV v).real (latticeV v (-(k : ℤ))) : ℂ) ^
        Fintype.card (SymIdx r) := by
    intro z
    have e : (fun u : SymIdx r → Fv => ballSym v k u * (psiV v (∑ p, u p * z p) : ℂ)) =
        fun u => ∏ p, (ballIndV v 0 (-(k : ℤ)) (u p) * (psiV v (u p * z p) : ℂ)) := by
      funext u
      rw [ballSym, Finset.prod_mul_distrib, addChar_sum, Analysis.coe_prod_circle]
    rw [e, muSym, integral_fintype_prod_eq_prod (f := fun p b => ballIndV v 0 (-(k : ℤ)) b * (psiV v (b * z p) : ℂ))]
    simp only [hb1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  -- the `X`-integral is the volume of the congruence set
  rw [hfub]
  simp only [hb]
  have hx : ∫ X, oneG v m r X * ((∏ p, ballIndV v 0 (j : ℤ) (y X p)) *
      ((selfDualV v).real (latticeV v (-(k : ℤ))) : ℂ) ^ Fintype.card (SymIdx r)) ∂muG (localDataV v) m r =
      ((selfDualV v).real (latticeV v (-(k : ℤ))) : ℂ) ^ Fintype.card (SymIdx r) *
        (((muG (localDataV v) m r).real (congSetR v a T j) : ℝ) : ℂ) := by
    simp only [← mul_assoc]
    rw [integral_mul_const, mul_comm]
    congr 1
    rw [integral_congr_ae (Filter.Eventually.of_forall (oneVG_mul_prod_ballIndV v a T j))]
    have e : (fun X => (congSetR v a T j).indicator (1 : PtG m r Fv → ℂ) X) =
        fun X => (((congSetR v a T j).indicator (1 : PtG m r Fv → ℝ) X : ℝ) : ℂ) := by
      funext X; by_cases hX : X ∈ congSetR v a T j <;> simp [hX]
    rw [e, integral_complex_ofReal, integral_indicator_one (isClosed_congSetR v a T j).measurableSet]
  rw [hx]
  push_cast
  ring

/-- **The identity before the limit.** For every $k \ge d_v$ and $T$ with coefficients in $\mathcal O_v$, with $j = k - d_v$ and
$R = r(r+1)/2$, $r \le n$:
$$\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}f_v(wn(B))\psi_v(-\operatorname{tr}(T_GB))\,dB =
  \gamma_V^{\,r}c_B^{\,r}\operatorname{vol}(\mathcal O_v)^{nr-R}\,\frac{A_{\mathfrak p^j}(Q, T)}{q^{j(nr-R)}}.$$ -/
@[kb "weil1965" "Ch. II; Siegel (1935), §1 (the local factor as a limit of counts) [unverified]"]
theorem whittakerTrR_eq (hrn : r ≤ 2 * m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (T : QuadForm 𝔬 r) (k : ℕ)
    (hk : diffExp v ≤ k) :
    whittakerTrR v a (T.map (algebraMap 𝔬 Fv)) k = (localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r *
      ((((selfDualV v).real (latticeV v 0) ^ (2 * m * r - r * (r + 1) / 2) *
        ((LocalDensity.DVR.repCountForm (QO v a ha) T (LocalDensity.NF.π v) (k - diffExp v) : ℝ) /
          (LocalDensity.DVR.q 𝔬 : ℝ) ^ ((k - diffExp v) * (2 * m * r - r * (r + 1) / 2)))) : ℝ) : ℂ) := by
  set j := k - diffExp v with hj
  set d := diffExp v
  set R := r * (r + 1) / 2 with hR
  set A := (LocalDensity.DVR.repCountForm (QO v a ha) T (LocalDensity.NF.π v) j : ℝ) with hA
  have hRle : R ≤ 2 * m * r := by
    have h1 : r * (r + 1) ≤ 2 * (2 * m * r) := by
      rcases Nat.eq_zero_or_pos r with h0 | hr
      · simp [h0]
      · nlinarith
    exact Nat.div_le_of_le_mul h1
  have key : (selfDualV v).real (latticeV v (-(k : ℤ))) ^ R * (A * (selfDualV v).real (latticeV v j) ^ (2 * m * r)) =
      (selfDualV v).real (latticeV v 0) ^ (2 * m * r - R) * (A / (LocalDensity.DVR.q 𝔬 : ℝ) ^ (j * (2 * m * r - R))) := by
    have hΔ : (0 : ℝ) < modV v := by exact_mod_cast modV_pos v
    have hq : (LocalDensity.DVR.q 𝔬 : ℝ) = (modV v : ℝ)⁻¹ := by
      rw [LocalDensity.NF.q_completion, modV_eq, inv_inv]
    rw [selfDualV_real_latticeV, selfDualV_real_latticeV, selfDualV_real_latticeV, hq, zpow_zero, mul_one,
      inv_pow, div_inv_eq_mul]
    set c := (modV v : ℝ) ^ ((d : ℝ) / 2)
    set Δ := (modV v : ℝ)
    have hc2 : c * c = Δ ^ d := by
      rw [← Real.rpow_add hΔ, add_halves, Real.rpow_natCast]
    have hcpos : 0 < c := Real.rpow_pos_of_pos hΔ _
    have hkjd : (k : ℤ) = (j : ℤ) + (d : ℤ) := by omega
    have e1 : Δ ^ (-(k : ℤ)) = ((Δ ^ j)⁻¹ * (Δ ^ d)⁻¹) := by
      rw [hkjd, neg_add, zpow_add₀ hΔ.ne', _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
    rw [e1, zpow_natCast]
    obtain ⟨E, hE⟩ : ∃ E, 2 * m * r = R + E := ⟨2 * m * r - R, by omega⟩
    rw [hE, Nat.add_sub_cancel_left, mul_pow, mul_pow, mul_pow, pow_add c, pow_add (Δ ^ j), ← hc2, inv_pow, inv_pow,
      ← pow_mul, mul_pow c c]
    have hX : (0 : ℝ) < Δ ^ j := pow_pos hΔ _
    field_simp
    rw [pow_mul]
  rw [whittakerTrR_eq_vol v a _ k hk, card_symIdx, ← hR, muG_congSetR v a j ha T, ← key, hA]
  push_cast
  ring

/-! ### The limit: Whittaker = forms-by-forms local density -/

/-- The constant $\gamma_V^{\,r}c_B^{\,r}\operatorname{vol}(\mathcal O_v)^{nr - r(r+1)/2}$ of the Whittaker–density identity, $n = 2m$. -/
def whittakerConstR (r : ℕ) : ℂ :=
  (localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r *
    (((selfDualV v).real (latticeV v 0) ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ)

/-- **The truncated Whittaker integrals are eventually constant**, equal to $\gamma_V^rc_B^r\operatorname{vol}(\mathcal O_v)^{nr-R}\beta_v(Q, T)$,
for $T$ nondegenerate over $\mathcal O_v$ and $r \le n$ (from the stabilization `DVR.localDensityForm_eventually_eq`). -/
theorem whittakerTrR_eventually_eq (hrn : r ≤ 2 * m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (T : QuadForm 𝔬 r)
    (hT : T.Nondegenerate) :
    ∀ᶠ k in atTop, whittakerTrR v a (T.map (algebraMap 𝔬 Fv)) k = whittakerConstR v a r *
      (LocalDensity.DVR.localDensityForm (QO v a ha) T (LocalDensity.NF.π v) : ℂ) := by
  have hst := LocalDensity.DVR.localDensityForm_eventually_eq (QO v a ha) T hT (LocalDensity.NF.π v)
    (LocalDensity.NF.irreducible_π v) hrn
  have hshift := (tendsto_sub_atTop_nat (diffExp v)).eventually hst
  filter_upwards [hshift, eventually_ge_atTop (diffExp v)] with k hk hkd
  rw [whittakerTrR_eq v a hrn ha T k hkd, whittakerConstR, ← hk]
  push_cast
  ring

/-- **Whittaker = forms-by-forms local density** (every finite place $v$, **dyadic included**). For
$V_v = \langle a_0, \dots, a_{n-1}\rangle$, $n = 2m$, $a_i \in \mathcal O_v\setminus\{0\}$, $\Phi_v = \mathbf 1_{M_{n\times r}(\mathcal O_v)}$, $r \le n$,
and $T$ a nondegenerate quadratic form in $r$ variables with coefficients in $\mathcal O_v$:
$$W_{T,v}(\Phi_v) = \lim_k\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}(\omega_v(wn(B))\Phi_v)(0)\,\psi_v(-\operatorname{tr}(T_GB))\,dB
  = \gamma_V^{\,r}\cdot\prod_{i<n}|2a_i|_v^{r/2}\cdot\operatorname{vol}(\mathcal O_v)^{nr - r(r+1)/2}\cdot\beta_v(Q, T),$$
$\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$, and $\beta_v(Q, T) = \lim_jA_{\mathfrak p^j}(Q, T)/q^{j(nr - r(r+1)/2)}$ = `DVR.localDensityForm`. -/
@[kb "weil1965" "Ch. II, the local factors of Siegel's formula for forms [unverified]; kudla2008 §1 [unverified]"]
theorem whittakerR_eq_localDensityForm (hrn : r ≤ 2 * m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (T : QuadForm 𝔬 r)
    (hT : T.Nondegenerate) :
    whittakerR v a (T.map (algebraMap 𝔬 Fv)) = (localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r *
      (((selfDualV v).real (latticeV v 0) ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ) *
        (LocalDensity.DVR.localDensityForm (QO v a ha) T (LocalDensity.NF.π v) : ℂ) := by
  have h := whittakerTrR_eventually_eq v a hrn ha T hT
  exact (tendsto_const_nhds.congr' (h.mono fun k hk => hk.symm)).limUnder_eq

/-- **The Whittaker integral as a limit** (the truncations converge to $W_{T,v}$). -/
theorem tendsto_whittakerTrR (hrn : r ≤ 2 * m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (T : QuadForm 𝔬 r)
    (hT : T.Nondegenerate) :
    Tendsto (whittakerTrR v a (T.map (algebraMap 𝔬 Fv))) atTop (𝓝 (whittakerR v a (T.map (algebraMap 𝔬 Fv)))) := by
  rw [whittakerR_eq_localDensityForm v a hrn ha T hT]
  exact tendsto_const_nhds.congr' ((whittakerTrR_eventually_eq v a hrn ha T hT).mono fun k hk => by
    rw [hk, whittakerConstR])

/-- **At a good place the Whittaker integral is the density**: if $d_v = 0$, $v \nmid 2$ and all $a_i$ are units (`IsGoodV`), then
$W_{T,v}(\mathbf 1_{L_v^r}) = \beta_v(Q, T)$. -/
theorem whittakerR_eq_localDensityForm_of_good (hrn : r ≤ 2 * m) (hg : IsGoodV v a) (T : QuadForm 𝔬 r)
    (hT : T.Nondegenerate) :
    whittakerR v a (T.map (algebraMap 𝔬 Fv)) = (LocalDensity.DVR.localDensityForm
      (QO v a (fun i => (hg.2.2 i).le)) T (LocalDensity.NF.π v) : ℂ) := by
  rw [whittakerR_eq_localDensityForm v a hrn (fun i => (hg.2.2 i).le) T hT, gammaV_eq_one_of_good hg]
  have hcB : (localDataV v).cB a = 1 := by
    unfold LocalData.cB
    refine Finset.prod_eq_one fun i _ => ?_
    rw [md_eq_one v (by rw [map_mul, hg.2.1, hg.2.2 i, one_mul])]
    simp
  have hvol : (selfDualV v).real (latticeV v 0) = 1 := by
    rw [selfDualV_real_latticeV, hg.1]; simp
  rw [hcB, hvol]; simp

/-! ### Over $\mathcal O_F$ -/

lemma Qp_map_coe (T : QuadForm (𝓞 F) r) :
    (LocalDensity.NF.Qp v T).map (algebraMap 𝔬 Fv) = T.map ((algebraMap 𝔬 Fv).comp (LocalDensity.NF.ι v)) := by
  ext i j; rfl

/-- **Whittaker = forms-by-forms local density over $\mathcal O_F$** (every finite prime $\mathfrak p$, dyadic included): for
$Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m$, and $T$ a nondegenerate quadratic form in $r \le n$ variables
over $\mathcal O_F$,
$$W_{T,\mathfrak p}(\mathbf 1_{L_\mathfrak p^r}) = \gamma_{V,\mathfrak p}^{\,r}\cdot\prod_{i<n}|2b_i|_\mathfrak p^{r/2}\cdot
  N(\mathfrak d_\mathfrak p)^{-(nr - r(r+1)/2)/2}\cdot\beta_\mathfrak p(Q, T),$$
with $\beta_\mathfrak p(Q, T)$ = `NF.localDensityForm` (Siegel 1935; Kitaoka 1993, §5.6). -/
@[kb "weil1965" "Ch. II [unverified]; siegel1935 §1 (the densities) [unverified]"]
theorem whittakerR_eq_NF_localDensityForm (hrn : r ≤ 2 * m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (T : QuadForm (𝓞 F) r) (hT : T.Nondegenerate) :
    whittakerR v (aOfInt v b hb) (LocalDensity.NF.Qp v T |>.map (algebraMap 𝔬 Fv)) =
      (localDataV v).gammaV (aOfInt v b hb) ^ r * (localDataV v).cB (aOfInt v b hb) ^ r *
        (((((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2)) ^ (2 * m * r - r * (r + 1) / 2) : ℝ) : ℂ) *
          (LocalDensity.NF.localDensityForm v (QuadForm.diag b) T : ℂ) := by
  rw [whittakerR_eq_localDensityForm v (aOfInt v b hb) hrn (aOfInt_le_one v b hb) _
      (LocalDensity.NF.nondegenerate_Qp v hT), QO_aOfInt, ← LocalDensity.NF.localDensityForm_eq_completion,
    selfDualV_real_Ov]

/-! ### Non-integral $T$ -/

/-- **$W_{T,v} = 0$ if a coefficient of $T$ is not in $\mathcal O_v$**: $Q\circ X$ has coefficients in $\mathcal O_v$ for $X$ integral,
so the congruence sets are empty. -/
theorem whittakerR_eq_zero_of_not_int (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) {T : QuadForm Fv r} (p : SymIdx r)
    (hT : 1 < Valued.v (T.coeff p.1.1 p.1.2)) : whittakerR v a T = 0 := by
  have hempty : ∀ j, congSetR v a T j = ∅ := by
    intro j
    ext X
    simp only [congSetR, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_forall, not_le]
    intro hX
    refine ⟨p, ?_⟩
    by_contra hle
    push Not at hle
    have h1 : Valued.v (((Qd a).compMat X).coeff p.1.1 p.1.2) ≤ 1 := by
      rw [← compMat_coeff_coe v a ha X hX]
      exact (((QO v a ha).compMat (intMat v X hX)).coeff p.1.1 p.1.2).2
    have h2 : Valued.v (((Qd a).compMat X).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2) ≤ 1 :=
      hle.trans (by rw [← exp_zero, exp_le_exp]; omega)
    have : Valued.v (T.coeff p.1.1 p.1.2) ≤ 1 := by
      calc Valued.v (T.coeff p.1.1 p.1.2) = Valued.v (((Qd a).compMat X).coeff p.1.1 p.1.2 -
            (((Qd a).compMat X).coeff p.1.1 p.1.2 - T.coeff p.1.1 p.1.2)) := by ring_nf
        _ ≤ max _ _ := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le h1 h2
    exact absurd hT (not_lt.mpr this)
  refine (tendsto_const_nhds.congr' ((eventually_ge_atTop (diffExp v)).mono fun k hk => ?_)).limUnder_eq
  rw [whittakerTrR_eq_vol v a T k hk, hempty]
  simp

end QuadFormsKB.SiegelWeil.Forms
