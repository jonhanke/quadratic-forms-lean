/-
# O'Meara §106F, toward 106.r38: bases and Gram matrices of $E_m \perp \mathbb Z^k$, $m = 8, 12$

**Layer:** $V = \mathbb Q^{m+k}$ with $Q = I_{m+k}$ (`sumSqForm`), the lattice $E_m \perp \mathbb Z^k$ = `omearaEPerp m (m + k)`
(O'Meara's matrix $\Phi_m \perp I_k$). Indices are 0-based.

The basis of $E_m$ used here ($m = 8, 12$) is
$$h = \tfrac12(x_0 - x_1 - \dots - x_{m-2} + x_{m-1}),\quad x_0 + x_1,\quad x_1 - x_0,\quad x_2 - x_1,\quad \dots,\quad
x_{m-2} - x_{m-3},$$
with Gram matrix the $E_m$ Cartan matrix (Mathlib's `CartanMatrix.E m`, Bourbaki's labelling) except for the entry
$h \cdot h = m/4$: for $m = 8$ this is the $E_8$ Cartan matrix, for $m = 12$ it is `d12Gram` (entry $3$ in place of $2$).
The basis matrix is stored as the integer matrix $W = 2B$ with $V = 2B^{-1}$; the identities $WV = VW = 4$ and
$W^{\mathsf T}W = 4G$ are checked by `decide +kernel`.

**Proves** (all unconditional)
* `glImage_eBlock`: the lattice spanned by the block basis $B \oplus 1_k$ is $E_m \perp \mathbb Z^k$;
* `gram_eBlock`: its Gram form is $G \oplus I_k$ (`ConwaySloane.Mass.sumI`);
* `isUnimodularZ_omearaEPerp`: $E_m \perp \mathbb Z^k$ is unimodular for $m = 8, 12$ and every $k$.
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank9
import QuadFormsKB.Tamagawa.BlockForm



open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel LocalDensity QuadFormsKB.Tamagawa.Frames

/-- Twice the basis matrix of $E_8$ (columns $2h$, $2(x_0+x_1)$, $2(x_1-x_0)$, …). -/
def e8W : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, -2, 0, 0, 0, 0, 0;
    -1, 2, 2, -2, 0, 0, 0, 0;
    -1, 0, 0, 2, -2, 0, 0, 0;
    -1, 0, 0, 0, 2, -2, 0, 0;
    -1, 0, 0, 0, 0, 2, -2, 0;
    -1, 0, 0, 0, 0, 0, 2, -2;
    -1, 0, 0, 0, 0, 0, 0, 2;
    1, 0, 0, 0, 0, 0, 0, 0]

/-- Twice the inverse of the basis matrix of $E_8$. -/
def e8V : Matrix (Fin 8) (Fin 8) ℤ := !![0, 0, 0, 0, 0, 0, 0, 4;
    1, 1, 1, 1, 1, 1, 1, 5;
    -1, 1, 1, 1, 1, 1, 1, 7;
    0, 0, 2, 2, 2, 2, 2, 10;
    0, 0, 0, 2, 2, 2, 2, 8;
    0, 0, 0, 0, 2, 2, 2, 6;
    0, 0, 0, 0, 0, 2, 2, 4;
    0, 0, 0, 0, 0, 0, 2, 2]

/-- Twice the basis matrix of $E_{12} = D_{12}^+$. -/
def e12W : Matrix (Fin 12) (Fin 12) ℤ := !![1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 2, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2;
    -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Twice the inverse of the basis matrix of $E_{12}$. -/
def e12V : Matrix (Fin 12) (Fin 12) ℤ := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4;
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9;
    -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11;
    0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 18;
    0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 16;
    0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 14;
    0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 12;
    0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 10;
    0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 8;
    0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 6;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2]

/-- **The Gram matrix of $E_{12} = D_{12}^+$** in the basis above: the $E_{12}$ Cartan matrix with the entry $(0, 0)$
replaced by $3 = h \cdot h$. -/
def d12Gram : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of fun i j => if i.val = 0 ∧ j.val = 0 then 3 else CartanMatrix.E 12 i j

/-- **Basis data of $E_m$**: integer matrices $W = 2B$, $V = 2B^{-1}$ and the Gram matrix $G$, with the certificates
`hWV`, `hVW` ($WV = VW = 4$), `hgram` ($W^{\mathsf T}W = 4G$), `hcol` (every column of $W$ has entries of one parity and
sum divisible by $4$, i.e. $\tfrac12$ of it lies in $E_m$) and `hrow` (the same for the rows of $V$, which makes
$B^{-1}x$ integral for $x \in E_m$). -/
structure EBasisData (m : ℕ) where
  /-- Twice the basis matrix. -/
  W : Matrix (Fin m) (Fin m) ℤ
  /-- Twice its inverse. -/
  V : Matrix (Fin m) (Fin m) ℤ
  /-- The Gram matrix. -/
  G : Matrix (Fin m) (Fin m) ℤ
  hWV : W * V = (4 : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ)
  hVW : V * W = (4 : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ)
  hgram : Wᵀ * W = (4 : ℤ) • G
  hcol : ∀ j, (∀ i i', (W i j - W i' j) % 2 = 0) ∧ (∑ i, W i j) % 4 = 0
  hrow : ∀ r, (∀ i i', (V r i - V r i') % 2 = 0) ∧ (∑ i, V r i) % 4 = 0

/-- The basis data of $E_8$ (Gram matrix the $E_8$ Cartan matrix). -/
def e8Data : EBasisData 8 where
  W := e8W
  V := e8V
  G := CartanMatrix.E 8
  hWV := by decide +kernel
  hVW := by decide +kernel
  hgram := by decide +kernel
  hcol := by decide +kernel
  hrow := by decide +kernel

/-- The basis data of $E_{12}$ (Gram matrix `d12Gram`). -/
def e12Data : EBasisData 12 where
  W := e12W
  V := e12V
  G := d12Gram
  hWV := by decide +kernel
  hVW := by decide +kernel
  hgram := by decide +kernel
  hcol := by decide +kernel
  hrow := by decide +kernel

/-! ### The criterion "same parity, sum divisible by 4" -/

/-- If $w \in \mathbb Z^m$ has entries of one parity and $4 \mid \sum w_i$, then $\tfrac12 w \in E_m$ ($4 \mid m$). -/
theorem half_mem_omearaE {m : ℕ} (h4 : 4 ∣ m) (hm : 0 < m) (w : Fin m → ℤ)
    (hp : ∀ i i', (w i - w i') % 2 = 0) (hs : (∑ i, w i) % 4 = 0) :
    (fun i => (w i : ℚ) / 2) ∈ omearaE m := by
  rw [omeara106_11 h4 hm]
  refine ⟨fun i => ⟨w i, by ring⟩, fun i j => ⟨(w i - w j) / 2, ?_⟩, ⟨(∑ i, w i) / 4, ?_⟩⟩
  · obtain ⟨c, hc⟩ : ∃ c, w i - w j = 2 * c := ⟨(w i - w j) / 2, by have := hp i j; omega⟩
    have hc' : (w i - w j) / 2 = c := by omega
    rw [hc']
    have : ((w i : ℚ) - w j) = 2 * c := by exact_mod_cast hc
    linarith
  · obtain ⟨c, hc⟩ : ∃ c, ∑ i, w i = 4 * c := ⟨(∑ i, w i) / 4, by omega⟩
    have hc' : (∑ i, w i) / 4 = c := by omega
    rw [hc', ← Finset.sum_div]
    have : (∑ i, (w i : ℚ)) = 4 * c := by exact_mod_cast hc
    rw [this]; ring

/-- If $v \in \mathbb Z^m$ has entries of one parity and $4 \mid \sum v_i$, then $\tfrac12\sum v_ix_i \in \mathbb Z$ for every
$x \in E_m$ ($4 \mid m$). -/
theorem half_dot_int {m : ℕ} (h4 : 4 ∣ m) (hm : 0 < m) (v : Fin m → ℤ)
    (hp : ∀ i i', (v i - v i') % 2 = 0) (hs : (∑ i, v i) % 4 = 0) {x : Fin m → ℚ} (hx : x ∈ omearaE m) :
    ∃ z : ℤ, (∑ i, (v i : ℚ) * x i) / 2 = z := by
  obtain ⟨h1, h2, s, hsx⟩ := (omeara106_11 h4 hm x).mp hx
  set i0 : Fin m := ⟨0, hm⟩
  obtain ⟨a, ha⟩ := h1 i0
  choose d hd using fun i => h2 i i0
  have hx' : ∀ i, x i = d i + x i0 := fun i => by rw [← hd i]; ring
  obtain ⟨k, hk⟩ := h4
  rcases Int.emod_two_eq_zero_or_one (v i0) with hv0 | hv0
  · -- all entries even: v = 2u with Σ u even
    have hev : ∀ i, v i = 2 * (v i / 2) := fun i => by have := hp i i0; omega
    have hsum : (∑ i, v i / 2) % 2 = 0 := by
      have : ∑ i, v i = 2 * ∑ i, v i / 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hev i
      omega
    obtain ⟨t, ht⟩ : ∃ t, ∑ i, v i / 2 = 2 * t := ⟨(∑ i, v i / 2) / 2, by omega⟩
    refine ⟨∑ i, v i / 2 * d i + t * a, ?_⟩
    have e : (∑ i, (v i : ℚ) * x i) / 2 = ∑ i, ((v i / 2 : ℤ) : ℚ) * d i + ((∑ i, v i / 2 : ℤ) : ℚ) * x i0 := by
      rw [Finset.sum_div]; push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx' i]
      have : (v i : ℚ) = 2 * ((v i / 2 : ℤ) : ℚ) := by exact_mod_cast hev i
      rw [this]; push_cast; ring
    rw [e, ht]; push_cast; rw [← ha]; ring
  · -- all entries odd: v = 1 + 2u with Σ u even (as 4 ∣ m)
    have hod : ∀ i, v i = 1 + 2 * (v i / 2) := fun i => by have := hp i i0; omega
    have hsum : (∑ i, v i / 2) % 2 = 0 := by
      have : ∑ i, v i = m + 2 * ∑ i, v i / 2 := by
        rw [Finset.mul_sum]
        calc ∑ i, v i = ∑ i, (1 + 2 * (v i / 2)) := Finset.sum_congr rfl fun i _ => hod i
          _ = _ := by rw [Finset.sum_add_distrib]; simp
      have hm' : ((m : ℕ) : ℤ) = 4 * (k : ℤ) := by rw [hk]; push_cast; ring
      rw [hm'] at this; omega
    obtain ⟨t, ht⟩ : ∃ t, ∑ i, v i / 2 = 2 * t := ⟨(∑ i, v i / 2) / 2, by omega⟩
    refine ⟨s + ∑ i, v i / 2 * d i + t * a, ?_⟩
    have e : (∑ i, (v i : ℚ) * x i) / 2 =
        (∑ i, x i) / 2 + (∑ i, ((v i / 2 : ℤ) : ℚ) * d i + ((∑ i, v i / 2 : ℤ) : ℚ) * x i0) := by
      rw [Finset.sum_div, Finset.sum_div]; push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (v i : ℚ) = 1 + 2 * ((v i / 2 : ℤ) : ℚ) := by exact_mod_cast hod i
      rw [this, hx' i]; ring
    rw [e, hsx, ht]; push_cast; rw [← ha]; ring

/-! ### The basis matrix and the block basis -/

/-- Integer vectors in $\mathbb Q^n$: $x \in \mathbb Z^n$ iff every coordinate is an integer. -/
theorem mem_intVec_iff_int {n : ℕ} {x : Fin n → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [mem_intVec]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    exact ⟨m, by rw [← ha, ← hm]; simp⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m : 𝓞 ℚ), by rw [hm]; simp⟩

namespace EBasisData

variable {m : ℕ} (D : EBasisData m)

/-- The basis matrix $B = \tfrac12 W$ of $E_m$ (its columns are the basis vectors). -/
def B : Matrix (Fin m) (Fin m) ℚ := (1 / 2 : ℚ) • D.W.map (Int.castRingHom ℚ)

/-- The inverse $B^{-1} = \tfrac12 V$. -/
def Binv : Matrix (Fin m) (Fin m) ℚ := (1 / 2 : ℚ) • D.V.map (Int.castRingHom ℚ)

theorem map_four_smul (M : Matrix (Fin m) (Fin m) ℤ) :
    ((4 : ℤ) • M).map (Int.castRingHom ℚ) = (4 : ℚ) • M.map (Int.castRingHom ℚ) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul,
    map_mul]
  simp

theorem B_mul_Binv : D.B * D.Binv = 1 := by
  have h := congrArg (fun M => M.map (Int.castRingHom ℚ)) D.hWV
  simp only [Matrix.map_mul] at h
  unfold B Binv
  rw [Matrix.smul_mul, Matrix.mul_smul, h, map_four_smul, Matrix.map_one _ (map_zero _) (map_one _), smul_smul,
    smul_smul]
  norm_num

theorem Binv_mul_B : D.Binv * D.B = 1 := by
  have h := congrArg (fun M => M.map (Int.castRingHom ℚ)) D.hVW
  simp only [Matrix.map_mul] at h
  unfold B Binv
  rw [Matrix.smul_mul, Matrix.mul_smul, h, map_four_smul, Matrix.map_one _ (map_zero _) (map_one _), smul_smul,
    smul_smul]
  norm_num

/-- $B^{\mathsf T}B = G$. -/
theorem B_gram : D.Bᵀ * D.B = D.G.map (Int.castRingHom ℚ) := by
  have h := congrArg (fun M => M.map (Int.castRingHom ℚ)) D.hgram
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  unfold B
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h, map_four_smul, smul_smul, smul_smul]
  norm_num

/-- The Gram matrix is symmetric. -/
theorem G_symm : D.Gᵀ = D.G := by
  have h := D.hgram
  have h2 : (4 : ℤ) • D.Gᵀ = (4 : ℤ) • D.G := by
    rw [← Matrix.transpose_smul, ← h, Matrix.transpose_mul, Matrix.transpose_transpose]
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  omega

/-- The block basis $B \oplus 1_k$ of $E_m \perp \mathbb Z^k$, as an element of $\mathrm{GL}_{m+k}(\mathbb Q)$. -/
def blk (k : ℕ) : GL (Fin (m + k)) ℚ :=
  ⟨blockMat D.B 0 0 1, blockMat D.Binv 0 0 1,
    by rw [blockMat_mul]; simp [D.B_mul_Binv, blockMat_one],
    by rw [blockMat_mul]; simp [D.Binv_mul_B, blockMat_one]⟩

theorem blk_val (k : ℕ) : (D.blk k).val = blockMat D.B 0 0 1 := rfl

theorem blk_inv_val (k : ℕ) : ((D.blk k)⁻¹).val = blockMat D.Binv 0 0 1 := rfl

theorem blockMat_mulVec_castAdd' {k : ℕ} (P : Matrix (Fin m) (Fin m) ℚ) (v : Fin (m + k) → ℚ) (i : Fin m) :
    (blockMat P 0 0 (1 : Matrix (Fin k) (Fin k) ℚ) *ᵥ v) (Fin.castAdd k i) = (P *ᵥ fun a => v (Fin.castAdd k a)) i := by
  simp [mulVec, dotProduct, Fin.sum_univ_add]

theorem blockMat_mulVec_natAdd' {k : ℕ} (P : Matrix (Fin m) (Fin m) ℚ) (v : Fin (m + k) → ℚ) (j : Fin k) :
    (blockMat P 0 0 (1 : Matrix (Fin k) (Fin k) ℚ) *ᵥ v) (Fin.natAdd m j) = v (Fin.natAdd m j) := by
  simp [mulVec, dotProduct, Fin.sum_univ_add, Matrix.one_apply]

theorem head_apply {k : ℕ} (x : Fin (m + k) → ℚ) (j : Fin m) :
    omearaEPerpHead m (m + k) x j = x (Fin.castAdd k j) := by
  simp only [omearaEPerpHead, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (by omega)]
  rfl

/-- The columns of $B$ lie in $E_m$. -/
theorem col_mem (h4 : 4 ∣ m) (hm : 0 < m) (j : Fin m) : (fun i => D.B i j) ∈ omearaE m := by
  have := half_mem_omearaE h4 hm (fun i => D.W i j) (D.hcol j).1 (D.hcol j).2
  convert this using 1
  funext i; simp [B]; ring

/-- $B c \in E_m$ for $c \in \mathbb Z^m$. -/
theorem mulVec_int_mem (h4 : 4 ∣ m) (hm : 0 < m) (c : Fin m → ℤ) :
    (D.B *ᵥ fun i => (c i : ℚ)) ∈ omearaE m := by
  have e : (D.B *ᵥ fun i => (c i : ℚ)) = ∑ j, (c j : ℚ) • (fun i => D.B i j) := by
    funext i; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun j _ => intCast_smul_mem (D.col_mem h4 hm j) (c j)

/-- $B^{-1}x \in \mathbb Z^m$ for $x \in E_m$. -/
theorem Binv_mulVec_int (h4 : 4 ∣ m) (hm : 0 < m) {x : Fin m → ℚ} (hx : x ∈ omearaE m) (r : Fin m) :
    ∃ z : ℤ, (D.Binv *ᵥ x) r = z := by
  obtain ⟨z, hz⟩ := half_dot_int h4 hm (fun i => D.V r i) (D.hrow r).1 (D.hrow r).2 hx
  refine ⟨z, ?_⟩
  rw [← hz]
  simp [Binv, mulVec, dotProduct, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **The block basis spans $E_m \perp \mathbb Z^k$.** -/
theorem glImage_blk (h4 : 4 ∣ m) (hm : 0 < m) (k : ℕ) :
    glImage (D.blk k) intVec = omearaEPerp m (m + k) := by
  ext x
  rw [mem_glImage]
  constructor
  · rintro ⟨c, hc, rfl⟩
    choose z hz using mem_intVec_iff_int.mp hc
    refine ⟨?_, ?_⟩
    · show omearaEPerpHead m (m + k) _ ∈ omearaE m
      have e : omearaEPerpHead m (m + k) ((D.blk k).val *ᵥ c) = D.B *ᵥ fun a => (z (Fin.castAdd k a) : ℚ) := by
        funext j
        rw [head_apply, blk_val, blockMat_mulVec_castAdd']
        congr 1; funext a; exact hz _
      rw [e]
      exact D.mulVec_int_mem h4 hm _
    · intro i hi
      obtain ⟨j, rfl⟩ : ∃ j : Fin k, i = Fin.natAdd m j := ⟨⟨i.val - m, by omega⟩, by ext; simp; omega⟩
      exact ⟨z (Fin.natAdd m j), by rw [blk_val, blockMat_mulVec_natAdd', hz]⟩
  · rintro ⟨hh, ht⟩
    refine ⟨((D.blk k)⁻¹).val *ᵥ x, ?_, ?_⟩
    · rw [mem_intVec_iff_int]
      intro i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · rw [blk_inv_val, blockMat_mulVec_castAdd']
        have e : (fun a => x (Fin.castAdd k a)) = omearaEPerpHead m (m + k) x := by
          funext j; rw [head_apply]
        rw [e]
        exact D.Binv_mulVec_int h4 hm hh a
      · rw [blk_inv_val, blockMat_mulVec_natAdd']
        exact ht _ (by simp)
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/-- $(B \oplus 1)^{\mathsf T}(B \oplus 1) = G \oplus 1$. -/
theorem blk_gram (k : ℕ) :
    (D.blk k).valᵀ * (D.blk k).val = (blockMat D.G 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).map (Int.castRingHom ℚ) := by
  rw [blk_val, blockMat_transpose, blockMat_mul, blockMat_map, D.B_gram]
  simp [Matrix.map_one _ (map_zero _) (map_one _)]

/-- **The Gram identity of the block basis:** $\sum_i ((B \oplus 1)x)_i^2 = x^{\mathsf T}(G \oplus 1)x$. -/
theorem blk_norm (k : ℕ) (x : Fin (m + k) → ℚ) :
    ((D.blk k).val *ᵥ x) ⬝ᵥ ((D.blk k).val *ᵥ x) =
      x ⬝ᵥ ((blockMat D.G 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).map (Int.castRingHom ℚ) *ᵥ x) := by
  rw [← D.blk_gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm]

/-- The basis matrix as an element of $\mathrm{GL}_m(\mathbb Q)$. -/
def gl : GL (Fin m) ℚ := ⟨D.B, D.Binv, D.B_mul_Binv, D.Binv_mul_B⟩

theorem gl_val : D.gl.val = D.B := rfl

/-- **The basis spans $E_m$.** -/
theorem glImage_gl (h4 : 4 ∣ m) (hm : 0 < m) : glImage D.gl intVec = omearaE m := by
  ext x
  rw [mem_glImage]
  constructor
  · rintro ⟨c, hc, rfl⟩
    choose z hz using mem_intVec_iff_int.mp hc
    have e : c = fun i => (z i : ℚ) := funext hz
    rw [e, gl_val]
    exact D.mulVec_int_mem h4 hm z
  · intro hx
    refine ⟨D.Binv *ᵥ x, mem_intVec_iff_int.mpr (D.Binv_mulVec_int h4 hm hx), ?_⟩
    rw [gl_val, mulVec_mulVec, D.B_mul_Binv, one_mulVec]

/-- $(Bx) \cdot (Bx) = x^{\mathsf T}Gx$. -/
theorem gl_norm (x : Fin m → ℚ) :
    (D.B *ᵥ x) ⬝ᵥ (D.B *ᵥ x) = x ⬝ᵥ (D.G.map (Int.castRingHom ℚ) *ᵥ x) := by
  rw [← D.B_gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm]

end EBasisData

/-- **$E_m$ has no vector of norm $1$** ($4 \mid m$, $m \ge 8$). -/
theorem omearaE_norm_ne_one {m : ℕ} (h4 : 4 ∣ m) (h8 : 8 ≤ m) {v : Fin m → ℚ} (hv : v ∈ omearaE m) :
    ∑ i, v i * v i ≠ 1 := by
  have hm : 0 < m := by omega
  obtain ⟨h1, h2, s, hs⟩ := (omeara106_11 h4 hm v).mp hv
  choose a ha using h1
  set i0 : Fin m := ⟨0, hm⟩
  have hpar : ∀ i, (a i - a i0) % 2 = 0 := by
    intro i
    obtain ⟨d, hd⟩ := h2 i i0
    have e : ((a i - a i0 : ℤ) : ℚ) = 2 * d := by push_cast; rw [← ha, ← ha]; linarith
    have : a i - a i0 = 2 * d := by exact_mod_cast e
    omega
  intro hn
  have h4n : ∑ i, a i * a i = 4 := by
    have e : ((∑ i, a i * a i : ℤ) : ℚ) = 4 * ∑ i, v i * v i := by
      push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [← ha]; ring
    rw [hn] at e; exact_mod_cast e
  rcases Int.emod_two_eq_zero_or_one (a i0) with h0 | h0
  · have hev : ∀ i, a i = 2 * (a i / 2) := fun i => by have := hpar i; omega
    have hsum : ∑ i, a i / 2 = 2 * s := by
      have e : ((∑ i, a i / 2 : ℤ) : ℚ) = 2 * s := by
        rw [← hs]; push_cast; refine Finset.sum_congr rfl fun i _ => ?_
        have e := ha i
        have e2 : (a i : ℚ) = 2 * ((a i / 2 : ℤ) : ℚ) := by exact_mod_cast hev i
        rw [e2] at e; linarith
      exact_mod_cast e
    have hn2 : ∑ i, (a i / 2) * (a i / 2) = 1 := by
      have e : ∑ i, a i * a i = 4 * ∑ i, (a i / 2) * (a i / 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          conv_lhs => rw [hev i]
          ring
      omega
    have hd : (2 : ℤ) ∣ ∑ i, ((a i / 2) * (a i / 2) - a i / 2) :=
      Finset.dvd_sum fun i _ => by
        obtain ⟨c, hc⟩ := Int.even_mul_pred_self (a i / 2)
        exact ⟨c, by nlinarith [hc]⟩
    rw [Finset.sum_sub_distrib, hn2, hsum] at hd
    omega
  · have hodd : ∀ i, 1 ≤ a i * a i := fun i => by
      have h1 : a i % 2 = 1 := by have := hpar i; omega
      have h2 : a i ≠ 0 := by omega
      rcases lt_or_gt_of_ne h2 with h | h <;> nlinarith
    have hle : (m : ℤ) ≤ ∑ i, a i * a i := by
      calc (m : ℤ) = ∑ _i : Fin m, (1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => hodd i
    omega

/-- The Gram matrix of a basis of $E_m$ has no vector of norm $1$. -/
theorem EBasisData.no_norm_one {m : ℕ} (D : EBasisData m) (h4 : 4 ∣ m) (h8 : 8 ≤ m) (x : Fin m → ℤ) :
    x ⬝ᵥ (D.G *ᵥ x) ≠ 1 := by
  intro h
  have hmem := D.mulVec_int_mem h4 (by omega) x
  apply omearaE_norm_ne_one h4 h8 hmem
  have e := D.gl_norm (fun i => (x i : ℚ))
  simp only [dotProduct] at e ⊢
  rw [e]
  have : ((x ⬝ᵥ (D.G *ᵥ x) : ℤ) : ℚ) = 1 := by exact_mod_cast h
  rw [← this]
  simp [dotProduct, mulVec, Matrix.map_apply]

/-! ### $E_m \perp \mathbb Z^k$ is unimodular -/

/-- $E_m \perp \mathbb Z^{k+1} = (E_m \perp \mathbb Z^k) \perp \mathbb Z$, for $n \ge m$. -/
theorem omearaEPerp_succ {m n : ℕ} (hn : m ≤ n) : omearaEPerp m (n + 1) = splitLat (omearaEPerp m n) := by
  ext x
  have hh : omearaEPerpHead m (n + 1) x = omearaEPerpHead m n (fun i : Fin n => x (Fin.castSucc i)) := by
    funext j
    simp only [omearaEPerpHead, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hj : (j : ℕ) < n
    · rw [dif_pos hj, dif_pos (by omega)]; rfl
    · exfalso; have := j.isLt; omega
  change (omearaEPerpHead m (n + 1) x ∈ omearaE m ∧ _) ↔ _
  rw [mem_splitLat, hh]
  change _ ↔ (omearaEPerpHead m n _ ∈ omearaE m ∧ _) ∧ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, fun i hi => h2 (Fin.castSucc i) hi⟩, h2 (Fin.last n) (by simp; omega)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun i hi => ?_⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact h2 j hi
    · exact h3

/-- **$E_m \perp \mathbb Z^{k}$ is unimodular** ($4 \mid m$, $m \ge 8$, every $k$). -/
theorem isUnimodularZ_omearaEPerp {m : ℕ} (h4 : 4 ∣ m) (h8 : 8 ≤ m) (k : ℕ) :
    IsUnimodularZ (sumSqForm (m + k)) (omearaEPerp m (m + k)) := by
  induction k with
  | zero =>
    rw [Nat.add_zero, omearaEPerp_self]
    exact (omeara106_r29_adjacent h4 h8).1
  | succ k ih =>
    rw [← Nat.add_assoc, omearaEPerp_succ (by omega)]
    exact splitLat_unimodular ih

end QuadFormsKB.Lattices
