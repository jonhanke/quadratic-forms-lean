/-
# Kneser neighbours, part 6: certificates checked by the kernel

**Layer:** integral forms (`QuadForm ℤ n`), lattices in $\mathbb{Q}^n$ (`Siegel/Neighbors.lean`).

The neighbour method needs three kinds of facts about concrete forms: a form is **in the genus** of $Q$, two forms are
**equivalent**, and two forms are **not equivalent**. This file defines finite, decidable **certificates** for the first
two; an algorithm (`Siegel/KneserGen.lean`, or any external program) produces them, and Lean checks them with `decide`
(kernel evaluation of integer matrix identities; never `native_decide`).

**Defines and proves**
- `IsoCert` / `IsoCert.intEquiv`: integer matrices $M, N$ with $MN = 1$ and $M^{\mathsf T}H_QM = H_{Q'}$ certify
  $Q \sim_{\mathbb{Z}} Q'$ (`IntEquiv`).
- `DetCert` / `DetCert.not_dvd_det`: an integer matrix $X$ with $H X = d\cdot 1$ and $p \nmid d$ certifies $p \nmid \det H$
  (without computing a determinant in the kernel).
- `NbCert` / `NbCert.sameGenus`: data $(\vec{v}, G, \dots)$ certifying that $Q'$ is the Gram form of the explicit
  $p$-neighbour $L(\vec{v})$ of $\mathbb{Z}^n$ (`nbLat`) in the basis given by the columns of $\frac1pG$; hence (AWS notes,
  Thm. 1.10.3(1)) **$Q'$ is in the genus of $Q$** (`sameGenus_of_neighbor`).

*The neighbour certificate.* For $\vec{v}$ with $p^2 \mid Q(\vec{v})$, $\vec{v} \not\equiv 0$, put $\vec{u} = H\vec{v}$ and pick $\vec{w}$ with
$B(\vec{w}, \vec{v}) \equiv 1 \pmod p$. Then $L_{\vec{v}} = \{\vec{y} \in \mathbb{Z}^n : p \mid B(\vec{y}, \vec{v})\}$ is spanned by $p\vec{w}$ and the
$\vec{e}_i - u_i\vec{w}$, so $L(\vec{v}) = L_{\vec{v}} + \mathbb{Z}\frac1p\vec{v}$ is spanned by these and $\frac1p\vec{v}$. The certificate gives a
matrix $G$ whose columns, divided by $p$, lie in $L(\vec{v})$ (`k`: $G_j \equiv k_j\vec{v} \pmod p$ and $p^2 \mid B(G_j, \vec{v})$), and
integer coordinates of all the spanning vectors in that basis (`A`, `cW`, `cV`); so $\frac1pG\,\mathbb{Z}^n = L(\vec{v})$
(`imgLat_eq_nbLat`). Finally $G^{\mathsf T}HG = p^2H_{Q'}$ says $Q'(\vec{x}) = Q(\frac1pG\vec{x})$.
-/
import QuadFormsKB.Siegel.KneserMass
import QuadFormsKB.Siegel.NeighborGenus

open Matrix

namespace QuadFormsKB.Siegel.Kneser

open QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Equivalence certificates -/

/-- **An equivalence certificate:** integer matrices $M$ (the change of variables) and $N$ (its inverse). -/
structure IsoCert (n : ℕ) where
  /-- The change of variables $M \in \mathrm{GL}_n(\mathbb{Z})$. -/
  M : Matrix (Fin n) (Fin n) ℤ
  /-- Its inverse. -/
  N : Matrix (Fin n) (Fin n) ℤ

/-- **Validity of an equivalence certificate** for $Q \sim Q'$: $MN = 1$ and $M^{\mathsf T}H_QM = H_{Q'}$ (decidable). -/
def IsoCert.Valid (Q Q' : QuadForm ℤ n) (c : IsoCert n) : Prop :=
  c.M * c.N = 1 ∧ c.Mᵀ * Q.hessian * c.M = Q'.hessian

instance (Q Q' : QuadForm ℤ n) (c : IsoCert n) : Decidable (c.Valid Q Q') := by
  unfold IsoCert.Valid; infer_instance

/-- **A valid equivalence certificate proves $Q \sim_{\mathbb{Z}} Q'$:** $Q(M\vec{x}) = Q'(\vec{x})$ with $M \in \mathrm{GL}_n(\mathbb{Z})$. -/
theorem IsoCert.intEquiv {Q Q' : QuadForm ℤ n} {c : IsoCert n} (h : c.Valid Q Q') : IntEquiv Q Q' :=
  ⟨⟨c.M, c.N, h.1, mul_eq_one_comm.mp h.1⟩, (eval_mulVec_eq_iff_hessian Q Q' c.M).mpr h.2⟩

/-! ### Determinant certificates -/

/-- **A certificate that $p \nmid \det H$:** an integer matrix $X$ and $d \in \mathbb{Z}$ with $HX = d\cdot 1$, $p \nmid d$
(e.g. $X = \operatorname{adj} H$, $d = \det H$). -/
structure DetCert (n : ℕ) where
  /-- The matrix $X$ with $HX = d \cdot 1$. -/
  X : Matrix (Fin n) (Fin n) ℤ
  /-- The scalar $d$. -/
  d : ℤ

/-- Validity of a determinant certificate for $H$ and $p$ (decidable). -/
def DetCert.Valid (H : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) (c : DetCert n) : Prop :=
  H * c.X = c.d • (1 : Matrix (Fin n) (Fin n) ℤ) ∧ ¬ (p : ℤ) ∣ c.d

instance (H : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) (c : DetCert n) : Decidable (c.Valid H p) := by
  unfold DetCert.Valid; infer_instance

/-- **A valid determinant certificate proves $p \nmid \det H$:** $\det H \det X = d^n$, and $p$ is prime. -/
theorem DetCert.not_dvd_det {H : Matrix (Fin n) (Fin n) ℤ} {p : ℕ} [hp : Fact p.Prime] {c : DetCert n}
    (h : c.Valid H p) : ¬ (p : ℤ) ∣ H.det := by
  intro hd
  have e := congrArg Matrix.det h.1
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at e
  have : (p : ℤ) ∣ c.d ^ n := e ▸ dvd_mul_of_dvd_left hd _
  exact h.2 ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow this)

/-! ### Neighbour certificates -/

/-- **A neighbour certificate** for $Q'$ being the Gram form of the $p$-neighbour $L(\vec{v})$ of $\mathbb{Z}^n$:
- `v`: the vector $\vec{v}$ ($p^2 \mid Q(\vec{v})$, $\vec{v} \not\equiv 0 \bmod p$);
- `G`: $p$ times a basis of $L(\vec{v})$ (columns);
- `k`: $G_j \equiv k_j\vec{v} \pmod p$;
- `w`: a vector with $B(\vec{w}, \vec{v}) \equiv 1 \pmod p$;
- `A`: $GA = p(1 - \vec{w}\vec{u}^{\mathsf T})$, $\vec{u} = H\vec{v}$ (coordinates of the $\vec{e}_i - u_i\vec{w}$);
- `cW`: $G\,\vec{c}_w = p^2\vec{w}$ (coordinates of $p\vec{w}$);
- `cV`: $G\,\vec{c}_v = \vec{v}$ (coordinates of $\frac1p\vec{v}$);
- `K`: $GK = p^2\cdot 1$ (so $\det G \ne 0$). -/
structure NbCert (n : ℕ) where
  /-- The isotropic vector $\vec{v}$. -/
  v : Fin n → ℤ
  /-- The basis matrix, scaled by $p$. -/
  G : Matrix (Fin n) (Fin n) ℤ
  /-- $G_j \equiv k_j \vec{v} \pmod p$. -/
  k : Fin n → ℤ
  /-- $B(\vec{w}, \vec{v}) \equiv 1 \pmod p$. -/
  w : Fin n → ℤ
  /-- Coordinates of $\vec{e}_i - u_i\vec{w}$, scaled. -/
  A : Matrix (Fin n) (Fin n) ℤ
  /-- Coordinates of $p\vec{w}$. -/
  cW : Fin n → ℤ
  /-- Coordinates of $\frac1p\vec{v}$. -/
  cV : Fin n → ℤ
  /-- $GK = p^2 \cdot 1$. -/
  K : Matrix (Fin n) (Fin n) ℤ

/-- **Validity of a neighbour certificate** for $(Q, p, Q')$ (decidable; see `NbCert`). -/
def NbCert.Valid (Q Q' : QuadForm ℤ n) (p : ℕ) (c : NbCert n) : Prop :=
  (p : ℤ) ^ 2 ∣ Q.eval c.v ∧ (∃ i, ¬ (p : ℤ) ∣ c.v i) ∧
  (∀ j r, (p : ℤ) ∣ c.G r j - c.k j * c.v r) ∧ (∀ j, (p : ℤ) ^ 2 ∣ bZ Q (fun r => c.G r j) c.v) ∧
  (p : ℤ) ∣ bZ Q c.w c.v - 1 ∧
  c.G * c.A = (p : ℤ) • (1 - vecMulVec c.w (Q.hessian *ᵥ c.v)) ∧
  c.G *ᵥ c.cW = ((p : ℤ) ^ 2) • c.w ∧ c.G *ᵥ c.cV = c.v ∧
  c.G * c.K = ((p : ℤ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℤ) ∧
  c.Gᵀ * Q.hessian * c.G = ((p : ℤ) ^ 2) • Q'.hessian

instance (Q Q' : QuadForm ℤ n) (p : ℕ) (c : NbCert n) : Decidable (c.Valid Q Q' p) := by
  unfold NbCert.Valid; infer_instance

/-- The rational basis matrix $g = \frac1pG$ of a neighbour certificate. -/
noncomputable def NbCert.g (p : ℕ) (c : NbCert n) : Matrix (Fin n) (Fin n) ℚ :=
  (1 / (p : ℚ)) • c.G.map (Int.castRingHom ℚ)

section Sound

variable {Q Q' : QuadForm ℤ n} {p : ℕ} [hp : Fact p.Prime] {c : NbCert n}

theorem cv_mulVec (G : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) :
    G.map (Int.castRingHom ℚ) *ᵥ cv y = cv (G *ᵥ y) := by
  ext i; simp [cv, mulVec, dotProduct]

omit hp in
theorem NbCert.g_mulVec (c : NbCert n) (y : Fin n → ℤ) :
    c.g p *ᵥ Kneser.cv y = (1 / (p : ℚ)) • Kneser.cv (c.G *ᵥ y) := by
  rw [NbCert.g, smul_mulVec, cv_mulVec]

theorem imgLat_le_iff {g : Matrix (Fin n) (Fin n) ℚ} {N : Submodule ℤ (Fin n → ℚ)} :
    imgLat g ≤ N ↔ ∀ j, g *ᵥ cv (Pi.single j 1) ∈ N := by
  constructor
  · intro h j; exact h ⟨_, rfl⟩
  · rintro h _ ⟨c, rfl⟩
    have e : cv c = ∑ j, c j • cv (Pi.single j 1) := by
      ext i; simp [cv, Finset.sum_apply, Pi.single_apply]
    rw [e, mulVec_sum]
    exact N.sum_mem fun j _ => by rw [mulVec_smul]; exact N.smul_mem _ (h j)

theorem mulVec_single (G : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    G *ᵥ Pi.single j 1 = fun r => G r j := by
  ext r; simp [mulVec, dotProduct, Pi.single_apply]

/-- **The certified basis spans $L(\vec{v})$:** $\frac1pG\,\mathbb{Z}^n = L(\vec{v})$. -/
theorem NbCert.imgLat_eq_nbLat (h : c.Valid Q Q' p) : imgLat (c.g p) = nbLat Q p c.v := by
  obtain ⟨hv, -, hk, hB, hw, hA, hcw, hcv, -, -⟩ := h
  have hp0 := p_ne_zero (p := p)
  apply le_antisymm
  · rw [imgLat_le_iff]
    intro j
    rw [NbCert.g_mulVec, mulVec_single, mem_nbLat_iff hv]
    refine ⟨?_, hB j⟩
    choose z hz using fun r => hk j r
    exact ⟨c.k j, fun r => z r, by ext r; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hz r]⟩
  · rintro _ ⟨y, k, ⟨t, ht⟩, rfl⟩
    refine ⟨c.A *ᵥ y + t • c.cW + k • c.cV, ?_⟩
    have hu : (Q.hessian *ᵥ c.v) ⬝ᵥ y = (p : ℤ) * t := by
      rw [← ht, bZ, dotProduct_comm]
    have h1 : c.G *ᵥ (c.A *ᵥ y) = (p : ℤ) • y - ((p : ℤ) * ((p : ℤ) * t)) • c.w := by
      rw [mulVec_mulVec, hA, smul_mulVec, sub_mulVec, one_mulVec, vecMulVec_mulVec, hu]
      ext i; simp; ring
    rw [NbCert.g_mulVec, mulVec_add, mulVec_add, h1, mulVec_smul, mulVec_smul, hcw, hcv]
    ext i
    simp only [cv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    field_simp
    ring

/-- The certified basis has $\det \frac1pG \ne 0$. -/
theorem NbCert.det_g_ne_zero (h : c.Valid Q Q' p) : (c.g p).det ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hK, -⟩ := h
  have hp0 := p_ne_zero (p := p)
  have e := congrArg Matrix.det hK
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at e
  have hG : c.G.det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e
    exact pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)) e.symm
  have hm : (c.G.map (Int.castRingHom ℚ)).det = (c.G.det : ℚ) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [NbCert.g, det_smul, hm]
  exact mul_ne_zero (pow_ne_zero _ (by simpa using hp0)) (by exact_mod_cast hG)

/-- The certified Gram form: $Q'(\vec{x}) = Q(\frac1pG\vec{x})$ on $\mathbb{Q}^n$. -/
theorem NbCert.evalIn_eq (h : c.Valid Q Q' p) (x : Fin n → ℚ) :
    Q'.evalIn ℚ x = Q.evalIn ℚ (c.g p *ᵥ x) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hH⟩ := h
  have hp0 := p_ne_zero (p := p)
  set F := (Int.castRingHom ℚ).mapMatrix (m := Fin n)
  have e : F c.Gᵀ * F Q.hessian * F c.G = ((p : ℚ) ^ 2) • F Q'.hessian := by
    have := congrArg F hH
    rw [map_mul, map_mul, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at this
    simpa using this
  have hT : F c.Gᵀ = (F c.G)ᵀ := by ext i j; rfl
  have hHq : Q'.hessian.map (algebraMap ℤ ℚ) =
      (c.g p)ᵀ * Q.hessian.map (algebraMap ℤ ℚ) * c.g p := by
    change F Q'.hessian = _
    have hg : c.g p = (1 / (p : ℚ)) • F c.G := rfl
    rw [hg, show Q.hessian.map (algebraMap ℤ ℚ) = F Q.hessian from rfl, transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← hT, e, smul_smul]
    rw [show 1 / (p : ℚ) * (1 / p) * p ^ 2 = 1 by field_simp, one_smul]
  have h1 := two_mul_evalIn (K := ℚ) Q' x
  have h2 := two_mul_evalIn (K := ℚ) Q (c.g p *ᵥ x)
  rw [hHq, dotProduct_conj] at h1
  linarith

/-- **A valid neighbour certificate proves that $Q'$ is in the genus of $Q$** (for an odd prime $p \nmid \det H_Q$):
$Q'$ is the Gram form of the $p$-neighbour $L(\vec{v})$ (`isNeighbor_nbLat`) in the certified basis, and Gram forms of
$p$-neighbours are in the genus (`sameGenus_of_neighbor`; AWS notes, Thm. 1.10.3(1)). -/
@[kb "hanke2011aws" "Thm. 1.10.3(1), p. 23"]
theorem NbCert.sameGenus (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (h : c.Valid Q Q' p) :
    SameGenus Q Q' := by
  have hv0 : red p c.v ≠ 0 := by
    obtain ⟨i, hi⟩ := h.2.1
    intro h0; exact hi ((red_eq_zero_iff c.v).mp h0 i)
  have hL : IsNeighbor Q p (imgLat (c.g p)) := by
    rw [NbCert.imgLat_eq_nbLat h]; exact isNeighbor_nbLat hdet h.1 hv0
  exact sameGenus_of_neighbor hp2 hdet (NbCert.det_g_ne_zero h) hL (NbCert.evalIn_eq h)

end Sound

end QuadFormsKB.Siegel.Kneser
