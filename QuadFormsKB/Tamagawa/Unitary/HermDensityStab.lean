import QuadFormsKB.LocalDensity.FormDensityStab
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.Tamagawa.Unitary.Local

/-!
# Stabilization of the hermitian local density at good places

**Layer:** (A) a discrete valuation ring $R$ with finite residue field, $T = R[\omega]$, $\omega^2 = a$; (B) $F$ a number field, $v$ a finite place.

**Setting.** $H$ an invertible hermitian matrix over $T = R[\omega]$ ($\omega^2 = a$, $\bar\omega = -\omega$), $2\in R^\times$.

**Proves**
* (A, `herm_count_succ`) $A_{\pi^{k+1}}(H,H) = q^{m^2} A_{\pi^k}(H,H)$ for $k \ge 1$, where
  $A_{\pi^N}(H, H) = \#\{X\in M_m((R/\pi^N)[\omega]) : X^*HX = H\}$; hence
  $A_{\pi^k}(H,H)/q^{km^2} = A_{\pi}(H,H)/q^{m^2}$ for all $k\ge1$ (`herm_count_normalized_eq`).
  *Proof.* The counting Hensel lemma `DVR.card_sol_succ` (a multivariable form of Hanke 2004, Lemma 3.2, and of Siegel's
  Hilfssatz 13 [unverified]) for the quadratic map $X\mapsto X^*HX$, $M_m(R[\omega]) = R^{m\times m\times 2}\to
  R^{m\times m}$ (the $m^2$ independent real coordinates of a hermitian matrix: `coord`), with $d = 0$. Its
  differential $W\mapsto W^*HX + X^*HW$ is onto at every solution modulo $\pi$: with $G = X^*HX$ (hermitian, unit
  determinant) and $C$ hermitian, $W = \tfrac12 XG^{-1}C$ gives $W^*HX + X^*HW = C$.
* (B, `hermDensity_eq_of_good`, `repCountHerm_succ`, `tendsto_repCountHerm`) the same over $\mathcal O_F$ at a finite
  place $v$ with $2\notin\mathfrak p_v$ and $\det H_0$ a unit modulo $\mathfrak p_v$:
  $\beta^h_v(\Lambda,\Lambda) = A_{\mathfrak p}(H_0,H_0)/N\mathfrak p^{m^2}$, via $\mathcal O_F/\mathfrak p^k\cong\mathfrak o_v/\varpi^k$.
-/

open Matrix Filter
open scoped QuadraticAlgebra

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

/-! ### Coefficientwise maps of quadratic algebras and the coordinates of a hermitian matrix -/

section Coord

variable {S S' : Type*} [CommRing S] [CommRing S'] {m : ℕ}

/-- **Coefficientwise ring map** $S[\omega]\to S'[\omega]$, $x + y\omega\mapsto f(x) + f(y)\omega$
($\omega^2 = a\mapsto\omega^2 = f(a)$; the middle coefficient stays literally $0$). -/
def qmap (f : S →+* S') (a : S) : QuadraticAlgebra S a 0 →+* QuadraticAlgebra S' (f a) 0 where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp] theorem qmap_re (f : S →+* S') (a : S) (z : QuadraticAlgebra S a 0) : (qmap f a z).re = f z.re := rfl

@[simp] theorem qmap_im (f : S →+* S') (a : S) (z : QuadraticAlgebra S a 0) : (qmap f a z).im = f z.im := rfl

theorem qmap_star (f : S →+* S') (a : S) (z : QuadraticAlgebra S a 0) :
    qmap f a (star z) = star (qmap f a z) := by
  ext <;> simp

theorem qmap_norm (f : S →+* S') (a : S) (z : QuadraticAlgebra S a 0) :
    (qmap f a z).norm = f z.norm := by
  simp [QuadraticAlgebra.norm_def]

theorem star_smul' {a : S} (c : S) (z : QuadraticAlgebra S a 0) : star (c • z) = c • star z := by
  ext <;> simp

theorem conjTranspose_smul' {m : ℕ} {a : S} (c : S) (W : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) :
    (c • W)ᴴ = c • Wᴴ := by
  refine Matrix.ext fun i j => ?_
  simp [conjTranspose_apply, star_smul']

/-- **The $m^2$ independent coordinates of a hermitian matrix** over $S[\omega]$: for $i\le j$ the real part of
entry $(i,j)$, for $i > j$ the imaginary part of entry $(j,i)$. (A hermitian matrix has $\mathrm{im}\,G_{ii} = 0$
when $2\in S^\times$ and $G_{ij} = \overline{G_{ji}}$.) -/
def coord {m : ℕ} {a : S} (G : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) : Fin m × Fin m → S :=
  fun p => if p.1 ≤ p.2 then (G p.1 p.2).re else (G p.2 p.1).im

theorem coord_add {m : ℕ} {a : S} (A B : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) :
    coord (A + B) = coord A + coord B := by
  funext p
  simp only [coord, Pi.add_apply]
  split_ifs <;> simp

theorem coord_smul {m : ℕ} {a : S} (c : S) (A : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) :
    coord (c • A) = c • coord A := by
  funext p
  simp only [coord, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem coord_add_smul {m : ℕ} {a : S} (A B : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) (c : S) :
    coord (A + c • B) = coord A + c • coord B := by
  rw [coord_add, coord_smul]

theorem coord_map {m : ℕ} {a : S} (f : S →+* S') (G : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) :
    coord (G.map (qmap f a)) = f ∘ coord G := by
  funext p
  simp only [coord, Function.comp_apply]
  split_ifs <;> simp

/-- **A hermitian matrix is determined by its coordinates** ($2$ invertible). -/
theorem eq_of_coord_eq {m : ℕ} {a : S} (h2 : IsUnit (2 : S))
    {G G' : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)} (hG : G.IsHermitian) (hG' : G'.IsHermitian)
    (h : coord G = coord G') : G = G' := by
  have key : ∀ i j : Fin m, i ≤ j → G i j = G' i j := by
    intro i j hij
    have hre : (G i j).re = (G' i j).re := by
      have := congrFun h (i, j)
      simpa [coord, hij] using this
    ext
    · exact hre
    · rcases hij.lt_or_eq with hlt | heq
      · have := congrFun h (j, i)
        simpa [coord, not_le.mpr hlt] using this
      · subst heq
        have e1 := hG.apply i i
        have e2 := hG'.apply i i
        have a1 : (2 : S) * (G i i).im = 0 := by
          have := congrArg QuadraticAlgebra.im e1
          simp only [QuadraticAlgebra.im_star] at this
          linear_combination -this
        have a2 : (2 : S) * (G' i i).im = 0 := by
          have := congrArg QuadraticAlgebra.im e2
          simp only [QuadraticAlgebra.im_star] at this
          linear_combination -this
        rw [(h2.mul_right_eq_zero).mp a1, (h2.mul_right_eq_zero).mp a2]
  refine Matrix.ext fun i j => ?_
  rcases le_total i j with hij | hij
  · rw [key i j hij]
  · rw [← hG.apply i j, ← hG'.apply i j, key j i hij]

/-- Index set of the real coordinates ($\mathrm{re},\mathrm{im}$ of each entry) of $X\in M_m(S[\omega])$. -/
abbrev HIdx (m : ℕ) := Fin m × Fin m × Fin 2

/-- The matrix $X\in M_m(S[\omega])$ with entries $x_{(i,j,0)} + x_{(i,j,1)}\omega$. -/
def xmat (a : S) (x : HIdx m → S) : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0) :=
  Matrix.of fun i j => ⟨x (i, j, 0), x (i, j, 1)⟩

/-- The coordinates of a matrix over $S[\omega]$ (inverse of `xmat`). -/
def xcoords {a : S} (W : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) : HIdx m → S :=
  fun p => if p.2.2 = 0 then (W p.1 p.2.1).re else (W p.1 p.2.1).im

theorem xmat_xcoords {a : S} (W : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)) :
    xmat a (xcoords W) = W := by
  refine Matrix.ext fun i j => ?_
  ext <;> simp [xmat, xcoords]

theorem xcoords_xmat {m : ℕ} (a : S) (x : HIdx m → S) : xcoords (xmat a x) = x := by
  funext p
  obtain ⟨i, j, k⟩ := p
  fin_cases k <;> simp [xcoords, xmat]

/-- Matrices over $S[\omega]$ are the same as vectors in $S^{m\times m\times 2}$. -/
def xequiv {m : ℕ} (a : S) : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0) ≃ (HIdx m → S) where
  toFun := xcoords
  invFun := xmat a
  left_inv := xmat_xcoords
  right_inv := xcoords_xmat a

/-- **Every coordinate vector is realized by a hermitian matrix.** -/
theorem exists_herm_coord {m : ℕ} (a : S) (c : Fin m × Fin m → S) :
    ∃ C : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0), C.IsHermitian ∧ coord C = c := by
  refine ⟨Matrix.of fun i j => if i < j then ⟨c (i, j), c (j, i)⟩ else if i = j then ⟨c (i, i), 0⟩
    else ⟨c (j, i), -c (i, j)⟩, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    rcases lt_trichotomy i j with h | h | h
    · have h' : ¬ j < i := not_lt.mpr h.le
      have h'' : j ≠ i := h.ne'
      simp only [Matrix.of_apply, h, h', h'', ite_true, ite_false]
      ext <;> simp
    · subst h
      simp only [Matrix.of_apply, lt_irrefl, ite_false, ite_true]
      ext <;> simp
    · have h' : ¬ j > i := not_lt.mpr h.le
      have h'' : j ≠ i := h.ne
      simp only [Matrix.of_apply, h, h', h'', ite_true, ite_false, h.ne']
      ext <;> simp
  · funext p
    obtain ⟨i, j⟩ := p
    simp only [coord]
    by_cases hij : i ≤ j
    · rcases hij.lt_or_eq with h | h
      · simp [hij, h]
      · subst h; simp
    · have h : j < i := not_le.mp hij
      simp [hij, h]

/-- **Congruence of hermitian matrices modulo an ideal, in coordinates** ($2$ invertible). -/
theorem map_eq_iff_coord {m : ℕ} {a : S} (h2 : IsUnit (2 : S)) (I : Ideal S)
    {G G' : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0)} (hG : G.IsHermitian) (hG' : G'.IsHermitian) :
    G.map (qmap (Ideal.Quotient.mk I) a) = G'.map (qmap (Ideal.Quotient.mk I) a) ↔
      ∀ j, coord G j - coord G' j ∈ I := by
  constructor
  · intro h j
    have := congrFun (congrArg coord h) j
    rw [coord_map, coord_map] at this
    exact Ideal.Quotient.eq.mp this
  · intro h
    apply eq_of_coord_eq (h2.map (Ideal.Quotient.mk I))
      (hG.map _ fun z => qmap_star _ _ z) (hG'.map _ fun z => qmap_star _ _ z)
    rw [coord_map, coord_map]
    funext j
    exact Ideal.Quotient.eq.mpr (h j)

end Coord

/-! ### (A) The quadratic map $X\mapsto X^*HX$ over a discrete valuation ring -/

section DVRPart

open QuadFormsKB.LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {m : ℕ}

theorem xmat_add (a : R) (x y : HIdx m → R) : xmat a (x + y) = xmat a x + xmat a y := by
  refine Matrix.ext fun i j => ?_
  ext <;> simp [xmat]

theorem xmat_smul (a : R) (c : R) (x : HIdx m → R) : xmat a (c • x) = c • xmat a x := by
  refine Matrix.ext fun i j => ?_
  ext <;> simp [xmat]

/-- **The quadratic map** $X\mapsto \mathrm{coord}(X^*HX)$, $R^{m\times m\times 2}\to R^{m\times m}$. -/
def hermF (a : R) (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (x : HIdx m → R) :
    Fin m × Fin m → R :=
  coord ((xmat a x)ᴴ * H * xmat a x)

/-- **Its differential** at $X$: $W\mapsto\mathrm{coord}(W^*HX + X^*HW)$. -/
def hermD (a : R) (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (x : HIdx m → R) :
    (HIdx m → R) →ₗ[R] (Fin m × Fin m → R) where
  toFun w := coord ((xmat a w)ᴴ * H * xmat a x + (xmat a x)ᴴ * H * xmat a w)
  map_add' w w' := by
    rw [← coord_add]
    congr 1
    simp only [xmat_add, conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c w := by
    rw [← coord_smul]
    congr 1
    simp only [xmat_smul, conjTranspose_smul', Matrix.smul_mul, Matrix.mul_smul, smul_add,
      RingHom.id_apply]

/-- **Taylor expansion** $F(x + cw) = F(x) + c\,D_xw + c^2F(w)$. -/
theorem hermF_add_smul (a : R) (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (x w : HIdx m → R)
    (c : R) : hermF a H (x + c • w) = hermF a H x + c • hermD a H x w + c ^ 2 • hermF a H w := by
  unfold hermF
  have e : (xmat a (x + c • w))ᴴ * H * xmat a (x + c • w) =
      ((xmat a x)ᴴ * H * xmat a x + c • ((xmat a w)ᴴ * H * xmat a x + (xmat a x)ᴴ * H * xmat a w)) +
        c ^ 2 • ((xmat a w)ᴴ * H * xmat a w) := by
    simp only [xmat_add, xmat_smul, conjTranspose_add, conjTranspose_smul', Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, pow_two]
    abel
  rw [e, coord_add, coord_add_smul, coord_smul]
  rfl

/-- A quadratic-algebra element that is a unit modulo $\pi$ is a unit. -/
theorem isUnit_of_qmap_isUnit {π : R} (hπ : Irreducible π) (a : R) {z : QuadraticAlgebra R a 0}
    (hz : IsUnit (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a z)) : IsUnit z := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit] at hz ⊢
  rw [qmap_norm] at hz
  apply dvr_isUnit_of_not_dvd hπ
  intro hd
  have h0 : Ideal.Quotient.mk (Ideal.span {π ^ 1}) z.norm = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; simpa using hd
  rw [h0] at hz
  have : Nontrivial (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]; simpa using hπ.not_isUnit)
  exact not_isUnit_zero hz

/-- **The differential is onto at every solution modulo $\pi^K$, $K\ge1$** ($d = 0$): with $G = X^*HX$ (hermitian,
unit determinant) and $C$ hermitian, $W = \tfrac12 XG^{-1}C$ satisfies $W^*HX + X^*HW = C$. -/
theorem hermD_surj (π : R) (hπ : Irreducible π) (a : R)
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (hH : H.IsHermitian) (h2 : IsUnit (2 : R))
    (hdet : IsUnit ((H.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a)).det))
    (K : ℕ) (hK : 1 ≤ K) (x : HIdx m → R) (hx : ∀ j, π ^ K ∣ hermF a H x j - coord H j)
    (c : Fin m × Fin m → R) : ∃ w, hermD a H x w = π ^ 0 • c := by
  classical
  obtain ⟨X, hX⟩ : ∃ X, X = xmat a x := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G, G = Xᴴ * H * X := ⟨_, rfl⟩
  have hG : G.IsHermitian := hGdef ▸ isHermitian_conjTranspose_mul_mul X hH
  have hGH : G.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a) =
      H.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a) := by
    rw [map_eq_iff_coord h2 _ hG hH]
    intro j
    rw [Ideal.mem_span_singleton]
    have := hx j
    unfold hermF at this
    rw [← hX, ← hGdef] at this
    exact (pow_dvd_pow π hK).trans this
  have hdetG : IsUnit G.det := by
    apply isUnit_of_qmap_isUnit hπ a
    have := RingHom.map_det (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a) G
    rw [this]
    change IsUnit ((G.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a)).det)
    rw [hGH]; exact hdet
  obtain ⟨C, hC, hCc⟩ := exists_herm_coord a c
  obtain ⟨u2, hu2⟩ : ∃ u2 : R, u2 + u2 = 1 := by
    refine ⟨((h2.unit⁻¹ : Rˣ) : R), ?_⟩
    have := h2.unit.inv_mul
    rw [IsUnit.unit_spec] at this
    linear_combination this
  obtain ⟨W, hW⟩ : ∃ W, W = u2 • (X * G⁻¹ * C) := ⟨_, rfl⟩
  have hinvH : (G⁻¹)ᴴ = G⁻¹ := hG.inv.eq
  have t1 : C * (G⁻¹ * Xᴴ) * H * X = C := by
    have : C * (G⁻¹ * Xᴴ) * H * X = C * (G⁻¹ * (Xᴴ * H * X)) := by simp only [Matrix.mul_assoc]
    rw [this, ← hGdef, Matrix.nonsing_inv_mul _ hdetG, Matrix.mul_one]
  have t2 : Xᴴ * H * (X * G⁻¹ * C) = C := by
    have : Xᴴ * H * (X * G⁻¹ * C) = (Xᴴ * H * X) * G⁻¹ * C := by simp only [Matrix.mul_assoc]
    rw [this, ← hGdef, Matrix.mul_nonsing_inv _ hdetG, Matrix.one_mul]
  have hsum : Wᴴ * H * X + Xᴴ * H * W = C := by
    rw [hW, conjTranspose_smul', conjTranspose_mul, conjTranspose_mul, hinvH, hC.eq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, t1, t2]
    rw [← add_smul, hu2, one_smul]
  refine ⟨xcoords W, ?_⟩
  show coord ((xmat a (xcoords W))ᴴ * H * xmat a x + (xmat a x)ᴴ * H * xmat a (xcoords W)) = _
  rw [xmat_xcoords, ← hX, hsum, hCc, pow_zero, one_smul]

/-! #### Counts in coordinates and the stabilization -/

/-- **$A_{\pi^N}(H, H)$ over a discrete valuation ring:** $\#\{X\in M_m((R/\pi^N)[\omega]) : X^*\bar HX = \bar H\}$, where
$\bar H$ is the reduction of $H$ mod $\pi^N$ and $\omega^2 = \bar a$. -/
def hermCount (π : R) (a : R) (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (N : ℕ) : ℕ :=
  Nat.card {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra (R ⧸ Ideal.span {π ^ N})
      (Ideal.Quotient.mk (Ideal.span {π ^ N}) a) 0) //
    Xᴴ * H.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ N})) a) * X =
      H.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ N})) a)}

/-- **$A_{\pi^N}(H,H)$ in coordinates:** the number of $\vec x\in(R/\pi^N)^{m\times m\times2}$ whose lift satisfies
$\pi^N\mid\mathrm{coord}(X^*HX) - \mathrm{coord}(H)$ (`hermF`). -/
theorem hermCount_eq_card_sol (π : R) (a : R) (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0))
    (hH : H.IsHermitian) (h2 : IsUnit (2 : R)) (N : ℕ) :
    hermCount π a H N = Nat.card {x : HIdx m → R ⧸ Ideal.span {π ^ N} //
      ∀ j, π ^ N ∣ hermF a H (liftI π N x) j - coord H j} := by
  unfold hermCount
  refine Nat.card_congr (Equiv.subtypeEquiv (xequiv (m := m) (Ideal.Quotient.mk (Ideal.span {π ^ N}) a)).symm
    fun x => ?_).symm
  have hlift : ∀ p, Ideal.Quotient.mk (Ideal.span {π ^ N}) (liftI π N x p) = x p :=
    fun p => congrFun (redI_liftI π N x) p
  have hX : (xequiv (m := m) (Ideal.Quotient.mk (Ideal.span {π ^ N}) a)).symm x =
      (xmat a (liftI π N x)).map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ N})) a) := by
    refine Matrix.ext fun i j => ?_
    ext <;> simp [xequiv, xmat, hlift]
  rw [hX, ← conjTranspose_map _ (fun z => qmap_star _ a z), ← Matrix.map_mul, ← Matrix.map_mul]
  rw [map_eq_iff_coord h2 _ ?_ hH]
  · simp only [Ideal.mem_span_singleton]
    rfl
  · exact isHermitian_conjTranspose_mul_mul _ hH

section Stab

variable [Finite (IsLocalRing.ResidueField R)]

/-- **Stabilization of the hermitian count at a good place** (Siegel 1935, Hilfssatz 13 [unverified], in the
hermitian setting; multivariable Hanke 2004, Lemma 3.2): $R$ a discrete valuation ring, $H$ hermitian over $R[\omega]$
($\omega^2 = a$), $2\in R^\times$, $\det H$ a unit modulo $\pi$. Then for $k\ge1$,
$$A_{\pi^{k+1}}(H,H) = q^{m^2} A_{\pi^k}(H,H).$$ -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem herm_count_succ (π : R) (hπ : Irreducible π) (a : R)
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (hH : H.IsHermitian) (h2 : IsUnit (2 : R))
    (hdet : IsUnit ((H.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a)).det))
    (k : ℕ) (hk : 1 ≤ k) :
    hermCount π a H (k + 1) = q R ^ (m ^ 2) * hermCount π a H k := by
  have h := card_sol_succ π hπ (hermF a H) (hermD a H) (hermF_add_smul a H) (coord H) 0 k (by omega)
    fun x hx c => hermD_surj π hπ a H hH h2 hdet k hk x hx c
  rw [← hermCount_eq_card_sol π a H hH h2, ← hermCount_eq_card_sol π a H hH h2] at h
  have hc1 : Fintype.card (Fin m × Fin m) = m ^ 2 := by simp [sq]
  have hc2 : Fintype.card (HIdx m) = 2 * m ^ 2 := by simp [sq]; ring
  rw [hc1, hc2, pow_mul'] at h
  have hq : 0 < q R ^ (m ^ 2) := pow_pos (q_pos (R := R)) _
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h]
  ring

/-- **Stabilization of the normalized counts** ($k\ge1$): $A_{\pi^k}(H,H)/q^{km^2} = A_\pi(H,H)/q^{m^2}$. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem herm_count_normalized_eq (π : R) (hπ : Irreducible π) (a : R)
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (hH : H.IsHermitian) (h2 : IsUnit (2 : R))
    (hdet : IsUnit ((H.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a)).det))
    (k : ℕ) (hk : 1 ≤ k) :
    (hermCount π a H k : ℝ) / (q R : ℝ) ^ (k * m ^ 2) =
      (hermCount π a H 1 : ℝ) / (q R : ℝ) ^ (1 * m ^ 2) := by
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih, herm_count_succ π hπ a H hH h2 hdet k hk]
    push_cast
    rw [show (k + 1) * m ^ 2 = m ^ 2 + k * m ^ 2 by ring, pow_add]
    have : (q R : ℝ) ^ (m ^ 2) ≠ 0 := pow_ne_zero _ hq0
    field_simp

/-- **The limit of the normalized counts exists and is attained from $k = 1$ on.** -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem tendsto_hermCount (π : R) (hπ : Irreducible π) (a : R)
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (hH : H.IsHermitian) (h2 : IsUnit (2 : R))
    (hdet : IsUnit ((H.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a)).det)) :
    Tendsto (fun k : ℕ => (hermCount π a H k : ℝ) / (q R : ℝ) ^ (k * m ^ 2)) atTop
      (nhds ((hermCount π a H 1 : ℝ) / (q R : ℝ) ^ (1 * m ^ 2))) := by
  apply tendsto_const_nhds.congr'
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun k hk => (herm_count_normalized_eq π hπ a H hH h2 hdet k hk).symm⟩

/-- **Corollary with $\det H$ a unit of $R[\omega]$** (the hypothesis of the task statement). -/
theorem herm_count_succ_of_isUnit_det (π : R) (hπ : Irreducible π) (a : R)
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra R a 0)) (hH : H.IsHermitian) (h2 : IsUnit (2 : R))
    (hdet : IsUnit H.det) (k : ℕ) (hk : 1 ≤ k) :
    hermCount π a H (k + 1) = q R ^ (m ^ 2) * hermCount π a H k :=
  herm_count_succ π hπ a H hH h2 (by
    have := hdet.map (qmap (Ideal.Quotient.mk (Ideal.span {π ^ 1})) a)
    rwa [RingHom.map_det] at this) k hk

end Stab

end DVRPart

/-! ### (B) The number field: $\mathcal O_F/\mathfrak p^k\cong\mathfrak o_v/\varpi^k$ -/

section Bridge

variable {S S' : Type*} [CommRing S] [CommRing S'] {m : ℕ}

theorem qmap_injective {f : S →+* S'} (hf : Function.Injective f) (a : S) :
    Function.Injective (qmap f a) := by
  intro z w h
  ext
  · exact hf (congrArg QuadraticAlgebra.re h)
  · exact hf (congrArg QuadraticAlgebra.im h)

theorem qmap_surjective {f : S →+* S'} (hf : Function.Surjective f) (a : S) :
    Function.Surjective (qmap f a) := by
  intro w
  obtain ⟨x, hx⟩ := hf w.re
  obtain ⟨y, hy⟩ := hf w.im
  exact ⟨⟨x, y⟩, by ext <;> simp [hx, hy]⟩

/-- **Hermitian counts are invariant under a ring isomorphism of the coefficient rings** ($e : S\cong S'$,
$a' = e(a)$, $H'$ the transport of $H$ coefficientwise). -/
theorem card_herm_congr (e : S ≃+* S') (a : S) (a' : S') (ha : (e : S →+* S') a = a') {m : ℕ}
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0))
    (H' : Matrix (Fin m) (Fin m) (QuadraticAlgebra S' a' 0))
    (hH' : ∀ i j, (H' i j).re = e (H i j).re ∧ (H' i j).im = e (H i j).im) :
    Nat.card {X : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0) // Xᴴ * H * X = H} =
      Nat.card {Y : Matrix (Fin m) (Fin m) (QuadraticAlgebra S' a' 0) // Yᴴ * H' * Y = H'} := by
  subst ha
  have hH : H' = H.map (qmap (e : S →+* S') a) := Matrix.ext fun i j => by
    ext
    · exact (hH' i j).1
    · exact (hH' i j).2
  subst hH
  have hf : Function.Bijective (qmap (e : S →+* S') a) :=
    ⟨qmap_injective e.injective a, qmap_surjective e.surjective a⟩
  have hM : Function.Bijective (fun X : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0) =>
      X.map (qmap (e : S →+* S') a)) := by
    refine ⟨Matrix.map_injective hf.1, fun Y => ⟨Y.map (Function.surjInv hf.2), ?_⟩⟩
    refine Matrix.ext fun i j => ?_
    exact Function.surjInv_eq hf.2 (Y i j)
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hM) fun X => ?_)
  simp only [Equiv.ofBijective_apply]
  rw [← conjTranspose_map _ (fun z => qmap_star _ a z), ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective hf.1).eq_iff.symm

/-- Unit determinants are transported by the same coefficientwise isomorphism. -/
theorem isUnit_det_congr (e : S ≃+* S') (a : S) (a' : S') (ha : (e : S →+* S') a = a') {m : ℕ}
    (H : Matrix (Fin m) (Fin m) (QuadraticAlgebra S a 0))
    (H' : Matrix (Fin m) (Fin m) (QuadraticAlgebra S' a' 0))
    (hH' : ∀ i j, (H' i j).re = e (H i j).re ∧ (H' i j).im = e (H i j).im) (hd : IsUnit H.det) :
    IsUnit H'.det := by
  subst ha
  have hH : H' = H.map (qmap (e : S →+* S') a) := Matrix.ext fun i j => by
    ext
    · exact (hH' i j).1
    · exact (hH' i j).2
  subst hH
  have := hd.map (qmap (e : S →+* S') a)
  rwa [RingHom.map_det] at this

end Bridge

section Good

open QuadFormsKB.LocalDensity.NF QuadFormsKB.LocalDensity.DVR NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (v : HeightOneSpectrum (𝓞 F))

/-- **$H_0$ over $\mathfrak o_v[\omega]$**, $\omega^2 = \iota(-D)$: the coefficientwise image of $H_0$. -/
def hermLocal (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) :
    Matrix (Fin m) (Fin m) (QuadraticAlgebra (v.adicCompletionIntegers F) (ι v (-D)) 0) :=
  H₀.map (qmap (ι v) (-D))

theorem hermLocal_isHermitian {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) :
    (hermLocal D v H₀).IsHermitian :=
  hH.map _ fun z => qmap_star _ _ z

/-- The entries of `H₀ mod 𝔭^k` and of `hermLocal mod ϖ^k` correspond under `quotEquiv`. -/
theorem hermLocal_entries (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) (k : ℕ) (i j : Fin m) :
    ((hermLocal D v H₀).map (qmap (Ideal.Quotient.mk (Ideal.span {π v ^ k})) (ι v (-D))) i j).re =
        quotEquiv v k ((H₀.map (resQ D v k)) i j).re ∧
    ((hermLocal D v H₀).map (qmap (Ideal.Quotient.mk (Ideal.span {π v ^ k})) (ι v (-D))) i j).im =
        quotEquiv v k ((H₀.map (resQ D v k)) i j).im := by
  constructor <;> simp [hermLocal, resQ]

/-- **Counts over $\mathcal O_F/\mathfrak p^k$ equal counts over $\mathfrak o_v/\varpi^k$** (hermitian version of
`NF.repCountForm_eq_completion`). -/
theorem repCountHerm_eq_hermCount (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) (k : ℕ) :
    repCountHerm D H₀ v k = hermCount (π v) (ι v (-D)) (hermLocal D v H₀) k := by
  unfold repCountHerm hermCount
  exact card_herm_congr (quotEquiv v k) _ _ (quotEquiv_mk v k (-D)) _ _ (hermLocal_entries D v H₀ k)

/-- The reduced determinant hypothesis transports to the completion. -/
theorem isUnit_det_hermLocal (H₀ : Matrix (Fin m) (Fin m) (QuadO D))
    (hdet : IsUnit ((H₀.map (resQ D v 1)).det)) :
    IsUnit (((hermLocal D v H₀).map
      (qmap (Ideal.Quotient.mk (Ideal.span {π v ^ 1})) (ι v (-D)))).det) :=
  isUnit_det_congr (quotEquiv v 1) _ _ (quotEquiv_mk v 1 (-D)) _ _ (hermLocal_entries D v H₀ 1) hdet

theorem isUnit_two_completion (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : IsUnit (2 : v.adicCompletionIntegers F) := by
  apply dvr_isUnit_of_not_dvd (irreducible_π v)
  intro h
  have := (π_pow_dvd_two_iff v 1).mp (by simpa using h)
  exact h2 (by simpa using this)

/-- **Stabilization of the hermitian counts at a good place** (Siegel 1935, Hilfssatz 13 [unverified], hermitian
version): if $2\notin\mathfrak p_v$, $H_0$ is hermitian and $\det H_0$ is a unit modulo $\mathfrak p_v$, then for
$k\ge1$, $A_{\mathfrak p^{k+1}}(H_0,H_0) = N\mathfrak p^{m^2} A_{\mathfrak p^k}(H_0,H_0)$. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem repCountHerm_succ (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) (hH : H₀.IsHermitian)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hdet : IsUnit ((H₀.map (resQ D v 1)).det)) (k : ℕ) (hk : 1 ≤ k) :
    repCountHerm D H₀ v (k + 1) = Ideal.absNorm v.asIdeal ^ (m ^ 2) * repCountHerm D H₀ v k := by
  rw [repCountHerm_eq_hermCount, repCountHerm_eq_hermCount, ← q_completion v]
  exact herm_count_succ (π v) (irreducible_π v) _ _ (hermLocal_isHermitian D v hH)
    (isUnit_two_completion v h2) (isUnit_det_hermLocal D v H₀ hdet) k hk

/-- **The limit defining the hermitian density exists** at a good place, and is attained from $k = 1$ on. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem tendsto_repCountHerm (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) (hH : H₀.IsHermitian)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hdet : IsUnit ((H₀.map (resQ D v 1)).det)) :
    Tendsto (fun k : ℕ => (repCountHerm D H₀ v k : ℝ) / (Ideal.absNorm v.asIdeal : ℝ) ^ (k * m ^ 2)) atTop
      (nhds ((repCountHerm D H₀ v 1 : ℝ) / (Ideal.absNorm v.asIdeal : ℝ) ^ m ^ 2)) := by
  have h := tendsto_hermCount (π v) (irreducible_π v) _ _ (hermLocal_isHermitian D v hH)
    (isUnit_two_completion v h2) (isUnit_det_hermLocal D v H₀ hdet)
  simp only [← repCountHerm_eq_hermCount, q_completion, one_mul] at h
  exact h

/-- **The hermitian local density at a good place** (Siegel 1935, Hilfssatz 13 [unverified]): if $2\notin\mathfrak p_v$,
$H_0$ is hermitian and $\det H_0$ is a unit modulo $\mathfrak p_v$, then
$$\beta^h_v(\Lambda,\Lambda) = A_{\mathfrak p}(H_0,H_0)/N\mathfrak p^{m^2},$$
a count over the residue ring $(\mathcal O_F/\mathfrak p)[\omega]$. Unconditional given these hypotheses. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem hermDensity_eq_of_good (H₀ : Matrix (Fin m) (Fin m) (QuadO D)) (hH : H₀.IsHermitian)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hdet : IsUnit ((H₀.map (resQ D v 1)).det)) :
    hermDensity D H₀ v =
      (repCountHerm D H₀ v 1 : ℝ) / (Ideal.absNorm v.asIdeal : ℝ) ^ m ^ 2 :=
  (tendsto_repCountHerm D v H₀ hH h2 hdet).limUnder_eq

end Good

end QuadFormsKB.Tamagawa.Unitary
