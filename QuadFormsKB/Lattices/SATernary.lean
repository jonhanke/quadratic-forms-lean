/-
# Strong approximation for ternary rotations via quaternions (O'Meara 104:4, step 2)

**Layer:** a nondegenerate ternary form $Q$ over a number field $F$, similar to the norm form on pure quaternions:
$d\,Q(Py) = \operatorname{nrd}(y_0 i + y_1 j + y_2 k)$ in $D = (a,b)_F$ (`Quat.exists_isometric_smul_pureForm`), and the
conjugation action $y \mapsto \alpha y\alpha^{-1}$ of $D^\times$ on $D^0$ (`Tamagawa/QuaternionSO3.lean`).

**Proves** (O'Meara 1973, 104:4 step 2, pp. 317–319 = PDF pp. 325–327, in the language of `RotApprox`):
* `transport_symm`, `transport_symmProd`: under the similarity, symmetries $\tau_x$ of $Q$ become the reflections of
  $D^0$, and a product of an even number $2r$ of them is conjugation by $\beta = \prod u_{2i-1}u_{2i}$ with
  $\operatorname{nrd}\beta = d^{2r}\prod Q(x_i)$;
* `exists_conj_of_mem_spinorKernel`: every $\varphi \in O'(V_K)$ is conjugation by some $\alpha \in D_K$ with
  $\operatorname{nrd}\alpha = 1$ (O'Meara's Proposition 57:13 direction used in step 2b);
* `mem_spinorKernel_of_conj`: conversely conjugation by $\alpha$ with $\operatorname{nrd}\alpha = 1$ lies in $O'(V)$.
-/
import QuadFormsKB.Lattices.SAVectorsIsotropic
import QuadFormsKB.Tamagawa.QuaternionSO3

open NumberField IsDedekindDomain Matrix WithZero Topology Filter Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

/-! ### Transporting symmetries to reflections of pure quaternions -/

section Transport

variable (K : Type*) [Field K] [Algebra F K] [CharZero K]

variable {Q : QuadForm F 3} {a b d : F} {P : GL (Fin 3) F}

/-- The similarity matrix over $K$. -/
abbrev PK (P : GL (Fin 3) F) (K : Type*) [Field K] [Algebra F K] : Matrix (Fin 3) (Fin 3) K :=
  (P : Matrix (Fin 3) (Fin 3) F).map (algebraMap F K)

/-- Its inverse over $K$. -/
abbrev PKi (P : GL (Fin 3) F) (K : Type*) [Field K] [Algebra F K] : Matrix (Fin 3) (Fin 3) K :=
  ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (algebraMap F K)

theorem PK_mul_PKi : PK P K * PKi P K = 1 := map_mul_map_inv P K

theorem PKi_mul_PK : PKi P K * PK P K = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem PKi_PK (y : Fin 3 → K) : PKi P K *ᵥ (PK P K *ᵥ y) = y := by
  rw [mulVec_mulVec, PKi_mul_PK, one_mulVec]

theorem PK_PKi (y : Fin 3 → K) : PK P K *ᵥ (PKi P K *ᵥ y) = y := by
  rw [mulVec_mulVec, PK_mul_PKi, one_mulVec]

/-- The similarity hypothesis over $K$: $\langle -a,-b,ab\rangle(y) = d\,Q(Py)$. -/
def SimAt (Q : QuadForm F 3) (a b d : F) (P : GL (Fin 3) F) (K : Type*) [Field K] [Algebra F K] : Prop :=
  ∀ y : Fin 3 → K, Quat.Q3 (algebraMap F K a) (algebraMap F K b) y = algebraMap F K d * Q.evalIn K (PK P K *ᵥ y)

variable {K}

theorem B3_eq_qbil (hsim : SimAt Q a b d P K) (y z : Fin 3 → K) :
    Quat.B3 (algebraMap F K a) (algebraMap F K b) y z =
      algebraMap F K d * qbil Q K (PK P K *ᵥ y) (PK P K *ᵥ z) := by
  have h1 := Quat.Q3_add (a := algebraMap F K a) (b := algebraMap F K b) y z
  rw [hsim, hsim, hsim, mulVec_add] at h1
  have h2 := QuadForm.polar_eq_hessian K Q (PK P K *ᵥ y) (PK P K *ᵥ z)
  rw [qbil, ← h2]
  linear_combination -h1

/-- **A symmetry of $Q$ is a reflection of $D^0$:** $P^{-1}\tau_x P = s_{P^{-1}x}$. -/
theorem transport_symm (hd : d ≠ 0) (hsim : SimAt Q a b d P K) {x : Fin 3 → K} (hx : Q.evalIn K x ≠ 0)
    (y : Fin 3 → K) :
    PKi P K *ᵥ (((symm Q K x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (PK P K *ᵥ y)) =
      Quat.refl (algebraMap F K a) (algebraMap F K b) (PKi P K *ᵥ x) y := by
  have hd' : algebraMap F K d ≠ 0 := (map_ne_zero _).mpr hd
  rw [symm_mulVec_bil Q K hx, mulVec_sub, mulVec_smul, PKi_PK, Quat.refl_apply, B3_eq_qbil hsim, hsim,
    PK_PKi, qbil_comm]
  congr 2
  field_simp

theorem Q3_PKi (hsim : SimAt Q a b d P K) (x : Fin 3 → K) :
    Quat.Q3 (algebraMap F K a) (algebraMap F K b) (PKi P K *ᵥ x) = algebraMap F K d * Q.evalIn K x := by
  rw [hsim, PK_PKi]

theorem Q3_PKi_ne_zero (hd : d ≠ 0) (hsim : SimAt Q a b d P K) {x : Fin 3 → K} (hx : Q.evalIn K x ≠ 0) :
    Quat.Q3 (algebraMap F K a) (algebraMap F K b) (PKi P K *ᵥ x) ≠ 0 := by
  rw [Q3_PKi hsim]; exact mul_ne_zero ((map_ne_zero _).mpr hd) hx

theorem nrd_pureUnit' {A B : K} (u : Fin 3 → K) (hu : Quat.Q3 A B u ≠ 0) :
    Quat.nrd ((Quat.pureUnit u hu : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = Quat.Q3 A B u := by
  rw [Quat.coe_pureUnit, Quat.nrd_pure, Quat.eval_pureForm]

/-- **A pair of symmetries is a conjugation:** $P^{-1}\tau_x\tau_wP$ is conjugation by $uw$ ($u = P^{-1}x$, $w' = P^{-1}w$). -/
theorem transport_pair (hd : d ≠ 0) (hsim : SimAt Q a b d P K) {x w : Fin 3 → K} (hx : Q.evalIn K x ≠ 0)
    (hw : Q.evalIn K w ≠ 0) (y : Fin 3 → K) :
    PKi P K *ᵥ (((symm Q K x * symm Q K w : orthGroup Q K) : GL (Fin 3) K).val *ᵥ (PK P K *ᵥ y)) =
      Quat.conjLin (Quat.pureUnit (PKi P K *ᵥ x) (Q3_PKi_ne_zero hd hsim hx) *
        Quat.pureUnit (PKi P K *ᵥ w) (Q3_PKi_ne_zero hd hsim hw)) y := by
  change PKi P K *ᵥ (((symm Q K x : GL (Fin 3) K).val * (symm Q K w : GL (Fin 3) K).val) *ᵥ (PK P K *ᵥ y)) = _
  rw [← mulVec_mulVec, ← PK_PKi (P := P) K (((symm Q K w : GL (Fin 3) K).val) *ᵥ (PK P K *ᵥ y)),
    transport_symm hd hsim hx, transport_symm hd hsim hw, Quat.conjLin_mul, Module.End.mul_apply,
    Quat.conjLin_pureUnit_apply, Quat.conjLin_pureUnit_apply, map_neg, neg_neg]

/-- **An even product of symmetries is a conjugation:** for anisotropic $x_1, \dots, x_{2r}$,
$P^{-1}\tau_{x_1}\cdots\tau_{x_{2r}}P$ is conjugation by some $\beta \in D_K^\times$ with
$\operatorname{nrd}\beta = d^{2r}Q(x_1)\cdots Q(x_{2r})$. -/
theorem transport_symmProd (hd : d ≠ 0) (hsim : SimAt Q a b d P K) :
    ∀ xs : List (Fin 3 → K), (∀ x ∈ xs, Q.evalIn K x ≠ 0) → Even xs.length →
      ∃ β : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ,
        (∀ y, PKi P K *ᵥ ((symmProd Q K xs : GL (Fin 3) K).val *ᵥ (PK P K *ᵥ y)) = Quat.conjLin β y) ∧
          Quat.nrd (β : ℍ[K, algebraMap F K a, algebraMap F K b]) =
            algebraMap F K d ^ xs.length * valProd Q K xs
  | [], _, _ => ⟨1, fun y => by simp [symmProd, Quat.conjLin_one, PKi_mul_PK (P := P) K], by simp [valProd]⟩
  | [_], _, h => by simp at h
  | x :: w :: rest, hxs, h => by
    have hx : Q.evalIn K x ≠ 0 := hxs x (by simp)
    have hw : Q.evalIn K w ≠ 0 := hxs w (by simp)
    have hrest : ∀ z ∈ rest, Q.evalIn K z ≠ 0 := fun z hz => hxs z (by simp [hz])
    have hlen : Even rest.length := by
      simp only [List.length_cons] at h
      rwa [show rest.length + 1 + 1 = rest.length + 2 by ring, Nat.even_add, iff_true_intro even_two,
        iff_true] at h
    obtain ⟨β, hβ, hnβ⟩ := transport_symmProd hd hsim rest hrest hlen
    set γ := Quat.pureUnit (PKi P K *ᵥ x) (Q3_PKi_ne_zero hd hsim hx) *
      Quat.pureUnit (PKi P K *ᵥ w) (Q3_PKi_ne_zero hd hsim hw)
    refine ⟨γ * β, fun y => ?_, ?_⟩
    · have hsp : symmProd Q K (x :: w :: rest) = (symm Q K x * symm Q K w) * symmProd Q K rest := by
        simp [symmProd, mul_assoc]
      rw [hsp, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec,
        ← PK_PKi (P := P) K ((symmProd Q K rest : GL (Fin 3) K).val *ᵥ (PK P K *ᵥ y)), hβ, Quat.conjLin_mul,
        Module.End.mul_apply]
      exact transport_pair hd hsim hx hw _
    · rw [Units.val_mul, Quat.nrd_mul, hnβ, Units.val_mul, Quat.nrd_mul, nrd_pureUnit', nrd_pureUnit',
        Q3_PKi hsim, Q3_PKi hsim]
      simp only [valProd, List.map_cons, List.prod_cons, List.length_cons]
      ring

/-- The scalar unit $c \in K^\times \subseteq D_K^\times$. -/
abbrev scalarUnit {A B : K} (c : K) (hc : c ≠ 0) : (ℍ[K,A,B])ˣ :=
  Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom (Units.mk0 c hc)

theorem conjLin_scalarUnit {A B : K} (c : K) (hc : c ≠ 0) :
    Quat.conjLin (scalarUnit (A := A) (B := B) c hc) = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  rw [Quat.conjLin_apply, LinearMap.id_apply]
  have h1 : ((scalarUnit (A := A) (B := B) c hc : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = (c : ℍ[K,A,B]) := rfl
  have h2 : (((scalarUnit (A := A) (B := B) c hc)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = ((c⁻¹ : K) : ℍ[K,A,B]) := by
    rw [← map_inv]; rfl
  rw [h1, h2, ← QuaternionAlgebra.coe_commutes, ← mul_assoc, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hc,
    QuaternionAlgebra.coe_one, one_mul, Quat.imv_pure]

theorem nrd_scalarUnit {A B : K} (c : K) (hc : c ≠ 0) :
    Quat.nrd ((scalarUnit (A := A) (B := B) c hc : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = c ^ 2 :=
  Quat.nrd_coe c

/-- **Rotations in $O'(V_K)$ are conjugations by norm-one quaternions** (O'Meara 57:13, as used in 104:4 step 2):
for $\varphi \in O'(V_K)$ there is $\alpha \in D_K^\times$ with $\operatorname{nrd}\alpha = 1$ and $P^{-1}\varphi P = (y \mapsto
\alpha y\alpha^{-1})$. -/
theorem exists_conj_of_mem_spinorKernel (hd : d ≠ 0) (hsim : SimAt Q a b d P K) {φ : orthGroup Q K}
    (hφ : φ ∈ spinorKernel Q K) :
    ∃ α : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ, Quat.nrd (α : ℍ[K, algebraMap F K a, algebraMap F K b]) = 1 ∧
      ∀ y, PKi P K *ᵥ ((φ : GL (Fin 3) K).val *ᵥ (PK P K *ᵥ y)) = Quat.conjLin α y := by
  obtain ⟨xs, ⟨hxa, ⟨r, hr⟩, ⟨s, hs⟩⟩, rfl⟩ := hφ
  obtain ⟨β, hβ, hnβ⟩ := transport_symmProd hd hsim xs hxa ⟨r, hr⟩
  set t := algebraMap F K d ^ r * s
  have hnβ' : Quat.nrd (β : ℍ[K, algebraMap F K a, algebraMap F K b]) = t ^ 2 := by
    rw [hnβ, hr, hs, pow_add]; ring
  have ht : t ≠ 0 := by
    intro h0; have := Quat.nrd_units_ne_zero β; rw [hnβ', h0] at this; simp at this
  refine ⟨scalarUnit t⁻¹ (inv_ne_zero ht) * β, ?_, fun y => ?_⟩
  · rw [Units.val_mul, Quat.nrd_mul, nrd_scalarUnit, hnβ']; field_simp
  · rw [hβ, Quat.conjLin_mul, conjLin_scalarUnit, Module.End.mul_apply, LinearMap.id_apply]

/-- **Conjugations by norm-one quaternions lie in $O'(V)$:** if $\sigma \in O(V)(K)$ has $\det\sigma = 1$ and
$P^{-1}\sigma P$ is conjugation by $\alpha$ with $\operatorname{nrd}\alpha = 1$, then $\sigma \in O'(V)(K)$. (Write $\sigma =
\tau_{x_1}\cdots\tau_{x_{2r}}$ by Cartan–Dieudonné; then $P^{-1}\sigma P$ is conjugation by $\beta$ with
$\operatorname{nrd}\beta = d^{2r}\prod Q(x_i)$; the kernel of conjugation is $K^\times$, so $\beta = c\,\alpha$ and
$\prod Q(x_i) = (c/d^r)^2$.) -/
theorem mem_spinorKernel_of_conj (hd : d ≠ 0) (ha : a ≠ 0) (hQ : Q.Nondegenerate) (hsim : SimAt Q a b d P K)
    {σ : orthGroup Q K} (hdet : ((σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    {α : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ} (hα : Quat.nrd (α : ℍ[K, algebraMap F K a, algebraMap F K b]) = 1)
    (hσ : ∀ y, PKi P K *ᵥ ((σ : GL (Fin 3) K).val *ᵥ (PK P K *ᵥ y)) = Quat.conjLin α y) :
    σ ∈ spinorKernel Q K := by
  obtain ⟨xs, hxa, rfl⟩ := exists_symmProd_eq Q K hQ σ
  have hlen : Even xs.length := by
    have h := detHom_symmProd Q K xs hxa
    rw [detHom_val, hdet] at h
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at h
    have : (2 : K) = 0 := by linear_combination h
    exact two_ne_zero this
  obtain ⟨β, hβ, hnβ⟩ := transport_symmProd hd hsim xs hxa hlen
  have hconj : Quat.conjLin β = Quat.conjLin α := LinearMap.ext fun y => by rw [← hβ, hσ]
  have hker : β * α⁻¹ ∈ (Quat.conjSO : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ →* _).ker := by
    rw [MonoidHom.mem_ker]
    ext : 2
    rw [Quat.coe_conjSO, Quat.conjLin_mul, hconj, ← Quat.conjLin_mul, mul_inv_cancel, Quat.conjLin_one,
      LinearMap.toMatrix'_id]
    rfl
  rw [Quat.ker_conjSO two_ne_zero ((map_ne_zero _).mpr ha), Quat.mem_centerUnits] at hker
  obtain ⟨c, hc⟩ := hker
  have hβc : (β : ℍ[K, algebraMap F K a, algebraMap F K b]) = (c : ℍ[K, algebraMap F K a, algebraMap F K b]) * α := by
    rw [← hc, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hn : algebraMap F K d ^ xs.length * valProd Q K xs = c ^ 2 := by
    rw [← hnβ, hβc, Quat.nrd_mul, Quat.nrd_coe, hα, mul_one]
  obtain ⟨r, hr⟩ := hlen
  have hd' : algebraMap F K d ≠ 0 := (map_ne_zero _).mpr hd
  refine ⟨xs, ⟨hxa, ⟨r, hr⟩, ⟨c / algebraMap F K d ^ r, ?_⟩⟩, rfl⟩
  rw [hr, pow_add] at hn
  field_simp
  linear_combination hn

end Transport

/-! ### The conjugation matrix in coordinates -/

section Matrix

variable {K : Type*} [Field K]

/-- The quaternion $x_0 + x_1 i + x_2 j + x_3 k$ with coordinate vector $x \in K^4$. -/
def qv {A B : K} (x : Fin 4 → K) : ℍ[K,A,B] := ⟨x 0, x 1, x 2, x 3⟩

/-- The coordinate vector of a quaternion. -/
def qc {A B : K} (q : ℍ[K,A,B]) : Fin 4 → K := ![q.re, q.imI, q.imJ, q.imK]

@[simp] theorem qv_qc {A B : K} (q : ℍ[K,A,B]) : qv (qc q) = q := by
  ext <;> simp [qv, qc]

theorem nMat_mulVec {A B : K} (q : ℍ[K,A,B]) (y : Fin 3 → K) :
    Quat.nMat q *ᵥ y = Quat.imv (q * Quat.pure y * star q) := by
  funext i
  fin_cases i <;>
  simp [Quat.nMat, mulVec, dotProduct, Quat.imv, Quat.pure, Fin.sum_univ_three, Pi.single_apply] <;> ring

theorem nMat_map {F' : Type*} [Field F'] [Algebra F' K] {a b : F'} (x : Fin 4 → F') :
    (Quat.nMat (qv x : ℍ[F',a,b])).map (algebraMap F' K) =
      Quat.nMat (qv (fun i => algebraMap F' K (x i)) : ℍ[K, algebraMap F' K a, algebraMap F' K b]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Quat.nMat, Quat.imv, Quat.pure, qv, Pi.single_apply]

theorem continuous_nMat [TopologicalSpace K] [IsTopologicalRing K] {A B : K} :
    Continuous fun x : Fin 4 → K => Quat.nMat (qv x : ℍ[K,A,B]) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
  simp [Quat.nMat, Quat.imv, Quat.pure, qv, Pi.single_apply] <;> fun_prop

/-- For $\operatorname{nrd}\alpha = 1$ the matrix of $y \mapsto \alpha y\bar\alpha$ is the matrix of conjugation. -/
theorem toMatrix'_conjLin_of_nrd {A B : K} (α : (ℍ[K,A,B])ˣ) (hα : Quat.nrd (α : ℍ[K,A,B]) = 1) :
    LinearMap.toMatrix' (Quat.conjLin α) = Quat.nMat (α : ℍ[K,A,B]) := by
  rw [Quat.toMatrix'_conjLin, hα, inv_one, one_smul]

/-- Quaternions with coordinates in a subring $S \ni A, B$ form a ring. -/
def QInt (S : Subring K) {A B : K} (p : ℍ[K,A,B]) : Prop := p.re ∈ S ∧ p.imI ∈ S ∧ p.imJ ∈ S ∧ p.imK ∈ S

theorem QInt.mul {S : Subring K} {A B : K} (hA : A ∈ S) (hB : B ∈ S) {p q : ℍ[K,A,B]} (hp : QInt S p)
    (hq : QInt S q) : QInt S (p * q) := by
  obtain ⟨p0, p1, p2, p3⟩ := hp
  obtain ⟨q0, q1, q2, q3⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul] <;>
  apply_rules [S.add_mem, S.mul_mem, S.sub_mem, S.neg_mem, S.zero_mem, S.one_mem]

theorem QInt.star {S : Subring K} {A B : K} {p : ℍ[K,A,B]} (hp : QInt S p) : QInt S (star p) := by
  obtain ⟨p0, p1, p2, p3⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star] <;>
  apply_rules [S.add_mem, S.mul_mem, S.sub_mem, S.neg_mem, S.zero_mem, S.one_mem]

theorem QInt.pure {S : Subring K} {A B : K} {y : Fin 3 → K} (hy : ∀ i, y i ∈ S) :
    QInt S (Quat.pure y : ℍ[K,A,B]) :=
  ⟨S.zero_mem, hy 0, hy 1, hy 2⟩

/-- **Integral conjugation:** if $\alpha$ and $y$ have coordinates in $S \ni A, B$, so does $\alpha y\bar\alpha$. -/
theorem nMat_mulVec_mem {S : Subring K} {A B : K} (hA : A ∈ S) (hB : B ∈ S) {q : ℍ[K,A,B]} (hq : QInt S q)
    {y : Fin 3 → K} (hy : ∀ i, y i ∈ S) (i : Fin 3) : (Quat.nMat q *ᵥ y) i ∈ S := by
  rw [nMat_mulVec]
  have h := (hq.mul hA hB (QInt.pure hy)).mul hA hB hq.star
  fin_cases i
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

end Matrix

section MatrixUnit

variable {K : Type*} [Field K]

theorem nMat_one {A B : K} : Quat.nMat (1 : ℍ[K,A,B]) = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply, nMat_mulVec, one_mul, star_one, mul_one, Quat.imv_pure, one_mulVec]

theorem nMat_mul_nMat_star {A B : K} {q : ℍ[K,A,B]} (hq : Quat.nrd q = 1) :
    Quat.nMat q * Quat.nMat (star q) = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply, ← mulVec_mulVec, one_mulVec, nMat_mulVec, star_star]
  rw [Quat.pure_imv (by simpa [star_star] using Quat.re_mul_pure_mul_star (star q) y)]
  have h1 : q * (star q * Quat.pure y * q) * star q = (q * star q) * Quat.pure y * (q * star q) := by
    simp only [mul_assoc]
  rw [h1, Quat.mul_star_eq_nrd, hq, QuaternionAlgebra.coe_one, one_mul, mul_one, Quat.imv_pure]

end MatrixUnit

/-! ### Strong approximation for ternary rotations from vectors in $D$ -/

section Ternary

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem mem_O_iff (x : Fv) : x ∈ (𝔬).toSubring ↔ Valued.v x ≤ 1 :=
  HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem mulVec_nMat_mem_std {A B : Fv} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) {q : ℍ[Fv,A,B]}
    (hq : QInt (𝔬).toSubring q) {y : Fin 3 → Fv} (hy : y ∈ std v) : Quat.nMat q *ᵥ y ∈ std v := by
  intro i
  rw [neg_zero, exp_zero, ← mem_O_iff]
  refine nMat_mulVec_mem ((mem_O_iff v A).mpr hA) ((mem_O_iff v B).mpr hB) hq (fun j => ?_) i
  rw [mem_O_iff]; have := hy j; rwa [neg_zero, exp_zero] at this

/-- **Integral conjugations stabilize $\mathfrak o_\mathfrak p^3$:** if $\sigma = P\,c_q\,P^{-1}$ with $q \in \mathfrak o_\mathfrak p\langle 1, i,
j, k\rangle$ of norm $1$ and $P, P^{-1}, a, b$ integral at $\mathfrak p$, then $\sigma \in O(\mathfrak o_\mathfrak p^3)$. -/
theorem mem_stdStab_of_conj {Q : QuadForm F 3} {a b : F} {P : GL (Fin 3) F} (hP : GLInt P v)
    (ha : Valued.v (algebraMap F Fv a) ≤ 1) (hb : Valued.v (algebraMap F Fv b) ≤ 1)
    {q : ℍ[Fv, algebraMap F Fv a, algebraMap F Fv b]} (hq : QInt (𝔬).toSubring q) (hn : Quat.nrd q = 1)
    {σ : orthGroup Q Fv} (hσ : omat σ = PK P Fv * Quat.nMat q * PKi P Fv) : σ ∈ stdStab Q v := by
  have hint : ∀ {q' : ℍ[Fv, algebraMap F Fv a, algebraMap F Fv b]}, QInt (𝔬).toSubring q' →
      ∀ z ∈ std v, (PK P Fv * Quat.nMat q' * PKi P Fv) *ᵥ z ∈ std v := by
    intro q' hq' z hz
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    exact mulVec_mem_std v hP.1 (mulVec_nMat_mem_std v ha hb hq' (mulVec_mem_std v hP.2 hz))
  change locAct v (σ : GL (Fin 3) Fv) (std v) = std v
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change omat σ *ᵥ z ∈ std v
    rw [hσ]; exact hint hq z hz
  · intro z hz
    refine ⟨(PK P Fv * Quat.nMat (star q) * PKi P Fv) *ᵥ z, hint hq.star z hz, ?_⟩
    change omat σ *ᵥ ((PK P Fv * Quat.nMat (star q) * PKi P Fv) *ᵥ z) = z
    rw [hσ, mulVec_mulVec]
    have : PK P Fv * Quat.nMat q * PKi P Fv * (PK P Fv * Quat.nMat (star q) * PKi P Fv) = 1 := by
      calc PK P Fv * Quat.nMat q * PKi P Fv * (PK P Fv * Quat.nMat (star q) * PKi P Fv)
          = PK P Fv * Quat.nMat q * (PKi P Fv * PK P Fv) * Quat.nMat (star q) * PKi P Fv := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [PKi_mul_PK, Matrix.mul_one, Matrix.mul_assoc (PK P Fv), nMat_mul_nMat_star hn,
            Matrix.mul_one, PK_mul_PKi]
    rw [this, one_mulVec]

theorem continuous_conjMat (a b : F) (P : GL (Fin 3) F) :
    Continuous fun x : Fin 4 → v.adicCompletion F => PK P (v.adicCompletion F) *
      Quat.nMat (qv x : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]) * PKi P (v.adicCompletion F) := by
  have h0 := continuous_nMat (K := v.adicCompletion F) (A := algebraMap F (v.adicCompletion F) a)
    (B := algebraMap F (v.adicCompletion F) b)
  have h1 := (continuous_matmul_joint v).comp ((continuous_const (y := PK P (v.adicCompletion F))).prodMk h0)
  have h2 := (continuous_matmul_joint v).comp (h1.prodMk (continuous_const (y := PKi P (v.adicCompletion F))))
  exact h2

/-- **Step 2 of O'Meara 104:4** (pp. 317–319): strong approximation for the rotations of a ternary space $V$, $d\,Q(Py)
= \operatorname{nrd}(y_0i + y_1j + y_2k)$, follows from strong approximation for vectors of norm $1$ in the quaternary
space $(D, \operatorname{nrd})$: approximate the local norm-one quaternions $\alpha_\mathfrak p$ with
$P^{-1}\varphi_\mathfrak pP = (y \mapsto \alpha_\mathfrak p y \alpha_\mathfrak p^{-1})$ by $\alpha \in D$ of norm $1$, integral off $T$, and take
$\sigma = P\,(y \mapsto \alpha y\bar\alpha)\,P^{-1}$. -/
theorem rotApprox_ternary {Q : QuadForm F 3} (hQ : Q.Nondegenerate) {a b d : F} (ha : a ≠ 0) (hd : d ≠ 0)
    {P : GL (Fin 3) F} (hsim : ∀ (K : Type) [Field K] [Algebra F K] [CharZero K], SimAt Q a b d P K)
    (hV : VecApprox (Quat.nrdForm a b)) : RotApprox Q := by
  classical
  intro T φ hφ U hU
  choose! α hαn hαφ using fun v (hv : v ∈ T) =>
    exists_conj_of_mem_spinorKernel hd (hsim (v.adicCompletion F)) (hφ v hv)
  set Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 4 → v.adicCompletion F) → Matrix (Fin 3) (Fin 3) (v.adicCompletion F) :=
    fun v x => PK P (v.adicCompletion F) *
      Quat.nMat (qv x : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]) * PKi P (v.adicCompletion F)
    with hΨ
  have hΨc : ∀ v : HeightOneSpectrum (𝓞 F), Continuous (Ψ v) := fun v => continuous_conjMat v a b P
  have hmatφ : ∀ v ∈ T, omat (φ v) = Ψ v (qc (α v : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b])) := by
    intro v hv
    simp only [hΨ, qv_qc]
    refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
    simp only [Matrix.toLin'_apply]
    have h := hαφ v hv (PKi P (v.adicCompletion F) *ᵥ z)
    rw [PK_PKi, ← LinearMap.toMatrix'_mulVec, toMatrix'_conjLin_of_nrd _ (hαn v hv)] at h
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← h, PK_PKi]
  -- good primes
  have hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, GLInt P v ∧
      Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1 := by
    filter_upwards [eventually_glInt P, eventually_valuation_le_one a, eventually_valuation_le_one b]
      with v h1 h2 h3
    exact ⟨h1, by rw [valued_algebraMap]; exact h2, by rw [valued_algebraMap]; exact h3⟩
  set B := (Filter.eventually_cofinite.mp hgood).toFinset
  have hB : ∀ v, v ∉ B → GLInt P v ∧ Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1 := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr hc)
  choose N hN hNσ using fun v : HeightOneSpectrum (𝓞 F) => exists_mem_nhds_stdStab v Q
  set e0 : Fin 4 → F := Pi.single 0 1 with he0
  have hqe0 : ∀ v : HeightOneSpectrum (𝓞 F),
      (qv (locVec v e0) : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]) = 1 := by
    intro v; ext <;> simp [qv, he0, locVec_apply]
  have hΨe0 : ∀ v : HeightOneSpectrum (𝓞 F), Ψ v (locVec v e0) = 1 := by
    intro v; simp only [hΨ, hqe0, nMat_one, Matrix.mul_one, PK_mul_PKi]
  have hnrde0 : (Quat.nrdForm a b).evalIn F e0 = 1 := by
    rw [Quat.evalIn_nrdForm]; simp [he0, Quat.nrd_mk]
  obtain ⟨y, hyn, hyZ, hystd⟩ := hV e0 (by rw [hnrde0]; exact one_ne_zero) (T ∪ B)
    (fun v _ => by
      intro i; rw [neg_zero, exp_zero, locVec_apply, he0]
      by_cases h : i = 0 <;> simp [h])
    (fun v => if v ∈ T then qc (α v : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]) else locVec v e0)
    (by
      intro v _
      split_ifs with h
      · rw [Quat.evalIn_nrdForm, hnrde0, map_one]
        change Quat.nrd (qv (qc (α v : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b]))) = 1
        rw [qv_qc]
        try exact hαn v h
      · rw [evalIn_locVec])
    (fun v => if v ∈ T then Ψ v ⁻¹' U v else Ψ v ⁻¹' N v)
    (by
      intro v _
      split_ifs with h
      · exact (hΨc v).continuousAt.preimage_mem_nhds (by rw [← hmatφ v h]; exact hU v h)
      · exact (hΨc v).continuousAt.preimage_mem_nhds (by rw [hΨe0]; exact hN v))
  -- the global norm-one quaternion and rotation
  have hnrd1 : Quat.nrd (qv y : ℍ[F, algebraMap F F a, algebraMap F F b]) = 1 := by
    have h := Quat.evalIn_nrdForm (K := F) a b y
    rw [hyn, hnrde0] at h
    exact h.symm
  set qg : ℍ[F, algebraMap F F a, algebraMap F F b] := qv y
  set αg : (ℍ[F, algebraMap F F a, algebraMap F F b])ˣ :=
    ((Quat.isUnit_iff_nrd_ne_zero qg).mpr (by rw [hnrd1]; exact one_ne_zero)).unit
  have hαg : ((αg : (ℍ[F, algebraMap F F a, algebraMap F F b])ˣ) : ℍ[F, algebraMap F F a, algebraMap F F b]) = qg :=
    rfl
  set Mg := PK P F * Quat.nMat qg * PKi P F
  have hMg_conj : ∀ z, PKi P F *ᵥ (Mg *ᵥ (PK P F *ᵥ z)) = Quat.conjLin αg z := by
    intro z
    rw [← LinearMap.toMatrix'_mulVec, toMatrix'_conjLin_of_nrd _ (by rw [hαg]; exact hnrd1), hαg]
    simp only [Mg, ← mulVec_mulVec, PKi_PK]
  have hdetMg : Mg.det = 1 := by
    simp only [Mg, Matrix.det_mul, Quat.det_nMat, hnrd1, one_pow, mul_one]
    rw [← Matrix.det_mul, PK_mul_PKi, Matrix.det_one]
  have hNconj : ∀ w, Quat.nMat qg *ᵥ w = Quat.conjLin αg w := by
    intro w
    rw [← LinearMap.toMatrix'_mulVec, toMatrix'_conjLin_of_nrd _ (by rw [hαg]; exact hnrd1), hαg]
  have hMg_val : ∀ x, Q.evalIn F (Mg *ᵥ x) = Q.evalIn F x := by
    intro x
    have hd' : algebraMap F F d ≠ 0 := hd
    apply mul_left_cancel₀ hd'
    calc algebraMap F F d * Q.evalIn F (Mg *ᵥ x)
        = algebraMap F F d * Q.evalIn F (PK P F *ᵥ (Quat.nMat qg *ᵥ (PKi P F *ᵥ x))) := by
          simp only [Mg, mulVec_mulVec, Matrix.mul_assoc]
      _ = Quat.Q3 (algebraMap F F a) (algebraMap F F b) (Quat.nMat qg *ᵥ (PKi P F *ᵥ x)) := (hsim F _).symm
      _ = Quat.Q3 (algebraMap F F a) (algebraMap F F b) (Quat.conjLin αg (PKi P F *ᵥ x)) := by rw [hNconj]
      _ = Quat.Q3 (algebraMap F F a) (algebraMap F F b) (PKi P F *ᵥ x) := Quat.Q3_conjLin _ _
      _ = algebraMap F F d * Q.evalIn F x := Q3_PKi (hsim F) x
  set g : GL (Fin 3) F := Matrix.nonsingInvUnit Mg (by rw [hdetMg]; exact isUnit_one)
  have hgval : (g : Matrix (Fin 3) (Fin 3) F) = Mg := rfl
  have hgO : g ∈ orthGroup Q F := by
    have hSO : g ∈ Quat.SO Q := ⟨by rw [hgval]; exact hdetMg, fun x => by rw [hgval]; exact hMg_val x⟩
    have h := ((Quat.mem_SO_iff_hessian two_ne_zero).mp hSO).2
    rw [mem_orthGroup]
    have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext i j; simp
    rw [e]; exact h
  set σ : orthGroup Q F := ⟨g, hgO⟩
  have hσO' : σ ∈ spinorKernel Q F :=
    mem_spinorKernel_of_conj hd ha hQ (hsim F) (σ := σ) hdetMg (by rw [hαg]; exact hnrd1) hMg_conj
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), omat (orthMap Q (v.adicCompletion F) σ) = Ψ v (locVec v y) := by
    intro v
    rw [omat, orthMap_val]
    change (PK P F * Quat.nMat qg * PKi P F).map (algebraMap F (v.adicCompletion F)) = _
    rw [Matrix.map_mul, Matrix.map_mul, nMat_map]
    have e1 : (PK P F).map (algebraMap F (v.adicCompletion F)) = PK P (v.adicCompletion F) := by
      ext i j; simp
    have e2 : (PKi P F).map (algebraMap F (v.adicCompletion F)) = PKi P (v.adicCompletion F) := by
      ext i j; simp
    rw [e1, e2]
    rfl
  refine ⟨σ, hσO', fun v hv => ?_, fun v hv => ?_⟩
  · have h := hyZ v (Finset.mem_union_left _ hv)
    simp only [hv, ite_true, Set.mem_preimage] at h
    rw [hloc]; exact h
  · by_cases hvB : v ∈ B
    · have h := hyZ v (Finset.mem_union_right _ hvB)
      simp only [hv, ite_false, Set.mem_preimage] at h
      exact hNσ v _ (by change omat _ ∈ N v; rw [hloc]; exact h)
    · obtain ⟨hP, ha', hb'⟩ := hB v hvB
      have hyv : locVec v y ∈ std v := hystd v (by simp [hv, hvB])
      refine mem_stdStab_of_conj v hP ha' hb' (q := qv (locVec v y)) ?_ ?_ (hloc v)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [qv] <;> rw [mem_O_iff] <;>
          [have := hyv 0; have := hyv 1; have := hyv 2; have := hyv 3] <;> rwa [neg_zero, exp_zero] at this
      · have h := Quat.evalIn_nrdForm (K := v.adicCompletion F) a b (locVec v y)
        rw [evalIn_locVec] at h
        have h1 : (Quat.nrdForm a b).eval y = 1 := by rw [QuadForm.eval, hyn, hnrde0]
        rw [h1, map_one] at h
        exact h.symm

end Ternary

/-! ### The similarity with $(D^0, \operatorname{nrd})$ and the ternary case -/

section Similarity

theorem evalIn_pureForm_Q3 (K : Type*) [Field K] [Algebra F K] (a b : F) (y : Fin 3 → K) :
    (Quat.pureForm a b).evalIn K y = Quat.Q3 (algebraMap F K a) (algebraMap F K b) y := by
  rw [Quat.pureForm, QuadForm.evalIn_diag, Fin.sum_univ_three]
  simp [Quat.Q3, map_mul, map_neg]
  ring

/-- **Every nondegenerate ternary form is similar to $(D^0, \operatorname{nrd})$, over every field $K \supseteq F$**:
$\langle -a,-b,ab\rangle(y) = d\,Q(Py)$ for some $a, b, d \in F^\times$ and $P \in \mathrm{GL}_3(F)$
(`Quat.exists_isometric_smul_pureForm`, transported from $F$ to $K$ as an identity of forms). -/
theorem exists_simAt (Q : QuadForm F 3) (hQ : Q.Nondegenerate) :
    ∃ (a b d : F) (P : GL (Fin 3) F), a ≠ 0 ∧ b ≠ 0 ∧ d ≠ 0 ∧
      ∀ (K : Type) [Field K] [Algebra F K] [CharZero K], SimAt Q a b d P K := by
  obtain ⟨a, b, d, ha, hb, hd, P, hPdet, hP⟩ := Quat.exists_isometric_smul_pureForm Q hQ
  set Pg : GL (Fin 3) F := Matrix.nonsingInvUnit P hPdet
  have hform : pullbackForm (d • Q) P = Quat.pureForm a b := by
    apply QuadForm.ext_eval
    intro y
    change (pullbackForm (d • Q) P).evalIn F y = (Quat.pureForm a b).evalIn F y
    rw [evalIn_pullback, matrix_map_algebraMap_self]
    exact hP y
  refine ⟨a, b, d, Pg, ha, hb, hd, fun K _ _ _ y => ?_⟩
  rw [← evalIn_pureForm_Q3, ← hform, evalIn_pullback, evalIn_smulForm]
  rfl

/-- Isotropy passes from $Q$ to the quaternary norm form $\langle 1 \rangle \perp \langle -a,-b,ab\rangle$. -/
theorem isotropicIn_nrdForm {Q : QuadForm F 3} {a b d : F} {P : GL (Fin 3) F} (K : Type) [Field K] [Algebra F K]
    [CharZero K] (hsim : SimAt Q a b d P K) (hiso : Q.IsotropicIn K) : (Quat.nrdForm a b).IsotropicIn K := by
  obtain ⟨x, hx0, hx⟩ := hiso
  set y := PKi P K *ᵥ x
  have hy0 : y ≠ 0 := by
    intro h; apply hx0
    rw [← PK_PKi (P := P) K x]; change PK P K *ᵥ y = 0; rw [h, mulVec_zero]
  refine ⟨Fin.cons 0 y, fun h => hy0 (funext fun i => by simpa using congrFun h i.succ), ?_⟩
  rw [Quat.evalIn_nrdForm_eq]
  have h3 : (Quat.pureForm a b).evalIn K ![(Fin.cons 0 y : Fin 4 → K) 1, (Fin.cons 0 y : Fin 4 → K) 2,
      (Fin.cons 0 y : Fin 4 → K) 3] = 0 := by
    have e : (![(Fin.cons 0 y : Fin 4 → K) 1, (Fin.cons 0 y : Fin 4 → K) 2, (Fin.cons 0 y : Fin 4 → K) 3] :
        Fin 3 → K) = y := by
      funext i; fin_cases i <;> rfl
    rw [e, evalIn_pureForm_Q3, hsim, PK_PKi, hx, mul_zero]
  rw [h3]; simp

/-- **Strong approximation for ternary rotations from quaternary vectors** (O'Meara 104:4 step 2): if
`VecApprox` holds for the norm form of the quaternion algebra attached to $Q$, then `RotApprox Q`. -/
theorem rotApprox_ternary_of {Q : QuadForm F 3} (hQ : Q.Nondegenerate)
    (hV : ∀ a b : F, a ≠ 0 → b ≠ 0 → (∀ (K : Type) [Field K] [Algebra F K] [CharZero K],
      Q.IsotropicIn K → (Quat.nrdForm a b).IsotropicIn K) → VecApprox (Quat.nrdForm a b)) :
    RotApprox Q := by
  obtain ⟨a, b, d, P, ha, hb, hd, hsim⟩ := exists_simAt Q hQ
  exact rotApprox_ternary hQ ha hd hsim (hV a b ha hb fun K _ _ _ h => isotropicIn_nrdForm K (hsim K) h)

/-- **Strong approximation for rotations of an isotropic ternary space** (O'Meara 104:4 step 2 with 104:3 in the
isotropic case): unconditional. -/
theorem rotApprox_ternary_isotropic {Q : QuadForm F 3} (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn F) :
    RotApprox Q :=
  rotApprox_ternary_of hQ fun _ _ ha hb hI =>
    vecApprox_of_isotropic _ le_rfl (Quat.nrdForm_nondegenerate two_ne_zero ha hb) (hI F hiso)

end Similarity

end QuadFormsKB.Lattices
