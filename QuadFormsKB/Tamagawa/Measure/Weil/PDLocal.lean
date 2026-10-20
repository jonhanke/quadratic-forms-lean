/-
# $D^\times/K^\times \cong SO(D^0)$ locally: the hessian form of $SO$, continuity, and integral lifts

**Layer:** a field $K$ (any $F$-algebra field, $F$ a number field, so $2 \ne 0$), $D = (A,B)_K$; then the completions
$F_v$ of a number field. This is the local half of `Quat.conjSO`
($\alpha\mapsto(y\mapsto\alpha y\alpha^{-1})$ on $D^0$) in the form needed by the adelic groups.

**Defines/proves**
* `conjGL_val`: the matrix of conjugation is $\operatorname{nrd}(\alpha^{-1})\cdot N(\alpha)$, $N$ = `nMat`
  ($y\mapsto\alpha y\bar\alpha$), so its entries are polynomials in the coordinates of $\alpha$ and $\alpha^{-1}$;
  `continuous_conjGL_comp`: continuity for any topological field;
* `nMat_mul` ($N(xy) = N(x)N(y)$) and **`trace_nMat_add_nrd`**: $\operatorname{tr}N(x) + \operatorname{nrd}(x) =
  4\operatorname{re}(x)^2$ (the trace of $z\mapsto xz\bar x$ on $D$ is $\operatorname{trd}(x)^2$);
* `conjOrth` ($K$ an $F$-algebra, $D = (\iota A,\iota B)_K$): $D^\times \to SO(\langle -A,-B,AB\rangle)(K)$ as an element
  of `Lattices.orthGroup` with determinant 1 (the library's hessian form of $SO$, via `mem_SO_iff_hessian`);
* at a finite place $v$ with $|2|_v = |A|_v = |B|_v = 1$: **`exists_smul_mem_lamLocUnits`**: if the conjugation
  matrix of $\alpha \in D_v^\times$ is integral, some $c\alpha$ ($c\in F_v^\times$) lies in $\Lambda_v^\times$
  ($\Lambda_v = \mathfrak o_v\langle1,i,j,k\rangle$). *Proof:* scale $\alpha$ to be primitive; if
  $\operatorname{nrd}\alpha\in\mathfrak p_v$ then $N(\alpha) = \operatorname{nrd}(\alpha)\,c(\alpha) \equiv 0$, so by the trace
  identity $4\operatorname{re}(\alpha w)^2 \in \mathfrak p_v$ for $w = 1,i,j,k$, i.e. $\alpha_0, A\alpha_1, B\alpha_2,
  AB\alpha_3 \in \mathfrak p_v$, contradicting primitivity. (This replaces the normalizer computation
  $N(M_2(\mathfrak o_v)) = F_v^\times GL_2(\mathfrak o_v)$ of `TernaryLocalStab` and needs no PID, no frame.)
* `conj_mem_stdStab_of_mem_lamLocUnits`: conversely, conjugation by $u\in\Lambda_v^\times$ stabilizes $\mathfrak o_v^3$.

Source: Weil 1982, §3.7(a), p. 63 (the isomorphism $SO_3 \cong D^\times/G_m$); Voight 2021, §4.5 and §22.1
[unverified].
-/
import QuadFormsKB.Lattices.SATernary
import QuadFormsKB.Tamagawa.Measure.Weil.QuatFinite
import QuadFormsKB.Tamagawa.LocalVolume

open Matrix Quaternion NumberField IsDedekindDomain WithZero Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices

/-! ### Generic facts over a field -/

section Generic

variable {K : Type*} [Field K] {A B : K}

/-- $N(xy) = N(x)\,N(y)$ for $N(x)$ = the matrix of $y \mapsto x y \bar x$ on $D^0$. -/
theorem nMat_mul (x y : ℍ[K,A,B]) : nMat (x * y) = nMat x * nMat y := by
  refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
  simp only [Matrix.toLin'_apply, ← mulVec_mulVec, nMat_mulVec]
  rw [pure_imv (re_mul_pure_mul_star y z), star_mul]
  simp only [mul_assoc]

/-- **The trace identity** $\operatorname{tr}N(x) + \operatorname{nrd}(x) = 4\operatorname{re}(x)^2$: the trace of
$z\mapsto xz\bar x$ on $D = K\cdot1\oplus D^0$ is $\operatorname{trd}(x)\operatorname{trd}(\bar x)$. -/
theorem trace_nMat_add_nrd (x : ℍ[K,A,B]) : (nMat x).trace + nrd x = 4 * x.re ^ 2 := by
  simp [Matrix.trace, Fin.sum_univ_three, nMat, imv, Quat.pure, nrd, Pi.single_apply]
  ring

/-- The matrix of conjugation: $c(\alpha) = \operatorname{nrd}(\alpha^{-1})\,N(\alpha)$. -/
theorem conjGL_val (α : (ℍ[K,A,B])ˣ) :
    ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      nrd ((α⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) • nMat (α : ℍ[K,A,B]) := by
  change LinearMap.toMatrix' (conjLin α) = _
  rw [toMatrix'_conjLin]
  congr 1
  have h := nrd_mul (α : ℍ[K,A,B]) ((α⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
  rw [Units.mul_inv, nrd_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm).symm

theorem conjGL_inv_val (α : (ℍ[K,A,B])ˣ) :
    (((conjGL α)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((conjGL α⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

/-- $N(\alpha) = \operatorname{nrd}(\alpha)\,c(\alpha)$. -/
theorem nMat_eq_nrd_smul_conjGL (α : (ℍ[K,A,B])ˣ) :
    nMat (α : ℍ[K,A,B]) = nrd (α : ℍ[K,A,B]) • ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [conjGL_val, smul_smul, ← nrd_mul, Units.mul_inv, nrd_one, one_smul]

/-- Central scalars act trivially: $c(r\alpha) = c(\alpha)$. -/
theorem conjGL_smul (α : (ℍ[K,A,B])ˣ) (r : Kˣ) :
    conjGL (Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * α) = conjGL α := by
  ext : 1
  change LinearMap.toMatrix' (conjLin _) = LinearMap.toMatrix' (conjLin _)
  rw [conjLin_mul]
  have : conjLin (Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r) = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    rw [conjLin_apply, LinearMap.id_apply]
    have hc : ∀ z : ℍ[K,A,B], ((Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) * z =
        z * ((Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) :=
      fun z => Algebra.commutes (r : K) z
    rw [hc, mul_assoc, Units.mul_inv, mul_one, imv_pure]
  rw [this, ← Module.End.one_eq_id, one_mul]

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- **Continuity of conjugation** in the coordinates of $\alpha$ and $\alpha^{-1}$. -/
theorem continuous_conjGL_comp {X : Type*} [TopologicalSpace X] (f : X → (ℍ[K,A,B])ˣ)
    (h0 : Continuous fun x => (f x : ℍ[K,A,B]).re) (h1 : Continuous fun x => (f x : ℍ[K,A,B]).imI)
    (h2 : Continuous fun x => (f x : ℍ[K,A,B]).imJ) (h3 : Continuous fun x => (f x : ℍ[K,A,B]).imK)
    (h0' : Continuous fun x => (((f x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).re)
    (h1' : Continuous fun x => (((f x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).imI)
    (h2' : Continuous fun x => (((f x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).imJ)
    (h3' : Continuous fun x => (((f x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).imK) :
    Continuous fun x => (conjGL (f x) : GL (Fin 3) K) := by
  have key : ∀ g : X → (ℍ[K,A,B])ˣ, Continuous (fun x => (g x : ℍ[K,A,B]).re) →
      Continuous (fun x => (g x : ℍ[K,A,B]).imI) → Continuous (fun x => (g x : ℍ[K,A,B]).imJ) →
      Continuous (fun x => (g x : ℍ[K,A,B]).imK) →
      Continuous (fun x => (((g x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).re) →
      Continuous (fun x => (((g x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).imI) →
      Continuous (fun x => (((g x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).imJ) →
      Continuous (fun x => (((g x)⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]).imK) →
      Continuous fun x => ((conjGL (g x) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g g0 g1 g2 g3 g0' g1' g2' g3'
    simp only [conjGL_val]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
    simp [nMat, imv, Quat.pure, nrd, Pi.single_apply] <;> fun_prop
  refine Units.continuous_iff.mpr ⟨key f h0 h1 h2 h3 h0' h1' h2' h3', ?_⟩
  have := key (fun x => (f x)⁻¹) h0' h1' h2' h3' (by simpa using h0) (by simpa using h1) (by simpa using h2)
    (by simpa using h3)
  exact this.congr fun x => (conjGL_inv_val (f x)).symm

end Generic

/-! ### $D^\times \to SO(D^0)$ in the hessian form of `Lattices.orthGroup` -/

section Orth

variable {F : Type} [Field F] [NumberField F] (K : Type*) [Field K] [Algebra F K]

/-- $(\langle -a,-b,ab\rangle$ over $F)\otimes K = \langle -\iota a,-\iota b,\iota a\,\iota b\rangle$. -/
theorem hessian_pureForm_map (a b : F) :
    (pureForm a b).hessian.map (algebraMap F K) = (pureForm (algebraMap F K a) (algebraMap F K b)).hessian := by
  rw [← QuadForm.hessian_map]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pureForm, QuadForm.diag, QuadForm.map]

variable {K}

/-- **$D_K^\times \to SO(Q)(K)$** for a form $Q$ over $F$ equal to $\langle -a,-b,ab\rangle$: conjugation on $D^0$, as an
element of the library's `orthGroup Q K` ($g^{\mathsf T}Hg = H$). -/
@[kb "weil1982" "§3.7(a), p. 63"]
def conjOrth (Q : QuadForm F 3) {a b : F} (hQ : Q = pureForm a b) :
    (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ →* orthGroup Q K where
  toFun α := ⟨conjGL α, by
    subst hQ
    rw [mem_orthGroup, hessian_pureForm_map]
    exact ((mem_SO_iff_hessian (two_ne_zero_of_algebra (F := F) K)).1 (conjGL_mem α)).2⟩
  map_one' := by
    ext : 2
    exact congrArg (fun g : SO (pureForm (algebraMap F K a) (algebraMap F K b)) => ((g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) (map_one conjSO)
  map_mul' α β := by
    ext : 2
    exact congrArg (fun g : SO (pureForm (algebraMap F K a) (algebraMap F K b)) => ((g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) (map_mul conjSO α β)

@[simp] theorem conjOrth_coe (Q : QuadForm F 3) {a b : F} (hQ : Q = pureForm a b)
    (α : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ) :
    ((conjOrth Q hQ α : orthGroup Q K) : GL (Fin 3) K) = conjGL α := rfl

theorem conjOrth_mem_soSub (Q : QuadForm F 3) {a b : F} (hQ : Q = pureForm a b)
    (α : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ) : conjOrth Q hQ α ∈ soSub Q K :=
  det_conjLin α

/-- **Conjugation into $SO(Q)(K)$** (`soSub`). -/
def conjSOK (Q : QuadForm F 3) {a b : F} (hQ : Q = pureForm a b) :
    (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ →* soSub Q K :=
  (conjOrth Q hQ).codRestrict _ (conjOrth_mem_soSub Q hQ)

@[simp] theorem conjSOK_coe (Q : QuadForm F 3) {a b : F} (hQ : Q = pureForm a b)
    (α : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ) :
    (((conjSOK Q hQ α : soSub Q K) : orthGroup Q K) : GL (Fin 3) K) = conjGL α := rfl

/-- **Surjectivity of $D_K^\times \to SO(Q)(K)$** ($a, b \ne 0$; `conjSO_surjective`). -/
theorem conjSOK_surjective (Q : QuadForm F 3) {a b : F} (hQ : Q = pureForm a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Surjective (conjSOK (K := K) Q hQ) := by
  intro g
  have h2 := two_ne_zero_of_algebra (F := F) K
  have ha' : algebraMap F K a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : algebraMap F K b ≠ 0 := (map_ne_zero _).2 hb
  have hg : ((g : orthGroup Q K) : GL (Fin 3) K) ∈ SO (pureForm (algebraMap F K a) (algebraMap F K b)) := by
    rw [mem_SO_iff_hessian h2, ← hessian_pureForm_map, ← hQ]
    exact ⟨mem_soSub.1 g.2, (mem_orthGroup Q).1 (g : orthGroup Q K).2⟩
  obtain ⟨α, hα⟩ := conjSO_surjective h2 ha' hb' ⟨_, hg⟩
  refine ⟨α, ?_⟩
  ext : 3
  exact congrArg (fun g : SO (pureForm (algebraMap F K a) (algebraMap F K b)) => ((g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) hα

/-- **The kernel of $D_K^\times \to SO(Q)(K)$ is $K^\times$** ($a \ne 0$; `ker_conjSO`). -/
theorem conjSOK_eq_one_iff (Q : QuadForm F 3) {a b : F} (hQ : Q = pureForm a b) (ha : a ≠ 0)
    (α : (ℍ[K, algebraMap F K a, algebraMap F K b])ˣ) :
    conjSOK Q hQ α = 1 ↔ α ∈ centerUnits (algebraMap F K a) (algebraMap F K b) := by
  rw [← ker_conjSO (two_ne_zero_of_algebra (F := F) K) ((map_ne_zero _).2 ha), MonoidHom.mem_ker]
  constructor
  · intro h
    ext : 2
    have := congrArg (fun g : soSub Q K => ((g : orthGroup Q K) : GL (Fin 3) K)) h
    exact congrArg Units.val this
  · intro h
    ext : 3
    have := congrArg (fun g : SO (pureForm (algebraMap F K a) (algebraMap F K b)) => ((g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) h
    exact this

end Orth

/-! ### Finite places: integral conjugations -/

section Place

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem conjGL_mulVec {K : Type*} [Field K] {A B : K} (α : (ℍ[K,A,B])ˣ) (y : Fin 3 → K) :
    ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y = conjLin α y :=
  LinearMap.toMatrix'_mulVec _ _

theorem nrdLoc_eq_nrd {K : Type*} [Field K] {A B : K} (x : QuatLoc A B) : nrdLoc A B x = nrd x := by
  rw [nrdLoc, mul_star_eq_nrd]; rfl

theorem qInt_of_mem_lamLoc {a b : F} {x : QuatV a b v} (hx : x ∈ lamLoc a b v) : QInt (𝔬).toSubring x := hx

theorem mem_std_iff' (y : Fin 3 → Fv) : y ∈ std v ↔ ∀ i, y i ∈ (𝔬).toSubring := by
  refine forall_congr' fun i => ?_
  rw [neg_zero, exp_zero, mem_O_iff]

/-- Conjugation by $u \in \Lambda_v^\times$ maps $\mathfrak o_v^3$ into itself ($a, b$ integral at $v$). -/
theorem conjGL_mulVec_mem_std {a b : F} (ha : Valued.v (algebraMap F Fv a) ≤ 1)
    (hb : Valued.v (algebraMap F Fv b) ≤ 1) {u : (QuatV a b v)ˣ} (hu : u ∈ lamLocUnits a b v) {y : Fin 3 → Fv}
    (hy : y ∈ std v) : ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) *ᵥ y ∈ std v := by
  rw [conjGL_mulVec, conjLin_apply, mem_std_iff']
  have hA := (mem_O_iff v _).2 ha
  have hB := (mem_O_iff v _).2 hb
  have h := ((qInt_of_mem_lamLoc v hu.1).mul hA hB (QInt.pure ((mem_std_iff' v y).1 hy))).mul hA hB
    (qInt_of_mem_lamLoc v hu.2)
  intro i
  fin_cases i
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- An isometry $g$ with $g\,\mathfrak o_v^3 \subseteq \mathfrak o_v^3$ and $g^{-1}\mathfrak o_v^3 \subseteq \mathfrak o_v^3$ lies in
$O(\mathfrak o_v^3)$. -/
theorem mem_stdStab_of_mulVec {n : ℕ} {Q : QuadForm F n} (g : orthGroup Q Fv)
    (h1 : ∀ y ∈ std v, omat g *ᵥ y ∈ std v) (h2 : ∀ y ∈ std v, omat g⁻¹ *ᵥ y ∈ std v) : g ∈ stdStab Q v := by
  change locAct v (g : GL (Fin n) Fv) (std v) = std v
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact h1 z hz
  · intro z hz
    refine ⟨omat g⁻¹ *ᵥ z, h2 z hz, ?_⟩
    change omat g *ᵥ (omat g⁻¹ *ᵥ z) = z
    rw [mulVec_mulVec, ← omat_mul, mul_inv_cancel, omat_one, one_mulVec]

/-- **Conjugation by $u \in \Lambda_v^\times$ lies in $O(\mathfrak o_v^3)$.** -/
theorem conjOrth_mem_stdStab {Q : QuadForm F 3} {a b : F} (hQ : Q = pureForm a b)
    (ha : Valued.v (algebraMap F Fv a) ≤ 1) (hb : Valued.v (algebraMap F Fv b) ≤ 1) {u : (QuatV a b v)ˣ}
    (hu : u ∈ lamLocUnits a b v) : conjOrth Q hQ u ∈ stdStab Q v := by
  refine mem_stdStab_of_mulVec v _ (fun y hy => conjGL_mulVec_mem_std v ha hb hu hy) (fun y hy => ?_)
  rw [← map_inv]
  exact conjGL_mulVec_mem_std v ha hb ⟨hu.2, by rw [inv_inv]; exact hu.1⟩ hy

/-- Entries of an element of $O(\mathfrak o_v^3)$ are integral. -/
theorem entry_le_one_of_mem_stdStab {n : ℕ} {Q : QuadForm F n} {g : orthGroup Q Fv} (hg : g ∈ stdStab Q v)
    (i j : Fin n) : Valued.v (omat g i j) ≤ 1 := by
  have hej : (Pi.single j 1 : Fin n → Fv) ∈ std v := by
    intro k
    rw [neg_zero, exp_zero]
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have hmem : omat g *ᵥ Pi.single j 1 ∈ locAct v (g : GL (Fin n) Fv) (std v) := ⟨_, hej, rfl⟩
  rw [show locAct v (g : GL (Fin n) Fv) (std v) = std v from hg] at hmem
  have := hmem i
  rw [neg_zero, exp_zero, mulVec_single_one] at this
  exact this

/-- **Integral lifts at good places.** Let $|2|_v = |a|_v = |b|_v = 1$ ($a, b$ integral everywhere). If the matrix of
conjugation by $\alpha \in D_v^\times$ is integral, then $c\alpha \in \Lambda_v^\times$ for some $c \in F_v^\times$.

*Proof.* Scale $\alpha$ by the inverse of a coordinate of maximal absolute value, so $\beta = c\alpha \in \Lambda_v$ has
a coordinate equal to $1$. If $|\operatorname{nrd}\beta|_v < 1$, then for $w \in \{1,i,j,k\}$:
$4\operatorname{re}(\beta w)^2 = \operatorname{tr}N(\beta w) + \operatorname{nrd}(\beta w) =
\operatorname{nrd}(\beta)\,(\operatorname{tr}(c(\alpha)N(w)) + \operatorname{nrd}w)$ (`trace_nMat_add_nrd`, `nMat_mul`),
so $|\operatorname{re}(\beta w)|_v < 1$, i.e. $|\beta_0|, |a\beta_1|, |b\beta_2|, |ab\beta_3| < 1$: every coordinate of
$\beta$ is in $\mathfrak p_v$, a contradiction. So $\operatorname{nrd}\beta \in \mathfrak o_v^\times$ and
$\beta\in\Lambda_v^\times$ (`mem_lamLocUnits_iff`). -/
theorem exists_smul_mem_lamLocUnits {a b : F}
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (w.adicCompletion F) a) ≤ 1)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (w.adicCompletion F) b) ≤ 1)
    (h2v : Valued.v (2 : Fv) = 1) (hav : Valued.v (algebraMap F Fv a) = 1) (hbv : Valued.v (algebraMap F Fv b) = 1)
    (α : (QuatV a b v)ˣ)
    (hint : ∀ i j, Valued.v (((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) i j) ≤ 1) :
    ∃ r : Fvˣ, Units.map (algebraMap Fv (QuatV a b v)).toMonoidHom r * α ∈ lamLocUnits a b v := by
  set x : QuatV a b v := (↑α : QuatV a b v) with hx
  let c : Fin 4 → Fv := ![x.re, x.imI, x.imJ, x.imK]
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (c i)) Finset.univ_nonempty
  have hci : c i ≠ 0 := by
    intro h0
    have hz : ∀ j, c j = 0 := fun j => by
      have := hi j (Finset.mem_univ _)
      rw [h0, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)
    apply α.ne_zero
    rw [← hx]
    exact QuaternionAlgebra.ext (hz 0) (hz 1) (hz 2) (hz 3)
  set r : Fvˣ := Units.mk0 (c i)⁻¹ (inv_ne_zero hci)
  refine ⟨r, ?_⟩
  set β := Units.map (algebraMap Fv (QuatV a b v)).toMonoidHom r * α with hβdef
  have hβval : (β : QuatV a b v) = (c i)⁻¹ • x := by
    rw [hβdef, Units.val_mul, Algebra.smul_def]; rfl
  have hcoord : ∀ j, Valued.v ((c i)⁻¹ * c j) ≤ 1 := fun j => by
    rw [map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hi j (Finset.mem_univ _)) zero_le
  have hβre : (β : QuatV a b v).re = (c i)⁻¹ * c 0 := by rw [hβval]; rfl
  have hβI : (β : QuatV a b v).imI = (c i)⁻¹ * c 1 := by rw [hβval]; rfl
  have hβJ : (β : QuatV a b v).imJ = (c i)⁻¹ * c 2 := by rw [hβval]; rfl
  have hβK : (β : QuatV a b v).imK = (c i)⁻¹ * c 3 := by rw [hβval]; rfl
  have hO : ∀ y : Fv, Valued.v y ≤ 1 → y ∈ 𝔬 := fun y hy => (mem_O_iff v y).2 hy
  have hβlam : (β : QuatV a b v) ∈ lamLoc a b v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hβre]; exact hO _ (hcoord 0)
    · rw [hβI]; exact hO _ (hcoord 1)
    · rw [hβJ]; exact hO _ (hcoord 2)
    · rw [hβK]; exact hO _ (hcoord 3)
  rw [mem_lamLocUnits_iff ha hb]
  refine ⟨hβlam, ?_⟩
  have hn1 := (mem_O_iff v _).1 (nrdLoc_mem_of_mem_lamLoc ha hb hβlam)
  refine le_antisymm hn1 (not_lt.1 fun hlt => ?_)
  rw [nrdLoc_eq_nrd] at hlt
  have hA : algebraMap F Fv a ∈ (𝔬).toSubring := (mem_O_iff v _).2 (ha v)
  have hB : algebraMap F Fv b ∈ (𝔬).toSubring := (mem_O_iff v _).2 (hb v)
  have hG : conjGL β = conjGL α := conjGL_smul α r
  -- the key estimate
  have key : ∀ w : QuatV a b v, QInt (𝔬).toSubring w → Valued.v (((β : QuatV a b v) * w).re) < 1 := by
    intro w hw
    have e : 4 * ((β : QuatV a b v) * w).re ^ 2 = nrd (β : QuatV a b v) *
        ((((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) * nMat w).trace + nrd w) := by
      rw [← trace_nMat_add_nrd, nMat_mul, nMat_eq_nrd_smul_conjGL β, hG, Matrix.smul_mul, Matrix.trace_smul,
        nrd_mul, smul_eq_mul]
      ring
    have ht : (((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) * nMat w).trace + nrd w ∈ (𝔬).toSubring := by
      refine Subring.add_mem _ ?_ ?_
      · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        refine Subring.sum_mem _ fun k _ => Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ ?_
        · exact (mem_O_iff v _).2 (hint k l)
        · have := nMat_mulVec_mem hA hB hw (y := Pi.single k 1) (fun m => by
            by_cases h : m = k
            · subst h; simp
            · simp [h]) l
          rw [mulVec_single_one] at this
          exact this
      · have h := (hw.mul hA hB hw.star).1
        rwa [mul_star_eq_nrd] at h
    have hv : Valued.v (((β : QuatV a b v) * w).re) ^ 2 < 1 := by
      have h4 : Valued.v (4 : Fv) = 1 := by
        rw [show (4 : Fv) = 2 * 2 by norm_num, map_mul, h2v, one_mul]
      have := congrArg Valued.v e
      rw [map_mul, map_mul, h4, one_mul, map_pow] at this
      rw [this]
      exact mul_lt_one_of_lt_of_le hlt ((mem_O_iff v _).1 ht)
    by_contra hge
    push Not at hge
    exact absurd hv (not_lt.2 (one_le_pow₀ hge))
  -- the four coordinates
  have k0 := key 1 ⟨Subring.one_mem _, Subring.zero_mem _, Subring.zero_mem _, Subring.zero_mem _⟩
  have k1 := key ⟨0, 1, 0, 0⟩ ⟨Subring.zero_mem _, Subring.one_mem _, Subring.zero_mem _, Subring.zero_mem _⟩
  have k2 := key ⟨0, 0, 1, 0⟩ ⟨Subring.zero_mem _, Subring.zero_mem _, Subring.one_mem _, Subring.zero_mem _⟩
  have k3 := key ⟨0, 0, 0, 1⟩ ⟨Subring.zero_mem _, Subring.zero_mem _, Subring.zero_mem _, Subring.one_mem _⟩
  simp only [mul_one, QuaternionAlgebra.re_mul, mul_zero, zero_add, add_zero, map_mul, hav, hbv, one_mul,
    zero_mul, sub_zero] at k0 k1 k2 k3
  have hall : ∀ j, Valued.v ((c i)⁻¹ * c j) < 1 := by
    intro j
    fin_cases j
    · show Valued.v ((c i)⁻¹ * c 0) < 1
      rw [← hβre]; simpa using k0
    · show Valued.v ((c i)⁻¹ * c 1) < 1
      rw [← hβI]; simpa [hav] using k1
    · show Valued.v ((c i)⁻¹ * c 2) < 1
      rw [← hβJ]; simpa [hbv] using k2
    · show Valued.v ((c i)⁻¹ * c 3) < 1
      rw [← hβK]; simpa [hav, hbv] using k3
  have := hall i
  rw [inv_mul_cancel₀ hci, map_one] at this
  exact lt_irrefl _ this

end Place

end QuadFormsKB.Tamagawa.Measure.Weil
