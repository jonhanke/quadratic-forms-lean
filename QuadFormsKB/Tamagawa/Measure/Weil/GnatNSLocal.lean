/-
# Non-square discriminant, locally: $G^\natural(K)/K^\times\cong SO(\langle1,-ad,-bd,abd\rangle)(K)$ in the forms needed adelically


**Layer:** a field $K$ with $2\ne0$ and $A, B, D\in K^\times$; the $E = K[\delta]/(\delta^2-D)$, $D_E = (A,B)_E$, $G^\natural\le D_E^\times$
and $\varphi : G^\natural\to SO(V_0)$ (`Quat.Gnat.phiSO`), uniform in $D$ (square or not); then a number field $F$, the integral
model `qNS a b d` and the completions $F_v$.

**Defines/proves**
* **`phiLin_eq_inv`**: $\varphi_\alpha(v) = \alpha\,v\,\sigma(\alpha^{-1})$ (no division by $\operatorname{nrd}\alpha$), so the matrix of $\varphi_\alpha$ is
  `nsMat α α⁻¹`, with entries polynomial in the coordinates of $\alpha$ and $\alpha^{-1}$ (`phiSO_val`, `continuous_nsMat_comp`);
* for a ring homomorphism $\rho : F\to K$: the hessian form (`phiSO_hessian_qNS`, `exists_phiSO_eq_qNS`), and for $F$-algebras
  `nsSOK : Gnat (ιa) (ιb) (ιd) →* soSub QF K` with `nsSOK_surjective`, `nsSOK_eq_one_iff` (kernel = $K^\times$);
* at a finite place $v$ with $|2|_v = |a|_v = |b|_v = |d|_v = 1$: **`exists_smul_mem_lamE_of_integral`** — if $\varphi_\alpha$ stabilizes
  $\mathfrak o_v^4$ then $c\alpha\in\Lambda_E^\times$ for some $c\in F_v^\times$ ($\Lambda_E = \mathfrak o_v[\delta]\langle1,i,j,k\rangle$), by the trace
  identity over $\mathfrak o_v[\delta]$: $u = \alpha\sigma(\alpha^{-1})\in\Lambda_E^\times$, conjugation by $\alpha$ is $z\mapsto(\alpha z\sigma(\alpha^{-1}))\sigma(u)$, hence
  integral, and $\sum_j[\gamma e_j\bar\gamma]_j = 4\operatorname{re}(\gamma)^2$ with $\gamma = \beta w$ shows that a primitive $\beta$ has a unit norm
  ($\mathfrak o_v[\delta]/\mathfrak p$ is reduced since $2d$ is a unit); and the converse `nsSOK_mem_stdStab`.

Source: Weil 1982, §3.7, pp. 64–65 [unverified]; Knus–Merkurjev–Rost–Tignol, §15 [unverified].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqGlobal

open Matrix Quaternion NumberField IsDedekindDomain WithZero Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Lattices

/-! ### $\varphi_\alpha$ without division -/

section Generic

variable {K : Type*} [Field K] {A B D : K}

theorem sig_smulK (c : K) (y : DE A B D) : sig (c • y) = c • sig y := by
  ext <;> simp [sig]

theorem inv_eq_smul_star {α : (DE A B D)ˣ} (hα : α ∈ Gnat A B D) :
    (((α⁻¹ : (DE A B D)ˣ)) : DE A B D) = (nrdK (α : DE A B D))⁻¹ • star (α : DE A B D) := by
  have h := nrdK_ne_zero hα
  have e : ((α : DE A B D)) * ((nrdK (α : DE A B D))⁻¹ • star (α : DE A B D)) = 1 := by
    rw [mul_smul_comm, mul_star_eq_nrdE, nrdE_eq_nrdK hα, coe_algebraMap_eq_smul_one, smul_smul,
      inv_mul_cancel₀ h, one_smul]
  calc (((α⁻¹ : (DE A B D)ˣ)) : DE A B D) = (((α⁻¹ : (DE A B D)ˣ)) : DE A B D) * ((α : DE A B D) *
        ((nrdK (α : DE A B D))⁻¹ • star (α : DE A B D))) := by rw [e, mul_one]
    _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- **$\varphi_\alpha(v) = \alpha\,v\,\sigma(\alpha^{-1})$** for $\alpha\in G^\natural$. -/
theorem phiLin_eq_inv {α : (DE A B D)ˣ} (hα : α ∈ Gnat A B D) (v : Fin 4 → K) :
    phiLin (α : DE A B D) v = coords ((α : DE A B D) * emb v * sig (((α⁻¹ : (DE A B D)ˣ)) : DE A B D)) := by
  rw [phiLin_apply, inv_eq_smul_star hα, sig_smulK, mul_smul_comm, coords_smul]

/-- The matrix of $x\mapsto x_1\,x\,\sigma(y_1)$ on $V_0$ in the coordinates `coords`/`emb`. -/
def nsMat (x y : DE A B D) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => coords (x * emb (Pi.single j 1) * sig y) i

variable (h2 : (2 : K) ≠ 0) (hA : A ≠ 0) (hD : D ≠ 0)

theorem phiSO_val (α : Gnat A B D) :
    ((phiSO h2 hA hD α : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      nsMat ((α : (DE A B D)ˣ) : DE A B D) ((((α : (DE A B D)ˣ))⁻¹ : (DE A B D)ˣ) : DE A B D) := by
  ext i j
  rw [coe_phiSO, LinearMap.toMatrix'_apply, phiLin_eq_inv α.2]
  simp only [nsMat, Matrix.of_apply]

theorem phiSO_inv_val (α : Gnat A B D) :
    (((phiSO h2 hA hD α)⁻¹ : SO (V0Form A B D)) : GL (Fin 4) K).val =
      nsMat ((((α : (DE A B D)ˣ))⁻¹ : (DE A B D)ˣ) : DE A B D) ((α : (DE A B D)ˣ) : DE A B D) := by
  rw [← map_inv, phiSO_val]
  simp only [Subgroup.coe_inv, inv_inv]

set_option maxHeartbeats 8000000 in
/-- **Continuity of the matrix of $\varphi$** in the eight coordinates of $x_1$ and of $y_1$ over $K$. -/
theorem continuous_nsMat_comp [TopologicalSpace K] [IsTopologicalRing K] {X : Type*} [TopologicalSpace X]
    (f g : X → DE A B D)
    (hf : ∀ c : DE A B D → QE D, (c = fun z => z.re) ∨ (c = fun z => z.imI) ∨ (c = fun z => z.imJ) ∨
      (c = fun z => z.imK) → Continuous (fun t => (c (f t)).re) ∧ Continuous (fun t => (c (f t)).im))
    (hg : ∀ c : DE A B D → QE D, (c = fun z => z.re) ∨ (c = fun z => z.imI) ∨ (c = fun z => z.imJ) ∨
      (c = fun z => z.imK) → Continuous (fun t => (c (g t)).re) ∧ Continuous (fun t => (c (g t)).im)) :
    Continuous fun t => nsMat (f t) (g t) := by
  obtain ⟨f0, f0'⟩ := hf _ (Or.inl rfl)
  obtain ⟨f1, f1'⟩ := hf _ (Or.inr (Or.inl rfl))
  obtain ⟨f2, f2'⟩ := hf _ (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨f3, f3'⟩ := hf _ (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨g0, g0'⟩ := hg _ (Or.inl rfl)
  obtain ⟨g1, g1'⟩ := hg _ (Or.inr (Or.inl rfl))
  obtain ⟨g2, g2'⟩ := hg _ (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨g3, g3'⟩ := hg _ (Or.inr (Or.inr (Or.inr rfl)))
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
  simp [nsMat, coords, emb, sig, Pi.single_apply, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> fun_prop

end Generic

/-! ### Over a number field: the integral model `qNS a b d` -/

section Model

variable {F : Type} [Field F] [NumberField F]

/-- $q_{\mathrm{ns}}(a,b,d)\otimes_\rho K = \langle1,-\rho a\rho d,-\rho b\rho d,\rho a\rho b\rho d\rangle$ = `V0Form (ρ a) (ρ b) (ρ d)`. -/
theorem qNS_map_ringHom {K : Type*} [Field K] (ρ : F →+* K) (a b d : 𝓞 F) :
    ((qNS a b d).map (algebraMap (𝓞 F) F)).map ρ = V0Form (ρ (a : F)) (ρ (b : F)) (ρ (d : F)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qNS, V0Form, QuadForm.diag, QuadForm.map]

theorem hessian_qNS_map_ringHom {K : Type*} [Field K] (ρ : F →+* K) (a b d : 𝓞 F) :
    ((qNS a b d).map (algebraMap (𝓞 F) F)).hessian.map ρ =
      (V0Form (ρ (a : F)) (ρ (b : F)) (ρ (d : F))).hessian := by
  rw [← qNS_map_ringHom ρ a b d, QuadFormsKB.Siegel.hessian_map_NF ρ (QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d))]

theorem phiSO_hessian_qNS {K : Type*} [Field K] (ρ : F →+* K) (a b d : 𝓞 F) (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0)
    (α : Gnat (ρ (a : F)) (ρ (b : F)) (ρ (d : F))) :
    ((phiSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hd) α : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)ᵀ * ((qNS a b d).map (algebraMap (𝓞 F) F)).hessian.map ρ *
        ((phiSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hd) α : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) = ((qNS a b d).map (algebraMap (𝓞 F) F)).hessian.map ρ ∧
      ((phiSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hd) α : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [hessian_qNS_map_ringHom]
  have := (mem_SO_iff_hessian (two_ne_zero_of_ringHom ρ)).1 (phiSO (two_ne_zero_of_ringHom ρ)
    ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hd) α).2
  exact ⟨this.2, this.1⟩

theorem exists_phiSO_eq_qNS {K : Type*} [Field K] (ρ : F →+* K) (a b d : 𝓞 F) (ha : (a : F) ≠ 0)
    (hb : (b : F) ≠ 0) (hd : (d : F) ≠ 0) (g : GL (Fin 4) K)
    (hg : (g : Matrix (Fin 4) (Fin 4) K)ᵀ * ((qNS a b d).map (algebraMap (𝓞 F) F)).hessian.map ρ * g =
      ((qNS a b d).map (algebraMap (𝓞 F) F)).hessian.map ρ)
    (hdet : (g : Matrix (Fin 4) (Fin 4) K).det = 1) :
    ∃ α : Gnat (ρ (a : F)) (ρ (b : F)) (ρ (d : F)),
      (phiSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hd) α : GL (Fin 4) K) = g := by
  rw [hessian_qNS_map_ringHom] at hg
  have hmem : g ∈ SO (V0Form (ρ (a : F)) (ρ (b : F)) (ρ (d : F))) :=
    (mem_SO_iff_hessian (two_ne_zero_of_ringHom ρ)).2 ⟨hdet, hg⟩
  obtain ⟨α, hα⟩ := phiSO_surjective (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hb)
    ((map_ne_zero ρ).2 hd) ⟨g, hmem⟩
  exact ⟨α, congrArg Subtype.val hα⟩

theorem phiSO_val_eq_one_iff {K : Type*} [Field K] (ρ : F →+* K) (a : 𝓞 F) (b : F) (d : 𝓞 F)
    (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0) (α : Gnat (ρ (a : F)) (ρ b) (ρ (d : F))) :
    (phiSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hd) α : GL (Fin 4) K) = 1 ↔
      α ∈ scalarsG (ρ (a : F)) (ρ b) (ρ (d : F)) := by
  rw [← ker_phiSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hd), MonoidHom.mem_ker]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

/-! #### $F$-algebras: `orthGroup` and `soSub` -/

variable (K : Type*) [Field K] [Algebra F K] (a b d : 𝓞 F)

local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)

/-- $D_E$ over $K$ for the model $(a,b,d)$. -/
abbrev DEr : Type _ := DE (algebraMap F K (a : F)) (algebraMap F K (b : F)) (algebraMap F K (d : F))

/-- $D_E^\times$ over $K$ for the model $(a,b,d)$. -/
abbrev DEK : Type _ := (DEr K a b d)ˣ

/-- $G^\natural(K)$ for the model $(a,b,d)$. -/
abbrev GnK : Type _ := Gnat (algebraMap F K (a : F)) (algebraMap F K (b : F)) (algebraMap F K (d : F))

/-- $\varphi$ as a matrix over an $F$-algebra field. -/
def nsGL (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0) : GnK K a b d →* GL (Fin 4) K :=
  (SO (V0Form (algebraMap F K (a : F)) (algebraMap F K (b : F)) (algebraMap F K (d : F)))).subtype.comp
    (phiSO (two_ne_zero_of_ringHom (algebraMap F K)) ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hd))

variable {K a b d}

theorem nsGL_apply (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0) (α : GnK K a b d) :
    nsGL K a b d ha hd α = phiSO (two_ne_zero_of_ringHom (algebraMap F K)) ((map_ne_zero _).2 ha)
      ((map_ne_zero _).2 hd) α := by
  simp only [nsGL, MonoidHom.comp_apply, Subgroup.coe_subtype]

variable (K a b d) in
/-- **$\alpha\mapsto\varphi_\alpha$ into `soSub QF K`** for an $F$-algebra field $K$. -/
def nsSOK (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0) : GnK K a b d →* soSub QF K :=
  ((nsGL K a b d ha hd).codRestrict (orthGroup QF K) fun α => by
    rw [mem_orthGroup, nsGL_apply]
    exact (phiSO_hessian_qNS (algebraMap F K) a b d ha hd α).1).codRestrict (soSub QF K) fun α => by
    change ((nsGL K a b d ha hd α).val).det = 1
    rw [nsGL_apply]
    exact (phiSO_hessian_qNS (algebraMap F K) a b d ha hd α).2

theorem nsSOK_coe (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0) (α : GnK K a b d) :
    (((nsSOK K a b d ha hd α : soSub QF K) : orthGroup QF K) : GL (Fin 4) K) = nsGL K a b d ha hd α := rfl

theorem nsSOK_surjective (ha : (a : F) ≠ 0) (hb : (b : F) ≠ 0) (hd : (d : F) ≠ 0) :
    Function.Surjective (nsSOK K a b d ha hd) := by
  intro g
  obtain ⟨α, hα⟩ := exists_phiSO_eq_qNS (algebraMap F K) a b d ha hb hd ((g : orthGroup QF K) : GL (Fin 4) K)
    ((mem_orthGroup QF).1 (g : orthGroup QF K).2) (mem_soSub.1 g.2)
  refine ⟨α, Subtype.ext (Subtype.ext ?_)⟩
  rw [nsSOK_coe, nsGL_apply, hα]

theorem nsSOK_eq_one_iff (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0) (α : GnK K a b d) :
    nsSOK K a b d ha hd α = 1 ↔ α ∈ scalarsG (algebraMap F K (a : F)) (algebraMap F K (b : F))
      (algebraMap F K (d : F)) := by
  rw [← phiSO_val_eq_one_iff (algebraMap F K) a (b : F) d ha hd α]
  constructor
  · intro h
    have h' := congrArg (fun g : soSub QF K => ((g : orthGroup QF K) : GL (Fin 4) K)) h
    simp only [nsSOK_coe, nsGL_apply, OneMemClass.coe_one] at h'
    exact h'
  · intro h
    apply Subtype.ext; apply Subtype.ext
    rw [nsSOK_coe, nsGL_apply, h]
    rfl

theorem nsSOK_mulVec (ha : (a : F) ≠ 0) (hd : (d : F) ≠ 0) (α : GnK K a b d) (v : Fin 4 → K) :
    omat (nsSOK K a b d ha hd α : orthGroup QF K) *ᵥ v =
      coords (((α : DEK K a b d) : DEr K a b d) * emb v * sig ((((α : DEK K a b d))⁻¹ : DEK K a b d) : DEr K a b d)) := by
  rw [omat, nsSOK_coe, nsGL_apply, coe_phiSO, LinearMap.toMatrix'_mulVec, phiLin_eq_inv α.2]

end Model

/-! ### Integral structures on $E$ and $D_E$ -/

section Integral

variable {K : Type*} [Field K] (S : Subring K) {A B D : K}

/-- Both coordinates of $z = x + y\delta\in E$ lie in $S$. -/
def QEInt (z : QE D) : Prop := z.re ∈ S ∧ z.im ∈ S

/-- All eight coordinates of $x\in D_E$ lie in $S$ ($x\in\Lambda_E$ for $S = \mathfrak o_v$). -/
def DEInt (x : DE A B D) : Prop := QEInt S x.re ∧ QEInt S x.imI ∧ QEInt S x.imJ ∧ QEInt S x.imK

variable {S}

theorem QEInt.add {z w : QE D} (hz : QEInt S z) (hw : QEInt S w) : QEInt S (z + w) :=
  ⟨S.add_mem hz.1 hw.1, S.add_mem hz.2 hw.2⟩

theorem QEInt.mul (hD : D ∈ S) {z w : QE D} (hz : QEInt S z) (hw : QEInt S w) : QEInt S (z * w) := by
  refine ⟨?_, ?_⟩ <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
  apply_rules [S.add_mem, S.mul_mem, S.zero_mem, hz.1, hz.2, hw.1, hw.2]

theorem QEInt.star {z : QE D} (hz : QEInt S z) : QEInt S (star z) := by
  refine ⟨?_, ?_⟩ <;> simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] <;>
  apply_rules [S.add_mem, S.mul_mem, S.zero_mem, S.neg_mem, hz.1, hz.2]

theorem QEInt.algebraMap {r : K} (hr : r ∈ S) : QEInt S (algebraMap K (QE D) r) := ⟨hr, S.zero_mem⟩

theorem DEInt.mul (hA : A ∈ S) (hB : B ∈ S) (hD : D ∈ S) {x y : DE A B D} (hx : DEInt S x) (hy : DEInt S y) :
    DEInt S (x * y) := by
  have hA' : QEInt S (algebraMap K (QE D) A) := QEInt.algebraMap hA
  have hB' : QEInt S (algebraMap K (QE D) B) := QEInt.algebraMap hB
  have h0 : QEInt S (0 : QE D) := ⟨S.zero_mem, S.zero_mem⟩
  have hneg : ∀ {z : QE D}, QEInt S z → QEInt S (-z) := fun hz => ⟨S.neg_mem hz.1, S.neg_mem hz.2⟩
  have hsub : ∀ {z w : QE D}, QEInt S z → QEInt S w → QEInt S (z - w) := fun hz hw => by
    rw [sub_eq_add_neg]; exact hz.add (hneg hw)
  obtain ⟨x0, x1, x2, x3⟩ := hx
  obtain ⟨y0, y1, y2, y3⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul] <;>
  apply_rules [QEInt.add, QEInt.mul hD, hsub, hneg]

theorem DEInt.star {x : DE A B D} (hx : DEInt S x) : DEInt S (star x) := by
  have hneg : ∀ {z : QE D}, QEInt S z → QEInt S (-z) := fun hz => ⟨S.neg_mem hz.1, S.neg_mem hz.2⟩
  obtain ⟨x0, x1, x2, x3⟩ := hx
  refine ⟨?_, hneg x1, hneg x2, hneg x3⟩
  simpa using x0

theorem DEInt.sig {x : DE A B D} (hx : DEInt S x) : DEInt S (sig x) :=
  ⟨hx.1.star, hx.2.1.star, hx.2.2.1.star, hx.2.2.2.star⟩

theorem DEInt.coe {z : QE D} (hz : QEInt S z) : DEInt S ((z : DE A B D)) :=
  ⟨hz, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩⟩

theorem DEInt.one : DEInt S (1 : DE A B D) := DEInt.coe ⟨S.one_mem, S.zero_mem⟩

theorem DEInt.add {x y : DE A B D} (hx : DEInt S x) (hy : DEInt S y) : DEInt S (x + y) :=
  ⟨hx.1.add hy.1, hx.2.1.add hy.2.1, hx.2.2.1.add hy.2.2.1, hx.2.2.2.add hy.2.2.2⟩

theorem DEInt.smul {c : K} (hc : c ∈ S) {x : DE A B D} (hx : DEInt S x) : DEInt S (c • x) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> apply_rules [S.mul_mem]

theorem DEInt_emb_iff (v : Fin 4 → K) : DEInt S (emb v : DE A B D) ↔ ∀ i, v i ∈ S := by
  constructor
  · rintro ⟨⟨h0, -⟩, ⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3]
  · intro h
    exact ⟨⟨h 0, S.zero_mem⟩, ⟨S.zero_mem, h 1⟩, ⟨S.zero_mem, h 2⟩, ⟨S.zero_mem, h 3⟩⟩

theorem coords_mem_of_DEInt {x : DE A B D} (hx : DEInt S x) (i : Fin 4) : coords x i ∈ S := by
  fin_cases i
  exacts [hx.1.1, hx.2.1.2, hx.2.2.1.2, hx.2.2.2.2]

/-- **Decomposition $\Lambda_E = (V_0\cap\Lambda_E) + \delta(V_0\cap\Lambda_E)$** ($D$ a unit of $S$). -/
theorem exists_emb_add_delta {x : DE A B D} (hx : DEInt S x) (hD : D ≠ 0) (hDi : D⁻¹ ∈ S) :
    ∃ w w' : Fin 4 → K, (∀ i, w i ∈ S) ∧ (∀ i, w' i ∈ S) ∧
      x = emb w + ((⟨0, 1⟩ : QE D) : DE A B D) * emb w' := by
  refine ⟨![x.re.re, x.imI.im, x.imJ.im, x.imK.im], ![x.re.im, x.imI.re * D⁻¹, x.imJ.re * D⁻¹, x.imK.re * D⁻¹],
    fun i => ?_, fun i => ?_, ?_⟩
  · fin_cases i
    exacts [hx.1.1, hx.2.1.2, hx.2.2.1.2, hx.2.2.2.2]
  · fin_cases i
    · exact hx.1.2
    · exact S.mul_mem hx.2.1.1 hDi
    · exact S.mul_mem hx.2.2.1.1 hDi
    · exact S.mul_mem hx.2.2.2.1 hDi
  · ext <;> simp [emb] <;> field_simp

end Integral

/-! ### The trace identity over a commutative ring -/

/-- **The trace of $z\mapsto\gamma z\bar\gamma$** on a quaternion algebra over a commutative ring is $\operatorname{trd}(\gamma)^2 = 4\operatorname{re}(\gamma)^2$. -/
theorem trace_conj_identity {R : Type*} [CommRing R] (c₁ c₃ : R) (γ : ℍ[R, c₁, 0, c₃]) :
    (γ * 1 * star γ).re + (γ * ⟨0, 1, 0, 0⟩ * star γ).imI + (γ * ⟨0, 0, 1, 0⟩ * star γ).imJ +
      (γ * ⟨0, 0, 0, 1⟩ * star γ).imK = 4 * γ.re ^ 2 := by
  simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
  ring

theorem re_mul_basis {R : Type*} [CommRing R] (c₁ c₃ : R) (β : ℍ[R, c₁, 0, c₃]) :
    (β * ⟨0, 1, 0, 0⟩).re = c₁ * β.imI ∧ (β * ⟨0, 0, 1, 0⟩).re = c₃ * β.imJ ∧
      (β * ⟨0, 0, 0, 1⟩).re = -(c₁ * c₃) * β.imK := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [QuaternionAlgebra.re_mul]

/-! ### Finite places: integral lifts -/

section Place

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a b d : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)

variable (a b d) in
/-- $\Lambda_E^\times$: units of $D_E\otimes F_v$ with all coordinates of $u$ and $u^{-1}$ in $\mathfrak o_v$. -/
def lamEUnits : Set (DEK Fv a b d) :=
  {u | DEInt (𝔬).toSubring (u : DEr Fv a b d) ∧ DEInt (𝔬).toSubring (((u⁻¹ : DEK Fv a b d)) : DEr Fv a b d)}

variable (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)

/-- **$\Lambda_E^\times\cap G^\natural$ acts integrally** on $\mathfrak o_v^4$. -/
theorem nsSOK_mem_stdStab (ha : Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1)
    (hb : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ 1)
    (hd : Valued.v (algebraMap F (v.adicCompletion F) (d : F)) ≤ 1)
    (α : GnK Fv a b d) (hα : (α : DEK Fv a b d) ∈ lamEUnits v a b d) :
    (nsSOK Fv a b d ha0 hd0 α : orthGroup QF Fv) ∈ stdStab QF v := by
  have hA : algebraMap F Fv (a : F) ∈ (𝔬).toSubring := (mem_O_iff v _).2 ha
  have hB : algebraMap F Fv (b : F) ∈ (𝔬).toSubring := (mem_O_iff v _).2 hb
  have hD : algebraMap F Fv (d : F) ∈ (𝔬).toSubring := (mem_O_iff v _).2 hd
  set x : DEr Fv a b d := ((α : DEK Fv a b d) : DEr Fv a b d) with hx
  set y : DEr Fv a b d := (((α : DEK Fv a b d)⁻¹ : DEK Fv a b d) : DEr Fv a b d) with hy
  have hxI : DEInt (𝔬).toSubring x := hα.1
  have hyI : DEInt (𝔬).toSubring y := hα.2
  refine mem_stdStab_of_mulVec v _ (fun w hw => ?_) (fun w hw => ?_)
  · have hwI : DEInt (𝔬).toSubring (emb w : DEr Fv a b d) := (DEInt_emb_iff w).2 ((mem_std_iff4 v w).1 hw)
    have key : DEInt (𝔬).toSubring (x * emb w * sig y) := (hxI.mul hA hB hD hwI).mul hA hB hD hyI.sig
    rw [nsSOK_mulVec, mem_std_iff4]
    intro i
    convert coords_mem_of_DEInt key i using 4
  · have hwI : DEInt (𝔬).toSubring (emb w : DEr Fv a b d) := (DEInt_emb_iff w).2 ((mem_std_iff4 v w).1 hw)
    have key : DEInt (𝔬).toSubring (y * emb w * sig x) := (hyI.mul hA hB hD hwI).mul hA hB hD hxI.sig
    rw [show ((nsSOK Fv a b d ha0 hd0 α : orthGroup QF Fv))⁻¹ = (nsSOK Fv a b d ha0 hd0 α⁻¹ : orthGroup QF Fv) by
      rw [map_inv]; rfl, nsSOK_mulVec, mem_std_iff4]
    simp only [Subgroup.coe_inv, inv_inv]
    intro i
    convert coords_mem_of_DEInt key i using 4

theorem sig_one {K : Type*} [Field K] {A B D : K} : sig (1 : DE A B D) = 1 := by ext <;> simp [sig]

/-- Valuation lemma behind "$\mathfrak o_v[\delta]/\mathfrak p$ is reduced": $|pq| < 1$, $|p^2+Dq^2| < 1$, $|D| = 1$ give $|p|, |q| < 1$. -/
theorem valued_lt_one_of_sq {p q D : Fv} (hD : Valued.v D = 1) (hpq : Valued.v (p * q) < 1)
    (hs : Valued.v (p ^ 2 + D * q ^ 2) < 1) : Valued.v p < 1 ∧ Valued.v q < 1 := by
  rw [map_mul] at hpq
  have sq_lt : ∀ {t : Fv}, Valued.v (t ^ 2) < 1 → Valued.v t < 1 := fun {t} ht => by
    by_contra h
    push Not at h
    rw [map_pow] at ht
    exact absurd ht (not_lt.2 (one_le_pow₀ h))
  have lt_sq : ∀ {t : Fv}, Valued.v t < 1 → Valued.v (t ^ 2) < 1 := fun {t} ht => by
    rw [map_pow]; exact pow_lt_one₀ zero_le ht (by norm_num)
  by_cases hp : Valued.v p < 1
  · refine ⟨hp, sq_lt ?_⟩
    have hDq : Valued.v (D * q ^ 2) < 1 := by
      have : D * q ^ 2 = (p ^ 2 + D * q ^ 2) - p ^ 2 := by ring
      rw [this]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hs (lt_sq hp))
    rwa [map_mul, hD, one_mul] at hDq
  · push Not at hp
    have hq : Valued.v q < 1 := by
      by_contra hq
      push Not at hq
      exact absurd hpq (not_lt.2 (one_le_mul_of_one_le_of_one_le hp hq))
    refine ⟨sq_lt ?_, hq⟩
    have hDq : Valued.v (D * q ^ 2) < 1 := by rw [map_mul, hD, one_mul]; exact lt_sq hq
    have : p ^ 2 = (p ^ 2 + D * q ^ 2) - D * q ^ 2 := by ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hs hDq)

end Place

section L1
variable {K : Type*} [Field K] {S : Subring K} {A B D : K}

theorem inV0_smulK {c : K} {z : DE A B D} (hz : InV0 z) : InV0 (c • z) := by
  unfold InV0 at *
  rw [sig_smulK, hz]
  ext <;> simp

/-- **Conjugation by $\alpha$ is integral** when $\varphi_\alpha$ is (generic over a subring $S\ni A, B, D, D^{-1}$). -/
theorem DEInt_conj_of_phi (h2 : (2 : K) ≠ 0) (hA : A ∈ S) (hB : B ∈ S) (hD : D ∈ S) (hD0 : D ≠ 0)
    (hDi : D⁻¹ ∈ S) {α : (DE A B D)ˣ} (hα : α ∈ Gnat A B D)
    (hφ : ∀ w : Fin 4 → K, (∀ i, w i ∈ S) → ∀ i,
      coords ((α : DE A B D) * emb w * sig (((α⁻¹ : (DE A B D)ˣ)) : DE A B D)) i ∈ S) :
    ∀ z : DE A B D, DEInt S z → DEInt S ((α : DE A B D) * z * (((α⁻¹ : (DE A B D)ˣ)) : DE A B D)) := by
  set x : DE A B D := (α : DE A B D)
  set y : DE A B D := (((α⁻¹ : (DE A B D)ˣ)) : DE A B D)
  have hyx : y * x = 1 := Units.inv_mul _
  have hV : ∀ w : Fin 4 → K, InV0 (x * emb w * sig y) := fun w => by
    rw [show y = (nrdK x)⁻¹ • star x from inv_eq_smul_star hα, sig_smulK, mul_smul_comm]
    exact inV0_smulK (inV0_conj x _ (inV0_emb w))
  have himg : ∀ w : Fin 4 → K, (∀ i, w i ∈ S) → DEInt S (x * emb w * sig y) := by
    intro w hw
    rw [← emb_coords h2 (hV w), DEInt_emb_iff]
    exact hφ w hw
  have himg' : ∀ z : DE A B D, DEInt S z → DEInt S (x * z * sig y) := by
    intro z hz
    obtain ⟨w, w', hw, hw', rfl⟩ := exists_emb_add_delta hz hD0 hDi
    set δ : DE A B D := ((⟨0, 1⟩ : QE D) : DE A B D)
    have hc : x * (δ * emb w') * sig y = δ * (x * emb w' * sig y) := by
      calc x * (δ * emb w') * sig y = (x * δ) * emb w' * sig y := by rw [← mul_assoc x]
        _ = (δ * x) * emb w' * sig y := by rw [QuaternionAlgebra.coe_commutes]
        _ = δ * (x * emb w' * sig y) := by simp only [mul_assoc]
    rw [mul_add, add_mul, hc]
    exact (himg w hw).add ((DEInt.coe ⟨S.zero_mem, S.one_mem⟩).mul hA hB hD (himg w' hw'))
  have hu : DEInt S (x * sig y) := by simpa using himg' 1 DEInt.one
  intro z hz
  have e : x * z * y = (x * z * sig y) * sig (x * sig y) := by
    rw [sig_mul, sig_sig]
    calc x * z * y = x * z * sig (y * x) * y := by rw [hyx, sig_one, mul_one]
      _ = _ := by rw [sig_mul]; simp only [mul_assoc]
  rw [e]
  exact (himg' z hz).mul hA hB hD hu.sig

end L1


theorem trace_conj_DE {K : Type*} [Field K] {A B D : K} (γ : DE A B D) :
    (γ * 1 * star γ).re + (γ * ⟨0, 1, 0, 0⟩ * star γ).imI + (γ * ⟨0, 0, 1, 0⟩ * star γ).imJ +
      (γ * ⟨0, 0, 0, 1⟩ * star γ).imK = 4 * γ.re ^ 2 := by
  simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
  ring

section L2
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem aux_small {p q D N sr si : Fv} (hD : Valued.v D = 1) (h2 : Valued.v (2 : Fv) = 1)
    (hN : Valued.v N < 1) (hsr : Valued.v sr ≤ 1) (hsi : Valued.v si ≤ 1)
    (hre : N * sr = 4 * (p * p + D * q * q)) (him : N * si = 4 * (p * q + q * p)) :
    Valued.v p < 1 ∧ Valued.v q < 1 := by
  have h4 : Valued.v (4 : Fv) = 1 := by rw [show (4 : Fv) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  have h8 : Valued.v (8 : Fv) = 1 := by rw [show (8 : Fv) = 4 * 2 by norm_num, map_mul, h4, h2, one_mul]
  refine valued_lt_one_of_sq v hD ?_ ?_
  · have e : (8 : Fv) * (p * q) = N * si := by linear_combination -him
    rw [show Valued.v (p * q) = Valued.v ((8 : Fv) * (p * q)) by rw [map_mul (Valued.v) (8 : Fv), h8, one_mul], e, map_mul]
    exact mul_lt_one_of_lt_of_le hN hsi
  · have e : (4 : Fv) * (p ^ 2 + D * q ^ 2) = N * sr := by linear_combination -hre
    rw [show Valued.v (p ^ 2 + D * q ^ 2) = Valued.v ((4 : Fv) * (p ^ 2 + D * q ^ 2)) by
      rw [map_mul (Valued.v) (4 : Fv), h4, one_mul], e, map_mul]
    exact mul_lt_one_of_lt_of_le hN hsr

theorem QEInt_nrdE {K : Type*} [Field K] {S : Subring K} {A B D : K} (hA : A ∈ S) (hB : B ∈ S) (hD : D ∈ S) {x : DE A B D}
    (hx : DEInt S x) : QEInt S (nrdE x) := by
  have h := (hx.mul hA hB hD hx.star).1
  rwa [mul_star_eq_nrdE] at h

/-- **A primitive integral $\beta\in G^\natural$ normalizing $\Lambda_E$ has a unit norm** ($|2|_v = |A|_v = |B|_v = |D|_v = 1$). -/
theorem valued_nrdK_eq_one {A B D : Fv} (h2v : Valued.v (2 : Fv) = 1) (hAv : Valued.v A = 1)
    (hBv : Valued.v B = 1) (hDv : Valued.v D = 1) {β : (DE A B D)ˣ} (hβ : β ∈ Gnat A B D)
    (hβI : DEInt (𝔬).toSubring (β : DE A B D))
    (hprim : ¬ (Valued.v (β : DE A B D).re.re < 1 ∧ Valued.v (β : DE A B D).re.im < 1 ∧
      Valued.v (β : DE A B D).imI.re < 1 ∧ Valued.v (β : DE A B D).imI.im < 1 ∧
      Valued.v (β : DE A B D).imJ.re < 1 ∧ Valued.v (β : DE A B D).imJ.im < 1 ∧
      Valued.v (β : DE A B D).imK.re < 1 ∧ Valued.v (β : DE A B D).imK.im < 1))
    (hconj : ∀ z : DE A B D, DEInt (𝔬).toSubring z →
      DEInt (𝔬).toSubring ((β : DE A B D) * z * (((β⁻¹ : (DE A B D)ˣ)) : DE A B D))) :
    Valued.v (nrdK (β : DE A B D)) = 1 := by
  set S := (𝔬).toSubring
  have hO : ∀ t : Fv, Valued.v t ≤ 1 → t ∈ S := fun t ht => (mem_O_iff v t).2 ht
  have hO' : ∀ t : Fv, t ∈ S → Valued.v t ≤ 1 := fun t ht => (mem_O_iff v t).1 ht
  have hA : A ∈ S := hO _ hAv.le
  have hB : B ∈ S := hO _ hBv.le
  have hD : D ∈ S := hO _ hDv.le
  set N := nrdK (β : DE A B D) with hNdef
  have hN0 : N ≠ 0 := nrdK_ne_zero hβ
  have hNS : N ∈ S := (QEInt_nrdE hA hB hD hβI).1
  refine le_antisymm (hO' _ hNS) (not_lt.1 fun hNlt => hprim ?_)
  have hstar : star (β : DE A B D) = N • (((β⁻¹ : (DE A B D)ˣ)) : DE A B D) := by
    rw [inv_eq_smul_star hβ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  have h4 : Valued.v (4 : Fv) = 1 := by rw [show (4 : Fv) = 2 * 2 by norm_num, map_mul, h2v, one_mul]
  have key : ∀ w : DE A B D, DEInt S w →
      Valued.v ((β : DE A B D) * w).re.re < 1 ∧ Valued.v ((β : DE A B D) * w).re.im < 1 := by
    intro w hw
    have hT : ∀ e : DE A B D, ((β : DE A B D) * w) * e * star ((β : DE A B D) * w) =
        N • ((β : DE A B D) * (w * e * star w) * (((β⁻¹ : (DE A B D)ˣ)) : DE A B D)) := fun e => by
      rw [star_mul, hstar]
      simp only [mul_smul_comm, mul_assoc]
    have hTI : ∀ e : DE A B D, DEInt S e → DEInt S ((β : DE A B D) * (w * e * star w) *
        (((β⁻¹ : (DE A B D)ˣ)) : DE A B D)) := fun e he =>
      hconj _ ((hw.mul hA hB hD he).mul hA hB hD hw.star)
    have hb0 : DEInt S (1 : DE A B D) := DEInt.one
    have hb1 : DEInt S (⟨0, 1, 0, 0⟩ : DE A B D) :=
      ⟨⟨S.zero_mem, S.zero_mem⟩, ⟨S.one_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩⟩
    have hb2 : DEInt S (⟨0, 0, 1, 0⟩ : DE A B D) :=
      ⟨⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.one_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩⟩
    have hb3 : DEInt S (⟨0, 0, 0, 1⟩ : DE A B D) :=
      ⟨⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.one_mem, S.zero_mem⟩⟩
    have hsI := (((hTI _ hb0).1.add (hTI _ hb1).2.1).add (hTI _ hb2).2.2.1).add (hTI _ hb3).2.2.2
    have htr := trace_conj_DE ((β : DE A B D) * w)
    have e0 := congrArg QuaternionAlgebra.re (hT 1)
    have e1 := congrArg QuaternionAlgebra.imI (hT ⟨0, 1, 0, 0⟩)
    have e2 := congrArg QuaternionAlgebra.imJ (hT ⟨0, 0, 1, 0⟩)
    have e3 := congrArg QuaternionAlgebra.imK (hT ⟨0, 0, 0, 1⟩)
    simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
      QuaternionAlgebra.imK_smul] at e0 e1 e2 e3
    rw [e0, e1, e2, e3] at htr
    simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
      QuaternionAlgebra.imK_smul, ← smul_add] at htr
    have hre := congrArg QuadraticAlgebra.re htr
    have him := congrArg QuadraticAlgebra.im htr
    have hγI : QEInt S ((β : DE A B D) * w).re := (hβI.mul hA hB hD hw).1
    simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul, sq, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, mul_zero, zero_mul,
      add_zero] at hre him
    exact aux_small v hDv h2v hNlt (hO' _ hsI.1) (hO' _ hsI.2) hre him
  have hmulA : ∀ {t c : Fv}, Valued.v c = 1 → Valued.v (c * t) < 1 → Valued.v t < 1 := fun {t c} hc h => by
    rwa [map_mul, hc, one_mul] at h
  obtain ⟨k0, k0'⟩ := key 1 DEInt.one
  obtain ⟨k1, k1'⟩ := key ⟨0, 1, 0, 0⟩
    ⟨⟨S.zero_mem, S.zero_mem⟩, ⟨S.one_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩⟩
  obtain ⟨k2, k2'⟩ := key ⟨0, 0, 1, 0⟩
    ⟨⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.one_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩⟩
  obtain ⟨k3, k3'⟩ := key ⟨0, 0, 0, 1⟩
    ⟨⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.zero_mem, S.zero_mem⟩, ⟨S.one_mem, S.zero_mem⟩⟩
  obtain ⟨r1, r2, r3⟩ := re_mul_basis (algebraMap Fv (QE D) A) (algebraMap Fv (QE D) B) (β : DE A B D)
  rw [mul_one] at k0 k0'
  rw [r1] at k1 k1'
  rw [r2] at k2 k2'
  rw [r3] at k3 k3'
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, zero_mul, mul_zero, add_zero, zero_add, QuadraticAlgebra.re_neg,
    QuadraticAlgebra.im_neg, ← map_mul, neg_mul] at k1 k1' k2 k2' k3 k3'
  have hABv : Valued.v (A * B) = 1 := by rw [map_mul, hAv, hBv, one_mul]
  refine ⟨k0, k0', hmulA hAv k1, hmulA hAv k1', hmulA hBv k2, hmulA hBv k2', ?_, ?_⟩
  · refine hmulA hABv ?_
    rwa [Valuation.map_neg] at k3
  · refine hmulA hABv ?_
    rwa [Valuation.map_neg] at k3'

end L2


section L3
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a b d : 𝓞 F}
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)

theorem scalar_mem_Gnat {K : Type*} [Field K] {A B D : K} (r : Kˣ) :
    Units.map (algebraMap K (DE A B D)).toMonoidHom r ∈ Gnat A B D := by
  rw [mem_Gnat]
  change (nrdE (algebraMap K (DE A B D) (r : K))).im = 0
  rw [show algebraMap K (DE A B D) (r : K) = ((algebraMap K (QE D) (r : K) : QE D) : DE A B D) from rfl]
  simp [nrdE, sq]

set_option maxHeartbeats 1000000 in
/-- **Integral lifts at good places (non-square model).** -/
theorem exists_smul_mem_lamEUnits (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (h2v : Valued.v (2 : v.adicCompletion F) = 1)
    (hav : Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1)
    (hbv : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hdv : Valued.v (algebraMap F (v.adicCompletion F) (d : F)) = 1)
    (α : GnK Fv a b d) (hp : (nsSOK Fv a b d ha0 hd0 α : orthGroup QF Fv) ∈ stdStab QF v) :
    ∃ r : Fvˣ, Units.map (algebraMap Fv (DEr Fv a b d)).toMonoidHom r * (α : DEK Fv a b d) ∈
      lamEUnits v a b d := by
  have hO : ∀ t : Fv, Valued.v t ≤ 1 → t ∈ (𝔬).toSubring := fun t ht => (mem_O_iff v t).2 ht
  have hO' : ∀ t : Fv, t ∈ (𝔬).toSubring → Valued.v t ≤ 1 := fun t ht => (mem_O_iff v t).1 ht
  have hA := hO _ hav.le
  have hB := hO _ hbv.le
  have hD := hO _ hdv.le
  have hD0 : algebraMap F Fv (d : F) ≠ 0 := by intro h; rw [h, map_zero] at hdv; exact zero_ne_one hdv
  have hDi : (algebraMap F Fv (d : F))⁻¹ ∈ (𝔬).toSubring := hO _ (by rw [map_inv₀, hdv, inv_one])
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero_of_ringHom (algebraMap F Fv)
  -- conjugation by α is integral
  have hφ : ∀ w : Fin 4 → Fv, (∀ i, w i ∈ (𝔬).toSubring) → ∀ i,
      coords (((α : DEK Fv a b d) : DEr Fv a b d) * emb w *
        sig ((((α : DEK Fv a b d))⁻¹ : DEK Fv a b d) : DEr Fv a b d)) i ∈ (𝔬).toSubring := by
    intro w hw i
    have h3 := mulVec_mem_std_of_mem_stdStab v hp ((mem_std_iff4 v w).2 hw)
    rw [nsSOK_mulVec, mem_std_iff4] at h3
    convert h3 i using 4
  have hconj := DEInt_conj_of_phi h2 hA hB hD hD0 hDi α.2 hφ
  -- scaling to a primitive element
  set x : DEr Fv a b d := ((α : DEK Fv a b d) : DEr Fv a b d) with hx
  let c : Fin 8 → Fv := ![x.re.re, x.re.im, x.imI.re, x.imI.im, x.imJ.re, x.imJ.im, x.imK.re, x.imK.im]
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (c i)) Finset.univ_nonempty
  have hci : c i ≠ 0 := by
    intro h0
    have hz : ∀ j, c j = 0 := fun j => by
      have := hi j (Finset.mem_univ _)
      rw [h0, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)
    apply (α : DEK Fv a b d).ne_zero
    change x = 0
    exact QuaternionAlgebra.ext (QuadraticAlgebra.ext (hz 0) (hz 1)) (QuadraticAlgebra.ext (hz 2) (hz 3))
      (QuadraticAlgebra.ext (hz 4) (hz 5)) (QuadraticAlgebra.ext (hz 6) (hz 7))
  set r : Fvˣ := Units.mk0 (c i)⁻¹ (inv_ne_zero hci)
  refine ⟨r, ?_⟩
  set β : DEK Fv a b d := Units.map (algebraMap Fv (DEr Fv a b d)).toMonoidHom r * (α : DEK Fv a b d) with hβdef
  have hβG : β ∈ Gnat _ _ _ := (Gnat _ _ _).mul_mem (scalar_mem_Gnat r) α.2
  have hβval : (β : DEr Fv a b d) = (c i)⁻¹ • x := by
    rw [hβdef, Units.val_mul, Algebra.smul_def]; rfl
  have hβinv : ((β⁻¹ : DEK Fv a b d) : DEr Fv a b d) = (c i) • ((((α : DEK Fv a b d))⁻¹ : DEK Fv a b d) :
      DEr Fv a b d) := by
    rw [hβdef, _root_.mul_inv_rev, Units.val_mul, ← map_inv]
    change ((((α : DEK Fv a b d))⁻¹ : DEK Fv a b d) : DEr Fv a b d) * algebraMap Fv (DEr Fv a b d) ((r⁻¹ : Fvˣ) : Fv) = _
    rw [← Algebra.commutes, ← Algebra.smul_def]
    congr 1
    simp [r]
  have hcoord : ∀ j, Valued.v ((c i)⁻¹ * c j) ≤ 1 := fun j => by
    rw [map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hi j (Finset.mem_univ _)) zero_le
  have hβI : DEInt (𝔬).toSubring (β : DEr Fv a b d) := by
    rw [hβval]
    exact ⟨⟨by simpa [c] using hO _ (hcoord 0), by simpa [c] using hO _ (hcoord 1)⟩,
      ⟨by simpa [c] using hO _ (hcoord 2), by simpa [c] using hO _ (hcoord 3)⟩,
      ⟨by simpa [c] using hO _ (hcoord 4), by simpa [c] using hO _ (hcoord 5)⟩,
      ⟨by simpa [c] using hO _ (hcoord 6), by simpa [c] using hO _ (hcoord 7)⟩⟩
  have hprim : ¬ (Valued.v (β : DEr Fv a b d).re.re < 1 ∧ Valued.v (β : DEr Fv a b d).re.im < 1 ∧
      Valued.v (β : DEr Fv a b d).imI.re < 1 ∧ Valued.v (β : DEr Fv a b d).imI.im < 1 ∧
      Valued.v (β : DEr Fv a b d).imJ.re < 1 ∧ Valued.v (β : DEr Fv a b d).imJ.im < 1 ∧
      Valued.v (β : DEr Fv a b d).imK.re < 1 ∧ Valued.v (β : DEr Fv a b d).imK.im < 1) := by
    rw [hβval]
    intro h
    have hall : ∀ j, Valued.v ((c i)⁻¹ * c j) < 1 := by
      intro j
      fin_cases j
      · simpa [c] using h.1
      · simpa [c] using h.2.1
      · simpa [c] using h.2.2.1
      · simpa [c] using h.2.2.2.1
      · simpa [c] using h.2.2.2.2.1
      · simpa [c] using h.2.2.2.2.2.1
      · simpa [c] using h.2.2.2.2.2.2.1
      · simpa [c] using h.2.2.2.2.2.2.2
    have := hall i
    rw [inv_mul_cancel₀ hci, map_one] at this
    exact lt_irrefl _ this
  have hconjβ : ∀ z : DEr Fv a b d, DEInt (𝔬).toSubring z →
      DEInt (𝔬).toSubring ((β : DEr Fv a b d) * z * ((β⁻¹ : DEK Fv a b d) : DEr Fv a b d)) := by
    intro z hz
    rw [hβval, hβinv, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hci, one_smul]
    exact hconj z hz
  have hN := valued_nrdK_eq_one v h2v hav hbv hdv hβG hβI hprim hconjβ
  refine ⟨hβI, ?_⟩
  rw [inv_eq_smul_star hβG]
  exact DEInt.smul (hO _ (by rw [map_inv₀, hN, inv_one])) hβI.star

end L3

end QuadFormsKB.Tamagawa.Measure.Weil
