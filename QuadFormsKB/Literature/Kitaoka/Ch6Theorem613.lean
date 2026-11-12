/-
# Kitaoka 1993, Theorem 6.1.3: local representations give a representation by a lattice of the genus (regular spaces, every number field)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms*, Cambridge Tracts in Mathematics 106 (1993), §6.1, Theorem 6.1.3,
p. 134. Page numbers are the printed pages of the book.

**Setting.** $F$ is a number field, $U = (F^m, Q_U)$ and $V = (F^n, Q_V)$ are regular (nondegenerate) quadratic spaces,
$L$ and $M$ are full lattices on $U$ and $V$. The definitions `LatRep`, `LocLatRep`, `SpaceRepAt` of
`Literature/Kitaoka/Ch6Fundamentals.lean` are used. For $F = \mathbb Q$ the statement is the book's `Theorem613`, with the
extra hypotheses that $Q_U$ and $Q_V$ are nondegenerate.

**Proves** `theorem613_of_nondegenerate`: if $L_\mathfrak p \rightarrowtail M_\mathfrak p$ at every finite place
$\mathfrak p$ and $U_w \rightarrowtail V_w$ at every infinite place $w$, then $L \rightarrowtail N$ for a lattice $N$ in
the genus of $M$. The result is unconditional.

*Proof* (Kitaoka's). (1) A local isometry $L_\mathfrak p \rightarrowtail M_\mathfrak p$ extends to an injective isometry
$U_\mathfrak p \rightarrowtail V_\mathfrak p$ of the quadratic spaces over the completion $F_\mathfrak p$
(`exists_extension`, `exists_local_extension`). (2) By the Hasse principle for representations
(`isRepresentedBy_of_everywhere`, Kitaoka Corollary 4.1.2) there is an injective isometry $\sigma : U \to V$ over $F$, given by
a matrix $S$. (3) By Witt's extension theorem over $F_\mathfrak p$ (`exists_orth_extend`) there is
$\tau_\mathfrak p \in O(V)(F_\mathfrak p)$ with $\tau_\mathfrak p S_\mathfrak p x = g_\mathfrak p x$ for $x \in F_\mathfrak p^m$, where $g_\mathfrak p$ is the
extension of step (1); so $\tau_\mathfrak p S_\mathfrak p L_\mathfrak p \subseteq M_\mathfrak p$. (4) Put
$N_\mathfrak p = \tau_\mathfrak p^{-1} M_\mathfrak p$, taking $\tau_\mathfrak p = 1$ whenever $S_\mathfrak p L_\mathfrak p \subseteq M_\mathfrak p$ already,
which holds for almost all $\mathfrak p$. Gluing the $N_\mathfrak p$ (`LocFamily.glue`) gives a lattice $N$ with
$N_\mathfrak p = \tau_\mathfrak p^{-1} M_\mathfrak p$, hence in the genus of $M$, and $S L \subseteq N$.
-/
import QuadFormsKB.Literature.Kitaoka.Ch6Fundamentals
import QuadFormsKB.Literature.Kitaoka.Ch4HassePrinciple
import QuadFormsKB.Tamagawa.SiegelGenusV

open NumberField IsDedekindDomain QuadFormsKB.Lattices WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka

/-! ### Step 1: a local isometry of lattices extends to the local spaces -/

section LocalExtension

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Every local vector is moved into any given box $\mathfrak p^k \mathfrak o_\mathfrak p^n$ by a power of the uniformizer. -/
theorem exists_smul_mem_ball {n : ℕ} (x : Fin n → Fv) (k : ℤ) :
    ∃ N : ℕ, ϖk v (N : ℤ) • x ∈ ball v k := by
  choose K hK using fun i => exists_valued_le v (x i)
  set K0 : ℕ := Finset.univ.sup K
  refine ⟨K0 + k.toNat, fun i => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, map_mul, valued_ϖk]
  calc exp (-((K0 + k.toNat : ℕ) : ℤ)) * Valued.v (x i)
      ≤ exp (-((K0 + k.toNat : ℕ) : ℤ)) * exp (K0 : ℤ) :=
        mul_le_mul' le_rfl ((hK i).trans (exp_le_exp.mpr (by exact_mod_cast Finset.le_sup (f := K) (Finset.mem_univ i))))
    _ ≤ exp (-k) := by rw [← exp_add, exp_le_exp]; push_cast; omega

/-- **A lattice isometry extends to the spaces:** if $\Lambda \subseteq F_\mathfrak p^m$ is a lattice and
$f : \Lambda \to \Lambda'$ is an injective $\mathfrak o_\mathfrak p$-linear map with $q_V(f x) = q_U(x)$, then $f$ is the
restriction of an injective $F_\mathfrak p$-linear map $g : F_\mathfrak p^m \to F_\mathfrak p^n$ with $q_V(g x) = q_U(x)$ for all
$x$. *Proof:* with $c = \varpi^k$ and $\mathfrak p^k\mathfrak o^m \subseteq \Lambda \subseteq \mathfrak p^{-k}\mathfrak o^m$, put
$g(e_i) = c^{-1} f(c e_i)$; then $c^2 g(x) = c^2 f(x)$ on $\Lambda$, and the isometry property follows by scaling
$x$ into $\Lambda$. -/
theorem exists_extension {m n : ℕ} {Λ : Submodule 𝔬 (Fin m → Fv)} (hΛ : Λ.IsLattice Fv)
    {Λ' : Submodule 𝔬 (Fin n → Fv)} (qU : QuadraticForm Fv (Fin m → Fv))
    (qV : QuadraticForm Fv (Fin n → Fv)) (f : Λ →ₗ[𝔬] Λ') (hfi : Function.Injective f)
    (hf : ∀ x : Λ, qV (f x : Fin n → Fv) = qU (x : Fin m → Fv)) :
    ∃ g : (Fin m → Fv) →ₗ[Fv] (Fin n → Fv), (∀ x : Λ, g x = f x) ∧ Function.Injective g ∧
      ∀ x, qV (g x) = qU x := by
  classical
  obtain ⟨k, hk1, hk2⟩ := exists_local_bounds v hΛ
  set c : Fv := ϖk v (k : ℤ) with hc
  have hc0 : c ≠ 0 := ϖk_ne_zero v _
  have hcv : Valued.v c = exp (-(k : ℤ)) := valued_ϖk v _
  have hcle : Valued.v c ≤ 1 := by rw [hcv, ← exp_zero, exp_le_exp]; omega
  have hmem : ∀ i, (Pi.single i c : Fin m → Fv) ∈ Λ := fun i => hk1 (by
    intro j
    by_cases h : j = i
    · subst h; simp [hcv]
    · simp [h])
  let e : Fin m → Λ := fun i => ⟨Pi.single i c, hmem i⟩
  let w : Fin m → (Fin n → Fv) := fun i => c⁻¹ • (f (e i) : Fin n → Fv)
  let g : (Fin m → Fv) →ₗ[Fv] (Fin n → Fv) := Fintype.linearCombination Fv w
  have hgs : ∀ i, g (Pi.single i c) = (f (e i) : Fin n → Fv) := by
    intro i
    simp only [g, Fintype.linearCombination_apply]
    rw [Finset.sum_eq_single i]
    · simp [w, smul_smul, mul_inv_cancel₀ hc0]
    · intro j _ hj; simp [hj]
    · simp
  have hext : ∀ x : Λ, g (x : Fin m → Fv) = (f x : Fin n → Fv) := by
    intro x
    have hxk := hk2 x.2
    have hcx : ∀ i, Valued.v (c * (x : Fin m → Fv) i) ≤ 1 := fun i => by
      rw [map_mul, hcv]
      have := hxk i
      rw [neg_neg] at this
      calc exp (-(k : ℤ)) * Valued.v ((x : Fin m → Fv) i) ≤ exp (-(k : ℤ)) * exp (k : ℤ) :=
            mul_le_mul' le_rfl this
        _ = 1 := by rw [← exp_add]; simp
    let a : Fin m → 𝔬 := fun i => toO v (c * (x : Fin m → Fv) i) (hcx i)
    let c₀ : 𝔬 := toO v c hcle
    have hs : ∀ {k : ℕ} (r : 𝔬) (y : Fin k → Fv), r • y = (r : Fv) • y := fun r y => by ext i; rfl
    have hcc : ((c₀ * c₀ : 𝔬) : Fv) = c * c := rfl
    have ha : ∀ i, (a i : Fv) = c * (x : Fin m → Fv) i := fun i => rfl
    have hΛid : (c₀ * c₀) • x = ∑ i, a i • e i := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_sum, hs, hcc, ha]
      ext j
      simp [Finset.sum_apply, Pi.single_apply, e]
      ring
    have h1 : (c * c) • (f x : Fin n → Fv) = ∑ i, (c * (x : Fin m → Fv) i) • (f (e i) : Fin n → Fv) := by
      have := congrArg (fun z : Λ => (f z : Fin n → Fv)) hΛid
      simp only [map_smul, map_sum, Submodule.coe_smul, Submodule.coe_sum, hs, hcc, ha] at this
      exact this
    have h3 : ∑ i, (c * (x : Fin m → Fv) i) • (Pi.single i c : Fin m → Fv) = (c * c) • (x : Fin m → Fv) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
      ring
    have h2 : ∑ i, (c * (x : Fin m → Fv) i) • (f (e i) : Fin n → Fv) = (c * c) • g (x : Fin m → Fv) :=
      calc ∑ i, (c * (x : Fin m → Fv) i) • (f (e i) : Fin n → Fv)
          = ∑ i, (c * (x : Fin m → Fv) i) • g (Pi.single i c) := by simp_rw [hgs]
        _ = g (∑ i, (c * (x : Fin m → Fv) i) • (Pi.single i c : Fin m → Fv)) := by
          simp [map_sum, map_smul]
        _ = (c * c) • g (x : Fin m → Fv) := by rw [h3, map_smul]
    have h4 := h1.trans h2
    exact (smul_right_injective _ (mul_ne_zero hc0 hc0) h4).symm
  have hne : ∀ (x : Fin m → Fv), ∃ N : ℕ, ϖk v (N : ℤ) • x ∈ Λ := fun x =>
    (exists_smul_mem_ball v x k).imp fun N hN => hk1 hN
  refine ⟨g, hext, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨N, hN⟩ := hne x
    have h0 : g (ϖk v (N : ℤ) • x) = 0 := by rw [map_smul, hx, smul_zero]
    have h5 := hext ⟨_, hN⟩
    simp only at h5
    rw [h0] at h5
    have h6 : (⟨_, hN⟩ : Λ) = 0 := hfi (Subtype.ext (by simpa using h5.symm))
    have h7 : ϖk v (N : ℤ) • x = 0 := congrArg Subtype.val h6
    exact (smul_eq_zero.mp h7).resolve_left (ϖk_ne_zero v _)
  · intro x
    obtain ⟨N, hN⟩ := hne x
    have h5 := hf ⟨_, hN⟩
    rw [← hext ⟨_, hN⟩] at h5
    simp only at h5
    rw [map_smul, QuadraticMap.map_smul, QuadraticMap.map_smul] at h5
    exact smul_right_injective _ (mul_ne_zero (ϖk_ne_zero v _) (ϖk_ne_zero v _)) h5

end LocalExtension

/-! ### Step 2: matrices of global isometries -/

section Transfer

variable {F : Type} [Field F] [NumberField F] {m n : ℕ}

/-- Two square matrices with the same bilinear form are equal. -/
theorem matrix_eq_of_dot (A B : Matrix (Fin m) (Fin m) F)
    (h : ∀ x y, x ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ (B *ᵥ y)) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one] using this

/-- **The matrix of an isometry:** if $\sigma$ is an isometry $Q_U \to Q_V$ over $F$ with matrix $S$, then
$S^{\mathsf T} H_V S = H_U$ for the Hessians. -/
theorem hessian_transpose_mul (QU : QuadForm F m) (QV : QuadForm F n)
    (σ : QU.toQuadraticFormIn F →qᵢ QV.toQuadraticFormIn F) :
    (LinearMap.toMatrix' σ.toLinearMap)ᵀ * QV.hessian * LinearMap.toMatrix' σ.toLinearMap = QU.hessian := by
  set S := LinearMap.toMatrix' σ.toLinearMap with hSdef
  have hσ : ∀ x, QV.evalIn F (S *ᵥ x) = QU.evalIn F x := by
    intro x
    have := σ.map_app x
    rw [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply] at this
    rw [hSdef, LinearMap.toMatrix'_mulVec]
    exact this
  have polarF : ∀ (k : ℕ) (Q : QuadForm F k) (x y : Fin k → F),
      Q.evalIn F (x + y) - Q.evalIn F x - Q.evalIn F y = x ⬝ᵥ (Q.hessian *ᵥ y) := by
    intro k Q x y
    have := QuadForm.polar_eq_hessian F Q x y
    simpa using this
  refine matrix_eq_of_dot _ _ fun x y => ?_
  rw [← polarF, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    ← polarF, ← hσ, ← hσ x, ← hσ y, ← mulVec_add]

/-- If $S^{\mathsf T} H_V S = H_U$ over $F$, then $x \mapsto S x$ is an isometry $Q_U \to Q_V$ over every field
$K \supseteq F$ of characteristic $0$. -/
theorem evalIn_mulVec_map (K : Type) [Field K] [CharZero K] [Algebra F K] (QU : QuadForm F m)
    (QV : QuadForm F n) (S : Matrix (Fin n) (Fin m) F)
    (hS : Sᵀ * QV.hessian * S = QU.hessian) (y : Fin m → K) :
    QV.evalIn K (S.map (algebraMap F K) *ᵥ y) = QU.evalIn K y := by
  apply mul_left_cancel₀ (two_ne_zero : (2 : K) ≠ 0)
  rw [two_mul_evalIn, two_mul_evalIn]
  have : QU.hessian.map (algebraMap F K) =
      (S.map (algebraMap F K))ᵀ * QV.hessian.map (algebraMap F K) * S.map (algebraMap F K) := by
    rw [← hS]; simp [Matrix.map_mul, Matrix.transpose_map]
  rw [this]
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- If $S^{\mathsf T} H_V S = H_U$ with $Q_U$ nondegenerate, then $x \mapsto S x$ is injective over every field
$K \supseteq F$ of characteristic $0$. -/
theorem mulVec_map_injective (K : Type) [Field K] [CharZero K] [Algebra F K] (QU : QuadForm F m)
    (QV : QuadForm F n) (hU : QU.Nondegenerate) (S : Matrix (Fin n) (Fin m) F)
    (hS : Sᵀ * QV.hessian * S = QU.hessian) :
    Function.Injective (Matrix.mulVecLin (S.map (algebraMap F K))) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hdet : (QU.hessian.map (algebraMap F K)).det ≠ 0 := by
    rw [show (QU.hessian.map (algebraMap F K)).det = algebraMap F K QU.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ (algebraMap F K).injective).mpr hU
  have : QU.hessian.map (algebraMap F K) =
      (S.map (algebraMap F K))ᵀ * QV.hessian.map (algebraMap F K) * S.map (algebraMap F K) := by
    rw [← hS]; simp [Matrix.map_mul, Matrix.transpose_map]
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  rw [Matrix.mulVecLin_apply] at hy
  rw [this]
  simp [← mulVec_mulVec, hy]

end Transfer

/-! ### Step 3: Witt's extension -/

section Witt

variable {F : Type} [Field F] [NumberField F] {m n : ℕ}

/-- **Witt's extension in matrix form:** let $A : K^m \to K^n$ be an injective isometry $Q_U \to Q_V$ and
$g : K^m \to K^n$ another one, with $Q_V$ nondegenerate. Then there is $\tau \in O(V)(K)$ with
$\tau A x = g x$ for all $x$ (extend $A x \mapsto g x$ from the image of $A$ to $K^n$). -/
theorem exists_orth_extend {K : Type} [Field K] [CharZero K] [Algebra F K] (QU : QuadForm F m)
    (QV : QuadForm F n) (hV : QV.Nondegenerate) (A : Matrix (Fin n) (Fin m) K)
    (hAi : Function.Injective (Matrix.mulVecLin A))
    (hA : ∀ y, QV.evalIn K (A *ᵥ y) = QU.evalIn K y)
    (g : (Fin m → K) →ₗ[K] (Fin n → K)) (hgi : Function.Injective g)
    (hg : ∀ y, QV.evalIn K (g y) = QU.evalIn K y) :
    ∃ τ ∈ orthGroup QV K, ∀ y, τ.val *ᵥ (A *ᵥ y) = g y := by
  set q := QV.toQuadraticFormIn K with hqdef
  have hq := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn K hV
  let e := LinearEquiv.ofInjective (Matrix.mulVecLin A) hAi
  let σ' : LinearMap.range (Matrix.mulVecLin A) →ₗ[K] (Fin n → K) := g ∘ₗ e.symm.toLinearMap
  have hσi : Function.Injective σ' := hgi.comp e.symm.injective
  have he : ∀ y, ((e y : LinearMap.range (Matrix.mulVecLin A)) : Fin n → K) = A *ᵥ y := fun y => rfl
  have hσ : ∀ w, q (σ' w) = q w := by
    intro w
    obtain ⟨y, rfl⟩ := e.surjective w
    simp only [σ', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [he, hqdef, QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply, hg, hA]
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate q hq σ' hσi hσ
  have hφ : ∀ w, q w = QV.evalIn K ((LinearEquiv.refl K (Fin n → K)) w) := fun w => by
    rw [hqdef, QuadForm.toQuadraticFormIn_apply]; rfl
  refine ⟨Tamagawa.SiegelSpace.coordOrth hφ ρ, (Tamagawa.SiegelSpace.coordOrth hφ ρ).2, fun y => ?_⟩
  have h1 := Tamagawa.SiegelSpace.coordOrth_mulVec hφ ρ (A *ᵥ y)
  have h2 := hρ (e y)
  simp only [LinearEquiv.refl_apply] at h1
  rw [h1]
  have : ρ (A *ᵥ y) = σ' (e y) := h2
  rw [this]
  simp [σ']

end Witt

/-! ### Step 4: local data at one place -/

section LocalData

variable {F : Type} [Field F] [NumberField F] {m n : ℕ}

/-- The coordinatewise embedding commutes with rectangular matrices. -/
theorem locVec_mulVec_rect'(v : HeightOneSpectrum (𝓞 F)) (Mb : Matrix (Fin n) (Fin m) F) (t : Fin m → F) :
    locVec v (Mb *ᵥ t) = Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ locVec v t := by
  funext i
  simp only [locVec_apply, mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

/-- A local representation of lattices gives a local representation of spaces. -/
theorem exists_local_extension (QU : QuadForm F m) (QV : QuadForm F n)
    (v : HeightOneSpectrum (𝓞 F)) {L : Submodule (𝓞 F) (Fin m → F)} (hL : L.IsLattice F)
    {M : Submodule (𝓞 F) (Fin n → F)} (h : LocLatRep v QU QV L M) :
    ∃ g : (Fin m → v.adicCompletion F) →ₗ[v.adicCompletion F] (Fin n → v.adicCompletion F),
      (∃ f : loc v L →ₗ[v.adicCompletionIntegers F] loc v M, ∀ x : loc v L, g x = f x) ∧
      Function.Injective g ∧ ∀ x, QV.evalIn (v.adicCompletion F) (g x) = QU.evalIn (v.adicCompletion F) x := by
  obtain ⟨f, hfi, hf⟩ := h
  obtain ⟨g, hg1, hgi, hgq⟩ := exists_extension v (loc_isLattice v hL) _ _ f hfi hf
  refine ⟨g, ⟨f, hg1⟩, hgi, fun x => ?_⟩
  have := hgq x
  rwa [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply] at this

theorem isRepresentedBy_of_locLatRep (QU : QuadForm F m) (QV : QuadForm F n)
    (v : HeightOneSpectrum (𝓞 F)) {L : Submodule (𝓞 F) (Fin m → F)} (hL : L.IsLattice F)
    {M : Submodule (𝓞 F) (Fin n → F)} (h : LocLatRep v QU QV L M) :
    OMeara.IsRepresentedBy (QU.toQuadraticFormIn (v.adicCompletion F))
      (QV.toQuadraticFormIn (v.adicCompletion F)) := by
  obtain ⟨g, -, hgi, hgq⟩ := exists_local_extension QU QV v hL h
  exact ⟨⟨g, fun x => by rw [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply]; exact hgq x⟩, hgi⟩

/-- The local isometry of the genus: an element $\tau$ of $O(V)(F_\mathfrak p)$ with $\tau S\,L_\mathfrak p \subseteq M_\mathfrak p$. -/
theorem exists_local_orth (QU : QuadForm F m) (QV : QuadForm F n) (hU : QU.Nondegenerate)
    (hV : QV.Nondegenerate) (S : Matrix (Fin n) (Fin m) F) (hS : Sᵀ * QV.hessian * S = QU.hessian)
    (v : HeightOneSpectrum (𝓞 F)) {L : Submodule (𝓞 F) (Fin m → F)} (hL : L.IsLattice F)
    {M : Submodule (𝓞 F) (Fin n → F)} (h : LocLatRep v QU QV L M) :
    ∃ g ∈ orthGroup QV (v.adicCompletion F),
      ∀ y ∈ loc v L, g.val *ᵥ (S.map (algebraMap F (v.adicCompletion F)) *ᵥ y) ∈ loc v M := by
  obtain ⟨g, ⟨f, hgf⟩, hgi, hgq⟩ := exists_local_extension QU QV v hL h
  obtain ⟨τ, hτ, hτg⟩ := exists_orth_extend (K := v.adicCompletion F) QU QV hV
    (S.map (algebraMap F (v.adicCompletion F))) (mulVec_map_injective _ QU QV hU S hS)
    (evalIn_mulVec_map _ QU QV S hS) g hgi hgq
  refine ⟨τ, hτ, fun y hy => ?_⟩
  rw [hτg, show y = ((⟨y, hy⟩ : loc v L) : Fin m → v.adicCompletion F) from rfl, hgf]
  exact (f _).2

theorem eventually_mulVec_std (S : Matrix (Fin n) (Fin m) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ y ∈ (std v : Submodule (v.adicCompletionIntegers F) (Fin m → v.adicCompletion F)),
        S.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈
          (std v : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) := by
  have : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, v.valuation F (S i j) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_one _
  filter_upwards [this] with v hv y hy i
  rw [neg_zero, exp_zero]
  simp only [mulVec, dotProduct, Matrix.map_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, valued_algebraMap]
  have := hy j
  rw [neg_zero, exp_zero] at this
  exact mul_le_one' (hv i j) this

end LocalData

/-! ### Step 5: Theorem 6.1.3 -/

/-- **Kitaoka 1993, Theorem 6.1.3** (p. 134), for regular spaces over every number field: let $U = (F^m, Q_U)$ and
$V = (F^n, Q_V)$ be regular quadratic spaces over a number field $F$, and $L$, $M$ full lattices on $U$, $V$. If
$L_\mathfrak p \rightarrowtail M_\mathfrak p$ for every finite place $\mathfrak p$ (`LocLatRep`) and $U_w \rightarrowtail V_w$
for every infinite place $w$ (`SpaceRepAt`), then there is a full lattice $N$ on $V$ in the genus of $M$
(`SameGenus`) with $L \rightarrowtail N$ (`LatRep`). For $F = \mathbb Q$ this is `Theorem613` with the added
hypotheses that $Q_U$ and $Q_V$ are nondegenerate. Unconditional: the Hasse principle for representations
(`isRepresentedBy_of_everywhere`) and Witt's extension theorem are proved in the repository.

*Proof:* see the module docstring. -/
@[kb "kitaoka1993" "§6.1, Thm. 6.1.3, p. 134 (regular spaces, every number field)"]
theorem theorem613_of_nondegenerate {F : Type} [Field F] [NumberField F] {m n : ℕ}
    (QU : QuadForm F m) (QV : QuadForm F n) (hU : QU.Nondegenerate) (hV : QV.Nondegenerate)
    (L : Lat F m) (M : Lat F n)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), LocLatRep v QU QV L.1 M.1)
    (hinf : ∀ w : InfinitePlace F, SpaceRepAt w QU QV) :
    ∃ N : Lat F n, SameGenus QV M.1 N.1 ∧ LatRep QU QV L.1 N.1 := by
  classical
  have hglob : OMeara.IsRepresentedBy (QU.toQuadraticFormIn F) (QV.toQuadraticFormIn F) := by
    refine isRepresentedBy_of_everywhere QU QV hU hV ?_
    intro p
    cases p with
    | infinite w => exact hinf w
    | finite v => exact isRepresentedBy_of_locLatRep QU QV v L.2 (hloc v)
  obtain ⟨σ, hσi⟩ := hglob
  set S : Matrix (Fin n) (Fin m) F := LinearMap.toMatrix' σ.toLinearMap with hSdef
  have hσS : ∀ x, σ x = S *ᵥ x := fun x => (LinearMap.toMatrix'_mulVec _ _).symm
  have hS : Sᵀ * QV.hessian * S = QU.hessian := hessian_transpose_mul QU QV σ
  have hlocal : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : GL (Fin n) (v.adicCompletion F),
      g ∈ orthGroup QV (v.adicCompletion F) ∧
      (∀ y ∈ loc v L.1, g.val *ᵥ (S.map (algebraMap F (v.adicCompletion F)) *ᵥ y) ∈ loc v M.1) ∧
      ((∀ y ∈ loc v L.1, S.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ loc v M.1) → g = 1) := by
    intro v
    obtain ⟨g, hg, hgp⟩ := exists_local_orth QU QV hU hV S hS v L.2 (hloc v)
    by_cases hc : ∀ y ∈ loc v L.1, S.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ loc v M.1
    · exact ⟨1, Subgroup.one_mem _, fun y hy => by simpa using hc y hy, fun _ => rfl⟩
    · exact ⟨g, hg, hgp, fun h => absurd h hc⟩
  choose g hg hgp hg1 using hlocal
  let fam : LocFamily F n :=
    { M := fun v => locAct v (g v)⁻¹ (loc v M.1)
      isLattice := fun v => locAct_isLattice _ (loc_isLattice v M.2)
      eventually_std := by
        filter_upwards [loc_eventually_std L.2, loc_eventually_std M.2, eventually_mulVec_std S]
          with v hL hM hS'
        have h1 : g v = 1 := hg1 v fun y hy => by
          rw [hM]; exact hS' y (by rwa [← hL])
        show locAct v (g v)⁻¹ (loc v M.1) = std v
        rw [h1, inv_one, locAct_one, hM] }
  refine ⟨⟨fam.glue, fam.glue_isLattice⟩, fun v => ⟨(g v)⁻¹, Subgroup.inv_mem _ (hg v), ?_⟩, ?_⟩
  · show locAct v (g v)⁻¹ (loc v M.1) = loc v fam.glue
    rw [LocFamily.loc_glue]
  · have hmem : ∀ x ∈ L.1, (σ.toLinearMap.restrictScalars (𝓞 F)) x ∈ fam.glue := by
      intro x hx w
      show locVec w (σ x) ∈ locAct w (g w)⁻¹ (loc w M.1)
      rw [hσS, locVec_mulVec_rect']
      refine ⟨_, hgp w _ (locVec_mem_loc w hx), ?_⟩
      change (g w)⁻¹.val *ᵥ ((g w).val *ᵥ (S.map (algebraMap F (w.adicCompletion F)) *ᵥ locVec w x)) =
        S.map (algebraMap F (w.adicCompletion F)) *ᵥ locVec w x
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    refine ⟨(σ.toLinearMap.restrictScalars (𝓞 F)).restrict hmem, ?_, ?_⟩
    · intro a b hab
      exact Subtype.ext (hσi (congrArg Subtype.val hab))
    · intro x
      have := σ.map_app (x : Fin m → F)
      exact this

end QuadFormsKB.Kitaoka
