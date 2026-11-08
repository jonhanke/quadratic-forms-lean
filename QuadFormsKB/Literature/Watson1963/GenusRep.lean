/-
# Watson (1963), §4: a form of the genus represents what is represented locally

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576.

**Layer:** integer-valued positive definite forms $f$ in $n$ variables and $\varphi$ in $v$ variables
(`QuadForm ℤ n`, `QuadForm ℤ v`, `IntQF.PosDef`); the genus `Siegel.SameGenus`; representations of forms by forms
`Rep` (over $\mathbb Z$) and `RepOver` (over a commutative ring, here $\mathbb Z_p$) of `Watson1963/Perfect.lean`.

**Proves** (the base of Watson 1963, Lemma 2, §4, p. 555; O'Meara 1963, 102:5; Watson, *Integral Quadratic Forms*, 1960,
Theorem 40):
* `exists_sameGenus_rep`: if $f$ represents $\varphi$ over $\mathbb Z_p$ for every prime $p$, then some form $f'$ of the
  genus of $f$ represents $\varphi$ over $\mathbb Z$;
* `rep_of_encard_le_one`: if moreover the genus of $f$ consists of one class, $f$ itself represents $\varphi$ over
  $\mathbb Z$.

*Proof.* (1) The local-global principle for representations of forms over $\mathbb Q$ (`Frames.rep_of_local_forms`)
gives a rational matrix $X$ with $f(X\vec y) = \varphi(\vec y)$. (2) Let $K \subseteq \mathbb Q^n$ be the
$\mathbb Z$-span of the columns of $X$. At each prime $p$ the local integral representation $Y_p$ and $X$ are two
representations of the nondegenerate form $\varphi$, so Witt's theorem (several vectors, `exists_orthGroup_mulVec_eq`,
from Mathlib's `QuadraticForm` Witt extension theorem of this library) gives $g_p \in O(f)(\mathbb Q_p)$ with
$g_pY_p = X$; hence $K_p \subseteq g_p(\mathbb Z_p^n)$. (3) O'Meara 102:5 (`Lattices.exists_sameGenus_le`) gives a lattice
$L'$ in the genus of $\mathbb Z^n$ containing $K$. (4) $L' = \gamma\mathbb Z^n$ is free (class number one of $\mathbb Z$),
its Gram form $f'$ lies in the genus of $f$, and the columns of $X$ in $L'$ give an integral matrix $H$ with
$f'(H\vec y) = \varphi(\vec y)$.

The hypothesis is only at the finite primes: positive definiteness takes care of the real place.
-/
import QuadFormsKB.Literature.Watson1963.Perfect
import QuadFormsKB.Literature.OMeara.Sec102Rep
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Tamagawa.FrameHM
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Witt.Bridge

open Matrix NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n v : ℕ}

/-! ### Witt's theorem for several vectors -/

/-- **Witt's theorem for several vectors, in matrix form** (O'Meara 1963, 42:17). Let $K$ be a field of characteristic
$0$ containing $\mathbb Q$, $Q$ a nondegenerate form over $\mathbb Q$ in $n$ variables and $T$ a nondegenerate form over
$\mathbb Q$ in $m$ variables. If $X, Y \in K^{n\times m}$ both represent $T$, that is $Q(X\vec y) = T(\vec y) = Q(Y\vec y)$
for all $\vec y \in K^m$, then $gY = X$ for some $g \in O(Q)(K)$ (`Lattices.orthGroup`), in the form
$g(Y\vec y) = X\vec y$. Arguments: `Q`, `hQ` (nondegeneracy of `Q`), `T`, `hT`, the matrices `X`, `Y` and their
representation hypotheses `hX`, `hY`. (Nondegeneracy of $T$ makes $X$ and $Y$ injective, so $Y\vec y \mapsto X\vec y$ is
a well defined isometric embedding of the column space of $Y$, which extends to $K^n$.) -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem, several vectors)"]
theorem exists_orthGroup_mulVec_eq {K : Type} [Field K] [CharZero K] [Algebra ℚ K] (Q : QuadForm ℚ n)
    (hQ : Q.Nondegenerate) {m : ℕ} (T : QuadForm ℚ m) (hT : T.Nondegenerate)
    (X Y : Matrix (Fin n) (Fin m) K)
    (hX : ∀ y, Q.evalIn K (X *ᵥ y) = T.evalIn K y) (hY : ∀ y, Q.evalIn K (Y *ᵥ y) = T.evalIn K y) :
    ∃ g ∈ Lattices.orthGroup Q K, ∀ y, g.val *ᵥ (Y *ᵥ y) = X *ᵥ y := by
  have hinjAll : ∀ Z : Matrix (Fin n) (Fin m) K, (∀ y, Q.evalIn K (Z *ᵥ y) = T.evalIn K y) →
      Function.Injective Z.mulVecLin := by
    intro Z hZ
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := (Tamagawa.Frames.compMat_map_iff Q T Z).mpr hZ
    have h2 := congrArg QuadForm.hessian h1
    rw [QuadForm.hessian_compMat] at h2
    have hdet : (T.map (algebraMap ℚ K)).hessian.det ≠ 0 := by
      have : (T.map (algebraMap ℚ K)).hessian = T.hessian.map (algebraMap ℚ K) := by
        ext i j; simp [QuadForm.hessian, QuadForm.map]
      rw [this, show (T.hessian.map (algebraMap ℚ K)).det = algebraMap ℚ K T.hessian.det from
        (RingHom.map_det _ _).symm]
      exact (map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr hT
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    rw [← h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have : Z *ᵥ y = 0 := hy
    rw [this]; simp
  have hinj := hinjAll Y hY
  let V := Fin n → K
  let QF : QuadraticForm K V := Q.toQuadraticFormIn K
  have hQF : (QuadraticMap.polarBilin QF).Nondegenerate :=
    QuadForm.nondegenerate_polarBilin_toQuadraticFormIn K hQ
  let e := LinearEquiv.ofInjective Y.mulVecLin hinj
  let σ : (LinearMap.range Y.mulVecLin) →ₗ[K] V := X.mulVecLin ∘ₗ e.symm.toLinearMap
  have hσi : Function.Injective σ := by
    intro a b hab
    exact e.symm.injective (hinjAll X hX hab)
  have hσ : ∀ w, QF (σ w) = QF w := by
    intro w
    obtain ⟨y, rfl⟩ := e.surjective w
    have e1 : σ (e y) = X *ᵥ y := by simp [σ]; rfl
    have e2 : ((e y : LinearMap.range Y.mulVecLin) : V) = Y *ᵥ y := rfl
    rw [e1, e2]
    show Q.toQuadraticFormIn K (X *ᵥ y) = Q.toQuadraticFormIn K (Y *ᵥ y)
    rw [QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply, hX, hY]
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate QF hQF σ hσi hσ
  let g : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' ρ.toLinearEquiv.toLinearMap
  let gi : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' ρ.toLinearEquiv.symm.toLinearMap
  have hg1 : g * gi = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : ρ.toLinearEquiv.toLinearMap ∘ₗ ρ.toLinearEquiv.symm.toLinearMap = LinearMap.id := by
      exact LinearMap.ext fun x => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hg2 : gi * g = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : ρ.toLinearEquiv.symm.toLinearMap ∘ₗ ρ.toLinearEquiv.toLinearMap = LinearMap.id := by
      exact LinearMap.ext fun x => by simp
    rw [this, LinearMap.toMatrix'_id]
  let G : GL (Fin n) K := ⟨g, gi, hg1, hg2⟩
  have hGv : ∀ x, G.val *ᵥ x = ρ x := fun x => by
    show g *ᵥ x = _
    simp [g, LinearMap.toMatrix'_mulVec]
  refine ⟨G, ?_, fun y => ?_⟩
  · refine Lattices.mem_orthGroup_of_evalIn Q fun z => ?_
    rw [hGv]
    have := ρ.map_app z
    change QF (ρ z) = QF z at this
    have h1 : ∀ x, QF x = Q.evalIn K x := fun x => QuadForm.toQuadraticFormIn_apply K Q x
    rw [h1, h1] at this
    exact this
  · rw [hGv]
    have := hρ ⟨Y *ᵥ y, ⟨y, rfl⟩⟩
    rw [show (⟨Y *ᵥ y, ⟨y, rfl⟩⟩ : LinearMap.range Y.mulVecLin) = e y from rfl] at this
    rw [show Y *ᵥ y = ((e y : LinearMap.range Y.mulVecLin) : V) from rfl, this]
    simp only [σ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl

/-! ### Representations of forms and base change -/

/-- The value of an integral form $f$ at a vector over a field $K \supseteq \mathbb Q$ is the value of its base change to
$\mathbb Q$. Arguments: the form `f` and the vector `y`. -/
theorem evalIn_rat_eq (f : QuadForm ℤ n) {K : Type*} [Field K] [Algebra ℚ K] (y : Fin n → K) :
    (f.map (Int.castRingHom ℚ)).evalIn K y = f.evalIn K y := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- The value of an integral form $f$ over a commutative ring $R$ is the value of $f \otimes R$:
$f(\vec x) = (f \otimes R)(\vec x)$. -/
theorem evalIn_int_eq_eval_map (R : Type*) [CommRing R] {m : ℕ} (f : QuadForm ℤ m) (x : Fin m → R) :
    f.evalIn R x = (f.map (Int.castRingHom R)).eval x := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- **Base change of a representation of forms.** If $f(H\vec y) = \varphi(\vec y)$ for all $\vec y \in S^v$, then
$f((\psi H)\vec y) = \varphi(\vec y)$ for all $\vec y \in T^v$, for every ring homomorphism $\psi : S \to T$ (here
$\psi H$ is the entrywise image). Arguments: `ψ`, the matrix `H` with its identity `hH`, and the vector `y` over `T`.
(The identity over $S$ is an identity of forms, `QuadForm.eq_of_eval_eq`, which transports along $\psi$.) -/
theorem evalIn_map_mulVec {S T : Type*} [CommRing S] [CommRing T] (ψ : S →+* T) {f : QuadForm ℤ n}
    {φ : QuadForm ℤ v} {H : Matrix (Fin n) (Fin v) S} (hH : ∀ y, f.evalIn S (H *ᵥ y) = φ.evalIn S y)
    (y : Fin v → T) : f.evalIn T (H.map ψ *ᵥ y) = φ.evalIn T y := by
  have h1 : (f.map (Int.castRingHom S)).compMat H = φ.map (Int.castRingHom S) :=
    QuadForm.eq_of_eval_eq fun y => by
      rw [QuadForm.eval_compMat, ← evalIn_int_eq_eval_map, ← evalIn_int_eq_eval_map]; exact hH y
  have h2 := QuadForm.map_compMat ψ (f.map (Int.castRingHom S)) H
  rw [h1] at h2
  have mm : ∀ {m : ℕ} (Q : QuadForm ℤ m), (Q.map (Int.castRingHom S)).map ψ = Q.map (Int.castRingHom T) :=
    fun Q => by ext i j; simp [QuadForm.map]
  rw [mm, mm] at h2
  rw [evalIn_int_eq_eval_map, evalIn_int_eq_eval_map, ← QuadForm.eval_compMat, h2]

/-- **Positive definite integral forms are totally positive definite over $\mathbb Q$.** -/
theorem isTotallyPosDef_map_rat {f : QuadForm ℤ n} (hf : IntQF.PosDef f) :
    Lattices.IsTotallyPosDef (f.map (Int.castRingHom ℚ)) := by
  have := (Tamagawa.RatBridge.isTotallyPosDef_up_iff f).mpr hf
  rwa [Tamagawa.RatBridge.formF_up] at this

/-- Choose the rational prime of a finite place of $\mathbb Q$ and the ring isomorphism
$\mathbb Z_p \to \mathfrak o_w \subseteq \mathbb Q_w$ (as a ring homomorphism into the completion). -/
theorem exists_padic_hom (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (ψ : ℤ_[p] →+* w.adicCompletion ℚ),
      ∀ x, ψ x ∈ w.adicCompletionIntegers ℚ := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (Rat.HeightOneSpectrum.primesEquiv w : ℕ) = p := ⟨_, rfl⟩
  have hF : Fact p.Prime := ⟨hp ▸ (Rat.HeightOneSpectrum.primesEquiv w).2⟩
  obtain ⟨ψ⟩ := Lattices.exists_ringEquiv_padic w p hp
  exact ⟨p, hF, (w.adicCompletionIntegers ℚ).subtype.comp (ψ : ℤ_[p] →+* _), fun x => (ψ x).2⟩

/-- **Local-global principle for representations of positive definite forms over $\mathbb Q$** (O'Meara 1963, 66:3):
if $f$ and $\varphi$ are positive definite and $f$ represents $\varphi$ over every $\mathbb Z_p$, then
$f(X\vec y) = \varphi(\vec y)$ for a rational matrix $X$. Arguments: `hf`, `hφ`, and the local representations `hloc`. -/
theorem exists_rat_rep {f : QuadForm ℤ n} {φ : QuadForm ℤ v} (hf : IntQF.PosDef f) (hφ : IntQF.PosDef φ)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] f φ) :
    ∃ X : Matrix (Fin n) (Fin v) ℚ, ∀ y, f.evalIn ℚ (X *ᵥ y) = φ.evalIn ℚ y := by
  obtain ⟨X, hX⟩ := Tamagawa.Frames.rep_of_local_forms (f.map (Int.castRingHom ℚ))
    (isTotallyPosDef_map_rat hf) (φ.map (Int.castRingHom ℚ)) (isTotallyPosDef_map_rat hφ) (fun w => by
      obtain ⟨p, hp, ψ, -⟩ := exists_padic_hom w
      obtain ⟨H, hH⟩ := hloc p
      refine ⟨H.map ψ, fun y => ?_⟩
      rw [evalIn_rat_eq, evalIn_rat_eq]
      exact evalIn_map_mulVec ψ hH y)
  exact ⟨X, fun y => by rw [← evalIn_rat_eq, ← evalIn_rat_eq]; exact hX y⟩

/-! ### The theorem -/

/-- **A form of the genus represents what is represented locally everywhere** (Watson 1963, §4, proof of Lemma 2;
O'Meara 1963, 102:5; Watson, *Integral Quadratic Forms*, Theorem 40): let $f$ and $\varphi$ be positive definite integral
forms in $n$ and $v$ variables. If $f$ represents $\varphi$ over $\mathbb Z_p$ for every prime $p$
(`RepOver ℤ_[p] f φ`: $f(H_p\vec y) = \varphi(\vec y)$ for an $n \times v$ matrix $H_p$ over $\mathbb Z_p$), then some form
$f'$ in the genus of $f$ represents $\varphi$ over $\mathbb Z$ (`Rep f' φ`). Arguments: `hf`, `hφ` (positive
definiteness of $f$, $\varphi$) and `hloc` (the local representations). -/
@[kb "watson1963" "§4, proof of Lemma 2, p. 555 (representation by a form of the genus)"]
theorem exists_sameGenus_rep {f : QuadForm ℤ n} {φ : QuadForm ℤ v}
    (hf : IntQF.PosDef f) (hφ : IntQF.PosDef φ)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] f φ) :
    ∃ f' : QuadForm ℤ n, SameGenus f f' ∧ Rep f' φ := by
  classical
  obtain ⟨X, hX⟩ := exists_rat_rep hf hφ hloc
  have hQnd : (f.map (Int.castRingHom ℚ)).Nondegenerate := (isTotallyPosDef_map_rat hf).nondegenerate
  have hTnd : (φ.map (Int.castRingHom ℚ)).Nondegenerate := (isTotallyPosDef_map_rat hφ).nondegenerate
  let col : Fin v → (Fin n → ℚ) := fun j i => X i j
  let K : Submodule (𝓞 ℚ) (Fin n → ℚ) := Submodule.span (𝓞 ℚ) (Set.range col)
  have hK : K.FG := Submodule.fg_span (Set.finite_range _)
  -- the local hypothesis of O'Meara 102:5, by Witt's theorem
  have hlocal : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ g ∈ Lattices.orthGroup (f.map (Int.castRingHom ℚ))
      (w.adicCompletion ℚ), Lattices.loc w K ≤
        Lattices.locAct w g (Lattices.loc w (Lattices.stdLat : Lattices.Lat ℚ n).1) := by
    intro w
    obtain ⟨p, hp, ψ, hψ⟩ := exists_padic_hom w
    obtain ⟨H, hH⟩ := hloc p
    have hY : ∀ y, (f.map (Int.castRingHom ℚ)).evalIn (w.adicCompletion ℚ) (H.map ψ *ᵥ y) =
        (φ.map (Int.castRingHom ℚ)).evalIn (w.adicCompletion ℚ) y := fun y => by
      rw [evalIn_rat_eq, evalIn_rat_eq]; exact evalIn_map_mulVec ψ hH y
    have hX' : ∀ y, (f.map (Int.castRingHom ℚ)).evalIn (w.adicCompletion ℚ)
        (X.map (algebraMap ℚ (w.adicCompletion ℚ)) *ᵥ y) =
        (φ.map (Int.castRingHom ℚ)).evalIn (w.adicCompletion ℚ) y := fun y => by
      rw [evalIn_rat_eq, evalIn_rat_eq]
      exact evalIn_map_mulVec (algebraMap ℚ (w.adicCompletion ℚ)) (fun y => by
        rw [← evalIn_rat_eq, ← evalIn_rat_eq]; exact hX y) y
    obtain ⟨g, hg, hgY⟩ := exists_orthGroup_mulVec_eq (f.map (Int.castRingHom ℚ)) hQnd
      (φ.map (Int.castRingHom ℚ)) hTnd _ _ hX' hY
    refine ⟨g, hg, ?_⟩
    have hcol : ∀ j, Lattices.locVec w (col j) ∈
        Lattices.locAct w g (Lattices.loc w (Lattices.stdLat : Lattices.Lat ℚ n).1) := by
      intro j
      have h1 : Lattices.locVec w (col j) = X.map (algebraMap ℚ (w.adicCompletion ℚ)) *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_single_one]; rfl
      rw [h1, ← hgY]
      refine ⟨H.map ψ *ᵥ Pi.single j 1, ?_, rfl⟩
      change _ ∈ Lattices.loc w Lattices.intVec
      rw [Lattices.loc_intVec]
      intro i
      rw [Matrix.mulVec_single_one]
      simpa using (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hψ (H i j))
    rw [Lattices.loc, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (show z ∈ K from hz)
    · rintro _ ⟨j, rfl⟩; exact hcol j
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
    · intro a b _ hb; rw [Lattices.locVec_smul_int]; exact Submodule.smul_mem _ _ hb
  obtain ⟨L', hL', hKL'⟩ := Lattices.exists_sameGenus_le (f.map (Int.castRingHom ℚ))
    (Lattices.stdLat : Lattices.Lat ℚ n) hK hlocal
  have hM' : Lattices.SameGenus (HilbertModular.formF (Tamagawa.RatBridge.up f)) Lattices.intVec L'.1 := by
    rw [Tamagawa.RatBridge.formF_up]; exact hL'
  obtain ⟨γ, hγ, hi⟩ := Tamagawa.RatBridge.exists_free_of_sameGenus f L' hM'
  have hs : Lattices.SameGenus (HilbertModular.formF (Tamagawa.RatBridge.up f)) Lattices.intVec
      (Lattices.latOf γ) := hγ ▸ hM'
  refine ⟨Tamagawa.RatBridge.down (Lattices.gramZ (HilbertModular.formF (Tamagawa.RatBridge.up f)) γ hi),
    Tamagawa.RatBridge.sameGenus_down_gramZ f γ hs hi, ?_⟩
  -- the columns of `X` lie in `L' = γ ℤⁿ`
  have hcolγ : ∀ j, ∃ z : Fin n → 𝓞 ℚ, γ.val *ᵥ Lattices.intCoe z = col j := by
    intro j
    have hmem : col j ∈ Lattices.latOf γ := hγ ▸ hKL' (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨y, hy, hyc⟩ := hmem
    obtain ⟨z, rfl⟩ := Lattices.mem_intVec_iff_exists.mp hy
    exact ⟨z, hyc⟩
  choose z hz using hcolγ
  let Zm : Matrix (Fin n) (Fin v) (𝓞 ℚ) := fun i j => z j i
  let Zq : Matrix (Fin n) (Fin v) ℚ := Zm.map (algebraMap (𝓞 ℚ) ℚ)
  have hγZ : γ.val * Zq = X := by
    ext i j
    have h := congrFun (hz j) i
    rw [Matrix.mul_apply]
    exact h
  refine ⟨Zm.map Tamagawa.RatBridge.eZ, fun y => ?_⟩
  apply Int.cast_injective (α := ℚ)
  let y' : Fin v → 𝓞 ℚ := fun j => Tamagawa.RatBridge.eZ.symm (y j)
  have hH'y : Zm.map Tamagawa.RatBridge.eZ *ᵥ y = fun i => Tamagawa.RatBridge.eZ ((Zm *ᵥ y') i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, y', map_sum, map_mul]
  rw [hH'y, Tamagawa.RatBridge.down_map_eval, Lattices.eZ_cast_eq, Lattices.algebraMap_eval_gramZ]
  have hvec : γ.val *ᵥ Lattices.intCoe (Zm *ᵥ y') = X *ᵥ (fun j => ((y j : ℤ) : ℚ)) := by
    have : Lattices.intCoe (Zm *ᵥ y') = Zq *ᵥ (fun j => ((y j : ℤ) : ℚ)) := by
      funext i
      simp [Lattices.intCoe, Zq, Matrix.mulVec, dotProduct, y',
        map_sum, map_mul]
    rw [this, Matrix.mulVec_mulVec, hγZ]
  rw [hvec, Tamagawa.RatBridge.formF_up]
  refine (evalIn_rat_eq f _).trans ?_
  rw [hX, evalIn_intCast_vec]

/-- **One class in the genus: $f$ itself represents $\varphi$.** If $f$ and $\varphi$ are positive definite, $f$ represents
$\varphi$ over every $\mathbb Z_p$ and the genus of $f$ consists of at most one class of forms
(`(genusClasses f).encard ≤ 1`), then $f$ represents $\varphi$ over $\mathbb Z$. -/
@[kb "watson1963" "§4, proof of Lemma 2, p. 555 (genus of one class)"]
theorem rep_of_encard_le_one {f : QuadForm ℤ n} {φ : QuadForm ℤ v}
    (hf : IntQF.PosDef f) (hφ : IntQF.PosDef φ)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], RepOver ℤ_[p] f φ)
    (h1 : (genusClasses f).encard ≤ 1) : Rep f φ := by
  obtain ⟨f', hg, hr⟩ := exists_sameGenus_rep hf hφ hloc
  have hc := Set.encard_le_one_iff.mp h1 (classOf f') (classOf f) (classOf_mem_genusClasses_iff.mpr hg)
    (classOf_self_mem_genusClasses f)
  exact Rep.of_intEquiv_left (classOf_eq_classOf_iff.mp hc) hr

end QuadFormsKB.Watson1963
