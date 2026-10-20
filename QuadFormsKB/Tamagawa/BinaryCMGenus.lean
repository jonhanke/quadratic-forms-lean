import QuadFormsKB.Tamagawa.BinaryCMCoord

/-!
# The genus of the maximal order of $F(\sqrt{-D})$ for $\langle1,D\rangle$

**Layer:** as in `BinaryCMCoord.lean`: $Q = \langle1,D\rangle$ on $F^2$, $E = F(\theta)$, $\theta^2 = -D$, coordinates
$c(x) = x_0 + x_1\theta$, `latE` $= c^{-1}(\mathcal O_E)$.

**Proves**
* `glImage_rotE`: the global rotation by $u$, $N(u) = 1$ (`rotE`), acts on $c^{-1}(A)$ as multiplication by $u$; every proper
  global isometry is such a rotation (`exists_rotE_eq`).
* **`genus_mulMat_mem`**: every lattice $M$ in the genus of `latE` is an $\mathcal O_E$-module ($c(M)$ is a fractional ideal):
  locally $M_\mathfrak p = g\,\mathcal O_{E,\mathfrak p}$ with $g$ a rotation or rotation-reflection, and rotations commute with
  multiplication by $\mathcal O_E$ (`rotMat_mul_rotMat_comm`).
* **`exists_mem_eval_not_mem`**: every lattice in the genus of `latE` represents a $\mathfrak p$-adic unit, at every prime
  $\mathfrak p$ (approximate the image of $1 \in \mathcal O_{E,\mathfrak p}$ under the local isometry).

Source: O'Meara 1963, §§81–82, 102 (localization, genus) [unverified]; Shimura 2010, §4 [unverified].

-/

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne

/-! ### Rotation matrices commute up to conjugation -/

theorem rotMat_mul_rotMat_comm {R : Type*} [CommRing R] (d p q a b s : R) (hs : s ^ 2 = 1) :
    rotMat d p q 1 * rotMat d a b s = rotMat d a b s * rotMat d p (s * q) 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (d * b * q) * hs | linear_combination (-(q * a)) * hs

theorem rotMat_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (d a b s : R) :
    (rotMat d a b s).map f = rotMat (f d) (f a) (f b) (f s) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E)

local notation "QD" => formF (diagForm1 D)

/-! ### Coordinates of elements and global rotations -/

/-- The coordinates of $u \in E$: $u = c(\mathrm{coordOf}\,u)$. -/
def coordOf (u : E) : Fin 2 → F := (coordEquiv S).symm u

theorem cE_coordOf (u : E) : cE S (coordOf S u) = u := (coordEquiv S).apply_symm_apply u

theorem coordOf_cE (x : Fin 2 → F) : coordOf S (cE S x) = x := (coordEquiv S).symm_apply_apply x

theorem dIn_self : dIn D F = dF D := rfl

theorem dIn_map (K : Type*) [Field K] [Algebra F K] : algebraMap F K (dIn D F) = dIn D K := rfl

theorem norm_eq_coordOf (u : E) :
    Algebra.norm F u = coordOf S u 0 ^ 2 + dIn D F * coordOf S u 1 ^ 2 := by
  conv_lhs => rw [← cE_coordOf S u]
  rw [norm_cE]; rfl

theorem normOne_coords {u : E} (hu : Algebra.norm F u = 1) :
    coordOf S u 0 ^ 2 + dIn D F * coordOf S u 1 ^ 2 = 1 := by
  rw [← norm_eq_coordOf, hu]

/-- **The global rotation by $u$**, $N(u) = 1$: $x \mapsto c^{-1}(u\,c(x))$, an element of $SO(V)(F)$. -/
def rotE {u : E} (hu : Algebra.norm F u = 1) : GL (Fin 2) F := rotGL D (normOne_coords S hu) (one_pow 2)

theorem rotE_val {u : E} (hu : Algebra.norm F u = 1) :
    (rotE S hu).val = rotMat (dIn D F) (coordOf S u 0) (coordOf S u 1) 1 := rfl

theorem rotE_mem {u : E} (hu : Algebra.norm F u = 1) : rotE S hu ∈ orthGroup QD F := rotGL_mem D _ _

theorem det_rotE {u : E} (hu : Algebra.norm F u = 1) : (rotE S hu).val.det = 1 :=
  det_rotMat (normOne_coords S hu)

/-- The matrix of multiplication by $\omega \in E$. -/
def mulMat (ω : E) : Matrix (Fin 2) (Fin 2) F := rotMat (dIn D F) (coordOf S ω 0) (coordOf S ω 1) 1

theorem cE_mulMat (ω : E) (y : Fin 2 → F) : cE S (mulMat S ω *ᵥ y) = ω * cE S y := by
  rw [mulMat, cE_rotMat]
  congr 1
  conv_rhs => rw [← cE_coordOf S ω]
  congr 1; ext i; fin_cases i <;> rfl

theorem cE_rotE_mulVec {u : E} (hu : Algebra.norm F u = 1) (y : Fin 2 → F) :
    cE S ((rotE S hu).val *ᵥ y) = u * cE S y := cE_mulMat S u y

/-- **Rotations act on lattices of submodules of $E$ by multiplication:** $\gamma_u\,c^{-1}(A) = c^{-1}(uA)$. -/
theorem glImage_rotE {u : E} (hu : Algebra.norm F u = 1) (A : Submodule (𝓞 F) E) :
    glImage (rotE S hu) (latOf S A) = latOf S (smulLat u A) := by
  ext x
  rw [mem_glImage, mem_latOf, mem_smulLat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨cE S y, hy, (cE_rotE_mulVec S hu y).symm⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨coordOf S a, by rw [mem_latOf, cE_coordOf]; exact ha, cE_injective S ?_⟩
    rw [cE_rotE_mulVec, cE_coordOf, hax]

/-- **Every proper global isometry is a rotation** $\gamma_u$, $u = c(\gamma e_0)$. -/
theorem exists_rotE_eq {γ : GL (Fin 2) F} (hγ : γ ∈ orthGroup QD F) (hdet : γ.val.det = 1) :
    ∃ (u : E) (hu : Algebra.norm F u = 1), rotE S hu = γ := by
  obtain ⟨e1, -, e3, -⟩ := orth_diag D S.D_ne hγ
  set u := cE S ![γ.val 0 0, γ.val 1 0]
  have hc : coordOf S u = ![γ.val 0 0, γ.val 1 0] := coordOf_cE S _
  have hu : Algebra.norm F u = 1 := by
    rw [norm_eq_coordOf, hc]; simpa using e3
  refine ⟨u, hu, Units.ext ?_⟩
  rw [rotE_val, hc, e1, hdet]
  rfl

/-! ### The genus of `latE` consists of $\mathcal O_E$-modules -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Localization preserves stability under a matrix:** if $A L \subseteq L$ then $A L_\mathfrak p \subseteq L_\mathfrak p$. -/
theorem mulVec_mem_loc {n : ℕ} {L : Submodule (𝓞 F) (Fin n → F)} {A : Matrix (Fin n) (Fin n) F}
    (hA : ∀ x ∈ L, A *ᵥ x ∈ L) {y : Fin n → Fv} (hy : y ∈ loc v L) :
    A.map (algebraMap F Fv) *ᵥ y ∈ loc v L := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← locVec_mulVec]
    exact locVec_mem_loc v (hA x hx)
  | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c m _ hm =>
    rw [show (c • m : Fin n → Fv) = (c : Fv) • m from rfl, mulVec_smul]
    exact Submodule.smul_mem _ c hm

theorem mulMat_mem_latE {ω : E} (hω : IsIntegral ℤ ω) {x : Fin 2 → F} (hx : x ∈ latE S) :
    mulMat S ω *ᵥ x ∈ latE S := by
  rw [mem_latE] at hx ⊢
  rw [cE_mulMat]
  exact hω.mul hx

theorem mulMat_map (ω : E) :
    (mulMat S ω).map (algebraMap F Fv) =
      rotMat (dIn D Fv) (algebraMap F Fv (coordOf S ω 0)) (algebraMap F Fv (coordOf S ω 1)) 1 := by
  rw [mulMat, rotMat_map, map_one]; rfl

theorem std_le_loc_latE : (std v : Submodule _ (Fin 2 → Fv)) ≤ loc v (latE S) := by
  rw [← loc_intVec]; exact loc_mono v (intVec_le_latE S)

theorem e0_mem_std : (![1, 0] : Fin 2 → Fv) ∈ std v := by
  intro i; fin_cases i <;> simp

end Local

/-- **Lattices in the genus of `latE` are $\mathcal O_E$-modules:** $M \in \mathrm{gen}(\mathcal O_E)$, $\omega \in \mathcal O_E$
$\Rightarrow$ $\omega\,c(M) \subseteq c(M)$. *Proof:* locally $M_\mathfrak p = g\,\mathcal O_{E,\mathfrak p}$, $g = \mathrm{rotMat}(a,b,s)$
(`orth_diag`), and $m_\omega g = g\,m_{\omega'}$ with $\omega' = \omega$ ($s = 1$) or $\sigma\omega$ ($s = -1$). -/
theorem genus_mulMat_mem {M : Submodule (𝓞 F) (Fin 2 → F)} (hML : M.IsLattice F)
    (hM : SameGenus QD (latE S) M) {ω : E} (hω : IsIntegral ℤ ω) {x : Fin 2 → F} (hx : x ∈ M) :
    mulMat S ω *ᵥ x ∈ M := by
  rw [mem_iff_forall_loc hML]
  intro v
  obtain ⟨g, hg, hgM⟩ := hM v
  have hxv : locVec v x ∈ loc v M := locVec_mem_loc v hx
  rw [← hgM] at hxv
  obtain ⟨y, hy, hyx⟩ := mem_locAct.mp hxv
  obtain ⟨e1, -, -, e4⟩ := orth_diag D S.D_ne hg
  -- the conjugated multiplier
  have key : ∀ ω' : E, IsIntegral ℤ ω' →
      (mulMat S ω).map (algebraMap F (v.adicCompletion F)) * g.val =
        g.val * (mulMat S ω').map (algebraMap F (v.adicCompletion F)) →
      locVec v (mulMat S ω *ᵥ x) ∈ loc v M := by
    intro ω' hω' hcomm
    rw [locVec_mulVec, ← hyx, mulVec_mulVec, hcomm, ← mulVec_mulVec, ← hgM]
    exact mem_locAct.mpr ⟨_, mulVec_mem_loc v (fun z hz => mulMat_mem_latE S hω' hz) hy, rfl⟩
  have hcomm := rotMat_mul_rotMat_comm (dIn D (v.adicCompletion F))
    (algebraMap F (v.adicCompletion F) (coordOf S ω 0)) (algebraMap F (v.adicCompletion F) (coordOf S ω 1))
    (g.val 0 0) (g.val 1 0) g.val.det e4
  rw [← e1, ← mulMat_map] at hcomm
  have hs : g.val.det * g.val.det = 1 := by rw [← sq]; exact e4
  rcases mul_self_eq_one_iff.mp hs with h | h
  · refine key ω hω ?_
    rw [hcomm, h, one_mul, mulMat_map]
  · refine key (conj F E ω) (hω.map (conj F E)) ?_
    rw [hcomm, h, mulMat_map]
    congr 2
    · conv_rhs => rw [← cE_coordOf S ω, conj_cE, coordOf_cE]
      rfl
    · conv_rhs => rw [← cE_coordOf S ω, conj_cE, coordOf_cE]
      simp

/-- **Every lattice in the genus of `latE` represents a $\mathfrak p$-unit**, at every prime $\mathfrak p$: there is $x \in M$ with
$Q(x) = a \in \mathcal O_F \setminus \mathfrak p$. *Proof:* $y_0 = g e_0 \in M_\mathfrak p$ has $Q(y_0) = 1$; approximate $y_0$ by $x \in M$
modulo $\varpi M_\mathfrak p$; then $Q(x) - 1 = \varpi B(y_0, e') + \varpi^2Q(e') \in \mathfrak p\mathfrak o_\mathfrak p$ ($M$ integral). -/
theorem exists_mem_eval_not_mem {M : Submodule (𝓞 F) (Fin 2 → F)} (hML : M.IsLattice F)
    (hM : SameGenus QD (latE S) M) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x ∈ M, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (QD).eval x ∧ a ∉ v.asIdeal := by
  have hMi : IsIntegral QD M := SameGenus.isIntegral QD (isIntegral_latE S) hM
  obtain ⟨g, hg, hgM⟩ := hM v
  set y0 : Fin 2 → v.adicCompletion F := g.val *ᵥ ![1, 0]
  have hy0 : y0 ∈ loc v M := by
    rw [← hgM]; exact mem_locAct.mpr ⟨_, std_le_loc_latE S v (e0_mem_std v), rfl⟩
  have hQy0 : (QD).evalIn (v.adicCompletion F) y0 = 1 := by
    rw [evalIn_mulVec_of_mem QD hg, evalIn_formF_diag]; simp
  obtain ⟨d, hd, h1, -⟩ := exists_global_bounds hML
  obtain ⟨k, hk⟩ := exists_valued_int_eq v hd
  have hball : ball v (k : ℤ) ≤ loc v M := ball_le_loc v h1 hk
  obtain ⟨x, hx, hxe⟩ := exists_mem_approx v hML hy0 ((k : ℤ) + 1)
  set e := locVec v x - y0
  set e' : Fin 2 → v.adicCompletion F := ϖk v (-1) • e
  have he' : e' ∈ loc v M := by
    refine hball fun i => ?_
    show Valued.v (ϖk v (-1) * e i) ≤ exp (-(k : ℤ))
    rw [map_mul, valued_ϖk]
    calc exp (-(-1 : ℤ)) * Valued.v (e i) ≤ exp (-(-1 : ℤ)) * exp (-((k : ℤ) + 1)) :=
          mul_le_mul_right (hxe i) _
      _ = exp (-(k : ℤ)) := by rw [← exp_add]; congr 1; ring
  have hee : e = ϖk v 1 • e' := by
    rw [smul_smul, ϖk_mul]; simp
  have hxdec : locVec v x = y0 + ϖk v 1 • e' := by rw [← hee]; simp [e]
  obtain ⟨a, ha⟩ := hMi x hx
  refine ⟨x, hx, a, ha, fun hav => ?_⟩
  -- Q(x) ≡ 1 mod 𝔭
  have hpolar : ∀ y z : Fin 2 → v.adicCompletion F, (QD).evalIn (v.adicCompletion F) (y + z) =
      (QD).evalIn _ y + (QD).evalIn _ z + bilR QD (v.adicCompletion F) y z := by
    intro y z
    have h := QuadForm.polar_eq_hessian (v.adicCompletion F) QD y z
    rw [bilR, ← h]; ring
  have hQx : (QD).evalIn (v.adicCompletion F) (locVec v x) =
      1 + (ϖk v 1) ^ 2 * (QD).evalIn _ e' + ϖk v 1 * bilR QD (v.adicCompletion F) y0 e' := by
    rw [hxdec, hpolar, hQy0, evalIn_smul']
    congr 1
    rw [bilR, bilR, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hval : Valued.v ((QD).evalIn (v.adicCompletion F) (locVec v x) - 1) < 1 := by
    rw [hQx, show 1 + ϖk v 1 ^ 2 * (QD).evalIn (v.adicCompletion F) e' +
        ϖk v 1 * bilR QD (v.adicCompletion F) y0 e' - 1 =
        ϖk v 1 * (ϖk v 1 * (QD).evalIn (v.adicCompletion F) e' + bilR QD (v.adicCompletion F) y0 e') by ring,
      map_mul, valued_ϖk]
    have h2 : Valued.v (ϖk v 1 * (QD).evalIn (v.adicCompletion F) e' + bilR QD (v.adicCompletion F) y0 e') ≤ 1 := by
      refine Valuation.map_add_le _ ?_ (valued_bilR_loc_le_one QD v hMi hy0 he')
      rw [map_mul, valued_ϖk]
      exact mul_le_one' (by rw [← exp_zero, exp_le_exp]; omega) (valued_evalIn_loc_le_one QD v hMi he')
    calc exp (-(1 : ℤ)) * Valued.v (ϖk v 1 * (QD).evalIn (v.adicCompletion F) e' +
          bilR QD (v.adicCompletion F) y0 e') ≤ exp (-(1 : ℤ)) * 1 := mul_le_mul_right h2 _
      _ < 1 := by rw [mul_one, ← exp_zero, exp_lt_exp]; omega
  rw [evalIn_locVec, show (QD).eval x = algebraMap (𝓞 F) F a from ha.symm, ← IsScalarTower.algebraMap_apply, ← map_one (algebraMap (𝓞 F) _), ← map_sub,
    valued_algebraMap_int] at hval
  have h1mem : a - 1 ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem _).mp hval
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem hav h1mem
    simpa using this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

end QuadFormsKB.Tamagawa.BinaryCM
