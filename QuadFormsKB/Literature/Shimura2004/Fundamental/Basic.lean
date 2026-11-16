/-
# Shimura 2004, Theorem 11.6: the global lemmas

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §11.4–Theorem 11.6 (printed
pp. 103–105). Notation and dictionary as in `HGenus.lean`: $V = F^n$ over a number field $F$, `Q : QuadForm F n`,
$\varphi[x] = Q(x)$, $\varphi(x, y)$ = `OMeara.bil Q.toQuadraticForm x y`, matrices act on the left.

**Proves** (unconditional; standard axioms only)
* `bil_mulVec_of_mem`, `phiIdeal_image`, `mem_solSetLat_image`: an isometry $\gamma\in O^\varphi(V)$ carries
  $\varphi(x, \Lambda)$ to $\varphi(\gamma x, \gamma\Lambda)$ and $\Lambda[q, \mathfrak b]$ onto
  $(\gamma\Lambda)[q, \mathfrak b]$;
* `exists_so_mulVec_eq`: Witt's theorem for one vector in $SO^\varphi(V)$: if $\varphi[x] = \varphi[h] \ne 0$ and
  $n \ge 2$, then $x = \alpha h$ for some $\alpha \in SO^\varphi(V)$ (two symmetries, then a third one in a vector of
  $(Fh)^\perp$ to make the determinant $1$);
* `locFrac_phiIdeal`: $\varphi(h, \Lambda)_v = \varphi(h, \Lambda_v)$ at every finite prime $v$;
* `phiIdeal_eq_of_mem_hGenus`: every lattice $M$ of the $H$-genus of $L$ has $\varphi(h, M) = \varphi(h, L)$
  (the ideal is local, and $H_{\mathbf h}$ fixes $h$);
* `finite_of_isHGenusCover`: the index set of a minimal family of $G$-class representatives covering the
  $H$-genus is finite (it injects, up to a factor $2$, into the finite set of classes in the genus,
  `ClassFin.genusClasses_finite_nf`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave3.Formula1318
import QuadFormsKB.Literature.OMeara.Sec102Max
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Lattices.SAWeak
import QuadFormsKB.Literature.OMeara.Sec103Five
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- The instance `Invertible (2 : K)` used in the statements of `HGenus.lean` (for a field of characteristic $0$). -/
abbrev invTwo (K : Type*) [Field K] [CharZero K] : Invertible (2 : K) := invertibleOfNonzero two_ne_zero

attribute [local instance] invTwo

/-! ### Isometries, $\varphi(x, \Lambda)$ and $\Lambda[q, \mathfrak b]$ -/

theorem toQuadraticForm_mulVec_of_mem {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) (x : Fin n → F) :
    Q.toQuadraticForm (γ.val *ᵥ x) = Q.toQuadraticForm x := by
  rw [QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply]
  exact evalIn_mulVec_of_mem Q hγ x

/-- An isometry preserves $\varphi(x, y)$. -/
theorem bil_mulVec_of_mem {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) (x y : Fin n → F) :
    OMeara.bil Q.toQuadraticForm (γ.val *ᵥ x) (γ.val *ᵥ y) = OMeara.bil Q.toQuadraticForm x y := by
  simp only [OMeara.bil, QuadraticMap.associated_apply, ← mulVec_add,
    toQuadraticForm_mulVec_of_mem Q hγ]

/-- **$\varphi(\gamma x, \gamma\Lambda) = \varphi(x, \Lambda)$** for $\gamma \in O^\varphi(V)$. -/
theorem phiIdeal_image {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) (x : Fin n → F) (Λ : Lat F n) :
    phiIdeal Q.toQuadraticForm (γ.val *ᵥ x) (Lat.image γ Λ).1 = phiIdeal Q.toQuadraticForm x Λ.1 := by
  unfold phiIdeal
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (bil_mulVec_of_mem Q hγ x y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨γ.val *ᵥ y, ⟨y, hy, rfl⟩, bil_mulVec_of_mem Q hγ x y⟩

/-- **$\gamma(\Lambda[q, \mathfrak b]) \subseteq (\gamma\Lambda)[q, \mathfrak b]$** for $\gamma \in O^\varphi(V)$. -/
theorem mem_solSetLat_image {γ : GL (Fin n) F} (hγ : γ ∈ orthGroup Q F) {Λ : Lat F n} {q : F}
    {b : Submodule (𝓞 F) F} {x : Fin n → F} (hx : x ∈ solSetLat Q Λ q b) :
    γ.val *ᵥ x ∈ solSetLat Q (Lat.image γ Λ) q b := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · change Q.toQuadraticForm (γ.val *ᵥ x) = q
    rw [toQuadraticForm_mulVec_of_mem Q hγ]; exact h1
  · change phiIdeal Q.toQuadraticForm (γ.val *ᵥ x) (Lat.image γ Λ).1 = b
    rw [phiIdeal_image Q hγ]; exact h2

/-! ### Witt's theorem for one vector, in $SO^\varphi(V)$ -/

/-- A nondegenerate form in $n \ge 2$ variables has, for every $h$ with $\varphi[h] \ne 0$, an anisotropic vector
orthogonal to $h$. -/
theorem exists_anisotropic_perp_bil (hQ : Q.Nondegenerate) (hn : 2 ≤ n) {h : Fin n → F}
    (hh : Q.eval h ≠ 0) :
    ∃ w : Fin n → F, OMeara.bil Q.toQuadraticForm h w = 0 ∧ Q.eval w ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := exists_perp_aniso Q hQ hn hh
  refine ⟨w, ?_, hw0⟩
  rw [Sec103Five.bil_eq_hessian]
  have : qbil Q F h w = h ⬝ᵥ (Q.hessian *ᵥ w) := by
    simp [qbil, ClassFin.hessian_map_id]
  rw [← this, hw, zero_div]

/-- **Witt's theorem for one vector, in $SO^\varphi(V)$** (O'Meara 1963, 42:17; Shimura uses it in the proof of
Theorem 11.6): if $\varphi$ is nondegenerate, $n \ge 2$ and $\varphi[x] = \varphi[h] \ne 0$, then $x = \alpha h$ for
some $\alpha \in SO^\varphi(V)$. -/
theorem exists_so_mulVec_eq (hQ : Q.Nondegenerate) (hn : 2 ≤ n) {h x : Fin n → F}
    (hx : Q.eval x = Q.eval h) (hh : Q.eval h ≠ 0) :
    ∃ α : orthGroup Q F, α ∈ soSub Q F ∧ (α : GL (Fin n) F).val *ᵥ h = x := by
  obtain ⟨γ, hγ, hγh⟩ := ClassFin.exists_orth_mulVec_eq Q hx.symm hh
  rcases det_eq_one_or_neg_one Q hQ (⟨γ, hγ⟩ : orthGroup Q F) with hd | hd
  · exact ⟨⟨γ, hγ⟩, hd, hγh⟩
  · obtain ⟨w, hw, hw0⟩ := exists_perp_aniso Q hQ hn hh
    refine ⟨⟨γ, hγ⟩ * symm Q F w, ?_, ?_⟩
    · change ((γ : GL (Fin n) F) * (symm Q F w : GL (Fin n) F)).val.det = 1
      rw [Units.val_mul, det_mul, show γ.val.det = -1 from hd, symm_det Q F hw0]
      norm_num
    · change ((γ : GL (Fin n) F) * (symm Q F w : GL (Fin n) F)).val *ᵥ h = x
      rw [Units.val_mul, ← mulVec_mulVec, symm_mulVec Q F hw0]
      have : w ⬝ᵥ (Q.hessian.map (algebraMap F F) *ᵥ h) = 0 := by
        have := qbil_comm Q F h w
        rw [hw] at this
        exact this.symm
      rw [this, mul_zero, zero_smul, sub_zero]
      exact hγh

/-! ### Localization of $\varphi(h, \Lambda)$ -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Qv" => QuadForm.toQuadraticForm (QuadForm.map (algebraMap F (v.adicCompletion F)) Q)

/-- **$\varphi(h, \Lambda)_v = \varphi_v(h, \Lambda_v)$**: completing the ideal $\varphi(h, \Lambda)$ at a finite
prime $v$ gives the ideal of the completed vector and lattice. -/
theorem locFrac_phiIdeal (h : Fin n → F) (M : Submodule (𝓞 F) (Fin n → F)) :
    locFrac v (phiIdeal Q.toQuadraticForm h M) = phiIdeal Qv (locVec v h) (loc v M) := by
  rw [phiIdeal, locFrac_span, phiIdeal, loc]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨locVec v y, Submodule.subset_span ⟨y, hy, rfl⟩, ?_⟩
    exact bil_locVec v Q h y
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, ⟨y, hy, rfl⟩, (bil_locVec v Q h y).symm⟩
    | zero => simp [OMeara.bil]
    | add a b _ _ ha hb =>
      have : OMeara.bil Qv (locVec v h) (a + b) =
          OMeara.bil Qv (locVec v h) a + OMeara.bil Qv (locVec v h) b := by
        simp [OMeara.bil]
      rw [SetLike.mem_coe, this]; exact add_mem ha hb
    | smul c a _ ha =>
      have : OMeara.bil Qv (locVec v h) (c • a) = c • OMeara.bil Qv (locVec v h) a := by
        have e1 : c • a = (c : Fv) • a := rfl
        rw [e1]
        simp only [OMeara.bil, map_smul, smul_eq_mul]
        rfl
      rw [SetLike.mem_coe, this]; exact Submodule.smul_mem _ c ha

/-- A local isometry preserves $\varphi_v(x, \Lambda_v)$: $\varphi_v(gx, g\Lambda_v) = \varphi_v(x, \Lambda_v)$. -/
theorem phiIdeal_locAct {g : GL (Fin n) Fv} (hg : g ∈ orthGroup Q Fv) (x : Fin n → Fv)
    (M : Submodule (v.adicCompletionIntegers F) (Fin n → Fv)) :
    phiIdeal Qv (g.val *ᵥ x) (locAct v g M) = phiIdeal Qv x M := by
  have hQv : ∀ z, Qv (g.val *ᵥ z) = Qv z := fun z => by
    rw [QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply, eval_map_eq, eval_map_eq]
    exact evalIn_mulVec_of_mem Q hg z
  have hb : ∀ y, OMeara.bil Qv (g.val *ᵥ x) (g.val *ᵥ y) = OMeara.bil Qv x y := fun y => by
    simp only [OMeara.bil, QuadraticMap.associated_apply, ← mulVec_add, hQv]
  unfold phiIdeal
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (hb y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g.val *ᵥ y, ⟨y, hy, rfl⟩, hb y⟩

end Local

/-- $\varphi(h, \Lambda)$ is a finitely generated $\mathcal O_F$-module. -/
theorem phiIdeal_fg (h : Fin n → F) (Λ : Lat F n) : (phiIdeal Q.toQuadraticForm h Λ.1).FG := by
  let f : (Fin n → F) →ₗ[𝓞 F] F := (QuadraticMap.associated Q.toQuadraticForm h).restrictScalars (𝓞 F)
  have : phiIdeal Q.toQuadraticForm h Λ.1 = Λ.1.map f := by
    rw [phiIdeal]
    exact (Submodule.span_image f (s := (Λ.1 : Set (Fin n → F)))).trans (by rw [Submodule.span_eq])
  rw [this]
  exact Λ.2.fg.map f

/-- $\varphi(h, \Lambda) \ne 0$ for $h \ne 0$ and $\varphi$ nondegenerate ($\Lambda$ spans $V$). -/
theorem phiIdeal_ne_bot (hQ : Q.Nondegenerate) {h : Fin n → F} (hh : h ≠ 0) (Λ : Lat F n) :
    phiIdeal Q.toQuadraticForm h Λ.1 ≠ ⊥ := by
  intro h0
  let f : (Fin n → F) →ₗ[F] F := QuadraticMap.associated Q.toQuadraticForm h
  have hL : ∀ y ∈ Λ.1, f y = 0 := fun y hy => by
    have : OMeara.bil Q.toQuadraticForm h y ∈ phiIdeal Q.toQuadraticForm h Λ.1 := bil_mem_phiIdeal hy
    rw [h0] at this
    exact (Submodule.mem_bot _).1 this
  have hker : Submodule.span F (Λ.1 : Set (Fin n → F)) ≤ LinearMap.ker f :=
    Submodule.span_le.2 fun y hy => hL y hy
  rw [Λ.2.span_eq_top, top_le_iff] at hker
  have hall : ∀ y, h ⬝ᵥ (Q.hessian *ᵥ y) = 0 := fun y => by
    have h1 : f y = 0 := by
      have : y ∈ LinearMap.ker f := by rw [hker]; trivial
      exact this
    have h2 : f y = OMeara.bil Q.toQuadraticForm h y := rfl
    rw [h2, Sec103Five.bil_eq_hessian] at h1
    exact (div_eq_zero_iff.1 h1).resolve_right two_ne_zero
  have hv : Matrix.vecMul h Q.hessian = 0 := by
    funext j
    have := hall (Pi.single j 1)
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  exact hh (Matrix.eq_zero_of_vecMul_eq_zero hQ hv)

/-- **Every lattice of the $H$-genus of $L$ has the same $\varphi(h, \cdot)$ as $L$.** -/
theorem phiIdeal_eq_of_mem_hGenus (hQ : Q.Nondegenerate) {h : Fin n → F} (hh : h ≠ 0) {L M : Lat F n}
    (hM : M ∈ hGenus Q h L) :
    phiIdeal Q.toQuadraticForm h M.1 = phiIdeal Q.toQuadraticForm h L.1 := by
  obtain ⟨η, hη, rfl⟩ := hM
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locFrac v (phiIdeal Q.toQuadraticForm h (latSMul Q η L).1) =
        locFrac v (phiIdeal Q.toQuadraticForm h L.1) := fun v => by
    rw [locFrac_phiIdeal, locFrac_phiIdeal, loc_latSMul]
    have hfix : ((η v : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)).val *ᵥ locVec v h = locVec v h :=
      hη.2 v
    conv_lhs => rw [← hfix]
    exact phiIdeal_locAct Q v (η v).2 _ _
  apply le_antisymm
  · exact le_of_forall_locFrac_le (phiIdeal_fg Q h L) (phiIdeal_ne_bot Q hQ hh L) fun v => (hloc v).le
  · exact le_of_forall_locFrac_le (phiIdeal_fg Q h _) (phiIdeal_ne_bot Q hQ hh _) fun v => (hloc v).ge

/-- **The index set of a minimal cover is finite** (Shimura 2004, Theorem 11.6 (i): "$\{L_i\}$ is finite"): the
$L_i$ are pairwise not $SO^\varphi(V)$-equivalent lattices of one genus, and a genus has finitely many classes. -/
theorem finite_of_isHGenusCover (hQ : Q.Nondegenerate) {h : Fin n → F} {L : Lat F n} {I : Type}
    {Ls : I → Lat F n} (hcov : IsHGenusCover Q h L Ls) : Finite I := by
  classical
  let f : I → LatClass Q := fun i => Quotient.mk _ (Ls i)
  have hf : ∀ i, f i ∈ genusClasses Q L := fun i => by
    obtain ⟨ξ, -, hξ⟩ := hcov.mem i
    refine ⟨Ls i, rfl, ?_⟩
    have : Ls i ∈ @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L := ⟨ξ, hξ⟩
    rw [orbit_eq_genus] at this
    exact this
  -- each fibre has at most two elements
  have hfib : ∀ c ∈ genusClasses Q L, (f ⁻¹' {c}).Finite := by
    intro c _
    by_cases hne : (f ⁻¹' {c}).Nonempty
    · obtain ⟨i₀, hi₀⟩ := hne
      let S : Set I := {j | ∃ γ ∈ orthGroup Q F, γ.val.det = -1 ∧ glImage γ (Ls i₀).1 = (Ls j).1}
      have hS : S.Subsingleton := by
        rintro j ⟨γ, hγ, hd, hγj⟩ k ⟨δ, hδ, hd', hδk⟩
        refine hcov.minimal j k ⟨⟨δ * γ⁻¹, (orthGroup Q F).mul_mem hδ ((orthGroup Q F).inv_mem hγ)⟩, ?_, ?_⟩
        · change (δ * γ⁻¹).val.det = 1
          rw [Units.val_mul, det_mul, hd']
          have h1 := congrArg Matrix.det (Units.inv_mul γ)
          rw [det_mul, hd, det_one] at h1
          linear_combination h1
        · apply Lattices.Lat.ext
          change glImage (δ * γ⁻¹) (Ls j).1 = (Ls k).1
          rw [← hγj, ← glImage_mul, inv_mul_cancel_right, hδk]
      refine (Set.finite_singleton i₀).union hS.finite |>.subset ?_
      intro j hj
      have hij : f i₀ = f j := hi₀.trans hj.symm
      obtain ⟨γ, hγ, hγj⟩ := Quotient.exact hij
      rcases det_eq_one_or_neg_one Q hQ (⟨γ, hγ⟩ : orthGroup Q F) with hd | hd
      · left
        exact (hcov.minimal i₀ j ⟨⟨γ, hγ⟩, hd, Lattices.Lat.ext hγj⟩).symm
      · right
        exact ⟨γ, hγ, hd, hγj⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]; exact Set.finite_empty
  have hfin := (ClassFin.genusClasses_finite_nf Q hQ L).preimage' hfib
  have : f ⁻¹' genusClasses Q L = Set.univ := Set.eq_univ_of_forall hf
  rw [this] at hfin
  exact Set.finite_univ_iff.mp hfin

end QuadFormsKB.Shimura2004
