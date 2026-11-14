import QuadFormsKB.Tamagawa.Unitary.TraceForm

/-!
# $U(V)(K)\cong$ the commutant of $\omega$ in $O(V_F, q)(K)$

**Layer:** $K\supseteq F$ a field of characteristic $0$; $H_0$ an integral hermitian matrix (`TraceForm.lean`), $H = H_0$ over
$K[\omega]$ (`HK D K H₀`), $D\ne0$.

**Defines** `realifyR D K` (the realification of `Realify.lean`, reindexed to `Fin (m * 2)`) and
**`unitaryEquivOrth`** : `unitaryH D K H` $\cong$ `unitaryOrth D H₀ K`, $g\mapsto\mathrm{realify}(g)$.

**Proves**
* `realify_injective`; `omegaO_map` ($\omega$ in the coordinates is the realification of the scalar $\omega$);
* `eq_realify_of_commute`: a $2m\times2m$ matrix commuting with $\omega$ is a realification (Mathlib-free elementary
  computation; no hypothesis on $D$);
* `gramBlk_mul_cancel` ($D\ne0$), `realify_isometry_iff`: $\mathrm{realify}(g)^{\mathsf T}S\,\mathrm{realify}(g) = S\iff g^*Hg = H$;
* **`unitaryEquivOrth`**: the two presentations of $U(V)(K)$ agree (so `unitaryOrth` over $F_v$, $\mathbb R$, $\mathbb C$ is the
  unitary group of `Group.lean`, and `detU_surjective`, `ker_detU` apply to it).
-/

open Matrix
open scoped QuadraticAlgebra

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.Tamagawa.Measure.Weil NumberField QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)
variable (K : Type*) [Field K] [Algebra F K] [CharZero K] {m : ℕ}

local notation "ι" => fun x : 𝓞 F => algebraMap F K (algebraMap (𝓞 F) F x)

/-- **Realification reindexed** to the coordinates `Fin (m * 2)` of the trace form. -/
def realifyR : Matrix (Fin m) (Fin m) (QuadK D K) →+* Matrix (Fin (m * 2)) (Fin (m * 2)) K :=
  (reindexAlgEquiv K K (eCoord m)).toRingEquiv.toRingHom.comp (realify D K)

theorem reindex_mul_e (A B : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) :
    reindex (eCoord m) (eCoord m) (A * B) = reindex (eCoord m) (eCoord m) A * reindex (eCoord m) (eCoord m) B := by
  rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

theorem realifyR_apply (M : Matrix (Fin m) (Fin m) (QuadK D K)) :
    realifyR D K M = reindex (eCoord m) (eCoord m) (realify D K M) := by
  simp [realifyR]

/-- **Realification is injective** (the coordinates $(a,0),(b,0)$ and $(a,1),(b,0)$ recover $\mathrm{re}$ and $\mathrm{im}$). -/
theorem realify_injective : Function.Injective (realify D K (m := m)) := by
  intro M N h
  ext a b
  · simpa [realify_apply, rot_apply] using congrFun (congrFun h (a, 0)) (b, 0)
  · simpa [realify_apply, rot_apply] using congrFun (congrFun h (a, 1)) (b, 0)

theorem realifyR_injective : Function.Injective (realifyR D K (m := m)) := by
  intro M N h
  rw [realifyR_apply, realifyR_apply] at h
  exact realify_injective D K ((reindex (eCoord m) (eCoord m)).injective h)

/-- **$\omega$ in the coordinates** is the realification of the scalar matrix $\omega\cdot1$. -/
theorem omegaO_map : (omegaO D m).map ι = realify D K (Matrix.scalar (Fin m) (QuadraticAlgebra.omega)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [map_apply, omegaO, of_apply, realify_apply, scalar_apply, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    fin_cases i <;> fin_cases j <;> simp [rot_apply, QuadraticAlgebra.omega, dD]
  · fin_cases i <;> fin_cases j <;> simp [hab, rot_apply]

theorem omegaR_eq : omegaR D m K = realifyR D K (Matrix.scalar (Fin m) (QuadraticAlgebra.omega)) := by
  rw [realifyR_apply, ← omegaO_map, omegaR]
  rfl

/-- **The commutant of $\omega$ consists of realifications**: if $M\omega = \omega M$ then $M = \mathrm{realify}(M')$ with
$M'_{ab} = M_{(a,0),(b,0)} + M_{(a,1),(b,0)}\,\omega$. -/
theorem eq_realify_of_commute (M : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K)
    (hM : M * (omegaO D m).map ι = (omegaO D m).map ι * M) :
    M = realify D K (Matrix.of fun a b => (⟨M (a, 0) (b, 0), M (a, 1) (b, 0)⟩ : QuadK D K)) := by
  have key : ∀ p q, (M * (omegaO D m).map ι) p q = ((omegaO D m).map ι * M) p q := fun p q => by rw [hM]
  have hL : ∀ (p : Fin m × Fin 2) (b : Fin m) (j : Fin 2), (M * (omegaO D m).map ι) p (b, j) =
      ∑ k : Fin 2, M p (b, k) * ι (!![0, -D; 1, 0] k j) := by
    intro p b j
    simp only [mul_apply, map_apply, omegaO, of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  have hR : ∀ (a : Fin m) (i : Fin 2) (q : Fin m × Fin 2), ((omegaO D m).map ι * M) (a, i) q =
      ∑ k : Fin 2, ι (!![0, -D; 1, 0] i k) * M (a, k) q := by
    intro a i q
    simp only [mul_apply, map_apply, omegaO, of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  ext ⟨a, i⟩ ⟨b, j⟩
  have e00 := key (a, 0) (b, 0)
  have e10 := key (a, 1) (b, 0)
  rw [hL, hR] at e00 e10
  simp [Fin.sum_univ_two] at e00 e10
  fin_cases i <;> fin_cases j <;> simp [realify_apply, rot_apply, dD]
  all_goals first | exact e00 | exact e10

/-- $(G_{\mathrm{blk}}X)_{(a,i),q} = G_{ii}X_{(a,i),q}$ ($G_{\mathrm{blk}}$ is diagonal). -/
theorem gramBlk_mul_apply (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (a : Fin m) (i : Fin 2)
    (q : Fin m × Fin 2) :
    (gramBlk D K * X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) (a, i) q = gram2 D K i i * X (a, i) q := by
  simp only [mul_apply, Fintype.sum_prod_type, gramBlk_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  fin_cases i <;> simp [Fin.sum_univ_two, gram2]

/-- **$G_{\mathrm{blk}} = \mathrm{diag}(1, D, \dots)$ is left-cancellable** for $D\ne0$. -/
theorem gramBlk_mul_cancel (hD : D ≠ 0) {X Y : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K}
    (h : gramBlk D K * X = gramBlk D K * Y) : X = Y := by
  have hDK : algebraMap F K (algebraMap (𝓞 F) F D) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F K).injective, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    exact hD
  ext ⟨a, i⟩ q
  have := congrFun (congrFun h (a, i)) q
  rw [gramBlk_mul_apply, gramBlk_mul_apply] at this
  fin_cases i
  · simpa [gram2] using this
  · simp only [gram2, dD] at this
    simpa [hDK] using this

/-- **Isometries of the trace form among realifications are the unitary matrices**:
$\mathrm{realify}(g)^{\mathsf T}S\,\mathrm{realify}(g) = S\iff g^*Hg = H$ ($D\ne0$). -/
theorem realify_isometry_iff (hD : D ≠ 0) (H g : Matrix (Fin m) (Fin m) (QuadK D K)) :
    (realify D K g)ᵀ * traceGram D K H * realify D K g = traceGram D K H ↔ gᴴ * H * g = H := by
  rw [traceGram, ← Matrix.mul_assoc, realify_transpose_mul_gramBlk, Matrix.mul_assoc, Matrix.mul_assoc, ← map_mul,
    ← map_mul, ← Matrix.mul_assoc]
  constructor
  · intro h
    exact realify_injective D K (gramBlk_mul_cancel D K hD h)
  · intro h; rw [h]


/-- The Hessian of the trace form over $K$ is $2S$ (reindexed), $S$ = `traceGram` of $H$, for hermitian $H_0$. -/
theorem hessian_traceQF_map {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) :
    (traceQFF D H₀).hessian.map (algebraMap F K) =
      reindex (eCoord m) (eCoord m) ((2 : K) • traceGram D K (HK D K H₀)) := by
  have h1 : (traceQFF D H₀).hessian.map (algebraMap F K) = ((traceQF D H₀).hessian).map ι := by
    simp only [traceQFF, QuadForm.hessian, QuadForm.map, Matrix.map_add, Matrix.transpose_map, Matrix.map_map]
    rfl
  have hS : ∀ p q, traceS D H₀ q p = traceS D H₀ p q := fun p q => by
    simpa using congrFun (congrFun (traceS_transpose D hH) p) q
  have hM : ∀ p q, traceGram D K (HK D K H₀) p q = ι (traceS D H₀ p q) := fun p q => by
    rw [← traceS_map]; rfl
  rw [h1, hessian_traceQF]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, reindex_apply, submatrix_apply,
    Matrix.smul_apply, smul_eq_mul, hM, hS]
  rw [map_add, map_add]; ring

/-- Conjugating the isometry identity by the reindexing. -/
theorem reindex_isometry (R S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) K) :
    (reindex (eCoord m) (eCoord m) R)ᵀ * reindex (eCoord m) (eCoord m) ((2 : K) • S) * reindex (eCoord m) (eCoord m) R =
      reindex (eCoord m) (eCoord m) ((2 : K) • (Rᵀ * S * R)) := by
  rw [transpose_reindex, ← reindex_mul_e, ← reindex_mul_e, Matrix.mul_smul, Matrix.smul_mul]

/-- **The comparison map** $U(V)(K)\to$ `unitaryOrth D H₀ K`, $g\mapsto\mathrm{realify}(g)$. -/
def toUnitaryOrth {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) :
    unitaryH D K (HK D K H₀) →* unitaryOrth D H₀ K where
  toFun g := ⟨⟨Units.map (realifyR D K).toMonoidHom g, by
      rw [mem_orthGroup, hessian_traceQF_map D K hH]
      change (realifyR D K (g : GL (Fin m) (QuadK D K)).val)ᵀ * _ * realifyR D K (g : GL (Fin m) (QuadK D K)).val = _
      rw [realifyR_apply, reindex_isometry, realify_isometry D K g.2]⟩, by
      rw [mem_unitaryOrth]
      change realifyR D K (g : GL (Fin m) (QuadK D K)).val * _ = _ * realifyR D K (g : GL (Fin m) (QuadK D K)).val
      rw [omegaR_eq, ← map_mul, ← map_mul, (scalar_commute _ (fun _ => Commute.all _ _) _).eq]⟩
  map_one' := by ext : 3; simp
  map_mul' a b := by ext : 3; simp

theorem toUnitaryOrth_val {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian)
    (g : unitaryH D K (HK D K H₀)) :
    ((toUnitaryOrth D K hH g : orthGroup (traceQFF D H₀) K) : GL (Fin (m * 2)) K).val =
      realifyR D K (g : GL (Fin m) (QuadK D K)).val := rfl

theorem toUnitaryOrth_injective {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) :
    Function.Injective (toUnitaryOrth D K hH) := by
  intro g h hgh
  have := congrArg (fun x : unitaryOrth D H₀ K => ((x : orthGroup (traceQFF D H₀) K) : GL (Fin (m * 2)) K).val) hgh
  simp only [toUnitaryOrth_val] at this
  exact Subtype.ext (Units.ext (realifyR_injective D K this))

/-- Every element of `unitaryOrth D H₀ K` is a realification. -/
theorem exists_realifyR {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (x : unitaryOrth D H₀ K) :
    ∃ A : Matrix (Fin m) (Fin m) (QuadK D K),
      ((x : orthGroup (traceQFF D H₀) K) : GL (Fin (m * 2)) K).val = realifyR D K A := by
  set M := ((x : orthGroup (traceQFF D H₀) K) : GL (Fin (m * 2)) K).val
  have hc : M * omegaR D m K = omegaR D m K * M := (mem_unitaryOrth D).1 x.2
  set M' := reindex (eCoord m).symm (eCoord m).symm M
  have hO : (omegaO D m).map ι = reindex (eCoord m).symm (eCoord m).symm (omegaR D m K) := by
    ext p q; simp [omegaR]
  have hM' : M' * (omegaO D m).map ι = (omegaO D m).map ι * M' := by
    rw [hO]
    simp only [M', reindex_apply, submatrix_mul_equiv]
    rw [hc]
  refine ⟨Matrix.of fun a b => (⟨M' (a, 0) (b, 0), M' (a, 1) (b, 0)⟩ : QuadK D K), ?_⟩
  rw [realifyR_apply, ← eq_realify_of_commute D K M' hM']
  simp only [M', reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]

theorem toUnitaryOrth_surjective (hD : D ≠ 0) {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) :
    Function.Surjective (toUnitaryOrth D K hH) := by
  intro x
  obtain ⟨A, hA⟩ := exists_realifyR D K x
  obtain ⟨B, hB⟩ := exists_realifyR D K x⁻¹
  have hx1 : ((x : orthGroup (traceQFF D H₀) K) : GL (Fin (m * 2)) K).val *
      (((x⁻¹ : unitaryOrth D H₀ K) : orthGroup (traceQFF D H₀) K) : GL (Fin (m * 2)) K).val = 1 := by
    rw [Subgroup.coe_inv, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAB : A * B = 1 := by
    apply realifyR_injective D K
    rw [map_mul, map_one, ← hA, ← hB, hx1]
  let g : GL (Fin m) (QuadK D K) := ⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩
  have hmem : g ∈ unitaryH D K (HK D K H₀) := by
    rw [mem_unitaryH, ← realify_isometry_iff D K hD]
    have ho := (mem_orthGroup _).1 (x : orthGroup (traceQFF D H₀) K).2
    rw [hessian_traceQF_map D K hH, hA, realifyR_apply, reindex_isometry] at ho
    have := (reindex (eCoord m) (eCoord m)).injective ho
    exact smul_right_injective _ (two_ne_zero) this
  refine ⟨⟨g, hmem⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  rw [toUnitaryOrth_val]
  exact hA.symm

/-- **The two presentations of $U(V)(K)$ agree**: `unitaryH D K H` $\cong$ `unitaryOrth D H₀ K` via realification
($D\ne0$, $H_0$ hermitian; $K\supseteq F$ any field of characteristic $0$). -/
@[kb "ganhankeyu2001" "§3, p. 105 (G the unitary group of V) [running text]"]
def unitaryEquivOrth (hD : D ≠ 0) {H₀ : Matrix (Fin m) (Fin m) (QuadO D)} (hH : H₀.IsHermitian) :
    unitaryH D K (HK D K H₀) ≃* unitaryOrth D H₀ K :=
  MulEquiv.ofBijective (toUnitaryOrth D K hH) ⟨toUnitaryOrth_injective D K hH, toUnitaryOrth_surjective D K hD hH⟩

end QuadFormsKB.Tamagawa.Unitary
