/-
# The norm lattice of an order, and the base case for every class number

**Layer:** $F$ a number field (any class number), $a, b \in \mathcal O_F$, $D = (a,b)_F$, $\mathcal O \subset D$ an $\mathcal O_F$-order.
The PID file `OrderNormForm` writes the reduced norm of $\mathcal O$ in an $\mathcal O_F$-basis; for $h_F > 1$ the order need not
be free. Here $\mathcal O$ is viewed as a *lattice* $L_{\mathcal O} \subset F^4$ (coordinates $1, i, j, k$; `orderLat`), integral for
$Q_0 = \langle 1,-a,-b,ab\rangle$ (the reduced norm), and $\tau$ is computed on it by `LatChange.tauSOLat`. No basis of $\mathcal O$ is chosen.

* `orderLat O hO : Lat F 4`, `isIntegral_orderLat`.
* **`tauSOLat_orderLat`**: $\tau$ of the norm form computed on $L_{\mathcal O}$ equals $\tau(\langle1,-a,-b,ab\rangle)$ (`tauSOLat_eq_tauSO`).
* **`ternaryTamagawaTwo_of_orders_nf`**: `TernaryTamagawaTwo F` follows from $\tau_{L_{\mathcal O}} = 2$ for one order $\mathcal O$ of each
  totally definite $(a,b)_F$ (a maximal order), any class number.

Sources: Voight 2021, §15.2; Weil 1982, §2.2.1, p. 14 (independence of the lattice), via `tauSOLat_eq_tauSO`.
-/
import QuadFormsKB.Tamagawa.QuatOrderGlobal
import QuadFormsKB.Tamagawa.RankFourNF
import QuadFormsKB.Tamagawa.LatticeChangeNF

open Matrix NumberField Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.QuadForm QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Tamagawa
  QuadFormsKB.HilbertModular IsLocalization Submodule

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-- The coordinate map $D \to F^4$, $x \mapsto (x_0,x_1,x_2,x_3)$, as an $F$-linear equivalence (`tup`). -/
abbrev tupEquiv (a b : 𝓞 F) : QuatF F a b ≃ₗ[F] (Fin 4 → F) := QuaternionAlgebra.linearEquivTuple _ _ _

theorem tupEquiv_apply (x : QuatF F a b) : tupEquiv a b x = tup x := rfl

/-- The $\mathcal O_F$-submodule of $F^4$ given by an order, in the coordinates $1, i, j, k$. -/
def orderSub (O : Subalgebra (𝓞 F) (QuatF F a b)) : Submodule (𝓞 F) (Fin 4 → F) :=
  (Subalgebra.toSubmodule O).map ((tupEquiv a b).toLinearMap.restrictScalars (𝓞 F))

theorem mem_orderSub {O : Subalgebra (𝓞 F) (QuatF F a b)} {y : Fin 4 → F} :
    y ∈ orderSub O ↔ ∃ x ∈ O, tup x = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem isLattice_orderSub {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    (orderSub O).IsLattice F where
  fg := hO.fg.map _
  span_eq_top := by
    have h : Submodule.span F ((orderSub O : Set (Fin 4 → F))) =
        Submodule.map (tupEquiv a b).toLinearMap (Submodule.span F (O : Set (QuatF F a b))) := by
      rw [Submodule.map_span]; rfl
    rw [h, hO.span, Submodule.map_top, LinearMap.range_eq_top]
    exact (tupEquiv a b).surjective

/-- **The norm lattice of an order** $L_{\mathcal O} \subset F^4$ (coordinates $1,i,j,k$). -/
def orderLat {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) : Lat F 4 :=
  ⟨orderSub O, isLattice_orderSub hO⟩

/-- The reduced norm is integral on an order: $L_{\mathcal O}$ is integral for $\langle1,-a,-b,ab\rangle$. -/
theorem isIntegral_orderLat {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    Lattices.IsIntegral ((normForm a b).map (algebraMap (𝓞 F) F)) (orderLat hO).1 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_orderSub.1 hy
  have := (isInteger_trd_nrd hO hx).2
  have h2 : ((normForm a b).map (algebraMap (𝓞 F) F)).evalIn F (tup x) = nrd x := by
    rw [nrd_eq_evalIn, map_normForm]
  rw [h2]; exact this

/-- **$\tau$ computed on the norm lattice of an order is $\tau(\langle1,-a,-b,ab\rangle)$.** -/
theorem tauSOLat_orderLat (hpd : IsTotallyPosDef (formF (normForm a b)))
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    LatChange.tauSOLat (normForm a b) (orderLat hO) = tauSO (normForm a b) :=
  LatChange.tauSOLat_eq_tauSO _ (nondegenerate_of_map hpd.nondegenerate) (by norm_num) hpd _ (isIntegral_orderLat hO)

/-! ### The trace-zero lattice -/

/-- Every element of $D$ is cleared into an order by a nonzero element of $\mathcal O_F$. -/
theorem exists_smul_mem_order_nf {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) (x : QuatF F a b) :
    ∃ n : 𝓞 F, n ≠ 0 ∧ n • x ∈ O := by
  have hx : x ∈ Submodule.span F (O : Set (QuatF F a b)) := hO.span ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact O.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, hn, hny⟩ := hy
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have h1 : (n * m) • y = m • (n • y) := by rw [mul_comm, mul_smul]
    have h2 : (n * m) • z = n • (m • z) := mul_smul _ _ _
    rw [smul_add, h1, h2]
    exact O.add_mem (O.smul_mem hny _) (O.smul_mem hmz _)
  | smul c y _ hy =>
    obtain ⟨n, hn, hny⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    refine ⟨q * n, mul_ne_zero hq0 hn, ?_⟩
    have hqF : algebraMap (𝓞 F) F q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hq0
    have : (q * n) • ((algebraMap (𝓞 F) F p / algebraMap (𝓞 F) F q) • y) = p • (n • y) := by
      rw [← algebraMap_smul F (q * n), ← algebraMap_smul F p, ← algebraMap_smul F n, smul_smul, smul_smul, map_mul]
      congr 1; field_simp
    rw [this]; exact O.smul_mem hny _

/-- The pure-coordinate map $x \mapsto (x_1, x_2, x_3)$ (coefficients of $i, j, k$). -/
def pureTup (a b : 𝓞 F) : QuatF F a b →ₗ[F] (Fin 3 → F) where
  toFun x := ![x.imI, x.imJ, x.imK]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- The trace-zero part $\mathcal O^0 = \{x \in \mathcal O : \operatorname{trd}x = 0\}$ as an $\mathcal O_F$-submodule of $D$. -/
def traceZeroSub (O : Subalgebra (𝓞 F) (QuatF F a b)) : Submodule (𝓞 F) (QuatF F a b) where
  carrier := {x | x ∈ O ∧ x.re = 0}
  add_mem' := fun ⟨hx, hx0⟩ ⟨hy, hy0⟩ => ⟨O.add_mem hx hy, by simp [hx0, hy0]⟩
  zero_mem' := ⟨O.zero_mem, rfl⟩
  smul_mem' := fun c x ⟨hx, hx0⟩ => ⟨O.smul_mem hx c, by
    rw [← algebraMap_smul F c x]; simp [hx0]⟩

/-- The trace-zero part of an order in the coordinates $(i,j,k)$, as an $\mathcal O_F$-submodule of $F^3$. -/
def pureSub (O : Subalgebra (𝓞 F) (QuatF F a b)) : Submodule (𝓞 F) (Fin 3 → F) :=
  (traceZeroSub O).map ((pureTup a b).restrictScalars (𝓞 F))

theorem isLattice_pureSub {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    (pureSub O).IsLattice F where
  fg := by
    refine Submodule.FG.map _ ?_
    have hN : IsNoetherian (𝓞 F) (Subalgebra.toSubmodule O) := isNoetherian_of_fg_of_noetherian _ hO.fg
    exact @Submodule.FG.of_le_of_isNoetherian _ _ _ _ _ _ _ hN (fun x hx => hx.1)
  span_eq_top := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨n, hn, hnx⟩ := exists_smul_mem_order_nf hO (⟨0, y 0, y 1, y 2⟩ : QuatF F a b)
    have hnF : algebraMap (𝓞 F) F n ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hn
    have hmem : n • y ∈ pureSub O := by
      refine ⟨n • (⟨0, y 0, y 1, y 2⟩ : QuatF F a b), ⟨hnx, ?_⟩, ?_⟩
      · rw [← algebraMap_smul F n]; simp
      · ext i
        change (pureTup a b) (n • (⟨0, y 0, y 1, y 2⟩ : QuatF F a b)) i = (n • y) i
        rw [← algebraMap_smul F n, map_smul]
        fin_cases i <;> simp [pureTup, Algebra.smul_def]
    have : y = ((algebraMap (𝓞 F) F n)⁻¹ : F) • (n • y) := by
      rw [← algebraMap_smul F n, smul_smul, inv_mul_cancel₀ hnF, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/-- **The trace-zero lattice of an order** $L_{\mathcal O^0} \subset F^3$ (coordinates of $i,j,k$). -/
def pureLat {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) : Lat F 3 :=
  ⟨pureSub O, isLattice_pureSub hO⟩

/-- The reduced norm is integral on $\mathcal O^0$: $L_{\mathcal O^0}$ is integral for $\langle-a,-b,ab\rangle$. -/
theorem isIntegral_pureLat {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    Lattices.IsIntegral ((pureFormO a b).map (algebraMap (𝓞 F) F)) (pureLat hO).1 := by
  rintro y ⟨x, ⟨hx, hx0⟩, rfl⟩
  have := (isInteger_trd_nrd hO hx).2
  have h2 : ((pureFormO a b).map (algebraMap (𝓞 F) F)).evalIn F (pureTup a b x) = nrd x := by
    rw [map_pureFormO]
    simp [QuadForm.evalIn_diag, Quat.pureForm, nrd, hx0, pureTup, Fin.sum_univ_three]
    ring
  change ((pureFormO a b).map (algebraMap (𝓞 F) F)).evalIn F (pureTup a b x) ∈ _
  rw [h2]; exact this

/-- **$\tau$ computed on the trace-zero lattice of an order is $\tau(\langle-a,-b,ab\rangle)$.** -/
theorem tauSOLat_pureLat (hQ : (pureFormO a b).Nondegenerate)
    (hpd : IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)))
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    LatChange.tauSOLat (pureFormO a b) (pureLat hO) = tauSO (pureFormO a b) :=
  LatChange.tauSOLat_eq_tauSO _ hQ (by norm_num) hpd _ (isIntegral_pureLat hO)

variable [IsTotallyReal F]

/-- **`TernaryTamagawaTwo F` for every class number, from $\tau = 2$ on the trace-zero lattice $\mathcal O^0$ of one order per
quaternion algebra** (e.g. a maximal order): the basis-free `ternaryTamagawaTwo_of_orders`, through
`ternaryTamagawaTwo_of_pureForm_nf` and `tauSOLat_pureLat`. -/
@[kb "weil1982" "§3.7(a), p. 62; Thm. 3.7.1 (m = 3), p. 65; §2.2.1, p. 14"]
theorem ternaryTamagawaTwo_of_orders_nf
    (h : ∀ a b : 𝓞 F, a ≠ 0 → b ≠ 0 → IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)) →
      ∃ (O : Subalgebra (𝓞 F) (QuatF F a b)) (hO : IsOrder (𝓞 F) F O),
        LatChange.tauSOLat (pureFormO a b) (pureLat hO) = 2) :
    TernaryTamagawaTwo F := by
  refine ternaryTamagawaTwo_of_pureForm_nf fun a b ha hb hpd => ?_
  obtain ⟨O, hO, hτ⟩ := h a b ha hb hpd
  have hQ : (pureFormO a b).Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  unfold TamagawaNumberTwo
  rw [← tauSOLat_pureLat hQ hpd hO, hτ]

end QuadFormsKB.QuatOrder
