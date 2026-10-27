/-
# O'Meara §91C: Jordan chains (91:10, 91:11)

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Defines** for a Jordan splitting $L = L_1 \perp \cdots \perp L_t$ (components `Ls 0, …, Ls (t-1)`) the Jordan chain
$L_{(i)} = L_1 \perp \cdots \perp L_i$ (`jordanChain Ls i`, components $0..i$) and the inverse Jordan chain
$L^{(i)} = L_i \perp \cdots \perp L_t$ (`invJordanChain Ls i`, components $i..t-1$) (**91:10**, p. 245).

**Proves**
* `jordanChain_mono`, `jordanChain_last`, `isOrthSum_jordanChain` (**91:10**): $L_{(1)} \subseteq \cdots \subseteq
  L_{(t)} = L$ and $L = L_{(i)} \perp L^{(i+1)}$;
* `isJordanSplitting_jordanChain`: $L_{(i)} = L_1 \perp \cdots \perp L_i$ is a Jordan splitting;
* `volume_eq_prod` ($\mathfrak v(L_1 \perp \cdots \perp L_t) = \prod \mathfrak a_i^{\dim L_i}$ for
  $\mathfrak a_i$-modular $L_i$, §82E, p. 229, and §82G);
* `exists_unit_det_jordanChain` (**91:11**, p. 246): for Jordan chains of lattices of the same Jordan type,
  $L_{(i)}$ and $K_{(i)}$ are of the same Jordan type, $\mathfrak vL_{(i)} = \mathfrak vK_{(i)}$, and hence
  $dL_{(i)}/dK_{(i)}$ is a unit.
-/
import QuadFormsKB.Literature.OMeara.Sec82Isom

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The Jordan chain** (O'Meara 1963, 91:10, p. 245): $L_{(i)} = L_1 \perp \cdots \perp L_i$; here
`jordanChain Ls i` is the sum of the components `Ls 0, …, Ls i`. -/
@[kb "omeara1963" "§91C, 91:10, p. 245 (Jordan chain L_(i))"]
def jordanChain {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) : Submodule R V :=
  ⨆ (j : Fin t) (_ : j ≤ i), Ls j

/-- **The inverse Jordan chain** (O'Meara 1963, 91:10, p. 246): $L^{(i)} = L_i \perp \cdots \perp L_t$; here
`invJordanChain Ls i` is the sum of the components `Ls i, …, Ls (t-1)`. -/
@[kb "omeara1963" "§91C, 91:10, p. 246 (inverse Jordan chain L^(i))"]
def invJordanChain {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) : Submodule R V :=
  ⨆ (j : Fin t) (_ : i ≤ j), Ls j

omit [Invertible (2 : F)] in
/-- **91:10** (O'Meara 1963, p. 246): $L_{(1)} \subseteq L_{(2)} \subseteq \cdots$. -/
theorem jordanChain_mono {t : ℕ} (Ls : Fin t → Submodule R V) : Monotone (jordanChain Ls) :=
  fun _ _ hij => iSup₂_mono' fun j hj => ⟨j, hj.trans hij, le_rfl⟩

/-- **91:10** (O'Meara 1963, p. 246): the last lattice of the Jordan chain is $L_{(t)} = L$. -/
theorem jordanChain_last {L : Submodule R V} {t : ℕ} {Ls : Fin (t + 1) → Submodule R V}
    (hL : IsOrthSplit Q L Ls) : jordanChain Ls (Fin.last t) = L := by
  rw [← hL.iSup_eq, jordanChain]
  exact le_antisymm (iSup₂_le fun j _ => le_iSup Ls j) (iSup_le fun j => le_iSup₂_of_le j (Fin.le_last j) le_rfl)

/-- **91:10** (O'Meara 1963, p. 246: "Clearly $L = L_{(i)} \perp L^{(i+1)}$"). -/
@[kb "omeara1963" "§91C, 91:10, p. 246 (L = L_(i) ⊥ L^(i+1))"]
theorem isOrthSum_jordanChain {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsOrthSplit Q L Ls) (i j : Fin t) (hij : i.val + 1 = j.val) :
    IsOrthSum Q L (jordanChain Ls i) (invJordanChain Ls j) := by
  have hsep : ∀ k l : Fin t, k ≤ i → j ≤ l → k ≠ l := fun k l hk hl h => by
    subst h; rw [Fin.le_def] at hk hl; omega
  refine ⟨fun x hx y hy => ?_, ?_, ?_⟩
  · refine iSup_induction _ (motive := fun x => bil Q x y = 0) hx (fun k x hx => ?_) (by simp [bil])
      (fun a b ha hb => by rw [bil_add_left, ha, hb, add_zero])
    refine iSup_induction _ (motive := fun x => bil Q x y = 0) hx (fun hk x hx => ?_) (by simp [bil])
      (fun a b ha hb => by rw [bil_add_left, ha, hb, add_zero])
    rw [bil_comm]
    refine iSup_induction _ (motive := fun y => bil Q y x = 0) hy (fun l y hy => ?_) (by simp [bil])
      (fun a b ha hb => by rw [bil_add_left, ha, hb, add_zero])
    refine iSup_induction _ (motive := fun y => bil Q y x = 0) hy (fun hl y hy => ?_) (by simp [bil])
      (fun a b ha hb => by rw [bil_add_left, ha, hb, add_zero])
    exact hL.orth l k (hsep k l hk hl).symm y hy x hx
  · have hd := hL.indep
    have : Disjoint (⨆ (k : Fin t) (_ : k ∈ {k | k ≤ i}), Ls k) (⨆ (k : Fin t) (_ : k ∈ {k | j ≤ k}), Ls k) :=
      hd.disjoint_biSup_biSup (by
        rw [Set.disjoint_left]; intro k hk hk'; exact hsep k k hk hk' rfl)
    simpa [jordanChain, invJordanChain] using this
  · rw [← hL.iSup_eq, jordanChain, invJordanChain]
    apply le_antisymm
    · exact sup_le (iSup₂_le fun k _ => le_iSup Ls k) (iSup₂_le fun k _ => le_iSup Ls k)
    · refine iSup_le fun k => ?_
      by_cases hk : k ≤ i
      · exact le_sup_of_le_left (le_iSup₂_of_le k hk le_rfl)
      · refine le_sup_of_le_right (le_iSup₂_of_le k ?_ le_rfl)
        rw [Fin.le_def]; rw [Fin.le_def] at hk; omega

end Defs

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Volume of an orthogonal sum** (O'Meara 1963, §82E, p. 229): $\mathfrak v(J \perp K) = \mathfrak vJ \cdot
\mathfrak vK$. -/
@[kb "omeara1963" "§82E, p. 229 (v(J ⊥ K) = vJ · vK)"]
theorem volume_eq_mul_of_isOrthSum {M J K : Submodule R V} (h : IsOrthSum Q M J K) (hJ : J.FG) (hK : K.FG) :
    volume Q M = volume Q J * volume Q K := by
  classical
  obtain ⟨bJ⟩ := exists_basis (R := R) (F := F) hJ
  obtain ⟨bK⟩ := exists_basis (R := R) (F := F) hK
  let x : Fin (finrank R J) ⊕ Fin (finrank R K) → V := Sum.elim (fun i => bJ i) (fun i => bK i)
  have hli : LinearIndependent R x := by
    refine LinearIndependent.sum_type ?_ ?_ ?_
    · exact LinearIndependent.map' bJ.linearIndependent J.subtype (ker_subtype J)
    · exact LinearIndependent.map' bK.linearIndependent K.subtype (ker_subtype K)
    · rw [span_basis_eq bJ, span_basis_eq bK]; exact h.disjoint
  have hspan : span R (Set.range x) = M := by
    rw [Set.Sum.elim_range, span_union, span_basis_eq bJ, span_basis_eq bK, h.sup_eq]
  let B := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hG : gram Q (fun i => (B i : V)) =
      Matrix.fromBlocks (gram Q fun i => (bJ i : V)) 0 0 (gram Q fun i => (bK i : V)) := by
    ext (i | i) (j | j)
    · simp [B, x, gram]
    · simp [B, x, gram, h.orth _ (bJ i).2 _ (bK j).2]
    · simp [B, x, gram, bil_comm Q (bK i : V), h.orth _ (bJ j).2 _ (bK i).2]
    · simp [B, x, gram]
  rw [volume_eq_span_det Q B, hG, Matrix.det_fromBlocks_zero₂₁, volume_eq_span_det Q bJ,
    volume_eq_span_det Q bK, span_mul_span, Set.singleton_mul_singleton]

/-- $L_{(i+1)} = L_{(i)} \perp L_{i+1}$. -/
theorem isOrthSum_jordanChain_succ {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i j : Fin t) (hij : i.val + 1 = j.val) :
    IsOrthSum Q (jordanChain Ls j) (jordanChain Ls i) (Ls j) := by
  have hle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  have hreg : IsRegular Q (Ls j) := (hL.modular j).isRegular Q (FG.of_le hfg (hle j))
  have horth : ∀ x ∈ jordanChain Ls i, ∀ y ∈ Ls j, bil Q x y = 0 := by
    intro x hx y hy
    refine bil_eq_zero_of_mem_iSup Q (P := fun k => k ≤ i) (fun k hk z hz => ?_) hx
    exact hL.split.orth k j (fun h => by subst h; rw [Fin.le_def] at hk; omega) z hz y hy
  refine ⟨horth, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (mem_bot R).mpr (hreg x hx2 fun y hy => horth x hx1 y hy)
  · apply le_antisymm
    · exact sup_le (jordanChain_mono Ls (by rw [Fin.le_def]; omega)) (le_iSup₂_of_le j le_rfl le_rfl)
    · refine iSup₂_le fun k hk => ?_
      by_cases hki : k ≤ i
      · exact le_sup_of_le_left (le_iSup₂_of_le k hki le_rfl)
      · have : k = j := Fin.ext (by rw [Fin.le_def] at hk hki; omega)
        subst this; exact le_sup_right

theorem jordanChain_zero {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) (hi : i.val = 0) :
    jordanChain Ls i = Ls i := by
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    have : k = i := Fin.ext (by rw [Fin.le_def] at hk; omega)
    rw [this]
  · exact le_iSup₂_of_le i le_rfl le_rfl

/-- **Volumes along Jordan chains** (O'Meara 1963, 91:11, p. 246): for Jordan splittings
$L = L_1 \perp \cdots \perp L_t$ and $K = K_1 \perp \cdots \perp K_t$ with $\mathfrak sL_i = \mathfrak sK_i$ and
$\dim L_i = \dim K_i$, the Jordan chains have $\mathfrak vL_{(i)} = \mathfrak vK_{(i)}$
($= \prod_{j \le i} (\mathfrak sL_j)^{\dim L_j}$). -/
theorem volume_jordanChain_eq {L : Submodule R V} {K : Submodule R V'} (hLfg : L.FG) (hKfg : K.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (hsc : ∀ i, scale Q (Ls i) = scale Q' (Ks i))
    (hrk : ∀ i, finrank R (Ls i) = finrank R (Ks i)) (i : Fin t) :
    volume Q (jordanChain Ls i) = volume Q' (jordanChain Ks i) := by
  have hcomp : ∀ i, volume Q (Ls i) = volume Q' (Ks i) := by
    intro i; rw [(hL.modular i).2.2, (hK.modular i).2.2, hsc, hrk]
  have hLle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  have hKle : ∀ k, Ks k ≤ K := fun k => hK.split.iSup_eq ▸ le_iSup Ks k
  obtain ⟨n, hn⟩ : ∃ n, i.val = n := ⟨_, rfl⟩
  induction n generalizing i with
  | zero => rw [jordanChain_zero Ls i hn, jordanChain_zero Ks i hn, hcomp]
  | succ n ih =>
    let i' : Fin t := ⟨n, by omega⟩
    have h1 := isOrthSum_jordanChain_succ Q hLfg hL i' i (by simp [i', hn])
    have h2 := isOrthSum_jordanChain_succ Q' hKfg hK i' i (by simp [i', hn])
    have hcL : (jordanChain Ls i').FG := FG.of_le hLfg (iSup₂_le fun k _ => hLle k)
    have hcK : (jordanChain Ks i').FG := FG.of_le hKfg (iSup₂_le fun k _ => hKle k)
    rw [volume_eq_mul_of_isOrthSum Q h1 hcL (FG.of_le hLfg (hLle i)),
      volume_eq_mul_of_isOrthSum Q' h2 hcK (FG.of_le hKfg (hKle i)), ih i' rfl, hcomp]

/-- **Example 91:11** (O'Meara 1963, p. 246): let $L_{(1)} \subseteq \cdots \subseteq L_{(t)}$ and
$K_{(1)} \subseteq \cdots \subseteq K_{(t)}$ be Jordan chains of lattices $L$ and $K$ of the same Jordan type. Then
$\mathfrak vL_{(i)} = \mathfrak vK_{(i)}$, and hence $dL_{(i)}/dK_{(i)} = \varepsilon$ is a unit: for all bases $b$ of
$L_{(i)}$ and $b'$ of $K_{(i)}$, $d(b) = \varepsilon\, d(b')$ with $\varepsilon \in \mathfrak u$. (O'Meara's first
assertion, that $L_{(i)}$ and $K_{(i)}$ are of the same Jordan type, is immediate from the definitions and is not stated
separately; the analogous statement for inverse Jordan chains is not formalized here.) -/
@[kb "omeara1963" "§91C, 91:11, p. 246"]
theorem exists_unit_det_jordanChain {L : Submodule R V} {K : Submodule R V'} (hLfg : L.FG) (hKfg : K.FG)
    {t : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (htype : SameJordanType Q Q' Ls Ks) (i : Fin t) :
    volume Q (jordanChain Ls i) = volume Q' (jordanChain Ks i) ∧
      ∀ (b : Basis (Fin (finrank R (jordanChain Ls i))) R (jordanChain Ls i))
        (b' : Basis (Fin (finrank R (jordanChain Ks i))) R (jordanChain Ks i)),
        ∃ ε : R, IsUnit ε ∧ (gram Q fun k => (b k : V)).det =
          algebraMap R F ε * (gram Q' fun k => (b' k : V')).det := by
  obtain ⟨htt, hty⟩ := htype
  have hsc : ∀ i, scale Q (Ls i) = scale Q' (Ks i) := fun i => by simpa using (hty i).1
  have hrk : ∀ i, finrank R (Ls i) = finrank R (Ks i) := fun i => by simpa using (hty i).2.1
  have hv := volume_jordanChain_eq Q Q' hLfg hKfg hL hK hsc hrk i
  refine ⟨hv, fun b b' => ?_⟩
  rw [volume_eq_span_det Q b, volume_eq_span_det Q' b'] at hv
  have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := F)
  obtain ⟨u, hu⟩ := (span_singleton_eq_span_singleton).mp hv
  refine ⟨↑u⁻¹, Units.isUnit _, ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

end DVR

end QuadFormsKB.OMeara
