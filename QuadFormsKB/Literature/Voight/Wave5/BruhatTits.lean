/-
# The Bruhat–Tits tree (Voight, section 23.5)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definitions 23.5.3, 23.5.5,
23.5.4, Proposition 23.5.8, 23.5.11, (23.5.12), 23.5.14, Lemma 23.5.15 (pp. 386–389).

**Setting.** $R$ is a discrete valuation ring with fraction field $F$ (`K`), uniformizer $\pi$, residue field $k$;
$V = F^2$; lattices are $R$-lattices in $V$ (`Lat R K`, Mathlib's `Submodule.IsLattice`).

**Contents.**
* `Homothetic` (Definition 23.5.3), `homothety` (the equivalence relation), `Vert R K` (homothety classes).
* `btRel`, `bruhatTits R K π` (Definition 23.5.5): the graph on `Vert R K` with an edge between $[L] \ne [L']$ when some
  representatives satisfy $\pi L \subsetneq L' \subsetneq L$ (23.5.6). Built with `SimpleGraph.fromRel`, which
  symmetrizes and removes loops; `btRel_irrefl` shows the relation has no loops anyway, so nothing is lost.
* `endOrder L`: $\operatorname{End}_R(L) \subseteq \mathrm M_2(F)$; `endOrder_colLat`: $\operatorname{End}_R(PR^2) = P\,\mathrm M_2(R)\,P^{-1}$.
* `vertEquivMaxOrder` (the sentence after Definition 23.5.5, with Lemma 23.5.2): $[L] \mapsto \operatorname{End}_R(L)$ is a
  bijection from the vertices onto the maximal $R$-orders of $\mathrm M_2(F)$.
* `smulVert`, `bruhatTits_adj_smul` (23.5.11): $\mathrm{GL}_2(F)$ acts on the vertices, preserving adjacency, and
  `smulVert_transitive`: transitively.
* `bruhatTits_connected` (Proposition 23.5.8, connectedness).
* `BruhatTitsDegree` (Proposition 23.5.8, degree part): every vertex has degree $\#k + 1$ (proved as
  `bruhatTitsDegree` in `Wave5/BruhatTitsDegree.lean`).
  The tree part (`bruhatTits_isTree`) and the distance (Lemma 23.5.15, `dist_diag`) are in `Wave5/BruhatTitsHeight.lean`.
-/
import QuadFormsKB.Literature.Voight.Wave5.LatticeBasis

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

open Matrix Pointwise

noncomputable section

namespace QuadFormsKB.Voight.Wave8

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5
  IsLocalization

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Lattices, homothety, vertices -/

/-- The $R$-lattices in $V = F^2$: finitely generated $R$-submodules $L$ with $FL = V$. -/
def Lat : Type _ := {L : Submodule R (Fin 2 → K) // Submodule.IsLattice K L}

variable {R K}

/-- **Homothety** (Voight 2021, Definition 23.5.3): $L' = aL$ for some $a \in F^\times$. -/
@[kb "voight2021" "Definition 23.5.3, p. 386"]
def Homothetic (L L' : Submodule R (Fin 2 → K)) : Prop := ∃ a : K, a ≠ 0 ∧ L' = a • L

theorem Homothetic.refl (L : Submodule R (Fin 2 → K)) : Homothetic L L := ⟨1, one_ne_zero, (one_smul _ _).symm⟩

theorem Homothetic.symm {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L') : Homothetic L' L := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a⁻¹, inv_ne_zero ha, by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

theorem Homothetic.trans {L L' L'' : Submodule R (Fin 2 → K)} (h : Homothetic L L') (h' : Homothetic L' L'') :
    Homothetic L L'' := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨b * a, mul_ne_zero hb ha, by rw [smul_smul]⟩

variable (R K) in
/-- Homothety as an equivalence relation on lattices (Voight 2021, after Definition 23.5.3). -/
def homothety : Setoid (Lat R K) where
  r L L' := Homothetic L.1 L'.1
  iseqv := ⟨fun L => Homothetic.refl L.1, Homothetic.symm, Homothetic.trans⟩

variable (R K) in
/-- **The vertices of the Bruhat–Tits tree**: homothety classes $[L]$ of $R$-lattices in $V$ (Definition 23.5.5). -/
@[kb "voight2021" "Definition 23.5.5, p. 387"]
def Vert : Type _ := Quotient (homothety R K)

/-- The class $[L]$. -/
abbrev Lat.cls (L : Lat R K) : Vert R K := Quotient.mk (homothety R K) L

theorem cls_eq_cls_iff {L L' : Lat R K} : L.cls = L'.cls ↔ Homothetic L.1 L'.1 := Quotient.eq

/-! ### The graph -/

/-- The adjacency relation (23.5.6): some representatives satisfy $\pi L \subsetneq L' \subsetneq L$. -/
def btRel (π : R) (x y : Vert R K) : Prop :=
  ∃ L L' : Lat R K, L.cls = x ∧ L'.cls = y ∧ algebraMap R K π • L.1 < L'.1 ∧ L'.1 < L.1

variable (R K) in
/-- **The Bruhat–Tits tree** $\mathcal T$ (Voight 2021, Definition 23.5.5): vertices are homothety classes of
$R$-lattices in $V$; an undirected edge joins $[L]$ and $[L']$ exactly when there are representatives with
$\pi L \subsetneq L' \subsetneq L$ (23.5.6). (`SimpleGraph.fromRel` symmetrizes the relation and excludes loops; by
23.5.7 and `btRel_irrefl` neither changes anything.) -/
@[kb "voight2021" "Definition 23.5.5, p. 387; 23.5.7, p. 387"]
def bruhatTits (π : R) : SimpleGraph (Vert R K) := SimpleGraph.fromRel (btRel π)

/-! ### Column lattices and scaling -/

theorem smul_colLat (a : K) (P : Matrix (Fin 2) (Fin 2) K) : a • colLat R P = colLat R (a • P) := by
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists, mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨r, rfl⟩ := mem_colLat.1 hw
    exact ⟨r, (Matrix.smul_mulVec a P _).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨P *ᵥ vecR r, mem_colLat.2 ⟨r, rfl⟩, (Matrix.smul_mulVec a P _).symm⟩

/-- The lattice $PR^2$ for $P \in \mathrm{GL}_2(F)$, as an element of `Lat R K`. -/
def latOf {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) : Lat R K := ⟨colLat R P, isLattice_colLat hPQ⟩

/-- Powers of a uniformizer: $\pi^k \in R$ iff $k \ge 0$. -/
theorem isInteger_zpow_iff [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) (k : ℤ) :
    IsInteger R (algebraMap R K π ^ k) ↔ 0 ≤ k := by
  constructor
  · intro h
    by_contra hk
    rw [not_le] at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    obtain ⟨r, hr⟩ := h
    have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
    have : algebraMap R K (r * π ^ (n + 1)) = algebraMap R K 1 := by
      rw [map_mul, hr, hn, map_pow, map_one, _root_.zpow_neg, ← zpow_natCast, Nat.cast_add, Nat.cast_one,
        inv_mul_cancel₀ (zpow_ne_zero _ hπK)]
    have h1 : r * π ^ (n + 1) = 1 := IsFractionRing.injective R K this
    exact hπ.not_isUnit (isUnit_of_dvd_one ⟨r * π ^ n, by rw [← h1]; ring⟩)
  · intro hk
    lift k to ℕ using hk
    exact ⟨π ^ k, by simp⟩

/-- $\pi^k\,PR^2 \subseteq PR^2$ iff $k \ge 0$ ($P$ invertible). -/
theorem zpow_smul_colLat_le_iff [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1) (k : ℤ) :
    algebraMap R K π ^ k • colLat R P ≤ colLat R P ↔ 0 ≤ k := by
  rw [smul_colLat, colLat_le_colLat_iff hPQ hQP, Matrix.mul_smul, hQP, mem_matOrder, ← isInteger_zpow_iff (K := K) hπ]
  constructor
  · intro h; simpa using h 0 0
  · intro h i j
    by_cases hij : i = j
    · subst hij; simpa using h
    · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]; exact ⟨0, by simp⟩

/-! ### No loops (23.5.7) -/

theorem smul_submodule_mono (a : K) {L M : Submodule R (Fin 2 → K)} (h : L ≤ M) : a • L ≤ a • M := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
  exact Submodule.smul_mem_pointwise_smul _ _ _ (h hw)

/-- Scaling by a unit of $R$ does not change an $R$-submodule. -/
theorem unit_smul_submodule (u : Rˣ) (L : Submodule R (Fin 2 → K)) : algebraMap R K u • L = L := by
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [algebraMap_smul]; exact L.smul_mem _ hw
  · intro hv
    refine ⟨algebraMap R K ((u⁻¹ : Rˣ) : R) • v, ?_, ?_⟩
    · rw [algebraMap_smul]; exact L.smul_mem _ hv
    · rw [smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]

/-- **No loops** (23.5.7): no lattice $L'$ homothetic to $L$ satisfies $\pi L \subsetneq L' \subsetneq L$. -/
@[kb "voight2021" "23.5.7, p. 387"]
theorem btRel_irrefl [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    (x : Vert R K) : ¬ btRel π x x := by
  rintro ⟨L, L', hL, hL', h1, h2⟩
  rw [← hL'] at hL
  obtain ⟨a, ha, hLL⟩ := (cls_eq_cls_iff.1 hL).symm
  obtain ⟨u, k, rfl⟩ := exists_unit_zpow hπ ha
  obtain ⟨P, Q, hPQ, hQP, hP⟩ := (isLattice_iff_exists_colLat L'.1).1 L'.2
  rw [hLL, mul_smul, unit_smul_submodule, hP] at h1 h2
  -- `L' < π^k L'` forces `k < 0`; `π^(k+1) L' < L'` forces `k ≥ 0`
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  have hk1 : ¬ 0 ≤ k := fun hk => h2.not_ge ((zpow_smul_colLat_le_iff hπ hPQ hQP k).2 hk)
  have hk2 : ¬ k ≤ -1 := by
    intro hk
    apply h1.not_ge
    have h3 := (zpow_smul_colLat_le_iff hπ hPQ hQP (-(k + 1))).2 (by omega)
    have := smul_submodule_mono (algebraMap R K π ^ (k + 1)) h3
    rw [smul_smul, ← zpow_add₀ hπK, add_neg_cancel, zpow_zero, one_smul] at this
    rwa [smul_smul, ← zpow_one_add₀ hπK, add_comm]
  omega

theorem bruhatTits_adj_iff [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    {x y : Vert R K} : (bruhatTits R K π).Adj x y ↔ btRel π x y ∨ btRel π y x := by
  rw [bruhatTits, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h <;> exact btRel_irrefl hπ x h

/-! ### Vertices and maximal orders -/

/-- **The endomorphism ring** $\operatorname{End}_R(L) = \{x \in \mathrm M_2(F) : xL \subseteq L\}$ of an $R$-submodule
$L \subseteq V$ (Voight 2021, section 10.5; Example 10.5.2). -/
@[kb "voight2021" "section 10.5, p. 160"]
def endOrder (L : Submodule R (Fin 2 → K)) : Subalgebra R (Matrix (Fin 2) (Fin 2) K) where
  carrier := {x | ∀ v ∈ L, x *ᵥ v ∈ L}
  mul_mem' {x y} hx hy v hv := by rw [← Matrix.mulVec_mulVec]; exact hx _ (hy v hv)
  one_mem' v hv := by rwa [Matrix.one_mulVec]
  add_mem' {x y} hx hy v hv := by rw [Matrix.add_mulVec]; exact L.add_mem (hx v hv) (hy v hv)
  zero_mem' v _ := by rw [Matrix.zero_mulVec]; exact L.zero_mem
  algebraMap_mem' c v hv := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact L.smul_mem c hv

theorem mem_endOrder {L : Submodule R (Fin 2 → K)} {x : Matrix (Fin 2) (Fin 2) K} :
    x ∈ endOrder L ↔ ∀ v ∈ L, x *ᵥ v ∈ L := Iff.rfl

/-- $\operatorname{End}_R(PR^2) = P\,\mathrm M_2(R)\,P^{-1}$ (Voight 2021, Example 10.5.2 after a change of basis). -/
@[kb "voight2021" "Example 10.5.2, p. 160"]
theorem endOrder_colLat {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    endOrder (colLat R P) = (matOrder R K).map (conjMap P Q hPQ hQP) := by
  ext x
  rw [mem_map_conj hPQ hQP, mem_endOrder, mul_assoc, ← colLat_le_colLat_iff hPQ hQP]
  constructor
  · intro h v hv
    obtain ⟨r, rfl⟩ := mem_colLat.1 hv
    rw [← Matrix.mulVec_mulVec]
    exact h _ (mem_colLat.2 ⟨r, rfl⟩)
  · intro h v hv
    obtain ⟨r, rfl⟩ := mem_colLat.1 hv
    rw [Matrix.mulVec_mulVec]
    exact h (mem_colLat.2 ⟨r, rfl⟩)

/-- Homothetic lattices have the same endomorphism ring. -/
theorem endOrder_smul {a : K} (ha : a ≠ 0) (L : Submodule R (Fin 2 → K)) : endOrder (a • L) = endOrder L := by
  have key : ∀ (b : K) (L : Submodule R (Fin 2 → K)), endOrder L ≤ endOrder (b • L) := by
    intro b L x hx v hv
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (hx w hw)
  apply le_antisymm _ (key a L)
  have := key a⁻¹ (a • L)
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this

variable (R K) in
/-- The map $[L] \mapsto \operatorname{End}_R(L)$ on vertices. -/
def vertOrder : Vert R K → Subalgebra R (Matrix (Fin 2) (Fin 2) K) :=
  Quotient.lift (fun L : Lat R K => endOrder L.1) (by
    rintro L L' ⟨a, ha, h⟩
    rw [h, endOrder_smul ha])

variable [IsPrincipalIdealRing R]

theorem isMaximalOrder_vertOrder [IsIntegrallyClosed R] (x : Vert R K) : IsMaximalOrder R K (vertOrder R K x) := by
  induction x using Quotient.inductionOn with | h L => ?_
  obtain ⟨P, Q, hPQ, hQP, hP⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
  change IsMaximalOrder R K (endOrder L.1)
  rw [hP, endOrder_colLat hPQ hQP]
  exact isMaximalOrder_matOrder.map (conjAlgEquiv P Q hPQ hQP)

/-- **Vertices of the Bruhat–Tits tree are maximal orders** (Voight 2021, sentence after Definition 23.5.5, using
Lemma 23.5.2 and Corollary 10.5.5): $[L] \mapsto \operatorname{End}_R(L)$ is a bijection from homothety classes of
$R$-lattices in $F^2$ onto the maximal $R$-orders of $\mathrm M_2(F)$. -/
@[kb "voight2021" "Definition 23.5.5, p. 387; Lemma 23.5.2, p. 386"]
theorem vertOrder_bijective [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    Function.Bijective (fun x : Vert R K => (⟨vertOrder R K x, isMaximalOrder_vertOrder x⟩ :
      {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K) // IsMaximalOrder R K O})) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with | h L => ?_
    induction y using Quotient.inductionOn with | h L' => ?_
    have h : endOrder L.1 = endOrder L'.1 := congrArg Subtype.val hxy
    obtain ⟨P, Q, hPQ, hQP, hP⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
    obtain ⟨P', Q', hPQ', hQP', hP'⟩ := (isLattice_iff_exists_colLat L'.1).1 L'.2
    rw [hP, hP', endOrder_colLat hPQ hQP, endOrder_colLat hPQ' hQP'] at h
    -- conjugating by `Q'` gives `(Q'P) M₂(R) (Q'P)⁻¹ = M₂(R)`
    have hgh : (Q' * P) * (Q * P') = 1 := by rw [mul_assoc, ← mul_assoc P, hPQ, one_mul, hQP']
    have hhg : (Q * P') * (Q' * P) = 1 := by rw [mul_assoc, ← mul_assoc P', hPQ', one_mul, hQP]
    have h2 : (matOrder R K).map (conjMap (Q' * P) (Q * P') hgh hhg) = matOrder R K := by
      have := congrArg (Subalgebra.map (conjMap Q' P' hQP' hPQ')) h
      rw [map_map_conj] at this
      calc _ = ((matOrder R K).map (conjMap P Q hPQ hQP)).map (conjMap Q' P' hQP' hPQ') := by
            rw [Subalgebra.map_map]
            congr 1
            apply AlgHom.ext; intro z
            simp only [AlgHom.comp_apply]
            change Q' * P * z * (Q * P') = Q' * (P * z * Q) * P'
            simp only [mul_assoc]
        _ = matOrder R K := this
    obtain ⟨c, U, U', hc, hU, -, hcU⟩ := (map_conj_matOrder_eq_iff hπ hgh hhg).1 h2
    apply Quotient.sound
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    change L'.1 = c⁻¹ • L.1
    rw [hP, hP', smul_colLat]
    have : P = c • (P' * mapR U) := by
      calc P = P' * (Q' * P) := by rw [← mul_assoc, hPQ', one_mul]
        _ = c • (P' * mapR U) := by rw [hcU, Matrix.mul_smul]
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul, colLat_mul_mapR hU]
  · rintro ⟨O, hO⟩
    obtain ⟨P, Q, hPQ, hQP, rfl⟩ := exists_eq_conj_matOrder hO
    refine ⟨(latOf (R := R) hPQ).cls, Subtype.ext ?_⟩
    change endOrder (colLat R P) = _
    exact endOrder_colLat hPQ hQP

/-! ### The action of $\mathrm{GL}_2(F)$ (23.5.11) -/

/-- $g \cdot L$: the image of $L$ under $g \in \mathrm{GL}_2(F)$. -/
def latMap (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (L : Submodule R (Fin 2 → K)) : Submodule R (Fin 2 → K) :=
  L.map ((Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) K)).restrictScalars R)

theorem mem_latMap {g : (Matrix (Fin 2) (Fin 2) K)ˣ} {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latMap g L ↔ ∃ w ∈ L, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = v := by
  simp [latMap]

theorem latMap_colLat (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (P : Matrix (Fin 2) (Fin 2) K) :
    latMap g (colLat R P) = colLat R ((g : Matrix (Fin 2) (Fin 2) K) * P) := by
  ext v
  rw [mem_latMap, mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨r, rfl⟩ := mem_colLat.1 hw
    exact ⟨r, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨P *ᵥ vecR r, mem_colLat.2 ⟨r, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩

theorem latMap_smul (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (a : K) (L : Submodule R (Fin 2 → K)) :
    latMap g (a • L) = a • latMap g L := by
  ext v
  simp only [mem_latMap, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, by rw [Matrix.mulVec_smul]⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨a • u, ⟨u, hu, rfl⟩, by rw [Matrix.mulVec_smul]⟩

theorem latMap_strictMono (g : (Matrix (Fin 2) (Fin 2) K)ˣ) : StrictMono (latMap (R := R) g) := by
  apply Submodule.map_strictMono_of_injective
  intro v w h
  have h' : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w := h
  have := congrArg (((g⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K) *ᵥ ·) h'
  change _ *ᵥ (_ *ᵥ v) = _ *ᵥ (_ *ᵥ w) at this
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at this

/-- $g \cdot L$ as a lattice. -/
def Lat.smul (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (L : Lat R K) : Lat R K :=
  ⟨latMap g L.1, by
    obtain ⟨P, Q, hPQ, -, hP⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
    rw [hP, latMap_colLat]
    have : ((g : Matrix (Fin 2) (Fin 2) K) * P) * (Q * ((g⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) :
        Matrix (Fin 2) (Fin 2) K)) = 1 := by
      rw [mul_assoc, ← mul_assoc P, hPQ, one_mul, Units.mul_inv]
    exact isLattice_colLat this⟩

/-- **The action of $\mathrm{GL}_2(F)$ on the vertices** (Voight 2021, 23.5.11): $g[L] = [gL]$. -/
@[kb "voight2021" "23.5.11, p. 388"]
def smulVert (g : (Matrix (Fin 2) (Fin 2) K)ˣ) : Vert R K → Vert R K :=
  Quotient.map (Lat.smul g) (by
    rintro L L' ⟨a, ha, h⟩
    exact ⟨a, ha, by change latMap g L'.1 = a • latMap g L.1; rw [h, latMap_smul]⟩)

theorem smulVert_cls (g : (Matrix (Fin 2) (Fin 2) K)ˣ) (L : Lat R K) : smulVert g L.cls = (L.smul g).cls := rfl

/-- **$\mathrm{GL}_2(F)$ preserves adjacency** (Voight 2021, 23.5.11). -/
@[kb "voight2021" "23.5.11, p. 388"]
theorem bruhatTits_adj_smulVert {π : R} (g : (Matrix (Fin 2) (Fin 2) K)ˣ) {x y : Vert R K}
    (h : (bruhatTits R K π).Adj x y) : (bruhatTits R K π).Adj (smulVert g x) (smulVert g y) := by
  have key : ∀ x y : Vert R K, btRel π x y → btRel π (smulVert g x) (smulVert g y) := by
    rintro _ _ ⟨L, L', rfl, rfl, h1, h2⟩
    refine ⟨L.smul g, L'.smul g, rfl, rfl, ?_, ?_⟩
    · change algebraMap R K π • latMap g L.1 < latMap g L'.1
      rw [← latMap_smul]; exact latMap_strictMono g h1
    · exact latMap_strictMono g h2
  rw [bruhatTits, SimpleGraph.fromRel_adj] at h ⊢
  refine ⟨fun heq => h.1 ?_, h.2.imp (key x y) (key y x)⟩
  have hinv : ∀ z : Vert R K, smulVert g⁻¹ (smulVert g z) = z := by
    intro z
    induction z using Quotient.inductionOn with | h L => ?_
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change latMap g⁻¹ (latMap g L.1) = L.1
    ext v
    simp only [mem_latMap]
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · intro hv
      exact ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ v, ⟨v, hv, rfl⟩, by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]⟩
  rw [← hinv x, heq, hinv]

variable [IsPrincipalIdealRing R]

/-- **$\mathrm{GL}_2(F)$ acts transitively on the vertices** (Voight 2021, 23.5.11). -/
@[kb "voight2021" "23.5.11, p. 388; (23.5.12), p. 388"]
theorem smulVert_transitive (x y : Vert R K) : ∃ g : (Matrix (Fin 2) (Fin 2) K)ˣ, smulVert g x = y := by
  induction x using Quotient.inductionOn with | h L => ?_
  induction y using Quotient.inductionOn with | h L' => ?_
  obtain ⟨P, Q, hPQ, hQP, hP⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
  obtain ⟨P', Q', hPQ', hQP', hP'⟩ := (isLattice_iff_exists_colLat L'.1).1 L'.2
  refine ⟨⟨P' * Q, P * Q', by rw [mul_assoc, ← mul_assoc Q, hQP, one_mul, hPQ'],
    by rw [mul_assoc, ← mul_assoc Q', hQP', one_mul, hPQ]⟩, ?_⟩
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  change latMap _ L.1 = L'.1
  rw [hP, hP', latMap_colLat]
  change colLat R (P' * Q * P) = _
  rw [mul_assoc, hQP, mul_one]

/-! ### Connectedness (Proposition 23.5.8) -/

/-- Inclusion of diagonally rescaled column lattices: for $P$ invertible and $d, d'$ with nonzero entries,
$P\operatorname{diag}(d)R^2 \subseteq P\operatorname{diag}(d')R^2$ iff every $d_i/d'_i \in R$. -/
theorem colLat_mul_diagonal_le_iff {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {d d' : Fin 2 → K} (hd' : ∀ i, d' i ≠ 0) :
    colLat R (P * Matrix.diagonal d) ≤ colLat R (P * Matrix.diagonal d') ↔ ∀ i, IsInteger R (d i / d' i) := by
  have h1 : (P * Matrix.diagonal d') * (Matrix.diagonal (fun i => (d' i)⁻¹) * Q) = 1 := by
    rw [mul_assoc, ← mul_assoc (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
    rw [show (fun i => d' i * (d' i)⁻¹) = fun _ => (1 : K) from funext fun i => mul_inv_cancel₀ (hd' i)]
    rw [Matrix.diagonal_one, one_mul, hPQ]
  have h2 : (Matrix.diagonal (fun i => (d' i)⁻¹) * Q) * (P * Matrix.diagonal d') = 1 := by
    rw [mul_assoc, ← mul_assoc Q, hQP, one_mul, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (d' i)⁻¹ * d' i) = fun _ => (1 : K) from funext fun i => inv_mul_cancel₀ (hd' i)]
    rw [Matrix.diagonal_one]
  rw [colLat_le_colLat_iff h1 h2]
  have h3 : Matrix.diagonal (fun i => (d' i)⁻¹) * Q * (P * Matrix.diagonal d) =
      Matrix.diagonal (fun i => d i / d' i) := by
    rw [mul_assoc, ← mul_assoc Q, hQP, one_mul, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; rw [div_eq_inv_mul]
  rw [h3, mem_matOrder]
  constructor
  · intro h i; simpa using h i i
  · intro h i j
    by_cases hij : i = j
    · subst hij; simpa using h i
    · rw [Matrix.diagonal_apply_ne _ hij]; exact ⟨0, by simp⟩

theorem smul_colLat_mul_diagonal (a : K) (P : Matrix (Fin 2) (Fin 2) K) (d : Fin 2 → K) :
    a • colLat R (P * Matrix.diagonal d) = colLat R (P * Matrix.diagonal (fun i => a * d i)) := by
  rw [smul_colLat, ← Matrix.mul_smul]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem isInteger_one' : IsInteger R (1 : K) := ⟨1, by simp⟩

theorem not_isInteger_inv [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    ¬ IsInteger R (algebraMap R K π)⁻¹ := by
  have := (isInteger_zpow_iff (K := K) hπ (-1)).not.2 (by omega)
  simpa using this

/-- The strict inclusions $\pi L_i \subsetneq L_{i+1} \subsetneq L_i$ for $L_i = P\operatorname{diag}(1,\pi^i)R^2$. -/
theorem diagP_succ_lt [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) {P Q : Matrix (Fin 2) (Fin 2) K}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) :
    algebraMap R K π • colLat R (P * diagP π i) < colLat R (P * diagP π (i + 1)) ∧
      colLat R (P * diagP π (i + 1)) < colLat R (P * diagP π i) := by
  have hπK : algebraMap R K π ≠ 0 := algebraMap_ne_zero hπ.ne_zero
  have hne : ∀ j : ℕ, ∀ k, (![1, algebraMap R K π ^ j] : Fin 2 → K) k ≠ 0 := by
    intro j k; fin_cases k <;> simp [hπK]
  refine ⟨?_, ?_⟩
  · rw [diagP, diagP, smul_colLat_mul_diagonal]
    refine lt_of_le_not_ge ?_ ?_
    · rw [colLat_mul_diagonal_le_iff hPQ hQP (hne _)]
      intro k; fin_cases k
      · simpa using isInteger_algebraMap (K := K) π
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        convert isInteger_one' (R := R) (K := K) using 1
        rw [pow_succ]; field_simp
    · have hne' : ∀ k, (fun k => algebraMap R K π * (![1, algebraMap R K π ^ i] : Fin 2 → K) k) k ≠ 0 := by
        intro k; fin_cases k <;> simp [hπK]
      rw [colLat_mul_diagonal_le_iff hPQ hQP hne']
      intro h
      have := h 0
      simp only [Matrix.cons_val_zero, mul_one] at this
      rw [one_div] at this
      exact not_isInteger_inv hπ this
  · rw [diagP, diagP]
    refine lt_of_le_not_ge ?_ ?_
    · rw [colLat_mul_diagonal_le_iff hPQ hQP (hne _)]
      intro k; fin_cases k
      · simpa using isInteger_one' (R := R) (K := K)
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero _ hπK)]
        exact isInteger_algebraMap π
    · rw [colLat_mul_diagonal_le_iff hPQ hQP (hne _)]
      intro h
      have := h 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      rw [pow_succ, div_mul_cancel_left₀ (pow_ne_zero _ hπK)] at this
      exact not_isInteger_inv hπ this

/-- One step of the path $[L_i] — [L_{i+1}]$, $L_i = P\operatorname{diag}(1,\pi^i)R^2$, in the proof of
Proposition 23.5.8. -/
theorem btRel_diagP_succ [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) {P Q : Matrix (Fin 2) (Fin 2) K}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) :
    btRel π (latOf (R := R) (Q := diagQ π i * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π i), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π i * (diagQ π i * Q) = 1)).cls
      (latOf (R := R) (Q := diagQ π (i + 1) * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π (i + 1)), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π (i + 1) * (diagQ π (i + 1) * Q) = 1)).cls :=
  ⟨_, _, rfl, rfl, (diagP_succ_lt hπ hPQ hQP i).1, (diagP_succ_lt hπ hPQ hQP i).2⟩

/-- **The Bruhat–Tits tree is connected** (Voight 2021, Proposition 23.5.8, connectedness): every vertex is joined
by a path to $[R^2]$. -/
@[kb "voight2021" "Proposition 23.5.8, p. 387"]
theorem bruhatTits_connected [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    (bruhatTits R K π).Connected := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) K) * 1 = 1 := one_mul 1
  -- path from `[P R²]` to `[P diag(1,π^e) R²]`
  have path : ∀ {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1) (e : ℕ),
      (bruhatTits R K π).Reachable
        (latOf (R := R) (Q := diagQ π 0 * Q) (by
          rw [mul_assoc, ← mul_assoc (diagP π 0), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
          P * diagP π 0 * (diagQ π 0 * Q) = 1)).cls
        (latOf (R := R) (Q := diagQ π e * Q) (by
          rw [mul_assoc, ← mul_assoc (diagP π e), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
          P * diagP π e * (diagQ π e * Q) = 1)).cls := by
    intro P Q hPQ hQP e
    induction e with
    | zero => rfl
    | succ i ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [bruhatTits_adj_iff hπ]
      exact Or.inl (btRel_diagP_succ hπ hPQ hQP i)
  have : Nonempty (Vert R K) := ⟨(latOf (R := R) h1).cls⟩
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : Vert R K, (bruhatTits R K π).Reachable (latOf (R := R) h1).cls z from
    (h x).symm.trans (h y)
  intro z
  induction z using Quotient.inductionOn with | h L => ?_
  obtain ⟨P, Q, hPQ, hQP, hP⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
  obtain ⟨c, e, U, U', V, V', hc, hU, hU', hV, hV', hg⟩ := exists_eq_smul_mul_diag_mul (K := K) hπ hPQ
  have hUU : mapR (K := K) U * mapR U' = 1 := by rw [← mapR_mul, hU, mapR_one]
  have hUU' : mapR (K := K) U' * mapR U = 1 := by rw [← mapR_mul, hU', mapR_one]
  have key : ∀ a b a' b' : Vert R K, (bruhatTits R K π).Reachable a b → a = a' → b = b' →
      (bruhatTits R K π).Reachable a' b' := by
    rintro _ _ _ _ h rfl rfl; exact h
  refine key _ _ _ _ (path hUU hUU' e) ?_ ?_
  · apply congrArg (Quotient.mk _); apply Subtype.ext
    change colLat R (mapR U * diagP π 0) = colLat R 1
    rw [show diagP (K := K) π 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [diagP], mul_one,
      ← one_mul (mapR (K := K) U), colLat_mul_mapR hU]
  · apply Quotient.sound
    refine ⟨c, hc, ?_⟩
    change L.1 = c • colLat R (mapR U * diagP π e)
    rw [hP, hg, smul_colLat, mapR_mul, mapR_mul, mapR_diagR, ← Matrix.smul_mul, colLat_mul_mapR hV]

/-- **Lemma 23.5.15, upper bound**: for $L = PR^2$ and $L' = P\operatorname{diag}(1,\pi^e)R^2$ (bases $x_0, x_1$ and
$x_0, \pi^e x_1$; the book's $\pi^f$ rescaling does not change the vertex), $d([L],[L']) \le e$ (equality: `dist_diag`), via the path
$L_i = Rx_0 + \pi^i Rx_1$, $i = 0, \dots, e$. -/
@[kb "voight2021" "Lemma 23.5.15, p. 389"]
theorem dist_le_diag [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) {P Q : Matrix (Fin 2) (Fin 2) K}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (e : ℕ) :
    (bruhatTits R K π).dist (latOf (R := R) hPQ).cls
      (latOf (R := R) (Q := diagQ π e * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π e), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π e * (diagQ π e * Q) = 1)).cls ≤ e := by
  -- the walk `L_0 — L_1 — ⋯ — L_e`
  have walk : ∀ e : ℕ, ∃ w : (bruhatTits R K π).Walk
      (latOf (R := R) (Q := diagQ π 0 * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π 0), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π 0 * (diagQ π 0 * Q) = 1)).cls
      (latOf (R := R) (Q := diagQ π e * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π e), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π e * (diagQ π e * Q) = 1)).cls, w.length = e := by
    intro e
    induction e with
    | zero => exact ⟨SimpleGraph.Walk.nil, rfl⟩
    | succ i ih =>
      obtain ⟨w, hw⟩ := ih
      have hadj := (bruhatTits_adj_iff (K := K) hπ).2 (Or.inl (btRel_diagP_succ hπ hPQ hQP i))
      exact ⟨w.concat hadj, by rw [SimpleGraph.Walk.length_concat, hw]⟩
  obtain ⟨w, hw⟩ := walk e
  have h0 : (latOf (R := R) hPQ).cls = (latOf (R := R) (Q := diagQ π 0 * Q) (by
        rw [mul_assoc, ← mul_assoc (diagP π 0), diagP_mul_diagQ hπ.ne_zero, one_mul, hPQ] :
        P * diagP π 0 * (diagQ π 0 * Q) = 1)).cls := by
    apply congrArg (Quotient.mk _); apply Subtype.ext
    change colLat R P = colLat R (P * diagP π 0)
    rw [show diagP (K := K) π 0 = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [diagP], mul_one]
  rw [h0]
  calc _ ≤ w.length := SimpleGraph.dist_le w
    _ = e := hw

/-! ### Proposition 23.5.8, degree (the statement) -/

variable (R K) in
/-- **Proposition 23.5.8** (Voight 2021), degree part, as a named proposition: every vertex of $\mathcal T$ has exactly
$\#k + 1$ neighbours, $k = R/\pi R$ the residue field (counted with `ENat.card`, so the statement also covers an infinite
residue field, where both sides are $\infty$; in the book $k$ is finite, $\#k = q$).

Proved as `bruhatTitsDegree` (in `Wave5/BruhatTitsDegree.lean`): the neighbours of $[R^2]$ correspond to the lines of
$k^2$. The tree part of Proposition 23.5.8 is `bruhatTits_isTree` (in `Wave5/BruhatTitsHeight.lean`). -/
@[kb "voight2021" "Proposition 23.5.8, p. 387"]
def BruhatTitsDegree [IsDiscreteValuationRing R] (π : R) : Prop :=
  ∀ x : Vert R K, ENat.card ((bruhatTits R K π).neighborSet x) = ENat.card (IsLocalRing.ResidueField R) + 1

end QuadFormsKB.Voight.Wave8
