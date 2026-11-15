/-
# Eichler orders and the Bruhat–Tits tree (Voight, Lemma 23.5.15 and 23.5.16)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Lemma 23.5.15 and the paragraph
23.5.16 after it (Eichler orders correspond to paths in the Bruhat–Tits tree).

**Setting.** $R$ is a discrete valuation ring with fraction field $F$ (`K`) and uniformizer $\pi$; the vertices of the
Bruhat–Tits tree `bruhatTits R K π` are the homothety classes $[L]$ of $R$-lattices $L \subseteq F^2$, and
`vertOrder R K [L]` $= \operatorname{End}_R(L)$ is the maximal order attached to $[L]$ (`Wave5/BruhatTits.lean`).

**Contents.**
* `vertOrder_inf_eq_conj` (Lemma 23.5.15 in order form, 23.5.16): for vertices $x, y$ at distance $e$,
  $\operatorname{End}_R(x) \cap \operatorname{End}_R(y)$ is conjugate to the standard Eichler order
  $\mathcal O_0(\pi^e) = \begin{pmatrix} R & R \\ \pi^e R & R \end{pmatrix}$; so it is an Eichler order of level $\pi^e$.
* `level_eq_dist`: conversely the level is the distance: if $\operatorname{End}_R(x) \cap \operatorname{End}_R(y)$ is
  conjugate to $\mathcal O_0(\pi^f)$ then $f = d(x, y)$.
* `isEichler_iff_exists_vert` (23.5.16): the Eichler orders of $\mathrm M_2(F)$ are exactly the intersections
  $\operatorname{End}_R(x) \cap \operatorname{End}_R(y)$ of the maximal orders of two vertices (equivalently, the ends of a
  path of length $e$ in the tree, $e$ the level).
-/
import QuadFormsKB.Literature.Voight.Wave5.BruhatTitsHeight
import QuadFormsKB.Literature.Voight.Wave4.EichlerLevel

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

open Matrix Pointwise

noncomputable section

namespace QuadFormsKB.Voight.Wave8

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5
  IsLocalization

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **Lemma 23.5.15 and 23.5.16** (Voight 2021), Eichler orders from the tree: for vertices $x, y$ of the
Bruhat–Tits tree at distance $e = d(x, y)$ there is $P \in \mathrm{GL}_2(F)$ with
$$\operatorname{End}_R(x) \cap \operatorname{End}_R(y) = P\,\mathcal O_0(\pi^e)\,P^{-1}, \qquad
\mathcal O_0(\pi^e) = \begin{pmatrix} R & R \\ \pi^e R & R \end{pmatrix},$$
i.e. the intersection of the maximal orders of two vertices at distance $e$ is an Eichler order of level $\pi^e$.

Proof: write $x = [P_1R^2]$, $y = [P_2R^2]$ and $P_1^{-1}P_2 = cU\operatorname{diag}(1,\pi^e)V$ (Cartan decomposition,
`exists_eq_smul_mul_diag_mul`); with $P = P_1U$ we get $x = [PR^2]$, $y = [P\operatorname{diag}(1,\pi^e)R^2]$, so
$d(x,y) = e$ (`dist_diag`), and the intersection is $P(\mathrm M_2(R) \cap D\,\mathrm M_2(R)D^{-1})P^{-1}$,
$D = \operatorname{diag}(1, \pi^e)$, whose middle factor is $\mathcal O_0(\pi^e)$ (`stdEichlerOrder_eq_inf`). -/
@[kb "voight2021" "Lemma 23.5.15, p. 389; 23.5.16, p. 389"]
theorem vertOrder_inf_eq_conj {π : R} (hπ : Irreducible π) (x y : Vert R K) :
    ∃ (P Q : Matrix (Fin 2) (Fin 2) K) (hPQ : P * Q = 1) (hQP : Q * P = 1),
      vertOrder R K x ⊓ vertOrder R K y =
        (stdEichlerOrder R K π ((bruhatTits R K π).dist x y)).map (conjMap P Q hPQ hQP) := by
  induction x using Quotient.inductionOn with | h L => ?_
  induction y using Quotient.inductionOn with | h L' => ?_
  obtain ⟨P₁, Q₁, h₁₁, h₁₂, hL⟩ := (isLattice_iff_exists_colLat L.1).1 L.2
  obtain ⟨P₂, Q₂, h₂₁, h₂₂, hL'⟩ := (isLattice_iff_exists_colLat L'.1).1 L'.2
  have hgh : (Q₁ * P₂) * (Q₂ * P₁) = 1 := by
    rw [mul_assoc, ← mul_assoc P₂, h₂₁, one_mul, h₁₂]
  obtain ⟨c, e, U, U', V, V', hc, hU, hU', hV, hV', hg⟩ := exists_eq_smul_mul_diag_mul (K := K) hπ hgh
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set mU := mapR (K := K) U
  set mU' := mapR (K := K) U'
  set mV := mapR (K := K) V
  set mV' := mapR (K := K) V'
  set dP := diagP (K := K) π e
  set dQ := diagQ (K := K) π e
  have hdPQ : dP * dQ = 1 := diagP_mul_diagQ hπ0 e
  have hdQP : dQ * dP = 1 := diagQ_mul_diagP hπ0 e
  have hmUU' : mU * mU' = 1 := by rw [← mapR_mul, hU, mapR_one]
  have hmU'U : mU' * mU = 1 := by rw [← mapR_mul, hU', mapR_one]
  have hmVV' : mV * mV' = 1 := by rw [← mapR_mul, hV, mapR_one]
  have hg' : Q₁ * P₂ = c • (mU * dP * mV) := by rw [hg, mapR_mul, mapR_mul, mapR_diagR]
  have key₂ : P₁ * mU * dP = c⁻¹ • (P₂ * mV') := by
    have : Q₁ * P₂ * mV' = c • (mU * dP) := by
      rw [hg', Matrix.smul_mul]; congr 1; rw [mul_assoc, hmVV', mul_one]
    have h2 : P₂ * mV' = c • (P₁ * mU * dP) := by
      calc P₂ * mV' = P₁ * (Q₁ * P₂ * mV') := by simp only [← mul_assoc]; rw [h₁₁, one_mul]
        _ = c • (P₁ * mU * dP) := by rw [this, Matrix.mul_smul, ← mul_assoc]
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hPQ : (P₁ * mU) * (mU' * Q₁) = 1 := by
    rw [mul_assoc, ← mul_assoc mU, hmUU', one_mul, h₁₁]
  have hQP : (mU' * Q₁) * (P₁ * mU) = 1 := by
    rw [mul_assoc, ← mul_assoc Q₁, h₁₂, one_mul, hmU'U]
  have hPQd : P₁ * mU * dP * (dQ * (mU' * Q₁)) = 1 := by
    rw [mul_assoc, ← mul_assoc dP, hdPQ, one_mul, hPQ]
  have hQPd : dQ * (mU' * Q₁) * (P₁ * mU * dP) = 1 := by
    rw [mul_assoc, ← mul_assoc (mU' * Q₁), hQP, one_mul, hdQP]
  -- the two vertices
  have hx : (Quotient.mk (homothety R K) L : Vert R K) = (latOf (R := R) hPQ).cls := by
    apply congrArg Lat.cls
    apply Subtype.ext
    change L.1 = colLat R (P₁ * mU)
    rw [hL, colLat_mul_mapR hU]
  have hy : (Quotient.mk (homothety R K) L' : Vert R K) = (latOf (R := R) hPQd).cls := by
    apply cls_eq_cls_iff.2
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    change colLat R (P₁ * mU * dP) = c⁻¹ • L'.1
    rw [key₂, ← smul_colLat, colLat_mul_mapR hV', hL']
  have hdist : (bruhatTits R K π).dist (Quotient.mk (homothety R K) L) (Quotient.mk (homothety R K) L') = e := by
    rw [hx, hy]
    exact dist_diag hπ hPQ hQP e
  rw [hdist]
  refine ⟨P₁ * mU, mU' * Q₁, hPQ, hQP, ?_⟩
  rw [hx, hy]
  change endOrder (colLat R (P₁ * mU)) ⊓ endOrder (colLat R (P₁ * mU * dP)) = _
  rw [endOrder_colLat hPQ hQP, endOrder_colLat hPQd hQPd]
  ext z
  rw [Algebra.mem_inf, mem_map_conj, mem_map_conj, mem_map_conj, stdEichlerOrder_eq_inf hπ0, Algebra.mem_inf,
    mem_conjMatOrder]
  apply and_congr Iff.rfl
  rw [show dQ * (mU' * Q₁) * z * (P₁ * mU * dP) = dQ * (mU' * Q₁ * z * (P₁ * mU)) * dP by
    simp only [mul_assoc]]

/-- The intersection of the maximal orders of two vertices is an Eichler order (Voight 2021, 23.5.16). -/
theorem isEichler_vertOrder_inf (x y : Vert R K) :
    IsEichler R K (vertOrder R K x ⊓ vertOrder R K y) :=
  ⟨_, _, isMaximalOrder_vertOrder x, isMaximalOrder_vertOrder y, rfl⟩

/-- **The level is the distance** (Voight 2021, 23.5.16): if $\operatorname{End}_R(x) \cap \operatorname{End}_R(y)$ is
conjugate to the standard Eichler order $\mathcal O_0(\pi^f)$, then $f = d(x, y)$; so the Eichler order attached to two
vertices has level $\pi^{d(x,y)}$, and to a path of length $e$ in the tree corresponds an Eichler order of level
$\pi^e$. -/
@[kb "voight2021" "23.5.16, p. 389"]
theorem level_eq_dist {π : R} (hπ : Irreducible π) (x y : Vert R K) {f : ℕ}
    {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : vertOrder R K x ⊓ vertOrder R K y = (stdEichlerOrder R K π f).map (conjMap P Q hPQ hQP)) :
    f = (bruhatTits R K π).dist x y := by
  obtain ⟨P', Q', hPQ', hQP', h'⟩ := vertOrder_inf_eq_conj hπ x y
  exact (existsUnique_level hπ (isEichler_vertOrder_inf x y)).unique ⟨P, Q, hPQ, hQP, h⟩
    ⟨P', Q', hPQ', hQP', h'⟩

/-- **Eichler orders are pairs of vertices** (Voight 2021, 23.5.16): an $R$-subalgebra $\mathcal O \subseteq \mathrm M_2(F)$
is an Eichler order iff $\mathcal O = \operatorname{End}_R(x) \cap \operatorname{End}_R(y)$ for two vertices $x, y$ of the
Bruhat–Tits tree (its level is then $\pi^{d(x,y)}$, `level_eq_dist`). -/
@[kb "voight2021" "23.5.16, p. 389"]
theorem isEichler_iff_exists_vert {π : R} (hπ : Irreducible π) (O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)) :
    IsEichler R K O ↔ ∃ x y : Vert R K, O = vertOrder R K x ⊓ vertOrder R K y := by
  constructor
  · rintro ⟨O₁, O₂, h₁, h₂, rfl⟩
    obtain ⟨x, hx⟩ := (vertOrder_bijective (K := K) hπ).2 ⟨O₁, h₁⟩
    obtain ⟨y, hy⟩ := (vertOrder_bijective (K := K) hπ).2 ⟨O₂, h₂⟩
    have hx' : vertOrder R K x = O₁ := congrArg Subtype.val hx
    have hy' : vertOrder R K y = O₂ := congrArg Subtype.val hy
    exact ⟨x, y, by rw [hx', hy']⟩
  · rintro ⟨x, y, rfl⟩
    exact isEichler_vertOrder_inf x y

end QuadFormsKB.Voight.Wave8
