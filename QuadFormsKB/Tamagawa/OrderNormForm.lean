/-
# The norm form of an order, and the base case reduced to any order containing the standard one

**Layer:** $F$ a number field, $\mathcal O_F$ a PID, $a, b \in \mathcal O_F$, $D = (a,b)_F$.

An $\mathcal O_F$-order $\mathcal O \supseteq \mathcal O_F\langle 1,i,j,k\rangle$ of $D$ is a free $\mathcal O_F$-module of rank 4 (`IsLattice`, Mathlib);
in a basis $e_0, \dots, e_3$ the reduced norm is an integral quaternary form `Q` (`exists_orderForm`): its coefficients are
$\operatorname{nrd}(e_i)$ and $\operatorname{nrd}(e_i + e_j) - \operatorname{nrd}(e_i) - \operatorname{nrd}(e_j)$, integral by `isInteger_trd_nrd`. The standard
basis $1, i, j, k$ lies in $\mathcal O$, so $\langle 1,-a,-b,ab\rangle = Q\circ G$ for an integral $G$ with $\det G \ne 0$, and the change-of-lattice theorem `LatChange.tauSO_smul_compMat` gives
$$\tau(SO(\mathcal O, \operatorname{nrd})) = \tau(SO(\mathcal O_F\langle1,i,j,k\rangle, \operatorname{nrd}))\qquad(\texttt{tauSO\_orderForm}).$$
Consequently `TernaryTamagawaTwo F` follows from $\tau(SO(\mathcal O_D, \operatorname{nrd})) = 2$ for **one** order $\mathcal O_D \supseteq$ the
standard order of each totally definite $D$, e.g. a maximal order (`ternaryTamagawaTwo_of_orders`).

Sources: Voight, *Quaternion Algebras* (2021), §15.2 (the norm form of a lattice) ; Weil 1982, §2.2.1, p. 14 (independence of
the lattice), via `TernaryReduction`.
-/
import QuadFormsKB.Tamagawa.QuatOrder
import QuadFormsKB.Tamagawa.TernaryReduction
import Mathlib.Algebra.Module.Lattice

open Matrix NumberField Filter Topology Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.QuadForm QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Tamagawa
  QuadFormsKB.HilbertModular IsLocalization Submodule

variable {F : Type} [Field F] [NumberField F]

/-- The coordinate vector $(x_0, x_1, x_2, x_3)$ of $x = x_0 + x_1i + x_2j + x_3k$. -/
def tup {K : Type*} [Field K] {a b : K} (x : ℍ[K,a,b]) : Fin 4 → K := ![x.re, x.imI, x.imJ, x.imK]

theorem tup_linear {K : Type*} [Field K] {a b : K} (c : Fin 4 → K) (e : Fin 4 → ℍ[K,a,b]) :
    tup (∑ i, c i • e i) = fun r => ∑ i, tup (e i) r * c i := by
  ext r; fin_cases r <;> simp [tup, Fin.sum_univ_four, mul_comm]

theorem nrd_eq_evalIn (a b : F) (x : ℍ[F,a,b]) : nrd x = (nrdForm a b).evalIn F (tup x) := by
  rw [nrdForm, QuadForm.evalIn_diag, Fin.sum_univ_four]; simp [nrd, tup]; ring

/-- A form over $F$ with coefficients in $\mathcal O_F$ comes from a form over $\mathcal O_F$. -/
theorem exists_map_eq_of_isInteger {n : ℕ} (S : QuadForm F n) (h : ∀ i j, IsInteger (𝓞 F) (S.coeff i j)) :
    ∃ Q : QuadForm (𝓞 F) n, Q.map (algebraMap (𝓞 F) F) = S := by
  choose c hc using h
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective _ _
  refine ⟨⟨Matrix.of c, fun i j hij => hinj ?_⟩, ?_⟩
  · simp only [Matrix.of_apply, map_zero, hc]; exact S.upper hij
  · ext i j; simp [QuadForm.map, hc]

/-- The off-diagonal coefficients of a form by polarization: $c_{ij} = Q(e_i + e_j) - Q(e_i) - Q(e_j)$ ($i < j$). -/
theorem coeff_eq_polar {A : Type*} [CommRing A] {n : ℕ} (S : QuadForm A n) {i j : Fin n} (hlt : i < j) :
    S.coeff i j = S.eval (Pi.single i 1 + Pi.single j 1) - S.eval (Pi.single i 1) - S.eval (Pi.single j 1) := by
  rw [eval_polar, mulVec_single_one, single_one_dotProduct]
  have hz : S.coeff j i = 0 := S.upper (show id i < id j from hlt)
  simp [hessian, hz]

theorem one_smul_form' {n : ℕ} (S : QuadForm (𝓞 F) n) : (1 : 𝓞 F) • S = S := by ext a b; simp [smul_coeff]

section Form

variable [IsPrincipalIdealRing (𝓞 F)] (a b : 𝓞 F)

/-- **An order is a free $\mathcal O_F$-module of rank 4** ($\mathcal O_F$ a PID; Mathlib's `IsLattice`). -/
theorem finrank_order {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}
    (hO : IsOrder (𝓞 F) F O) : Module.finrank (𝓞 F) (Subalgebra.toSubmodule O) = 4 := by
  have hlat : IsLattice F (Subalgebra.toSubmodule O) := ⟨hO.fg, hO.span⟩
  have := IsLattice.rank' F (Subalgebra.toSubmodule O)
  rw [QuaternionAlgebra.rank_eq_four] at this
  exact Module.finrank_eq_of_rank_eq this

/-- A form over $\mathcal O_F$ is determined by its values over $F$. -/
theorem eq_of_evalIn_eq {n : ℕ} {Q Q' : QuadForm (𝓞 F) n} (h : ∀ y : Fin n → F, Q.evalIn F y = Q'.evalIn F y) :
    Q = Q' := by
  apply QuadFormsKB.LocalDensity.NF.map_injective (IsFractionRing.injective (𝓞 F) F)
  refine eq_of_eval_eq fun y => ?_
  have e1 : ∀ S : QuadForm (𝓞 F) n, (S.map (algebraMap (𝓞 F) F)).eval y = S.evalIn F y := fun S => by
    simp [QuadForm.evalIn, QuadForm.map]
  rw [e1, e1, h]

/-- **The norm form of an order containing the standard order.** Let $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ be an
$\mathcal O_F$-order of $(a,b)_F$ and $e$ an $\mathcal O_F$-basis of $\mathcal O$. There are an integral quaternary form $Q$ with
$Q(y) = \operatorname{nrd}(\sum_i y_ie_i)$ ($y \in F^4$) and $G \in M_4(\mathcal O_F)$ with $\det G \ne 0$ and
$Q\circ G = \langle 1,-a,-b,ab\rangle$ (`normForm a b`; the columns of $G$ are the coordinates of $1, i, j, k$ in the basis $e$).

Source: Voight 2021, §15.2 and Example 15.2.10 (the norm form and discriminant of the standard order). -/
@[kb "voight2021" "Ex. 15.2.10"]
theorem exists_orderForm {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}
    (hO : IsOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    ∃ (Q : QuadForm (𝓞 F) 4) (G : Matrix (Fin 4) (Fin 4) (𝓞 F)),
      (∀ y : Fin 4 → F, Q.evalIn F y = nrd (∑ i, y i • (e i : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]))) ∧
      G.det ≠ 0 ∧ Q.compMat G = normForm a b := by
  classical
  set D := ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]
  -- the coordinate matrix of the basis
  set E : Matrix (Fin 4) (Fin 4) F := Matrix.of fun r i => tup (e i : D) r
  set SF : QuadForm F 4 := (nrdForm (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)).compMat E
  have hSF : ∀ y : Fin 4 → F, SF.evalIn F y = nrd (∑ i, y i • (e i : D)) := by
    intro y
    have h1 : SF.evalIn F y = SF.eval y := by simp [QuadForm.eval]
    rw [h1, eval_compMat, nrd_eq_evalIn, tup_linear]
    simp only [QuadForm.eval]
    congr 1
  have hmemO : ∀ i, (e i : D) ∈ O := fun i => (e i).2
  -- integrality of the coefficients
  have key : ∀ y : Fin 4 → F, (∀ l, IsInteger (𝓞 F) (y l)) → IsInteger (𝓞 F) (SF.eval y) := by
    intro y hy
    choose c hc using hy
    have h1 : SF.eval y = SF.evalIn F y := by simp [QuadForm.eval]
    rw [h1, hSF]
    have : ∑ l, y l • (e l : D) ∈ O :=
      Subalgebra.sum_mem _ fun l _ => by
        rw [← hc l, algebraMap_smul]; exact Subalgebra.smul_mem _ (hmemO l) _
    exact (isInteger_trd_nrd hO this).2
  have hsingle : ∀ l k, IsInteger (𝓞 F) ((Pi.single k (1 : F) : Fin 4 → F) l) := by
    intro l k; by_cases h : l = k
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  have hint : ∀ i j, IsInteger (𝓞 F) (SF.coeff i j) := by
    intro i j
    by_cases hij : i ≤ j
    · rcases hij.lt_or_eq with hlt | rfl
      · rw [coeff_eq_polar SF hlt]
        obtain ⟨u, hu⟩ := key (Pi.single i 1 + Pi.single j 1) fun l => by
          obtain ⟨p, hp⟩ := hsingle l i; obtain ⟨q, hq⟩ := hsingle l j
          exact ⟨p + q, by simp only [map_add, hp, hq, Pi.add_apply]⟩
        obtain ⟨v, hv⟩ := key (Pi.single i 1) (fun l => hsingle l i)
        obtain ⟨w, hw⟩ := key (Pi.single j 1) (fun l => hsingle l j)
        exact ⟨u - v - w, by rw [map_sub, map_sub, hu, hv, hw]⟩
      · rw [← eval_single]; exact key _ fun l => hsingle l i
    · exact ⟨0, by rw [map_zero, SF.upper (not_le.1 hij)]⟩
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_isInteger SF hint
  -- the standard basis 1, i, j, k of the standard order, inside `O`
  let f : Fin 4 → D := ![1, qi, qj, qk]
  have hf : ∀ m, f m ∈ O := by
    intro m; fin_cases m
    · exact O.one_mem
    · exact hstd (qi_mem_stdOrder a b)
    · exact hstd (qj_mem_stdOrder a b)
    · exact hstd (qk_mem_stdOrder a b)
  let G : Matrix (Fin 4) (Fin 4) (𝓞 F) := Matrix.of fun i m => e.repr ⟨f m, hf m⟩ i
  have hsum : ∀ m, ∑ i, algebraMap (𝓞 F) F (G i m) • (e i : D) = f m := by
    intro m
    have h := congrArg Subtype.val (e.sum_repr ⟨f m, hf m⟩)
    rw [Submodule.coe_sum] at h
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebraMap_smul]; rfl
  have hEG : E * G.map (algebraMap (𝓞 F) F) = 1 := by
    ext r m
    have h1 : (E * G.map (algebraMap (𝓞 F) F)) r m = tup (f m) r := by
      rw [← hsum m, tup_linear]; simp [E, Matrix.mul_apply]
    rw [h1]
    fin_cases r <;> fin_cases m <;> simp [f, tup, qi, qj, qk]
  have hdetG : G.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hEG
    rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨Q, G, fun y => by rw [← hSF, ← hQ]; simp [QuadForm.evalIn, QuadForm.map], hdetG, ?_⟩
  apply QuadFormsKB.LocalDensity.NF.map_injective (IsFractionRing.injective (𝓞 F) F)
  rw [← map_compMat, hQ, compMat_mul, hEG, compMat_one, map_normForm]

end Form

section Tau

variable [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}

/-- **$\tau$ of the norm form of an order equals $\tau$ of the standard norm form:** if $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ is an
order of the totally definite $(a,b)_F$ and $Q$ is the norm form of $\mathcal O$ in an $\mathcal O_F$-basis $e$, then
$\tau(SO(Q)) = \tau(SO(\langle 1,-a,-b,ab\rangle))$ (the $\tau$, the lattice independence `LatChange.tauSO_smul_compMat`).

Source: Weil 1982, §2.2.1, p. 14 (the Tamagawa measure does not depend on the lattice). -/
@[kb "weil1982" "§2.2.1, p. 14"]
theorem tauSO_orderForm (hpd : IsTotallyPosDef (formF (normForm a b)))
    {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}
    (hO : IsOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) {Q : QuadForm (𝓞 F) 4}
    (hQ : ∀ y : Fin 4 → F, Q.evalIn F y = nrd (∑ i, y i • (e i : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]))) :
    tauSO Q = tauSO (normForm a b) := by
  obtain ⟨Q', G, hQ', hG, hQG⟩ := exists_orderForm a b hO hstd e
  obtain rfl : Q = Q' := eq_of_evalIn_eq fun y => by rw [hQ, hQ']
  set Gm := G.map (algebraMap (𝓞 F) F)
  have hGm : Gm.det ≠ 0 := by
    rw [show Gm = (algebraMap (𝓞 F) F).mapMatrix G from rfl, ← RingHom.map_det]
    exact fun h => hG ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 h)
  have hpdQ : IsTotallyPosDef (formF Q) := by
    have h1 : formF (normForm a b) = (formF Q).compMat Gm := by
      rw [← hQG, formF, formF, map_compMat]
    have h2 : formF Q = (formF (normForm a b)).compMat Gm⁻¹ := by
      rw [h1, compMat_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hGm), compMat_one]
    rw [h2]
    exact LatChange.isTotallyPosDef_compMat_of_det hpd (by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hGm)
  have hnd : Q.Nondegenerate := nondegenerate_of_map hpdQ.nondegenerate
  have := LatChange.tauSO_smul_compMat (by norm_num) (by norm_num) Q hnd hpdQ one_ne_zero G hG
    (by rw [one_smul_form', hQG]; exact hpd)
  rw [one_smul_form', hQG] at this
  exact this.symm

variable [IsTotallyReal F]

/-- **The base case `TernaryTamagawaTwo F` from $\tau = 2$ for one order per quaternion algebra** ($F$ totally real of degree
$\ge 2$, $\mathcal O_F$ a PID): if every totally definite $(a,b)_F$ ($a, b \in \mathcal O_F$) has an order $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$
(e.g. a maximal order, `exists_isMaximalOrder_ge_stdOrder`) whose norm form $Q$ in some $\mathcal O_F$-basis has $\tau(SO(Q)) = 2$,
then `TernaryTamagawaTwo F`. (`tauSO_orderForm`, `QuatZeta.tamagawaNumberTwo_normForm_iff`, `ternaryTamagawaTwo_iff_residues`.) -/
@[kb "weil1982" "§3.7(a), p. 62; Thm. 3.7.1 (m = 3), p. 65; §2.2.1, p. 14"]
theorem ternaryTamagawaTwo_of_orders (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (h : ∀ a b : 𝓞 F, IsTotallyPosDef (formF (normForm a b)) →
      ∃ O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b], IsOrder (𝓞 F) F O ∧
        stdOrder F a b ≤ O ∧ ∃ (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) (Q : QuadForm (𝓞 F) 4),
          (∀ y : Fin 4 → F, Q.evalIn F y = nrd (∑ i, y i • (e i : ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]))) ∧
          TamagawaNumberTwo Q) :
    TernaryTamagawaTwo F := by
  refine (LatChange.ternaryTamagawaTwo_iff_residues hd).2 fun a b hpd => ?_
  obtain ⟨O, hO, hstd, e, Q, hQ, hτ⟩ := h a b hpd
  refine (tamagawaNumberTwo_normForm_iff hpd).1 ?_
  unfold TamagawaNumberTwo at hτ ⊢
  rw [← tauSO_orderForm hpd hO hstd e hQ, hτ]

end Tau

end QuadFormsKB.QuatOrder
