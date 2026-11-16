/-
# Chenevier–Lannes, Proposition-Definition 3.2.1 at $p = 2$: the number of $2$-neighbours

Proves `NeighborCountTwo`: an even unimodular lattice of dimension $n > 0$ has exactly
$c_n(2) = 2^{n-1} - 1 + 2^{n/2-1}$ $2$-neighbours.

*Route* (a bridge, not a re-proof). The $2$-neighbours are the isotropic lines of $\mathbb{F}_2^n$ for the form
$Q \bmod 2$ (`Siegel.Kneser.card_neighbors`, valid for every prime $p \nmid \det H$). The number of zeros of
$Q \bmod 2$ is the dyadic case of Hanke's Table 1 (`DVR.card_mod_pi_of_level_zero_dyadic`, for the completion
$Q \otimes \mathbb{Z}_2$, transported to $\mathbb{Z}/2$ by `repCount_eq_padic`): $2^{n-1} + \varepsilon\,(2^{n/2} - 2^{n/2-1})$ with
the Arf sign $\varepsilon = \chi_8(\Delta)$, $\Delta = (-1)^{n/2}\det H = 1$ (`arfSignQ_two_eq_chi8`, $8 \mid n$).
-/
import QuadFormsKB.Literature.ChenevierLannes.Neighbors
import QuadFormsKB.Siegel.RatLevelGood

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.LocalDensity Classical

local notation "ι2" => Int.castRingHom ℤ_[2]

variable {n : ℕ}

/-- **Zeros of $Q \bmod 2$ for an even unimodular $Q$:** $\#\{\bar y \in \mathbb{F}_2^n : \bar Q(\bar y) = 0\} =
2^{n-1} + 2^{n/2-1}$ ($n > 0$; the Arf invariant is $0$ because $8 \mid n$). -/
theorem card_qv_zero_two {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hn : 0 < n) :
    ((Finset.univ.filter fun y : Fin n → ZMod 2 => qv Q 2 y = 0).card : ℤ) = 2 ^ (n - 1) + 2 ^ (n / 2 - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[2]) :=
    Fintype.ofEquiv (ZMod 2) PadicInt.residueField.symm.toEquiv
  obtain ⟨m, hm⟩ := eight_dvd_of_isEvenUnimodular hQ
  have hnd : Q.Nondegenerate := by
    show Q.hessian.det ≠ 0
    rw [hQ.det_one]; exact one_ne_zero
  have hev : Even n := ⟨4 * m, by omega⟩
  have hlev : level Q = 1 := by
    have := level_dvd_det hnd hev
    rw [hQ.det_one] at this
    exact Nat.dvd_one.1 (by simpa using this)
  have hodd : Odd (level Q) := by rw [hlev]; exact odd_one
  have hL := isLocalLevel_two_of_odd_level hnd hodd
  have h := DVR.card_mod_pi_of_level_zero_dyadic (Q.map ι2) irreducible_two_padicInt dvd_rfl two_ne_zero hL hn 0
  rw [arfSignQ_two_eq_chi8 hnd hn hodd, q_padicInt] at h
  have hdisc : disc Q = 1 := by
    rw [disc, hQ.det_one, hm, show 8 * m / 2 = 2 * (2 * m) by omega, pow_mul]; simp
  rw [hdisc] at h
  have h0 := h.1 (dvd_zero _)
  have hc := repCount_one_eq_card (Q := Q) (p := 2) 0
  have hb := (repCount_eq_padic Q 2 ∅ 1 0).1
  have e : (Finset.univ.filter fun y : Fin n → ZMod 2 => qv Q 2 y = 0).card = DVR.repCount (Q.map ι2) 2 1 0 := by
    have := hc.symm.trans hb
    simpa using this
  simp only [Int.cast_one, MulChar.map_one, one_mul] at h0
  rw [e, h0]
  obtain ⟨j, hj⟩ : ∃ j, n / 2 = j + 1 := ⟨n / 2 - 1, by omega⟩
  rw [hj, Nat.add_sub_cancel]
  push_cast
  ring

/-- **Proposition-Definition 3.2.1 at $p = 2$, proved** (Chenevier–Lannes, §1.2, p. 3, and pp. 55–56): an even unimodular
lattice of dimension $n > 0$ has exactly $c_n(2) = 2^{n-1} - 1 + 2^{n/2-1}$ $2$-neighbours. Unconditional. *Proof:* the
$2$-neighbours are the isotropic lines of $\mathbb{F}_2^n$ (`Siegel.Kneser.card_neighbors`), and $Q \bmod 2$ has
$2^{n-1} + 2^{n/2-1}$ zeros (`card_qv_zero_two`). -/
@[kb "chenevierlannes2019" "§1.2, p. 3; Prop.-Def. 3.2.1, pp. 55–56 (p = 2)"]
theorem card_neighbors_eq_cn_two {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hn : 0 < n) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; (neighbors Q 2).card = cn n 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdet := not_dvd_det hQ 2
  have h1 := card_neighbors (Q := Q) (p := 2) hdet
  have h2 := card_isoSet (Q := Q) (p := 2)
  have h3 := card_qv_zero_two hQ hn
  have hgeom : (∑ m ∈ Finset.range (n - 1), (2 : ℤ) ^ m) * ((2 : ℤ) - 1) = (2 : ℤ) ^ (n - 1) - 1 :=
    geom_sum_mul _ _
  have e1 : (((2 - 1) * (neighbors Q 2).card : ℕ) : ℤ) = ((isoSet Q 2).card : ℤ) := by rw [h1]
  push_cast at e1
  have e2 : (((isoSet Q 2).card + 1 : ℕ) : ℤ) = _ := congrArg (fun k : ℕ => (k : ℤ)) h2
  push_cast at e2
  show (neighbors Q 2).card = cn n 2
  have key : ((neighbors Q 2).card : ℤ) = (cn n 2 : ℤ) := by
    simp only [cn]
    push_cast
    linear_combination e1 + e2 + h3 - hgeom
  exact_mod_cast key

/-- **`NeighborCountTwo` holds** (unconditional). -/
@[kb "chenevierlannes2019" "Prop.-Def. 3.2.1, pp. 55–56 (p = 2)"]
theorem neighborCountTwo : NeighborCountTwo :=
  fun _ Q hQ hn => card_neighbors_eq_cn_two hQ hn

end QuadFormsKB.ChenevierLannes
