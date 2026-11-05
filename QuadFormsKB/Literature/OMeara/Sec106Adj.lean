/-
# O'Meara §106C–E: constructing adjacent lattices, and the lattice $E$ adjacent to $\mathbb Z^n$

**Layer:** $F = \mathbb Q$ (a number field), $V = \mathbb Q^n$ with a form `Q : QuadForm ℚ n`; lattices are
$\mathcal O_{\mathbb Q}$-submodules of $\mathbb Q^n$; O'Meara's bilinear form is $B = \tfrac12$ `bil Q` (so
$B(x,x) = Q(x)$); unimodular means `IsUnimodularZ Q` ($L^\# = L$ with `omearaDual`); "adjacent" is the library's
$2$-neighbour relation `Nbr.IsNbrL Q 2 L K` (see `Sec106C.lean`). For §106E: $Q = I_n$ = `sumSqForm n`,
$D = \mathbb Z^n$ = `intVec` (orthogonal base $x_0, \dots, x_{n-1}$, O'Meara's $x_1, \dots, x_n$ shifted by one),
$y = \tfrac12(x_0 + \dots + x_{n-1})$ = `omearaEHalf n`, $E$ = `omearaE n`, and $4 \mid n$, $n \ge 8$.

**Proves**
* Proposition 106:7 (`omeara106_7`): for unimodular $K$ and $y$ with $2y \in K$, $y \notin K$, $Q(y) \in \mathbb Z$, the
  lattice $J = \mathbb Zy + (\mathbb Zy + K)^\#$ is unimodular, contains $y$, is adjacent to $K$, and is the only such
  lattice;
* the procedure of p. 329 (`omeara106_r27`): every unimodular lattice adjacent to $K$ arises from a representative
  $y$ of $\tfrac12K$ modulo $2K$ with $Q(y) \in \mathbb Z$, $y \notin K$;
* §106E: `omeara106_r33` ($y$ is a vector of $\tfrac12D - D$ with $Q(y) = n/4$), `omeara106_r34` ($E$ is the unique
  unimodular lattice containing $y$ and adjacent to $D$), `omeara106_r29_adjacent` and `omeara106_r29`
  (existence of an indecomposable unimodular lattice adjacent to $D$), `omeara106_r30` (all such lattices are in the
  proper class of $E$), `omeara106_p3` (the vectors $x_{i+1} - x_i$, $x_0 + x_1$ of the indecomposability argument).

**Auxiliary** (not in the book): `adj_D_unimodular` ($D = \mathbb Z^n$ is unimodular for $I_n$).
-/
import QuadFormsKB.Literature.OMeara.Sec106C
import QuadFormsKB.Literature.OMeara.Sec106E
import QuadFormsKB.Literature.OMeara.Sec102

open Matrix NumberField QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ} (Q : QuadForm ℚ n)

/-! ### Helper lemmas (copies of private lemmas of `Sec106C.lean` / `Sec106E.lean`, and new ones) -/

private lemma adj_nm_two : nm (2 : 𝓞 ℚ) = 2 := by
  have h : (2 : 𝓞 ℚ) = ((2 : ℕ) : 𝓞 ℚ) := by norm_num
  rw [h, nm_natCast, NumberField.RingOfIntegers.rank]
  simp

private lemma adj_index_two {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 L K) :
    (L ⊓ K).toAddSubgroup.relIndex L.toAddSubgroup = 2 := by
  have h1 := h.index_left
  rw [adj_nm_two] at h1
  have e : (L ⊓ K).toAddSubgroup = L.toAddSubgroup ⊓ K.toAddSubgroup := rfl
  rw [e, AddSubgroup.inf_relIndex_left, h1]

private lemma adj_exists_out {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 L K) :
    ∃ y ∈ L, y ∉ K := by
  by_contra hcon
  have hle : L ≤ K := fun x hx => by
    by_contra hxK
    exact hcon ⟨x, hx, hxK⟩
  have h1 := adj_index_two Q h
  rw [inf_eq_left.mpr hle, AddSubgroup.relIndex_self] at h1
  omega

private lemma adj_mem_dual {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} {x : Fin n → ℚ} :
    x ∈ omearaDual Q L ↔ ∀ y ∈ L, ∃ m : ℤ, bil Q x y / 2 = m := Iff.rfl

private lemma adj_dual_anti {M N : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : M ≤ N) :
    omearaDual Q N ≤ omearaDual Q M :=
  fun _ hx y hy => hx y (h hy)

private lemma adj_uni_mem {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) {x y : Fin n → ℚ}
    (hx : x ∈ L) (hy : y ∈ L) : ∃ m : ℤ, bil Q x y / 2 = m := by
  have : x ∈ omearaDual Q L := by rw [hL]; exact hx
  exact this y hy

private lemma adj_uni_eq {M N : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IsUnimodularZ Q M)
    (hN : IsUnimodularZ Q N) (h : M ≤ N) : M = N := by
  refine le_antisymm h ?_
  have := adj_dual_anti Q h
  rw [hM, hN] at this
  exact this

private lemma adj_bil_add_l (x x' y : Fin n → ℚ) : bil Q (x + x') y = bil Q x y + bil Q x' y := by
  simp [bil, add_dotProduct]

private lemma adj_bil_add_r (x y y' : Fin n → ℚ) : bil Q x (y + y') = bil Q x y + bil Q x y' := by
  simp [bil, Matrix.mulVec_add, dotProduct_add]

private lemma adj_bil_sub_l (x x' y : Fin n → ℚ) : bil Q (x - x') y = bil Q x y - bil Q x' y := by
  simp [bil, sub_dotProduct]

private lemma adj_bil_sub_r (x y y' : Fin n → ℚ) : bil Q x (y - y') = bil Q x y - bil Q x y' := by
  simp [bil, Matrix.mulVec_sub, dotProduct_sub]

private lemma adj_bil_smul_r (c : ℚ) (x y : Fin n → ℚ) : bil Q x (c • y) = c * bil Q x y := by
  simp [bil, Matrix.mulVec_smul, dotProduct_smul]

private lemma adj_bil_smul_l (c : ℚ) (x y : Fin n → ℚ) : bil Q (c • x) y = c * bil Q x y := by
  simp [bil, smul_dotProduct]

private lemma adj_smul_int (c : 𝓞 ℚ) (y : Fin n → ℚ) : ∃ k : ℤ, c • y = (k : ℚ) • y := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
    ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩
  subst hk
  refine ⟨k, ?_⟩
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

private lemma adj_intsmul_mem {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} {x : Fin n → ℚ} (hx : x ∈ M) (k : ℤ) :
    (k : ℚ) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx k

private lemma adj_two_smul_mem {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} {x : Fin n → ℚ} (hx : x ∈ M) :
    (2 : ℚ) • x ∈ M := by
  have := adj_intsmul_mem hx 2
  rwa [Int.cast_ofNat] at this

private lemma adj_nbr_two_smul {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hadj : Nbr.IsNbrL Q 2 L K)
    {y : Fin n → ℚ} (hyL : y ∈ L) : (2 : ℚ) • y ∈ K := by
  have h := hadj.smul_right y hyL
  have e : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
  rw [e] at h
  exact h

private lemma adj_nbr_two_smul_left {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hadj : Nbr.IsNbrL Q 2 L K)
    {y : Fin n → ℚ} (hyK : y ∈ K) : (2 : ℚ) • y ∈ L := by
  have h := hadj.smul_left y hyK
  have e : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
  rw [e] at h
  exact h

private lemma adj_kmem_iff {K : Submodule (𝓞 ℚ) (Fin n → ℚ)} {y : Fin n → ℚ} (hyK : y ∉ K)
    (h2 : (2 : ℚ) • y ∈ K) (k : ℤ) : (k : ℚ) • y ∈ K ↔ Even k := by
  constructor
  · intro h
    by_contra hk
    obtain ⟨j, hj⟩ := Int.not_even_iff_odd.mp hk
    apply hyK
    have e : (k : ℚ) • y - (j : ℚ) • ((2 : ℚ) • y) = y := by
      rw [hj]
      push_cast
      module
    rw [← e]
    exact K.sub_mem h (adj_intsmul_mem h2 j)
  · rintro ⟨j, hj⟩
    have e : (k : ℚ) • y = (j : ℚ) • ((2 : ℚ) • y) := by
      rw [hj]
      push_cast
      module
    rw [e]
    exact adj_intsmul_mem h2 j

private lemma adj_eval_of_bil {x : Fin n → ℚ} {m : ℤ} (h : bil Q x x / 2 = m) : Q.eval x = m := by
  have := bil_self Q x
  linarith

private lemma adj_bil_of_eval {x : Fin n → ℚ} {m : ℤ} (h : Q.eval x = m) : bil Q x x / 2 = m := by
  have := bil_self Q x
  linarith

private lemma adj_isIntegral {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) :
    IsIntegral Q L := by
  intro x hx
  obtain ⟨m, hm⟩ := adj_uni_mem Q hL hx hx
  exact ⟨(m : 𝓞 ℚ), by simpa using (adj_eval_of_bil Q hm).symm⟩

private lemma adj_half {a b : ℚ} (ha : ∃ m : ℤ, 2 * a = m) (hb : ∃ m : ℤ, 2 * b = m)
    (h : (∃ n : ℤ, a = n) ↔ (∃ n : ℤ, b = n)) : ∃ n : ℤ, a - b = n := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨m', hm'⟩ := hb
  rcases Int.even_or_odd' m with ⟨c, rfl | rfl⟩
  · have hac : a = c := by push_cast at hm; linarith
    obtain ⟨d, hd⟩ := h.mp ⟨c, hac⟩
    exact ⟨c - d, by push_cast; rw [hac, hd]⟩
  · have hac : a = c + 1 / 2 := by push_cast at hm; linarith
    rcases Int.even_or_odd' m' with ⟨d, rfl | rfl⟩
    · exfalso
      have hbd : b = d := by push_cast at hm'; linarith
      obtain ⟨e, he⟩ := h.mpr ⟨d, hbd⟩
      have h1 : (2 * e : ℚ) = 2 * c + 1 := by rw [← he, hac]; ring
      have h2 : 2 * e = 2 * c + 1 := by exact_mod_cast h1
      omega
    · have hbd : b = d + 1 / 2 := by push_cast at hm'; linarith
      exact ⟨c - d, by push_cast; rw [hac, hbd]; ring⟩

/-- The lattice $(\mathbb Zy + K)^\#$ is $\{w \in K : B(w, y) \in \mathbb Z\}$ (for unimodular $K$). -/
private lemma adj_N_mem {K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K) (y : Fin n → ℚ)
    {w : Fin n → ℚ} :
    w ∈ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K) ↔ w ∈ K ∧ ∃ m : ℤ, bil Q w y / 2 = m := by
  constructor
  · intro hw
    have hwK : w ∈ omearaDual Q K := adj_dual_anti Q (le_sup_right : K ≤ Submodule.span (𝓞 ℚ) {y} ⊔ K) hw
    rw [hK] at hwK
    exact ⟨hwK, hw y (Submodule.mem_sup_left (Submodule.mem_span_singleton_self y))⟩
  · rintro ⟨hwK, m, hm⟩
    rw [adj_mem_dual]
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨k, hk⟩ := adj_smul_int c y
    obtain ⟨m2, hm2⟩ := adj_uni_mem Q hK hwK hb
    refine ⟨k * m + m2, ?_⟩
    rw [hk, adj_bil_add_r, adj_bil_smul_r, add_div, mul_div_assoc, hm, hm2]
    push_cast
    rfl

/-- The construction of 106:7, with $N = (\mathbb Zy + K)^\#$ abstracted through its description
$N = \{w \in K : B(w, y) \in \mathbb Z\}$. -/
private lemma adj_construct {K N : Submodule (𝓞 ℚ) (Fin n → ℚ)} {y : Fin n → ℚ} (hK : IsUnimodularZ Q K)
    (hN : ∀ w, w ∈ N ↔ w ∈ K ∧ ∃ m : ℤ, bil Q w y / 2 = m)
    (h2 : (2 : ℚ) • y ∈ K) (hyK : y ∉ K) (hQy : ∃ m : ℤ, Q.eval y = m) :
    IsUnimodularZ Q (Submodule.span (𝓞 ℚ) {y} ⊔ N) ∧ y ∈ Submodule.span (𝓞 ℚ) {y} ⊔ N ∧
      Nbr.IsNbrL Q 2 (Submodule.span (𝓞 ℚ) {y} ⊔ N) K := by
  have hyspan : y ∈ Submodule.span (𝓞 ℚ) {y} := Submodule.mem_span_singleton_self y
  have hyJ : y ∈ Submodule.span (𝓞 ℚ) {y} ⊔ N := Submodule.mem_sup_left hyspan
  have hNK : N ≤ K := fun w hw => ((hN w).mp hw).1
  have hNJ : N ≤ Submodule.span (𝓞 ℚ) {y} ⊔ N := le_sup_right
  have hyy : ∃ m : ℤ, bil Q y y / 2 = m := by
    obtain ⟨m, hm⟩ := hQy
    exact ⟨m, adj_bil_of_eval Q hm⟩
  have hhalfK : ∀ w ∈ K, ∃ m : ℤ, 2 * (bil Q w y / 2) = m := by
    intro w hw
    obtain ⟨m, hm⟩ := adj_uni_mem Q hK hw h2
    exact ⟨m, by rw [adj_bil_smul_r] at hm; linarith⟩
  have h2N : ∀ w ∈ K, (2 : ℚ) • w ∈ N := by
    intro w hw
    refine (hN _).mpr ⟨adj_two_smul_mem hw, ?_⟩
    obtain ⟨m, hm⟩ := hhalfK w hw
    exact ⟨m, by rw [adj_bil_smul_l]; linarith⟩
  have hdec : ∀ x ∈ Submodule.span (𝓞 ℚ) {y} ⊔ N,
      ∃ (k : ℤ) (t : Fin n → ℚ), t ∈ N ∧ x = (k : ℚ) • y + t := by
    intro x hx
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨k, hk⟩ := adj_smul_int c y
    exact ⟨k, t, ht, by rw [hk]⟩
  have hmemN : ∀ (k : ℤ) (t : Fin n → ℚ), t ∈ N → ((k : ℚ) • y + t ∈ N ↔ Even k) := by
    intro k t ht
    constructor
    · intro h
      have hK' : (k : ℚ) • y + t ∈ K := hNK h
      have : (k : ℚ) • y ∈ K := by
        have := K.sub_mem hK' (hNK ht)
        simpa using this
      exact (adj_kmem_iff hyK h2 k).mp this
    · intro hk
      have hkK : (k : ℚ) • y ∈ K := (adj_kmem_iff hyK h2 k).mpr hk
      refine N.add_mem ?_ ht
      refine (hN _).mpr ⟨hkK, ?_⟩
      obtain ⟨m, hm⟩ := hyy
      exact ⟨k * m, by rw [adj_bil_smul_l, mul_div_assoc, hm]; push_cast; rfl⟩
  have hJint : ∀ x ∈ Submodule.span (𝓞 ℚ) {y} ⊔ N, ∀ x' ∈ Submodule.span (𝓞 ℚ) {y} ⊔ N,
      ∃ m : ℤ, bil Q x x' / 2 = m := by
    intro x hx x' hx'
    obtain ⟨k, t, ht, rfl⟩ := hdec x hx
    obtain ⟨k', t', ht', rfl⟩ := hdec x' hx'
    obtain ⟨m0, hm0⟩ := hyy
    obtain ⟨a, ha⟩ := ((hN t).mp ht).2
    obtain ⟨b, hb⟩ := ((hN t').mp ht').2
    obtain ⟨c, hc⟩ := adj_uni_mem Q hK ((hN t).mp ht).1 ((hN t').mp ht').1
    refine ⟨k * k' * m0 + k * b + k' * a + c, ?_⟩
    have e : bil Q ((k : ℚ) • y + t) ((k' : ℚ) • y + t') =
        k * k' * bil Q y y + k * bil Q t' y + k' * bil Q t y + bil Q t t' := by
      simp only [adj_bil_add_l, adj_bil_add_r, adj_bil_smul_l, adj_bil_smul_r]
      rw [bil_comm Q y t']
      ring
    have h1 : bil Q y y = 2 * m0 := by linarith
    have h2' : bil Q t' y = 2 * b := by linarith
    have h3 : bil Q t y = 2 * a := by linarith
    have h4 : bil Q t t' = 2 * c := by linarith
    rw [e, h1, h2', h3, h4]
    push_cast
    ring
  have hJuni : IsUnimodularZ Q (Submodule.span (𝓞 ℚ) {y} ⊔ N) := by
    refine le_antisymm ?_ (fun x hx z hz => hJint x hx z hz)
    intro x hx
    have hxy := hx y hyJ
    have hxN : ∀ w ∈ N, ∃ m : ℤ, bil Q x w / 2 = m := fun w hw => hx w (hNJ hw)
    by_cases hP : ∀ w ∈ K, ∃ m : ℤ, bil Q x w / 2 = m
    · have hxK : x ∈ K := by
        have : x ∈ omearaDual Q K := hP
        rwa [hK] at this
      exact hNJ ((hN x).mpr ⟨hxK, hxy⟩)
    · obtain ⟨w0, hw0K, hw0⟩ : ∃ w0 ∈ K, ¬ ∃ m : ℤ, bil Q x w0 / 2 = m := by
        by_contra hc
        apply hP
        intro w hw
        by_contra h
        exact hc ⟨w, hw, h⟩
      have hhalfx : ∀ w ∈ K, ∃ m : ℤ, 2 * (bil Q x w / 2) = m := by
        intro w hw
        obtain ⟨m, hm⟩ := hxN _ (h2N w hw)
        exact ⟨m, by rw [adj_bil_smul_r] at hm; linarith⟩
      have hnotR0 : ¬ ∃ m : ℤ, bil Q w0 y / 2 = m := fun h =>
        hw0 (hxN w0 ((hN w0).mpr ⟨hw0K, h⟩))
      have key : ∀ w ∈ K, (∃ n : ℤ, bil Q x w / 2 = n) ↔ (∃ n : ℤ, bil Q w y / 2 = n) := by
        intro w hw
        constructor
        · intro hxw
          by_contra hR
          have hwN : w - w0 ∈ N := by
            refine (hN _).mpr ⟨K.sub_mem hw hw0K, ?_⟩
            obtain ⟨n1, hn1⟩ := adj_half (a := bil Q w y / 2) (b := bil Q w0 y / 2)
              (hhalfK w hw) (hhalfK w0 hw0K) (by
              constructor
              · intro h; exact absurd h hR
              · intro h; exact absurd h hnotR0)
            exact ⟨n1, by rw [adj_bil_sub_l]; linarith⟩
          obtain ⟨n2, hn2⟩ := hxN _ hwN
          obtain ⟨n3, hn3⟩ := hxw
          apply hw0
          exact ⟨n3 - n2, by rw [adj_bil_sub_r] at hn2; push_cast; linarith⟩
        · intro hR
          exact hxN w ((hN w).mpr ⟨hw, hR⟩)
      have hxyK : x - y ∈ K := by
        have : x - y ∈ omearaDual Q K := by
          intro w hw
          obtain ⟨n1, hn1⟩ := adj_half (a := bil Q x w / 2) (b := bil Q y w / 2)
            (hhalfx w hw) (by
            obtain ⟨m, hm⟩ := hhalfK w hw
            exact ⟨m, by rw [bil_comm Q y w]; exact hm⟩) (by
            rw [bil_comm Q y w]
            exact key w hw)
          exact ⟨n1, by rw [adj_bil_sub_l]; linarith⟩
        rwa [hK] at this
      have hxyN : x - y ∈ N := by
        refine (hN _).mpr ⟨hxyK, ?_⟩
        obtain ⟨m, hm⟩ := hxy
        obtain ⟨m0, hm0⟩ := hyy
        exact ⟨m - m0, by rw [adj_bil_sub_l]; push_cast; linarith⟩
      exact Submodule.mem_sup.mpr ⟨y, hyspan, x - y, hxyN, by abel⟩
  have hJK : (Submodule.span (𝓞 ℚ) {y} ⊔ N) ⊓ K = N := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxJ, hxK⟩ := Submodule.mem_inf.mp hx
      obtain ⟨k, t, ht, rfl⟩ := hdec x hxJ
      refine (hmemN k t ht).mpr ((adj_kmem_iff hyK h2 k).mp ?_)
      have := K.sub_mem hxK (hNK ht)
      simpa using this
    · intro x hx
      exact Submodule.mem_inf.mpr ⟨hNJ hx, hNK hx⟩
  have hNJidx : N.toAddSubgroup.relIndex (Submodule.span (𝓞 ℚ) {y} ⊔ N).toAddSubgroup = 2 := by
    rw [AddSubgroup.relIndex_eq_two_iff]
    refine ⟨y, hyJ, fun b hb => ?_⟩
    obtain ⟨k, t, ht, rfl⟩ := hdec b hb
    have e : (k : ℚ) • y + t + y = ((k + 1 : ℤ) : ℚ) • y + t := by push_cast; module
    simp only [Submodule.mem_toAddSubgroup]
    rw [e, hmemN _ _ ht, hmemN _ _ ht]
    by_cases h : Even k
    · right
      exact ⟨h, by rw [Int.even_add_one]; exact not_not.mpr h⟩
    · left
      exact ⟨by rw [Int.even_add_one]; exact h, h⟩
  have hNKidx : N.toAddSubgroup.relIndex K.toAddSubgroup = 2 := by
    obtain ⟨w0, hw0K, hw0⟩ : ∃ w0 ∈ K, ¬ ∃ m : ℤ, bil Q w0 y / 2 = m := by
      by_contra hcon
      apply hyK
      have : y ∈ omearaDual Q K := by
        intro w hw
        obtain ⟨m, hm⟩ : ∃ m : ℤ, bil Q w y / 2 = m := by
          by_contra h
          exact hcon ⟨w, hw, h⟩
        exact ⟨m, by rw [bil_comm Q y w]; exact hm⟩
      rwa [hK] at this
    rw [AddSubgroup.relIndex_eq_two_iff]
    refine ⟨w0, hw0K, fun b hb => ?_⟩
    simp only [Submodule.mem_toAddSubgroup]
    by_cases hbN : ∃ m : ℤ, bil Q b y / 2 = m
    · right
      refine ⟨(hN _).mpr ⟨hb, hbN⟩, fun h => hw0 ?_⟩
      obtain ⟨m1, hm1⟩ := hbN
      obtain ⟨m2, hm2⟩ := ((hN _).mp h).2
      exact ⟨m2 - m1, by rw [adj_bil_add_l] at hm2; push_cast; linarith⟩
    · left
      refine ⟨(hN _).mpr ⟨K.add_mem hb hw0K, ?_⟩, fun h => hbN ((hN b).mp h).2⟩
      obtain ⟨n1, hn1⟩ := adj_half (a := bil Q b y / 2) (b := -(bil Q w0 y / 2))
        (hhalfK b hb) (by
        obtain ⟨m, hm⟩ := hhalfK w0 hw0K
        exact ⟨-m, by push_cast; linarith⟩) (by
        constructor
        · intro h; exact absurd h hbN
        · rintro ⟨d, hd⟩
          exact absurd ⟨-d, by push_cast; linarith⟩ hw0)
      exact ⟨n1, by rw [adj_bil_add_l]; linarith⟩
  refine ⟨hJuni, hyJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : K.toAddSubgroup ⊓ (Submodule.span (𝓞 ℚ) {y} ⊔ N).toAddSubgroup = N.toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
      have := Submodule.mem_inf (p := Submodule.span (𝓞 ℚ) {y} ⊔ N) (q := K) (x := x)
      rw [hJK] at this
      rw [this]
      tauto
    rw [adj_nm_two, ← AddSubgroup.inf_relIndex_right, e1]
    exact hNJidx
  · have e2 : (Submodule.span (𝓞 ℚ) {y} ⊔ N).toAddSubgroup ⊓ K.toAddSubgroup = N.toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
      have := Submodule.mem_inf (p := Submodule.span (𝓞 ℚ) {y} ⊔ N) (q := K) (x := x)
      rw [hJK] at this
      rw [this]
    rw [adj_nm_two, ← AddSubgroup.inf_relIndex_right, e2]
    exact hNKidx
  · intro x hx
    have e : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
    rw [e]
    exact hNJ (h2N x hx)
  · intro x hx
    have e : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
    rw [e]
    obtain ⟨k, t, ht, rfl⟩ := hdec x hx
    have e2 : (2 : ℚ) • ((k : ℚ) • y + t) = (k : ℚ) • ((2 : ℚ) • y) + (2 : ℚ) • t := by module
    rw [e2]
    exact K.add_mem (adj_intsmul_mem h2 k) (adj_two_smul_mem (hNK ht))
  · exact adj_isIntegral Q hJuni
  · exact adj_isIntegral Q hK

/-! ### 106:7 and the construction procedure -/

/-- **Proposition 106:7** (O'Meara 1973, §106C, pp. 328–329, at the prime $2$ over $\mathbb Q$): let $K$ be a unimodular
lattice on $(\mathbb Q^n, Q)$ and let $y \in \tfrac12K - K$ (that is, $2y \in K$ and $y \notin K$) with
$Q(y) \in \mathbb Z$. Then the lattice $J = \mathbb Zy + (\mathbb Zy + K)^\#$ is unimodular, contains $y$, and is
adjacent to $K$ (`Nbr.IsNbrL Q 2 J K`); and $J$ is the *only* unimodular lattice containing $y$ that is adjacent to
$K$.

Hypotheses: `hK` ($K^\# = K$), `h2` ($2y \in K$), `hyK` ($y \notin K$), `hQy` ($Q(y) \in \mathbb Z$); $Q$ is an arbitrary
quadratic form over $\mathbb Q$ (the book's $V$ has matrix $J$, nondegenerate; nondegeneracy is not needed here).
Deviation: O'Meara proves existence with volumes; here the unimodularity of $J$ and the two indices
$[J : J \cap K] = [K : J \cap K] = 2$ are proved directly (uniqueness is 106:6, as in the book). "Adjacent" is the
library's $2$-neighbour relation, as in `Sec106C.lean`. -/
@[kb "omeara1963" "§106C, 106:7, pp. 328–329"]
theorem omeara106_7 {K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K) {y : Fin n → ℚ}
    (h2 : (2 : ℚ) • y ∈ K) (hyK : y ∉ K) (hQy : ∃ m : ℤ, Q.eval y = m) :
    IsUnimodularZ Q (Submodule.span (𝓞 ℚ) {y} ⊔ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K)) ∧
      y ∈ Submodule.span (𝓞 ℚ) {y} ⊔ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K) ∧
      Nbr.IsNbrL Q 2 (Submodule.span (𝓞 ℚ) {y} ⊔ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K)) K ∧
      ∀ L : Submodule (𝓞 ℚ) (Fin n → ℚ), IsUnimodularZ Q L → y ∈ L → Nbr.IsNbrL Q 2 L K →
        L = Submodule.span (𝓞 ℚ) {y} ⊔ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K) := by
  obtain ⟨h1, h2', h3⟩ := adj_construct Q hK (fun w => adj_N_mem Q hK y) h2 hyK hQy
  refine ⟨h1, h2', h3, fun L hL hyL hadj => ?_⟩
  obtain ⟨-, hL2, hL3, -⟩ := omeara106_6 Q hK hL hadj hyL hyK
  calc L = Submodule.span (𝓞 ℚ) {y} ⊔ (L ⊓ K) := hL2
    _ = _ := by rw [hL3]

/-- **The procedure for constructing all unimodular lattices adjacent to $K$** (O'Meara 1973, §106C, p. 329, after
106:8a): let $K$ be unimodular and let $R$ be a set of representatives of $\tfrac12K$ modulo $2K$, i.e. for every
$x \in V$ with $2x \in K$ there are $r \in R$ and $k \in K$ with $x - r = 2k$. Then every unimodular lattice $L$ adjacent
to $K$ (`Nbr.IsNbrL Q 2 L K`) equals $\mathbb Zy + (\mathbb Zy + K)^\#$ for some $y \in R$ with $y \notin K$,
$2y \in K$ and $Q(y) \in \mathbb Z$.

Proof as in the book: take $y_0 \in L - K$, replace it by the representative $y \in R$ of its class (106:8, since
$2K \subseteq L \cap K$), and apply 106:6. (Duplications are governed by 106:8a, `omeara106_8a`.) -/
@[kb "omeara1963" "§106C, p. 329 (procedure: all unimodular lattices adjacent to K, from 106:6 and 106:8)"]
theorem omeara106_r27 {K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K) (R : Set (Fin n → ℚ))
    (hR : ∀ x : Fin n → ℚ, (2 : ℚ) • x ∈ K → ∃ r ∈ R, ∃ k ∈ K, x - r = (2 : ℚ) • k)
    {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) (hadj : Nbr.IsNbrL Q 2 L K) :
    ∃ y ∈ R, y ∉ K ∧ (2 : ℚ) • y ∈ K ∧ (∃ m : ℤ, Q.eval y = m) ∧
      L = Submodule.span (𝓞 ℚ) {y} ⊔ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K) := by
  obtain ⟨y0, hy0L, hy0K⟩ := adj_exists_out Q hadj
  obtain ⟨r, hrR, k, hkK, hrk⟩ := hR y0 (adj_nbr_two_smul Q hadj hy0L)
  have hr : r = y0 - (2 : ℚ) • k := by
    rw [← hrk]; abel
  have hrL : r ∈ L := by
    rw [hr]
    exact L.sub_mem hy0L (adj_nbr_two_smul_left Q hadj hkK)
  have hrK : r ∉ K := by
    intro h
    apply hy0K
    have : y0 = r + (2 : ℚ) • k := by rw [hr]; abel
    rw [this]
    exact K.add_mem h (adj_two_smul_mem hkK)
  obtain ⟨-, hL2, hL3, -⟩ := omeara106_6 Q hK hL hadj hrL hrK
  obtain ⟨m, hm⟩ := adj_uni_mem Q hL hrL hrL
  refine ⟨r, hrR, hrK, adj_nbr_two_smul Q hadj hrL, ⟨m, adj_eval_of_bil Q hm⟩, ?_⟩
  calc L = Submodule.span (𝓞 ℚ) {r} ⊔ (L ⊓ K) := hL2
    _ = _ := by rw [hL3]

/-! ### §106E: $D = \mathbb Z^n$ and the lattice $E$ -/

private theorem adj_sumSq_eval (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

private theorem adj_sumSq_bil (x y : Fin n → ℚ) :
    bil (sumSqForm n) x y = 2 * ∑ i, x i * y i := by
  have h : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
    · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
  rw [bil, h, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct, smul_eq_mul]

private lemma adj_mem_range {q : ℚ} : q ∈ (algebraMap (𝓞 ℚ) ℚ).range ↔ ∃ m : ℤ, q = m := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    exact ⟨m, by simp⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(m : 𝓞 ℚ), by simp⟩

private lemma adj_D_coord {x : Fin n → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [mem_intVec]
  exact forall_congr' fun i => adj_mem_range

private lemma adj_dot_half (u : Fin n → ℚ) : ∑ l, u l * omearaEHalf n l = (∑ l, u l) / 2 := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun l _ => by unfold omearaEHalf; ring

/-- **$D = \mathbb Z^n$ is unimodular** for $I_n$ (auxiliary; O'Meara uses this tacitly in §106E, where $D$ is a
completely decomposable unimodular lattice with orthogonal base $x_0, \dots, x_{n-1}$ of norm $1$). -/
theorem adj_D_unimodular :
    IsUnimodularZ (sumSqForm n) (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
  unfold IsUnimodularZ
  ext x
  constructor
  · intro hx
    rw [adj_D_coord]
    intro i
    have hi : (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) :=
      adj_D_coord.mpr fun j => by
        by_cases h : j = i
        · subst h; exact ⟨1, by simp⟩
        · exact ⟨0, by simp [h]⟩
    obtain ⟨m, hm⟩ := hx _ hi
    refine ⟨m, ?_⟩
    rw [adj_sumSq_bil] at hm
    simpa [Pi.single_apply] using hm
  · intro hx z hz
    rw [adj_D_coord] at hx hz
    choose a ha using hx
    choose b hb using hz
    refine ⟨∑ i, a i * b i, ?_⟩
    have : ∑ i, x i * z i = ∑ i, (a i : ℚ) * b i := Finset.sum_congr rfl fun i _ => by rw [ha i, hb i]
    rw [adj_sumSq_bil, this]
    push_cast
    ring

/-- **The vector $y$ of §106E** (O'Meara 1973, p. 331): for $4 \mid n$, $n \ge 1$, the vector
$y = \tfrac12(x_0 + \dots + x_{n-1})$ satisfies $2y \in D = \mathbb Z^n$, $y \notin D$, and $Q(y) = n/4 \in \mathbb Z$ for
$Q = x_0^2 + \dots + x_{n-1}^2$ (`sumSqForm n`). (O'Meara states "$y$ is a vector in $\tfrac12D - D$, $Q(y) \in \mathbb Z$
since $n \equiv 0 \bmod 4$".) -/
@[kb "omeara1963" "§106E, p. 331 (y = ½(x₁+⋯+xₙ) lies in ½D − D with Q(y) = n/4 ∈ Z)"]
theorem omeara106_r33 {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n) :
    (2 : ℚ) • omearaEHalf n ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ∧
      omearaEHalf n ∉ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ∧
      (sumSqForm n).eval (omearaEHalf n) = (n : ℚ) / 4 ∧
      ∃ m : ℤ, (sumSqForm n).eval (omearaEHalf n) = m := by
  have hev : (sumSqForm n).eval (omearaEHalf n) = (n : ℚ) / 4 := by
    rw [adj_sumSq_eval]
    simp [omearaEHalf]
    ring
  refine ⟨adj_D_coord.mpr fun i => ⟨1, by simp [omearaEHalf]⟩, ?_, hev, ?_⟩
  · intro h
    obtain ⟨m, hm⟩ := adj_D_coord.mp h ⟨0, hn⟩
    simp only [omearaEHalf] at hm
    have h1 : (2 : ℚ) * m = 1 := by linarith
    have h2 : 2 * m = 1 := by exact_mod_cast h1
    omega
  · obtain ⟨k, hk⟩ := h4
    exact ⟨k, by rw [hev, hk]; push_cast; ring⟩

private lemma adj_E_eq {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    omearaE n = Submodule.span (𝓞 ℚ) {omearaEHalf n} ⊔
      omearaDual (sumSqForm n) (Submodule.span (𝓞 ℚ) {omearaEHalf n} ⊔ intVec) := by
  have hn : 0 < n := by omega
  have hN : ∀ w, w ∈ omearaDual (sumSqForm n) (Submodule.span (𝓞 ℚ) {omearaEHalf n} ⊔ intVec) ↔
      w ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ∧ ∃ m : ℤ, bil (sumSqForm n) w (omearaEHalf n) / 2 = m :=
    fun w => adj_N_mem (sumSqForm n) adj_D_unimodular (omearaEHalf n)
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    intro g hg
    rcases hg with (hg | hg) | hg
    · have : g = omearaEHalf n := hg
      subst this
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · obtain ⟨i, -, rfl⟩ := hg
      refine Submodule.mem_sup_right ((hN _).mpr ⟨?_, 1, ?_⟩)
      · refine adj_D_coord.mpr fun j => ?_
        by_cases h : j = i
        · subst h; exact ⟨2, by simp⟩
        · exact ⟨0, by simp [h]⟩
      · rw [adj_sumSq_bil, adj_dot_half]
        simp [Finset.sum_pi_single']
    · obtain ⟨i, j, -, rfl⟩ := hg
      refine Submodule.mem_sup_right ((hN _).mpr ⟨?_, 0, ?_⟩)
      · refine adj_D_coord.mpr fun l => ?_
        exact ⟨(if l = i then 1 else 0) - (if l = j then 1 else 0), by simp [Pi.single_apply]⟩
      · rw [adj_sumSq_bil, adj_dot_half]
        simp [Finset.sum_sub_distrib, Finset.sum_pi_single']
  · refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (Submodule.subset_span (Or.inl (Or.inl rfl)))) ?_
    intro w hw
    obtain ⟨hwD, m, hm⟩ := (hN w).mp hw
    choose a ha using adj_D_coord.mp hwD
    refine (omeara106_11 h4 hn w).mpr ⟨fun i => ⟨2 * a i, by rw [ha i]; push_cast; ring⟩,
      fun i j => ⟨a i - a j, by rw [ha i, ha j]; push_cast; ring⟩, ⟨m, ?_⟩⟩
    rw [adj_sumSq_bil, adj_dot_half] at hm
    linarith

/-- **$E$ is the unique unimodular lattice containing $y$ adjacent to $D$** (O'Meara 1973, §106E, p. 331, via 106:7):
for $4 \mid n$, $n \ge 8$, the lattice $E$ (`omearaE n`) equals $\mathbb Zy + (\mathbb Zy + D)^\#$, and every unimodular
lattice $L$ for $I_n$ with $y \in L$ that is adjacent to $D = \mathbb Z^n$ equals $E$. -/
@[kb "omeara1963" "§106E, p. 331 (E = Zy + (Zy + D)# is the unique unimodular lattice containing y adjacent to D)"]
theorem omeara106_r34 {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    omearaE n = Submodule.span (𝓞 ℚ) {omearaEHalf n} ⊔
      omearaDual (sumSqForm n) (Submodule.span (𝓞 ℚ) {omearaEHalf n} ⊔ intVec) ∧
    ∀ L : Submodule (𝓞 ℚ) (Fin n → ℚ), IsUnimodularZ (sumSqForm n) L → omearaEHalf n ∈ L →
      Nbr.IsNbrL (sumSqForm n) 2 L intVec → L = omearaE n := by
  obtain ⟨h2, hyD, -, hQ⟩ := omeara106_r33 h4 (by omega : 0 < n)
  obtain ⟨-, -, -, huniq⟩ := omeara106_7 (sumSqForm n) adj_D_unimodular h2 hyD hQ
  exact ⟨adj_E_eq h4 h8, fun L hL hyL hadj => by rw [adj_E_eq h4 h8]; exact huniq L hL hyL hadj⟩

/-- **$E$ is unimodular and adjacent to $D$** (O'Meara 1973, §106E, p. 331): for $4 \mid n$, $n \ge 8$, the lattice $E$ is
a unimodular lattice for $I_n$, it contains $y = \tfrac12(x_0 + \dots + x_{n-1})$, and it is adjacent to $D = \mathbb Z^n$. -/
@[kb "omeara1963" "§106E, p. 331 (E is a unimodular lattice adjacent to D containing y)"]
theorem omeara106_r29_adjacent {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    IsUnimodularZ (sumSqForm n) (omearaE n) ∧ omearaEHalf n ∈ omearaE n ∧
      Nbr.IsNbrL (sumSqForm n) 2 (omearaE n) intVec := by
  obtain ⟨h2, hyD, -, hQ⟩ := omeara106_r33 h4 (by omega : 0 < n)
  obtain ⟨h1, h3, h5, -⟩ := omeara106_7 (sumSqForm n) adj_D_unimodular h2 hyD hQ
  rw [← adj_E_eq h4 h8] at h1 h3 h5
  exact ⟨h1, h3, h5⟩

/-- **An indecomposable unimodular lattice adjacent to $D$ exists** (O'Meara 1973, §106E, p. 331): for $4 \mid n$,
$n \ge 8$, there is a unimodular lattice $L$ for $I_n$, adjacent to $D = \mathbb Z^n$, which is indecomposable (namely
$E$, by `omearaE_indecomposable`). -/
@[kb "omeara1963" "§106E, p. 331 (there is an indecomposable unimodular lattice adjacent to D)"]
theorem omeara106_r29 {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    ∃ L : Submodule (𝓞 ℚ) (Fin n → ℚ), IsUnimodularZ (sumSqForm n) L ∧
      Nbr.IsNbrL (sumSqForm n) 2 L intVec ∧ IsIndecomposable (sumSqForm n) L := by
  obtain ⟨h1, -, h3⟩ := omeara106_r29_adjacent h4 h8
  exact ⟨omearaE n, h1, h3, omearaE_indecomposable h4 h8⟩

/-! ### The vectors of the indecomposability argument (106.p3) -/

private lemma adj_sq_sub {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∑ l, ((Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ) : Fin n → ℚ) l) ^ 2 = 2 := by
  rw [Finset.sum_eq_add i j hij]
  · simp [hij, hij.symm]
    norm_num
  · intro c _ h1
    simp [h1.1, h1.2]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro h; exact absurd (Finset.mem_univ j) h

private lemma adj_sq_add {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∑ l, ((Pi.single i (1 : ℚ) + Pi.single j (1 : ℚ) : Fin n → ℚ) l) ^ 2 = 2 := by
  rw [Finset.sum_eq_add i j hij]
  · simp [hij, hij.symm]
    norm_num
  · intro c _ h1
    simp [h1.1, h1.2]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The indecomposability vectors of $E$** (O'Meara 1973, §106E, p. 332, the proof that $E$ is indecomposable): for
$4 \mid n$, $n \ge 8$, the $n$ vectors $x_{i+1} - x_i$ ($0 \le i \le n - 2$) and $x_0 + x_1$ all lie in $E$, all have
$Q = 2$ (for $Q = I_n$), and they span $V = \mathbb Q^n$ over $\mathbb Q$. Indices are $0$-based: O'Meara's
$x_2 - x_1, \dots, x_n - x_{n-1}, x_1 + x_2$ are $x_1 - x_0, \dots, x_{n-1} - x_{n-2}, x_0 + x_1$ here.
The remaining steps of the book's argument (`omearaE_not_represents_one`, `omearaE_indecomposable`) are in
`Sec106E.lean`. -/
@[kb "omeara1963" "§106E, p. 332 (the vectors x_{i+1} − x_i and x₁ + x₂ lie in E, have Q = 2 and span V)"]
theorem omeara106_p3 {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    (∀ i j : Fin n, j.val + 1 = i.val →
      (Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ omearaE n ∧
        (sumSqForm n).eval (Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ)) = 2) ∧
    (∀ a b : Fin n, a.val = 0 → b.val = 1 →
      (Pi.single a (1 : ℚ) + Pi.single b (1 : ℚ) : Fin n → ℚ) ∈ omearaE n ∧
        (sumSqForm n).eval (Pi.single a (1 : ℚ) + Pi.single b (1 : ℚ)) = 2) ∧
    Submodule.span ℚ ({v | ∃ i j : Fin n, j.val + 1 = i.val ∧
        v = (Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ) : Fin n → ℚ)} ∪
      {v | ∃ a b : Fin n, a.val = 0 ∧ b.val = 1 ∧
        v = (Pi.single a (1 : ℚ) + Pi.single b (1 : ℚ) : Fin n → ℚ)}) = ⊤ := by
  have hn : 2 < n := by omega
  have hne : ∀ i j : Fin n, j.val + 1 = i.val → i ≠ j := fun i j h hh => by
    subst hh; omega
  have hR : ∀ i j : Fin n, j.val + 1 = i.val →
      (Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ omearaE n := fun i j h =>
    Submodule.subset_span (Or.inr ⟨i, j, h, rfl⟩)
  refine ⟨fun i j h => ⟨hR i j h, by rw [adj_sumSq_eval]; exact adj_sq_sub i j (hne i j h)⟩,
    fun a b ha hb => ⟨?_, ?_⟩, ?_⟩
  · have hab : a ≠ b := fun h => by subst h; omega
    have e : (Pi.single a (1 : ℚ) + Pi.single b (1 : ℚ) : Fin n → ℚ) =
        Pi.single a (2 : ℚ) + (Pi.single b (1 : ℚ) - Pi.single a (1 : ℚ)) := by
      ext l
      by_cases h1 : l = a
      · subst h1; simp [hab]; norm_num
      · by_cases h2 : l = b
        · subst h2; simp [h1]
        · simp [h1, h2]
    rw [e]
    exact add_mem (Submodule.subset_span (Or.inl (Or.inr ⟨a, ha, rfl⟩))) (hR b a (by omega))
  · have hab : a ≠ b := fun h => by subst h; omega
    rw [adj_sumSq_eval]; exact adj_sq_add a b hab
  · set S := Submodule.span ℚ ({v | ∃ i j : Fin n, j.val + 1 = i.val ∧
        v = (Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ) : Fin n → ℚ)} ∪
      {v | ∃ a b : Fin n, a.val = 0 ∧ b.val = 1 ∧
        v = (Pi.single a (1 : ℚ) + Pi.single b (1 : ℚ) : Fin n → ℚ)}) with hS
    have hd : ∀ i j : Fin n, j.val + 1 = i.val →
        (Pi.single i (1 : ℚ) - Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ S := fun i j h =>
      Submodule.subset_span (Or.inl ⟨i, j, h, rfl⟩)
    have hz : ∀ a b : Fin n, a.val = 0 → b.val = 1 →
        (Pi.single a (1 : ℚ) + Pi.single b (1 : ℚ) : Fin n → ℚ) ∈ S := fun a b ha hb =>
      Submodule.subset_span (Or.inr ⟨a, b, ha, hb, rfl⟩)
    have key : ∀ t : ℕ, ∀ h : t + 1 < n,
        (Pi.single (⟨t, by omega⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) ∈ S ∧
        (Pi.single (⟨t + 1, h⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) ∈ S := by
      intro t
      induction t with
      | zero =>
        intro h
        have h1 := hd ⟨0 + 1, h⟩ ⟨0, by omega⟩ rfl
        have h2 := hz ⟨0, by omega⟩ ⟨0 + 1, h⟩ rfl rfl
        constructor
        · have e : (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) = (1 / 2 : ℚ) •
              ((Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℚ) + Pi.single (⟨0 + 1, h⟩ : Fin n) (1 : ℚ)) -
                (Pi.single (⟨0 + 1, h⟩ : Fin n) (1 : ℚ) - Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℚ))) := by
            ext l
            simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
            ring
          rw [e]
          exact S.smul_mem _ (S.sub_mem h2 h1)
        · have e : (Pi.single (⟨0 + 1, h⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) = (1 / 2 : ℚ) •
              ((Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℚ) + Pi.single (⟨0 + 1, h⟩ : Fin n) (1 : ℚ)) +
                (Pi.single (⟨0 + 1, h⟩ : Fin n) (1 : ℚ) - Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℚ))) := by
            ext l
            simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
            ring
          rw [e]
          exact S.smul_mem _ (S.add_mem h2 h1)
      | succ t ih =>
        intro h
        obtain ⟨-, h2⟩ := ih (by omega)
        refine ⟨h2, ?_⟩
        have h1 := hd ⟨t + 1 + 1, h⟩ ⟨t + 1, by omega⟩ rfl
        have e : (Pi.single (⟨t + 1 + 1, h⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) =
            (Pi.single (⟨t + 1 + 1, h⟩ : Fin n) (1 : ℚ) - Pi.single (⟨t + 1, by omega⟩ : Fin n) (1 : ℚ)) +
              Pi.single (⟨t + 1, by omega⟩ : Fin n) (1 : ℚ) := by abel
        rw [e]
        exact S.add_mem h1 h2
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : ℚ) : Fin n → ℚ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => S.smul_mem _ ?_
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · have e : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [e]
      exact (key 0 (by omega)).1
    · obtain ⟨t, ht⟩ : ∃ t, i.val = t + 1 := ⟨i.val - 1, by omega⟩
      have e : i = ⟨t + 1, by omega⟩ := Fin.ext ht
      rw [e]
      exact (key t (by omega)).2

/-! ### 106.r30: all indecomposable unimodular lattices adjacent to $D$ lie in the proper class of $E$ -/

private lemma adj_uni_glImage {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup Q ℚ)
    {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) : IsUnimodularZ Q (glImage γ L) := by
  unfold IsUnimodularZ
  ext x
  constructor
  · intro hx
    have h1 : γ⁻¹.val *ᵥ x ∈ omearaDual Q L := by
      intro y' hy'
      obtain ⟨m', hm'⟩ := hx _ (mulVec_mem_glImage hy')
      refine ⟨m', ?_⟩
      rw [← hm']
      congr 1
      calc bil Q (γ⁻¹.val *ᵥ x) y'
          = bil Q (γ.val *ᵥ (γ⁻¹.val *ᵥ x)) (γ.val *ᵥ y') := (bil_isometry Q hγ _ _).symm
        _ = bil Q x (γ.val *ᵥ y') := by rw [mulVec_inv_mulVec]
    rw [hL] at h1
    exact ⟨_, h1, mulVec_inv_mulVec γ x⟩
  · intro hx
    obtain ⟨u, hu, rfl⟩ := mem_glImage.mp hx
    intro z hz
    obtain ⟨v, hv, rfl⟩ := mem_glImage.mp hz
    obtain ⟨m', hm'⟩ := adj_uni_mem Q hL hu hv
    exact ⟨m', by rw [bil_isometry Q hγ]; exact hm'⟩

private lemma adj_diag {n : ℕ} (ε : Fin n → ℚ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ σ : GL (Fin n) ℚ, σ ∈ orthGroup (sumSqForm n) ℚ ∧ (∀ x i, (σ.val *ᵥ x) i = ε i * x i) ∧
      σ.val.det = ∏ i, ε i := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  have hMM : Matrix.diagonal ε * Matrix.diagonal ε = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hε2 i
  refine ⟨⟨Matrix.diagonal ε, Matrix.diagonal ε, hMM, hMM⟩, ?_, ?_, ?_⟩
  · apply mem_orthGroup_of_eval
    intro z
    show (sumSqForm n).eval ((Matrix.diagonal ε) *ᵥ z) = (sumSqForm n).eval z
    rw [adj_sumSq_eval, adj_sumSq_eval]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_diagonal]
    calc (ε i * z i) ^ 2 = (ε i * ε i) * z i ^ 2 := by ring
      _ = z i ^ 2 := by rw [hε2 i, one_mul]
  · intro x i
    exact Matrix.mulVec_diagonal ε x i
  · exact Matrix.det_diagonal

private lemma adj_diag_D {n : ℕ} {σ : GL (Fin n) ℚ} (ε : Fin n → ℚ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hσ : ∀ x i, (σ.val *ᵥ x) i = ε i * x i) :
    glImage σ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) = intVec := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  have hiff : ∀ x i, (∃ m : ℤ, (σ.val *ᵥ x) i = m) ↔ ∃ m : ℤ, x i = m := fun x i => by
    rw [hσ]
    rcases hε i with h | h <;> rw [h]
    · simp
    · constructor
      · rintro ⟨m, hm⟩
        exact ⟨-m, by push_cast; linarith⟩
      · rintro ⟨m, hm⟩
        exact ⟨-m, by push_cast; linarith⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact adj_D_coord.mpr fun i => (hiff z i).mpr (adj_D_coord.mp hz i)
  · intro hx
    refine ⟨σ.val *ᵥ x, adj_D_coord.mpr fun i => (hiff x i).mpr (adj_D_coord.mp hx i), ?_⟩
    show σ.val *ᵥ (σ.val *ᵥ x) = x
    funext i
    rw [hσ, hσ, ← mul_assoc, hε2 i, one_mul]

/-- The reflection $\tau_{x_0 - x_1}$ is an improper unit of $E$ (it swaps $x_0$ and $x_1$). -/
private lemma adj_swap_E {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    ∃ τ : orthGroup (sumSqForm n) ℚ, ((τ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = -1 ∧
      glImage (τ : GL (Fin n) ℚ) (omearaE n) = omearaE n := by
  have hn : 0 < n := by omega
  set a0 : Fin n := ⟨0, by omega⟩ with ha0
  set a1 : Fin n := ⟨1, by omega⟩ with ha1
  have hne : a0 ≠ a1 := fun h => by
    have := congrArg Fin.val h
    simp [ha0, ha1] at this
  set w : Fin n → ℚ := Pi.single a0 1 - Pi.single a1 1 with hw
  have hw2 : (sumSqForm n).evalIn ℚ w = 2 := by
    have : (sumSqForm n).eval w = 2 := by rw [adj_sumSq_eval]; exact adj_sq_sub a0 a1 hne
    exact this
  have hw0 : (sumSqForm n).evalIn ℚ w ≠ 0 := by rw [hw2]; norm_num
  have hperm : ∀ y : Fin n → ℚ, ((symm (sumSqForm n) ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ y =
      fun l => y (Equiv.swap a0 a1 l) := by
    intro y
    rw [symm_mulVec_bil _ ℚ hw0, hw2]
    have hq : qbil (sumSqForm n) ℚ w y = 2 * (y a0 - y a1) := by
      have : qbil (sumSqForm n) ℚ w y = bil (sumSqForm n) w y := by simp [qbil, bil]
      rw [this, adj_sumSq_bil]
      congr 1
      simp [hw, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
    rw [hq]
    funext l
    by_cases h0 : l = a0
    · subst h0
      simp [hw, hne]
    · by_cases h1 : l = a1
      · subst h1
        simp [hw, hne.symm]
      · simp [hw, h0, h1, Equiv.swap_apply_of_ne_of_ne h0 h1]
  have hmaps : ∀ z ∈ omearaE n, (fun l => z (Equiv.swap a0 a1 l)) ∈ omearaE n := by
    intro z hz
    obtain ⟨p1, p2, m, hm⟩ := (omeara106_11 h4 hn z).mp hz
    refine (omeara106_11 h4 hn _).mpr ⟨fun i => p1 _, fun i j => p2 _ _, m, ?_⟩
    have : ∑ i, (fun l => z (Equiv.swap a0 a1 l)) i = ∑ i, z i := Equiv.sum_comp _ _
    rw [this]
    exact hm
  refine ⟨symm (sumSqForm n) ℚ w, symm_det _ ℚ hw0, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := mem_glImage.mp hx
    rw [hperm]
    exact hmaps z hz
  · intro hx
    refine ⟨fun l => x (Equiv.swap a0 a1 l), hmaps x hx, ?_⟩
    show ((symm (sumSqForm n) ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ _ = x
    rw [hperm]
    funext l
    simp

/-- If $y' \in E' - D$ has an integral coordinate $y'_j \in \mathbb Z$, then the unimodular lattice $E'$ adjacent to
$D$ splits off $\mathbb Zx_j$ (O'Meara 1973, p. 333: "$x_j \in E' \cap D \subseteq E'$ by 106:6 and $E'$ would then be
split by $\mathbb Zx_j$"), so it is decomposable. -/
private lemma adj_split {n : ℕ} {E' : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hE' : IsUnimodularZ (sumSqForm n) E')
    (hadj : Nbr.IsNbrL (sumSqForm n) 2 E' intVec) (hind : IsIndecomposable (sumSqForm n) E')
    {y' : Fin n → ℚ} (hy'E : y' ∈ E') (hy'D : y' ∉ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)))
    (j : Fin n) (hj : ∃ c : ℤ, y' j = c) : False := by
  obtain ⟨c, hc⟩ := hj
  obtain ⟨e, he⟩ : ∃ e : Fin n → ℚ, e = Pi.single j 1 := ⟨_, rfl⟩
  have hej : e j = 1 := by rw [he]; simp
  have hel : ∀ l, l ≠ j → e l = 0 := fun l hl => by rw [he]; simp [hl]
  have hdot : ∀ z : Fin n → ℚ, ∑ i, z i * e i = z j := fun z => by
    rw [Finset.sum_eq_single j]
    · rw [hej, mul_one]
    · intro b _ hb
      rw [hel b hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hbile : ∀ z, bil (sumSqForm n) z e = 2 * z j := fun z => by
    rw [adj_sumSq_bil, hdot]
  have heD : e ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := adj_D_coord.mpr fun l => by
    by_cases h : l = j
    · subst h; exact ⟨1, by simp [hej]⟩
    · exact ⟨0, by simp [hel l h]⟩
  have heE : e ∈ E' := by
    obtain ⟨-, -, -, h4⟩ := omeara106_6 (sumSqForm n) adj_D_unimodular hE' hadj hy'E hy'D
    refine (Submodule.mem_inf.mp ((h4 e).mpr ⟨heD, c, ?_⟩)).1
    rw [bil_comm, hbile, hc]
    ring
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : Submodule (𝓞 ℚ) (Fin n → ℚ), ∀ z, z ∈ K₂ ↔ z ∈ E' ∧ z j = 0 :=
    ⟨E' ⊓ LinearMap.ker (LinearMap.proj j : (Fin n → ℚ) →ₗ[𝓞 ℚ] ℚ), fun z => by simp⟩
  have hmK₁ : ∀ m : ℤ, (m : ℚ) • e ∈ Submodule.span (𝓞 ℚ) {e} := fun m =>
    Submodule.mem_span_singleton.mpr ⟨(m : 𝓞 ℚ), by rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]⟩
  refine hind.2 ⟨Submodule.span (𝓞 ℚ) {e}, K₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : e ∈ Submodule.span (𝓞 ℚ) {e} := Submodule.mem_span_singleton_self e
    rw [h, Submodule.mem_bot] at h1
    have := congrFun h1 j
    rw [hej] at this
    simp at this
  · intro h
    have hv : y' - (c : ℚ) • e ∈ K₂ :=
      (hK₂ _).mpr ⟨E'.sub_mem hy'E (adj_intsmul_mem heE c), by simp [hc, hej]⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hv
    apply hy'D
    refine adj_D_coord.mpr fun l => ?_
    by_cases hl : l = j
    · subst hl
      exact ⟨c, hc⟩
    · exact ⟨0, by rw [hv]; simp [hel l hl]⟩
  · intro x hx z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨k, hk⟩ := adj_smul_int a e
    rw [hk, adj_bil_smul_l, bil_comm, hbile, ((hK₂ z).mp hz).2]
    ring
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    obtain ⟨k, hk⟩ := adj_smul_int a e
    rw [hk] at hx2 ⊢
    have h0 := ((hK₂ _).mp hx2).2
    simp only [Pi.smul_apply, hej, smul_eq_mul, mul_one] at h0
    rw [h0, zero_smul]
  · apply le_antisymm
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr heE) (fun z hz => ((hK₂ z).mp hz).1)
    · intro z hz
      obtain ⟨m, hm⟩ := adj_uni_mem (sumSqForm n) hE' hz heE
      rw [hbile] at hm
      have hzj : z j = m := by linarith
      exact Submodule.mem_sup.mpr ⟨(m : ℚ) • e, hmK₁ m, z - (m : ℚ) • e,
        (hK₂ _).mpr ⟨E'.sub_mem hz (adj_intsmul_mem heE m), by simp [hzj, hej]⟩, by abel⟩

/-- **All indecomposable unimodular lattices adjacent to $D$ lie in the proper class of $E$** (O'Meara 1973, §106E,
pp. 332–333): for $4 \mid n$, $n \ge 8$, let $E'$ be an indecomposable unimodular lattice for $I_n$ adjacent to
$D = \mathbb Z^n$. Then $E' = \gamma E$ for a rotation $\gamma \in O^+(V)$ (`IsProperIsometric (sumSqForm n) (omearaE n) E'`).

Proof as in the book: $E'$ contains some $y' = \tfrac12\sum a_ix_i \notin D$ with all $a_i$ odd (otherwise $x_i \in E'$
splits off $E'$); after changing $y'$ by an element of $2D \subseteq E' \cap D$ one may take all $a_i = \pm1$; the sign
change $\sigma$ ($\sigma x_i = \pm x_i$) satisfies $\sigma D = D$ and $\sigma y = y'$, so $\sigma E = E'$ by uniqueness
(106:8a); finally $\sigma$ or $\sigma\tau_{x_0 - x_1}$ is a rotation, since $\tau_{x_0 - x_1}$ is a unit of $E$ of
determinant $-1$ (swapping $x_0$ and $x_1$). Indices are $0$-based. -/
@[kb "omeara1963" "§106E, pp. 332–333 (any indecomposable unimodular lattice adjacent to D is in the proper class of E)"]
theorem omeara106_r30 {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) {E' : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hE' : IsUnimodularZ (sumSqForm n) E') (hadj : Nbr.IsNbrL (sumSqForm n) 2 E' intVec)
    (hind : IsIndecomposable (sumSqForm n) E') :
    IsProperIsometric (sumSqForm n) (omearaE n) E' := by
  have hn : 0 < n := by omega
  have hD := adj_D_unimodular (n := n)
  obtain ⟨y', hy'E, hy'D⟩ := adj_exists_out (sumSqForm n) hadj
  have h2y : ∀ i, ∃ a : ℤ, 2 * y' i = a := fun i => by
    obtain ⟨m, hm⟩ := adj_D_coord.mp (adj_nbr_two_smul _ hadj hy'E) i
    exact ⟨m, by simpa using hm⟩
  choose a ha using h2y
  have hodd : ∀ i, Odd (a i) := by
    intro j
    by_contra hnot
    obtain ⟨c, hc⟩ := Int.not_odd_iff_even.mp hnot
    refine adj_split hE' hadj hind hy'E hy'D j ⟨c, ?_⟩
    have : (a j : ℚ) = c + c := by exact_mod_cast hc
    linarith [ha j]
  have hsign : ∀ i, ∃ s : ℚ, ∃ d : ℤ, (s = 1 ∨ s = -1) ∧ y' i = s / 2 + 2 * d := by
    intro i
    obtain ⟨k, hk⟩ := hodd i
    by_cases h : a i % 4 = 1
    · refine ⟨1, a i / 4, Or.inl rfl, ?_⟩
      have h' : a i = 4 * (a i / 4) + 1 := by omega
      have h'' : (a i : ℚ) = 4 * ((a i / 4 : ℤ) : ℚ) + 1 := by exact_mod_cast h'
      linarith [ha i]
    · refine ⟨-1, a i / 4 + 1, Or.inr rfl, ?_⟩
      have h' : a i = 4 * (a i / 4 + 1) - 1 := by omega
      have h'' : (a i : ℚ) = 4 * ((a i / 4 + 1 : ℤ) : ℚ) - 1 := by exact_mod_cast h'
      linarith [ha i]
  choose ε d hε hd using hsign
  obtain ⟨σ, hσO, hσx, hσdet⟩ := adj_diag ε hε
  have hσD := adj_diag_D ε hε hσx
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  obtain ⟨hEu, hyE, hEadj⟩ := omeara106_r29_adjacent h4 h8
  have hσEuni := adj_uni_glImage (sumSqForm n) hσO hEu
  have hσEadj : Nbr.IsNbrL (sumSqForm n) 2 (glImage σ (omearaE n)) intVec := by
    have := hEadj.glImage hσO
    rwa [hσD] at this
  obtain ⟨y'', hy''⟩ : ∃ y'' : Fin n → ℚ, y'' = fun i => ε i / 2 := ⟨_, rfl⟩
  have hyσ : y'' = σ.val *ᵥ omearaEHalf n := by
    rw [hy'']
    funext i
    rw [hσx]
    simp only [omearaEHalf]
    ring
  have hy''σE : y'' ∈ glImage σ (omearaE n) := by
    rw [hyσ]
    exact mulVec_mem_glImage hyE
  have hy''E' : y'' ∈ E' := by
    have hdD : (fun i => (d i : ℚ)) ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) :=
      adj_D_coord.mpr fun i => ⟨d i, rfl⟩
    have h2d := adj_nbr_two_smul_left _ hadj hdD
    have : y'' = y' - (2 : ℚ) • (fun i => (d i : ℚ)) := by
      rw [hy'']
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hd i]
    rw [this]
    exact E'.sub_mem hy'E h2d
  have hy''D : y'' ∉ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := fun h => by
    obtain ⟨m, hm⟩ := adj_D_coord.mp h ⟨0, hn⟩
    rw [hy''] at hm
    rcases hε ⟨0, hn⟩ with h1 | h1 <;> simp only [h1] at hm
    · have h3 : (2 : ℚ) * m = 1 := by linarith
      have h4' : 2 * m = 1 := by exact_mod_cast h3
      omega
    · have h3 : (2 : ℚ) * m = -1 := by linarith
      have h4' : 2 * m = -1 := by exact_mod_cast h3
      omega
  have heq : glImage σ (omearaE n) = E' :=
    (omeara106_8a (sumSqForm n) hD hσEuni hE' hσEadj hadj hy''σE hy''D hy''E' hy''D).mpr
      ⟨by rw [sub_self]; exact Submodule.zero_mem _, adj_uni_mem (sumSqForm n) hE' hy''E' hy''E'⟩
  have hdet : σ.val.det = 1 ∨ σ.val.det = -1 := by
    rw [hσdet]
    have : (∏ i, ε i) * (∏ i, ε i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => hε2 i
    exact mul_self_eq_one_iff.mp this
  rcases hdet with h | h
  · exact ⟨⟨σ, hσO⟩, Tamagawa.mem_soSub.mpr h, heq⟩
  · obtain ⟨τ, hτdet, hτE⟩ := adj_swap_E h4 h8
    refine ⟨⟨σ, hσO⟩ * τ, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul]
      change σ.val.det * ((τ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1
      rw [h, hτdet]
      norm_num
    · rw [Subgroup.coe_mul, glImage_mul, hτE]
      exact heq


end QuadFormsKB.Lattices
