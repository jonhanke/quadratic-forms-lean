/-
# O'Meara §106C: rules of construction for adjacent lattices

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with a form `Q : QuadForm ℚ n`; $\mathbb Z$-lattices are
$\mathcal O_{\mathbb Q}$-submodules of $\mathbb Q^n$; O'Meara's bilinear form is $B = \tfrac12$ `bil Q` (so
$B(x, x) = Q(x)$), the dual is `omearaDual Q`, unimodular means `IsUnimodularZ Q` ($L^\# = L$), all from
`Literature/OMeara/Sec106Defs.lean`.

*Adjacency.* O'Meara (§106B, pp. 325–326) calls $K$ adjacent to $L$ when the invariant factors of $K$ in $L$ are
$\tfrac12\mathbb Z, \mathbb Z, \dots, \mathbb Z, 2\mathbb Z$. For unimodular $K, L$ this is the library's
$2$-neighbour relation `Lattices.Nbr.IsNbrL Q 2 L K` ($[L : L \cap K] = [K : L \cap K] = 2$, $2L \subseteq K$,
$2K \subseteq L$, $Q(L), Q(K) \subseteq \mathbb Z$): the indices force exactly one invariant factor $2\mathbb Z$ and
one $\tfrac12\mathbb Z$, and a unimodular lattice has $Q(L) \subseteq \mathfrak nL \subseteq \mathbb Z$. The statements
below use `IsNbrL Q 2` for "adjacent".

**Proves** (O'Meara 1973, §106C, pp. 328–330)
* Proposition 106:6 (`omeara106_6`): for $y \in L - K$, $L + K = \mathbb Zy + K$, $L = \mathbb Zy + (L \cap K)$ and
  $L \cap K = (\mathbb Zy + K)^\# = \{w \in K : B(w, y) \in \mathbb Z\}$;
* Proposition 106:8 (`omeara106_8`): $y + z \in L - K$ if and only if $z \in L \cap K$;
* Corollary 106:8a (`omeara106_8a`): two unimodular lattices $L, L'$ adjacent to $K$, with $y \in L - K$ and
  $y' \in L' - K$, are equal if and only if $y - y' \in K$ and $B(y, y') \in \mathbb Z$;
* Proposition 106:9 (`omeara106_9`): if $y \in L - K$ is $w + z$ with $Q(w) = 1$, $z \in K$ and
  $B(y, w) \in \tfrac12\mathbb Z - \mathbb Z$, then $K = \tau_wL$, so $\operatorname{cls}L = \operatorname{cls}K$.
-/
import QuadFormsKB.Literature.OMeara.Sec106Defs
import QuadFormsKB.Lattices.NeighborGenus
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Lattices.CartanDieudonne

open Matrix NumberField QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ} (Q : QuadForm ℚ n)

private lemma nm_two : nm (2 : 𝓞 ℚ) = 2 := by
  have h : (2 : 𝓞 ℚ) = ((2 : ℕ) : 𝓞 ℚ) := by norm_num
  rw [h, nm_natCast, NumberField.RingOfIntegers.rank]
  simp

private lemma index_two {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 L K) :
    (L ⊓ K).toAddSubgroup.relIndex L.toAddSubgroup = 2 := by
  have h1 := h.index_left
  rw [nm_two] at h1
  have e : (L ⊓ K).toAddSubgroup = L.toAddSubgroup ⊓ K.toAddSubgroup := rfl
  rw [e, AddSubgroup.inf_relIndex_left, h1]

private lemma eq_or_eq {H M G : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h1 : H ≤ M) (h2 : M ≤ G)
    (h : H.toAddSubgroup.relIndex G.toAddSubgroup = 2) : M = H ∨ M = G := by
  have e := AddSubgroup.relIndex_mul_relIndex H.toAddSubgroup M.toAddSubgroup G.toAddSubgroup
    (fun x hx => h1 hx) (fun x hx => h2 hx)
  rw [h] at e
  have hd : H.toAddSubgroup.relIndex M.toAddSubgroup ∣ 2 := ⟨_, e.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h3 | h3
  · left
    exact le_antisymm (fun x hx => AddSubgroup.relIndex_eq_one.mp h3 hx) h1
  · right
    rw [h3] at e
    have h4 : M.toAddSubgroup.relIndex G.toAddSubgroup = 1 := by omega
    exact le_antisymm h2 (fun x hx => AddSubgroup.relIndex_eq_one.mp h4 hx)

private lemma mem_dual {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} {x : Fin n → ℚ} :
    x ∈ omearaDual Q L ↔ ∀ y ∈ L, ∃ m : ℤ, bil Q x y / 2 = m := Iff.rfl

private lemma dual_anti {M N : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : M ≤ N) :
    omearaDual Q N ≤ omearaDual Q M :=
  fun _ hx y hy => hx y (h hy)

private lemma uni_mem {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) {x y : Fin n → ℚ}
    (hx : x ∈ L) (hy : y ∈ L) : ∃ m : ℤ, bil Q x y / 2 = m := by
  have : x ∈ omearaDual Q L := by rw [hL]; exact hx
  exact this y hy

private lemma uni_eq {M N : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IsUnimodularZ Q M)
    (hN : IsUnimodularZ Q N) (h : M ≤ N) : M = N := by
  refine le_antisymm h ?_
  have := dual_anti Q h
  rw [hM, hN] at this
  exact this

private lemma bil_add_l (x x' y : Fin n → ℚ) : bil Q (x + x') y = bil Q x y + bil Q x' y := by
  simp [bil, add_dotProduct]

private lemma bil_add_r (x y y' : Fin n → ℚ) : bil Q x (y + y') = bil Q x y + bil Q x y' := by
  simp [bil, Matrix.mulVec_add, dotProduct_add]

private lemma bil_sub_l (x x' y : Fin n → ℚ) : bil Q (x - x') y = bil Q x y - bil Q x' y := by
  simp [bil, sub_dotProduct]

private lemma bil_smul_r (c : ℚ) (x y : Fin n → ℚ) : bil Q x (c • y) = c * bil Q x y := by
  simp [bil, Matrix.mulVec_smul, dotProduct_smul]

private lemma qbil_eq (x y : Fin n → ℚ) : qbil Q ℚ x y = bil Q x y := by
  simp [qbil, bil]

private lemma smul_int (c : 𝓞 ℚ) (y : Fin n → ℚ) : ∃ k : ℤ, c • y = (k : ℚ) • y := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
    ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩
  subst hk
  refine ⟨k, ?_⟩
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

private lemma intsmul_mem {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} {x : Fin n → ℚ} (hx : x ∈ M) (k : ℤ) :
    (k : ℚ) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx k

private lemma two_smul_mem {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hadj : Nbr.IsNbrL Q 2 L K)
    {y : Fin n → ℚ} (hyL : y ∈ L) : (2 : ℚ) • y ∈ K := by
  have h := hadj.smul_right y hyL
  have e : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
  rw [e] at h
  exact h

private lemma kmem_iff {K : Submodule (𝓞 ℚ) (Fin n → ℚ)} {y : Fin n → ℚ} (hyK : y ∉ K)
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
    exact K.sub_mem h (intsmul_mem h2 j)
  · rintro ⟨j, hj⟩
    have e : (k : ℚ) • y = (j : ℚ) • ((2 : ℚ) • y) := by
      rw [hj]
      push_cast
      module
    rw [e]
    exact intsmul_mem h2 j

/-- **Proposition 106:6** (O'Meara 1973, §106C, p. 328): let $K, L$ be unimodular and adjacent, and $y \in L - K$.
Then $L + K = \mathbb Zy + K$, $L = \mathbb Zy + (L \cap K)$, and $L \cap K = (\mathbb Zy + K)^\# =
\{w \in K : B(w, y) \in \mathbb Z\}$. -/
@[kb "omeara1963" "§106C, 106:6, p. 328"]
theorem omeara106_6 {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K) (hL : IsUnimodularZ Q L)
    (hadj : Nbr.IsNbrL Q 2 L K) {y : Fin n → ℚ} (hyL : y ∈ L) (hyK : y ∉ K) :
    L ⊔ K = Submodule.span (𝓞 ℚ) {y} ⊔ K ∧ L = Submodule.span (𝓞 ℚ) {y} ⊔ (L ⊓ K) ∧
      L ⊓ K = omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K) ∧
      ∀ w, w ∈ L ⊓ K ↔ w ∈ K ∧ ∃ m : ℤ, bil Q w y / 2 = m := by
  have hyspan : y ∈ Submodule.span (𝓞 ℚ) {y} := Submodule.mem_span_singleton_self y
  have hspanL : Submodule.span (𝓞 ℚ) {y} ≤ L := by
    rw [Submodule.span_singleton_le_iff_mem]; exact hyL
  have h2 : L = Submodule.span (𝓞 ℚ) {y} ⊔ (L ⊓ K) := by
    have hle1 : L ⊓ K ≤ Submodule.span (𝓞 ℚ) {y} ⊔ (L ⊓ K) := le_sup_right
    have hle2 : Submodule.span (𝓞 ℚ) {y} ⊔ (L ⊓ K) ≤ L := sup_le hspanL inf_le_left
    rcases eq_or_eq hle1 hle2 (index_two Q hadj) with h | h
    · exfalso
      apply hyK
      have : y ∈ Submodule.span (𝓞 ℚ) {y} ⊔ (L ⊓ K) := Submodule.mem_sup_left hyspan
      rw [h] at this
      exact (Submodule.mem_inf.mp this).2
    · exact h.symm
  have h1 : L ⊔ K = Submodule.span (𝓞 ℚ) {y} ⊔ K := by
    apply le_antisymm
    · exact sup_le (h2.le.trans (sup_le_sup_left inf_le_right _)) le_sup_right
    · exact sup_le (hspanL.trans le_sup_left) le_sup_right
  have h3 : L ⊓ K = omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ K) := by
    rw [← h1]
    apply le_antisymm
    · intro x hx
      rw [mem_dual]
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨m1, hm1⟩ := uni_mem Q hL (Submodule.mem_inf.mp hx).1 ha
      obtain ⟨m2, hm2⟩ := uni_mem Q hK (Submodule.mem_inf.mp hx).2 hb
      exact ⟨m1 + m2, by rw [bil_add_r, add_div, hm1, hm2]; push_cast; rfl⟩
    · intro x hx
      have hxL : x ∈ omearaDual Q L := dual_anti Q (le_sup_left : L ≤ L ⊔ K) hx
      have hxK : x ∈ omearaDual Q K := dual_anti Q (le_sup_right : K ≤ L ⊔ K) hx
      rw [hL] at hxL
      rw [hK] at hxK
      exact Submodule.mem_inf.mpr ⟨hxL, hxK⟩
  refine ⟨h1, h2, h3, fun w => ?_⟩
  rw [h3]
  constructor
  · intro hw
    have hwK : w ∈ omearaDual Q K := dual_anti Q (le_sup_right : K ≤ Submodule.span (𝓞 ℚ) {y} ⊔ K) hw
    rw [hK] at hwK
    exact ⟨hwK, hw y (Submodule.mem_sup_left hyspan)⟩
  · rintro ⟨hwK, m, hm⟩
    rw [mem_dual]
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨k, hk⟩ := smul_int c y
    obtain ⟨m2, hm2⟩ := uni_mem Q hK hwK hb
    refine ⟨k * m + m2, ?_⟩
    rw [hk, bil_add_r, bil_smul_r, add_div, mul_div_assoc, hm, hm2]
    push_cast
    rfl

private lemma decomp {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K)
    (hL : IsUnimodularZ Q L) (hadj : Nbr.IsNbrL Q 2 L K) {y : Fin n → ℚ} (hyL : y ∈ L) (hyK : y ∉ K)
    {x : Fin n → ℚ} (hx : x ∈ L) :
    ∃ (k : ℤ) (t : Fin n → ℚ), t ∈ L ⊓ K ∧ x = (k : ℚ) • y + t ∧ (x ∈ K ↔ Even k) := by
  have h2 := (omeara106_6 Q hK hL hadj hyL hyK).2.1
  have hx' : x ∈ Submodule.span (𝓞 ℚ) {y} ⊔ (L ⊓ K) := by rw [← h2]; exact hx
  obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨k, hk⟩ := smul_int c y
  have htK : t ∈ K := (Submodule.mem_inf.mp ht).2
  refine ⟨k, t, ht, by rw [hk], ?_⟩
  rw [hk, ← kmem_iff hyK (two_smul_mem Q hadj hyL) k]
  constructor
  · intro h
    have := K.sub_mem h htK
    simpa using this
  · intro h
    exact K.add_mem h htK

/-- **Proposition 106:8** (O'Meara 1973, §106C, p. 329): let $K, L$ be unimodular and adjacent, and $y \in L - K$.
For $z \in V$: $y + z \in L - K$ if and only if $z \in L \cap K$. -/
@[kb "omeara1963" "§106C, 106:8, p. 329"]
theorem omeara106_8 {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K) (hL : IsUnimodularZ Q L)
    (hadj : Nbr.IsNbrL Q 2 L K) {y : Fin n → ℚ} (hyL : y ∈ L) (hyK : y ∉ K) (z : Fin n → ℚ) :
    (y + z ∈ L ∧ y + z ∉ K) ↔ z ∈ L ⊓ K := by
  constructor
  · rintro ⟨hyz, hyzK⟩
    have hzL : z ∈ L := by
      have := L.sub_mem hyz hyL
      simpa using this
    obtain ⟨k, t, ht, hx, hiff⟩ := decomp Q hK hL hadj hyL hyK hyz
    have hodd : ¬ Even k := fun h => hyzK (hiff.mpr h)
    obtain ⟨j, hj⟩ := Int.not_even_iff_odd.mp hodd
    have htK : t ∈ K := (Submodule.mem_inf.mp ht).2
    have e : z = ((j : ℚ) * 2) • y + t := by
      rw [hj] at hx
      push_cast at hx
      calc z = (y + z) - y := by abel
        _ = ((j : ℚ) * 2) • y + t := by rw [hx]; module
    have hzK : z ∈ K := by
      rw [e]
      exact K.add_mem (by rw [← smul_smul]; exact intsmul_mem (two_smul_mem Q hadj hyL) j) htK
    exact Submodule.mem_inf.mpr ⟨hzL, hzK⟩
  · intro hz
    obtain ⟨hzL, hzK⟩ := Submodule.mem_inf.mp hz
    refine ⟨L.add_mem hyL hzL, fun h => hyK ?_⟩
    have := K.sub_mem h hzK
    simpa using this

/-- **Corollary 106:8a** (O'Meara 1973, §106C, p. 329): let $L, L'$ be unimodular lattices adjacent to the unimodular
lattice $K$, $y \in L - K$, $y' \in L' - K$. Then $L = L'$ if and only if $y - y' \in K$ and $B(y, y') \in \mathbb Z$. -/
@[kb "omeara1963" "§106C, 106:8a, p. 329"]
theorem omeara106_8a {K L L' : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K) (hL : IsUnimodularZ Q L)
    (hL' : IsUnimodularZ Q L') (hadj : Nbr.IsNbrL Q 2 L K) (hadj' : Nbr.IsNbrL Q 2 L' K)
    {y y' : Fin n → ℚ} (hyL : y ∈ L) (hyK : y ∉ K) (hyL' : y' ∈ L') (hyK' : y' ∉ K) :
    L = L' ↔ y - y' ∈ K ∧ ∃ m : ℤ, bil Q y y' / 2 = m := by
  constructor
  · rintro rfl
    have h := (omeara106_8 Q hK hL hadj hyL hyK (y' - y)).mp
      ⟨by simpa using hyL', by simpa using hyK'⟩
    refine ⟨?_, uni_mem Q hL hyL hyL'⟩
    have := K.neg_mem (Submodule.mem_inf.mp h).2
    simpa using this
  · rintro ⟨hdK, m0, hm0⟩
    have hy'L : y' ∈ L := by
      have : y' ∈ omearaDual Q L := by
        rw [mem_dual]
        intro x hx
        obtain ⟨k, t, ht, rfl, -⟩ := decomp Q hK hL hadj hyL hyK hx
        obtain ⟨htL, htK⟩ := Submodule.mem_inf.mp ht
        obtain ⟨a, ha⟩ := uni_mem Q hL hyL htL
        obtain ⟨b, hb⟩ := uni_mem Q hK hdK htK
        refine ⟨k * m0 + a - b, ?_⟩
        have e : bil Q y' ((k : ℚ) • y + t) =
            k * bil Q y y' + bil Q y t - bil Q (y - y') t := by
          rw [bil_add_r, bil_smul_r, bil_comm Q y' y, bil_sub_l]
          ring
        rw [e, sub_div, add_div, mul_div_assoc, hm0, ha, hb]
        push_cast
        ring
      rw [hL] at this
      exact this
    obtain ⟨-, hL2, hL3, -⟩ := omeara106_6 Q hK hL hadj hy'L hyK'
    obtain ⟨-, hL2', hL3', -⟩ := omeara106_6 Q hK hL' hadj' hyL' hyK'
    have e : L ⊓ K = L' ⊓ K := hL3.trans hL3'.symm
    calc L = Submodule.span (𝓞 ℚ) {y'} ⊔ (L ⊓ K) := hL2
      _ = Submodule.span (𝓞 ℚ) {y'} ⊔ (L' ⊓ K) := by rw [e]
      _ = L' := hL2'.symm

/-- **Proposition 106:9** (O'Meara 1973, §106C, p. 330): let $K, L$ be unimodular and adjacent, and let $y \in L - K$
be $y = w + z$ with $Q(w) = 1$, $z \in K$ and $B(y, w) \in \tfrac12\mathbb Z - \mathbb Z$. Then the symmetry $\tau_w$
carries $L$ onto $K$; in particular $\operatorname{cls}L = \operatorname{cls}K$. -/
@[kb "omeara1963" "§106C, 106:9, p. 330"]
theorem omeara106_9 {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K) (hL : IsUnimodularZ Q L)
    (hadj : Nbr.IsNbrL Q 2 L K) {y w z : Fin n → ℚ} (hyL : y ∈ L) (hyK : y ∉ K) (hyw : y = w + z)
    (hw : Q.eval w = 1) (hz : z ∈ K) (hB : ∃ m : ℤ, bil Q y w / 2 = m + 1 / 2) :
    glImage (symm Q ℚ w : GL (Fin n) ℚ) L = K ∧ IsIsometric Q L K := by
  obtain ⟨m, hm⟩ := hB
  have hQw : Q.evalIn ℚ w ≠ 0 := by
    have : Q.evalIn ℚ w = 1 := hw
    rw [this]; exact one_ne_zero
  have hτx : ∀ x, ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x =
      x - (bil Q w x) • w := by
    intro x
    have h1 : Q.evalIn ℚ w = 1 := hw
    rw [symm_mulVec_bil Q ℚ hQw, qbil_eq, h1, div_one]
  have hinv : ∀ x, ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ
      (((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) = x := by
    intro x
    have h : ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *
        ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = 1 := by
      have := congrArg (fun g : orthGroup Q ℚ => ((g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ))
        (symm_mul_self Q ℚ w)
      simpa using this
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have hyw2 : bil Q y w = 2 * m + 1 := by linarith
  have hw' : w = y - z := by rw [hyw]; abel
  have h2w : (2 : ℚ) • w ∈ K := by
    rw [hw', smul_sub]
    exact K.sub_mem (two_smul_mem Q hadj hyL) (by have := intsmul_mem hz 2; rwa [Int.cast_ofNat] at this)
  have hy1 : ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ y ∈ K := by
    have e : ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ y =
        z - (m : ℚ) • ((2 : ℚ) • w) := by
      rw [hτx, bil_comm Q w y, hyw2]
      conv_lhs => rw [hyw]
      module
    rw [e]
    exact K.sub_mem hz (intsmul_mem h2w m)
  have ht1 : ∀ t ∈ L ⊓ K, ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ t ∈ K := by
    intro t ht
    obtain ⟨htL, htK⟩ := Submodule.mem_inf.mp ht
    obtain ⟨a, ha⟩ := uni_mem Q hL hyL htL
    obtain ⟨b, hb⟩ := uni_mem Q hK hz htK
    have hb' : bil Q w t = 2 * ((a : ℚ) - b) := by
      rw [hw', bil_sub_l]; linarith
    rw [hτx, hb']
    have e : t - (2 * ((a : ℚ) - b)) • w = t - (((a - b : ℤ)) : ℚ) • ((2 : ℚ) • w) := by
      push_cast
      module
    rw [e]
    exact K.sub_mem htK (intsmul_mem h2w _)
  have hsub : ∀ x ∈ L, ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x ∈ K := by
    intro x hx
    obtain ⟨k, t, ht, rfl, -⟩ := decomp Q hK hL hadj hyL hyK hx
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    exact K.add_mem (intsmul_mem hy1 k) (ht1 t ht)
  have hle : glImage (symm Q ℚ w : GL (Fin n) ℚ) L ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsub x hx
  have huni : IsUnimodularZ Q (glImage (symm Q ℚ w : GL (Fin n) ℚ) L) := by
    unfold IsUnimodularZ
    ext x
    constructor
    · intro hx
      have h1 : ((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x ∈ omearaDual Q L := by
        rw [mem_dual]
        intro y' hy'
        obtain ⟨m', hm'⟩ := hx _ (mulVec_mem_glImage hy')
        refine ⟨m', ?_⟩
        rw [← hm']
        congr 1
        calc bil Q (((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) y'
            = bil Q (((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)
              (((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ
                (((symm Q ℚ w : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ y')) := by rw [hinv y']
          _ = _ := bil_isometry Q (symm Q ℚ w).2 x _
      rw [hL] at h1
      exact ⟨_, h1, hinv x⟩
    · rintro ⟨u, hu, rfl⟩
      rw [mem_dual]
      rintro _ ⟨v, hv, rfl⟩
      have := bil_isometry Q (symm Q ℚ w).2 u v
      obtain ⟨m', hm'⟩ := uni_mem Q hL hu hv
      exact ⟨m', by rw [← hm', ← this]; rfl⟩
  have heq := uni_eq Q huni hK hle
  exact ⟨heq, ⟨(symm Q ℚ w : GL (Fin n) ℚ), (symm Q ℚ w).2, heq⟩⟩

end QuadFormsKB.Lattices
