/-
# Kneser's theorem: $\pi$-neighbours reach every class of the spinor genus

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$ (`Lattices/ClassSet.lean`), the spinor genus
(`Lattices/SpinorGenus.lean`), and $\pi$-neighbours of lattices (`IsNbrL`, `Lattices/NeighborGenus.lean`).

**Statement** (Kneser 1957, Satz 2 [unverified]; Schulze-Pillot 1991, §1; Scharlau–Hemkemeier 1998, Thm. 2.4
[unverified]). Let $n \ge 3$, $Q$ nondegenerate, $\pi$ a prime element with $\pi \nmid 2$ and $V_\pi$ isotropic, $L$ integral and
unimodular at $\pi$. Then for every $M$ in the spinor genus of $L$ there is $M' \cong M$ reachable from $L$ by a chain of
$\pi$-neighbours (`kneser_reach`). Hence, when the genus of $L$ is one spinor genus, the $\pi$-neighbour graph reaches every
class of the genus (`kneser_reach_genus`).

**Proof structure.**
1. *Global step* (`exists_isometric_agree_away`, **proved** from the named input `StrongApproximationSpinAt F`): if
   $M = \sigma\Sigma L$ with $\sigma \in O(V)$, $\Sigma \in O'(V_{\mathbb A_f})$, strong approximation away from $\{\pi, \infty\}$
   gives $\gamma \in O'(V)$ with $\gamma^{-1}\Sigma \in O(L_\mathfrak q)$ for all $\mathfrak q \ne (\pi)$; then $M' = \gamma^{-1}\Sigma L \cong M$
   and $M'_\mathfrak q = L_\mathfrak q$ for every $\mathfrak q \ne (\pi)$.
2. *Local step* (the named input `LocalNeighborChain F`): two lattices of one genus that agree away from $(\pi)$, with
   $L$ integral and unimodular at $\pi$, are joined by a chain of $\pi$-neighbours (induction on $[M : M \cap L]$: for
   $x \in M \setminus L$ with $\pi x \in L$, the neighbour $L_x + \mathcal O x$ of $L$ meets $M$ in more; Kneser 1957, §2
   [unverified]). Over $\mathbb Z$ this is the elementary-divisor argument; not formalized here.

**Inputs.** `StrongApproximationSpinAt F` is strong approximation for the rotation group with respect to
$S = \{(\pi)\} \cup \{\infty\}$ (O'Meara 1963, 104:4, p. 315, which uses 104:3, p. 311): it is the variant of the input
`StrongApproximationSpin F` (`Lattices/StrongApproximation.lean`, $S = \{\infty\}$, **indefinite** forms only) that applies to
**definite** forms, which is the case of interest for the neighbour method. `LocalNeighborChain F` is a purely local,
elementary statement (proof planned). Neither is equivalent to `kneser_reach`: the first is about the adelic group, the
second about lattices that already agree away from $\pi$.
-/
import QuadFormsKB.Lattices.SpinorGenus
import QuadFormsKB.Lattices.StrongApproximation
import QuadFormsKB.Lattices.NeighborGenus

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB

open Lattices Lattices.Nbr

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Strong approximation for rotations away from $\{\mathfrak p, \infty\}$ — a named, cited input.**
For every $n \ge 3$, every nondegenerate `Q : QuadForm F n`, every finite place $\mathfrak p$ at which $Q$ is isotropic
(`Q.IsotropicIn` $F_\mathfrak p$), every lattice $L$ and every $h \in O'(V_{\mathbb A_f})$ (`spinorKernelAf Q`), there is
$\gamma \in O'(V)$ (`spinorKernel Q F`) such that $\gamma^{-1}h$ stabilizes $L_\mathfrak q$ at **every finite place
$\mathfrak q \ne \mathfrak p$** (no condition at $\mathfrak p$).

This is the density of $O'(V)$ in $O'(V_{\mathbb A^S})$ for $S = \{\mathfrak p\} \cup \{\infty\}$ (O'Meara 1963, 104:4,
p. 315, there for an indefinite set of spots; Kneser 1966; it follows from strong approximation for $\mathrm{Spin}(V)$, which is simply connected and
non-compact at $\mathfrak p$). **Not proved in this repository.** Compare `StrongApproximationSpin F`
($S = \{\infty\}$, indefinite $Q$); this variant is the one needed for definite forms (Kneser's neighbour method). -/
@[kb "omeara1963" "§104, 104:4, p. 315 (S = finite primes except 𝔭)"]
structure StrongApproximationSpinAt (F : Type) [Field F] [NumberField F] : Prop where
  /-- $O'(V_{\mathbb A_f}) \subseteq O'(V)\cdot\prod_{\mathfrak q \ne \mathfrak p} O(L_\mathfrak q)$ for $V_\mathfrak p$ isotropic, $\dim V \ge 3$. -/
  approx : ∀ {n : ℕ} (Q : QuadForm F n), 3 ≤ n → Q.Nondegenerate → ∀ v : HeightOneSpectrum (𝓞 F),
    Q.IsotropicIn (v.adicCompletion F) → ∀ (L : Lat F n) (h : OAf Q), h ∈ spinorKernelAf Q →
      ∃ γ : orthGroup Q F, γ ∈ spinorKernel Q F ∧ ∀ w, w ≠ v →
        locAct w ((((diagF Q γ)⁻¹ * h) w : orthGroup Q _) : GL (Fin n) _) (loc w L.1) = loc w L.1

/-- **Unimodular at $\mathfrak p$** (for an integral lattice $L$): the dual $L^\# = \{x : B(x, L) \subseteq \mathcal O_F\}$ lies in
$L$ locally at $\mathfrak p$, i.e. every $x \in L^\#$ has $x \in L_\mathfrak p$ ($B(x, y) = x^{\mathsf T}Hy$, `bil`). With $L$ integral
($L \subseteq L^\#$) this says $L^\#_\mathfrak p = L_\mathfrak p$. For $L = \mathcal O_F^n$ and $\pi \nmid 2$ it amounts to $\pi \nmid \det H$. -/
@[kb "omeara1963" "§82G, p. 231 (unimodular lattice); 82:14b, p. 232 (L unimodular ⇔ L^# = L)"]
def IsUnimodularAt (Q : QuadForm F n) (L : Submodule (𝓞 F) (Fin n → F)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : Fin n → F, (∀ y ∈ L, bil Q y x ∈ (algebraMap (𝓞 F) F).range) → locVec v x ∈ loc v L

/-- **Kneser's local lemma — a named input (local, elementary; proof planned).** Let $\pi$ be a prime element with
$\pi \nmid 2$, $L$ an integral lattice unimodular at $(\pi)$, and $M$ in the genus of $L$ with $M_\mathfrak q = L_\mathfrak q$ for every
finite place $\mathfrak q \ne (\pi)$. Then $L$ and $M$ are joined by a chain of $\pi$-neighbours (`IsNbrL`).

Kneser 1957, §2 [unverified]; Schulze-Pillot 1991, §1 [unverified]. *Proof sketch:* induction on $[M : M \cap L]$; for
$x \in M \setminus L$ with $\pi x \in L$, $L' = \{y \in L : B(y, x) \in \mathcal O\} + \mathcal O x$ is a $\pi$-neighbour of $L$ (surjectivity
of $y \mapsto B(y, \pi x) \bmod \pi$ uses unimodularity), $L'$ is again unimodular at $\pi$ and agrees with $L$ away from $\pi$, and
$M \cap L' \supsetneq M \cap L$; when $M \subseteq L$, equal local volumes force $M = L$. -/
@[kb "kneser1957" "§2 [unverified]"]
structure LocalNeighborChain (F : Type) [Field F] [NumberField F] : Prop where
  /-- Lattices of one genus agreeing away from $(\pi)$ are joined by $\pi$-neighbour steps. -/
  chain : ∀ {n : ℕ} (Q : QuadForm F n) {π : 𝓞 F} (hπ : Prime π), ¬ π ∣ 2 → ∀ (L M : Lat F n),
    IsIntegral Q L.1 → IsUnimodularAt Q L.1 (hosOf hπ) → SameGenus Q L.1 M.1 →
    (∀ w, w ≠ hosOf hπ → loc w M.1 = loc w L.1) → Relation.ReflTransGen (IsNbrL Q π) L.1 M.1

variable (Q : QuadForm F n)

/-- **The global step of Kneser's theorem** (conditional on `StrongApproximationSpinAt F`): every $M$ in the spinor genus
of $L$ is isometric to a lattice $M'$ of the spinor genus of $L$ that agrees with $L$ at every finite place
$\mathfrak q \ne \mathfrak p$ ($V_\mathfrak p$ isotropic, $n \ge 3$). -/
@[kb "kneser1957" "§2 [unverified]"]
theorem exists_isometric_agree_away (hSA : StrongApproximationSpinAt F) (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    {v : HeightOneSpectrum (𝓞 F)} (hiso : Q.IsotropicIn (v.adicCompletion F)) {L M : Lat F n}
    (hM : SameSpinorGenus Q L M) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ SameSpinorGenus Q L M' ∧ ∀ w, w ≠ v → loc w M'.1 = loc w L.1 := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨σ, k, hk, rfl⟩ := (mem_latSpinorGenus Q).mp hM
  obtain ⟨γ, hγ, hloc⟩ := hSA.approx Q hn hQ v hiso L k hk
  refine ⟨latSMul Q ((diagF Q γ)⁻¹ * k) L, ?_, ?_, fun w hw => ?_⟩
  · -- M = σ γ M'
    have e : latSMul Q (diagF Q σ) (latSMul Q k L) =
        latSMul Q (diagF Q (σ * γ)) (latSMul Q ((diagF Q γ)⁻¹ * k) L) := by
      change (diagF Q σ) • (k • L) = (diagF Q (σ * γ)) • (((diagF Q γ)⁻¹ * k) • L)
      rw [← mul_smul, ← mul_smul, map_mul, mul_assoc, mul_inv_cancel_left]
    refine ⟨((σ * γ : orthGroup Q F) : GL (Fin n) F), (σ * γ).2, ?_⟩
    rw [e, diagF_smul]; rfl
  · refine (sameSpinorGenus_iff Q).mpr ⟨(diagF Q γ)⁻¹ * k, ?_, rfl⟩
    exact (spnGroup Q).mul_mem ((spnGroup Q).inv_mem (ratPoints_le_spnGroup Q ⟨γ, rfl⟩))
      (spinorKernelAf_le_spnGroup Q hk)
  · rw [loc_latSMul]; exact hloc w hw

/-- **Kneser's theorem** (Kneser 1957, Satz 2 [unverified]; conditional on the named inputs
`StrongApproximationSpinAt F` and `LocalNeighborChain F`). Let $n \ge 3$, $Q$ nondegenerate, $\pi$ a prime element with
$\pi \nmid 2$ and $Q$ isotropic over $F_\pi$, and $L$ integral and unimodular at $(\pi)$. Then for every $M$ in the spinor
genus of $L$ there is a lattice $M' \cong M$ reachable from $L$ by a chain of $\pi$-neighbours. -/
@[kb "kneser1957" "Satz 2 [unverified]"]
theorem kneser_reach (hSA : StrongApproximationSpinAt F) (hLoc : LocalNeighborChain F) (hn : 3 ≤ n)
    (hQ : Q.Nondegenerate) {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2)
    (hiso : Q.IsotropicIn ((hosOf hπ).adicCompletion F)) {L M : Lat F n} (hLi : IsIntegral Q L.1)
    (hLu : IsUnimodularAt Q L.1 (hosOf hπ)) (hM : SameSpinorGenus Q L M) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ Relation.ReflTransGen (IsNbrL Q π) L.1 M'.1 := by
  obtain ⟨M', hiM, hsM, hloc⟩ := exists_isometric_agree_away Q hSA hn hQ hiso hM
  exact ⟨M', hiM, hLoc.chain Q hπ h2 L M' hLi hLu (SameSpinorGenus.sameGenus Q hsM) hloc⟩

/-- **Kneser's theorem for a genus that is one spinor genus** (conditional as `kneser_reach`): if every lattice in the genus
of $L$ is in the spinor genus of $L$ (e.g. over $\mathbb Q$ when all local spinor norms $\theta(O^+(L_p))$ contain the units,
O'Meara 102:9, p. 304, and 104:5, p. 319; `Lattices/SpinorGlobal.lean` on branch `spinor-genera`), then the $\pi$-neighbour
graph starting at $L$ reaches every class of the genus of $L$. -/
@[kb "kneser1957" "Satz 2 [unverified]"]
theorem kneser_reach_genus (hSA : StrongApproximationSpinAt F) (hLoc : LocalNeighborChain F) (hn : 3 ≤ n)
    (hQ : Q.Nondegenerate) {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2)
    (hiso : Q.IsotropicIn ((hosOf hπ).adicCompletion F)) {L : Lat F n} (hLi : IsIntegral Q L.1)
    (hLu : IsUnimodularAt Q L.1 (hosOf hπ)) (hgs : ∀ M : Lat F n, SameGenus Q L.1 M.1 → SameSpinorGenus Q L M)
    {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    ∃ M' : Lat F n, IsIsometric Q M'.1 M.1 ∧ Relation.ReflTransGen (IsNbrL Q π) L.1 M'.1 :=
  kneser_reach Q hSA hLoc hn hQ hπ h2 hiso hLi hLu (hgs M hM)

end QuadFormsKB
