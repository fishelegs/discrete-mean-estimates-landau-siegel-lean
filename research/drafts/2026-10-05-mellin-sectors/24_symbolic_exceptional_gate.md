# Symbolic exceptional-family gate and the role of time parameters

Draft research note dated 2026-10-05. Independently source-reviewed conditional algebraic ledger; not Lean-certified. The exact accepted exceptional-budget source identities are in [SOURCE_PINS.json](SOURCE_PINS.json). Original assumption exponent 2022 and intended exponent 2024 remain fixed. The new untilted scalar saddle theorem does not itself change the original raw moment threshold 64.

## 1. Exact abstract inputs

Write L=log D and let the original prime-family mass M satisfy M>=c P² L^(-gamma). Let mu be the actual finite normalized Gaussian measure, of mass at most one. Let E be a fixed exceptional character mask with #E<=C M L^(-kappa). Fix positive moment orders r,s and the literal test polynomials A and Q, and suppose

 integral sum_all |N|² dmu <= C P² L^beta,
 integral sum_all |A|^(2r) dmu <= C P² L^eA,
 integral sum_all |Q|^(2s) dmu <= C P² L^eQ,

where 1/r+1/s<1. N is the genuine continued four-L numerator times the original finite G, not its coefficient truncation. Assume the exact critical-line correction identity and its finite contour attachment for this chosen family/time, with its unit-modulus factors and positive normalization bounded below. These are essential hypotheses; they are not supplied by the new scalar saddle theorem.

Hölder with exponents 2,2r,2s,1/theta, where theta=(1-1/r-1/s)/2, gives

 M^-1 integral sum_E |NAQ| dmu
 <= C L^[ beta/2 + eA/(2r)+eQ/(2s)
       +gamma*(1+1/r+1/s)/2 - kappa*(1-1/r-1/s)/2 ].

Thus the sufficient raw-numerator exponent gate for this term is

 G_Q = kappa*(1-1/r-1/s) - eA/r - eQ/s
                         - gamma*(1+1/r+1/s).

A moment exponent beta<G_Q gives o(1); beta<=G_Q-2m gives O(L^-m). Equality beta=G_Q yields only O(1) from this estimate. This is an upper-bound certificate, not a necessary condition on the actual correction.

For the exact integrated joint alternative I_Q, if sum_all |I_Q|²<=C P²L^B, Cauchy and the same mask yield L^[(B+gamma-kappa)/2]. Its sufficient gate is B<kappa-gamma. B is a different exponent for a different observable, and must never be substituted for beta.

## 2. Remaining multiplier term

The original exact identity also contains R=FG-1. Suppose ((1/M) integral sum_all |R|^6 dmu)^(1/6)=O(L^-rho), and the actual A,Q full-family sixth moments are bounded by C P² L^eA6 and C P² L^eQ6, respectively. The normalized R premise supplies M^(1/6)L^-rho, not (P²)^(1/6)L^-rho. Hölder (2,6,6,6) on N,A,Q,R gives

 M^-1 integral sum_all |NAQR| dmu
 <= C L^[beta/2+(eA6+eQ6+5gamma)/6-rho].

Its gate is G_R=2rho-(eA6+eQ6+5gamma)/3. A complete sufficient raw gate for the positive exceptional correction is min(G_J,G_H,G_R), subject also to paid contour endpoints and exact transfer. Any separate good-side or signed-main-term errors remain additional obligations.

## 3. Original substitution and time-independence of the Hölder arithmetic

The accepted independently reviewed source ledger gives

 gamma=77, kappa=739, eA6=eJ6=81, eH8=144,
 rho=1435/4, with a legal eH6=81.

For full J2 choose r=s=3: G_J=(kappa-547)/3=64.
For H2 choose r=3,s=4: G_H=(5kappa-2219)/12=123.
The multiplier gate is G_R=3211/6, hence it is not the active one here.
The integrated-joint gate is kappa-77=662.
Consequently beta<64, beta<=52, and beta<=40 give respectively o(1), O(L^-6), and O(L^-12) for the original exceptional correction, exactly as in the accepted source.

Now write the proposed time center T0=L^a and width W=L^w, with H=W L^5. Neither a nor w appears directly in these Hölder exponents. Gaussian normalization removes its total width; the original prime window still gives gamma=77. Fixed polynomial changes of T0 do not alter the legal moment orders: A³ has support below P²; full J2³=(P^.5 D T0)³ is below P² eventually; J2⁴=P²D4T0⁴ exceeds P² for every fixed real a. H2⁴ retains its original exponential shortening. Thus merely lowering a,w does not make the forbidden full-J2 eighth-moment substitution legal.

The original threshold predicates are centerwise polynomial conditions. Their source second-moment arguments use coefficient absolute values and are uniform under n^(-itc), so shifting the center alone does not improve their Markov exponents. This observation is about the predicate count, not a new good-family zero theorem. The genuine numerator moment itself depends on the new time; no original-parameter analytic bound is silently transferred to it.

## 4. Enlarged-family conditional gate

To avoid collision with time notation, denote the three threshold increments by u34,u35,u36. The accepted source audit gives the new complement count

 kappa=min(740+2u34, 746+2u35, 739+2u36).

These are predicates for a new family, not a better bound for the unchanged old exceptional set. If a complete new-family transfer supplies the same exact correction and moment normalizations, its conditional gate is

 beta < min((kappa-547)/3, (5kappa-2219)/12, 3211/6).

In the modest ranges audited previously, the first expression is active. At (u34,u35,u36)=(87/4,75/4,89/4), kappa=1567/2 and the first gate is 473/6. This reproduces an older conditional source result; it is not a new benefit proved by the [untilted scalar kernel](23_averaged_scalar_saddle.md). The separate integrated gate is B<kappa-77.

For proposed time parameters a,w, an honest notation is therefore

 beta_gate(a,w;family)=min_Q G_Q(kappa(a,w;family),
                    gamma(a,w), actual moment exponents), together with G_R.

There is no verified numerical function kappa(a,w;family) arising from a complete changed-time good-family proof in this packet. If all the original family/count/moment inputs remain the same, beta_gate(a,w)=64 identically, conditional on the new-time transfer. To obtain a larger gate one must actually prove an improved count or moment/normalization interface and all its good-side consequences. Improved scalar saddle feasibility may create room for such a redesign; it is not itself that redesign.

## 5. Exact boundaries

The independent untilted-saddle result replaces selected scalar consumers by weighted Fourier/Sobolev, Mellin and fixed-gap tail estimates. It says nothing by itself about the exceptional count, the literal J2 length, a genuine N moment or the signed main term. In [note 23](23_averaged_scalar_saddle.md), the local conditions b>=9 and 2b-a>=9 use b as WIDTH exponent. In this note those same conditions are w>=9 and 2w-a>=9; w is distinct from beta, the raw MOMENT exponent.

The accepted new-family review also corrects the geometric error threshold to (1/4)L^-9; it is not L^(-9/4). No optimization here uses the incorrect reading. No changed-time family, source theorem, Lean certificate, actual middle-energy gain or final strict gap is established.

## 6. Sources and verification

The original primary is [Yitang Zhang, Discrete mean estimates and the Landau–Siegel zero, arXiv:2211.02515v1](https://arxiv.org/pdf/2211.02515v1). This note derives its conditional algebra from the exact accepted source interfaces identified by hashes in [SOURCE_PINS.json](SOURCE_PINS.json); it does not redistribute the primary paper or raw source reviews. The [finite diagnostic](diagnostics/symbolic_exceptional_gate/independent_checks.py) is a portable extraction of the uniquely reviewed exact-rational computation and checks the general Hölder identity and numerical substitutions. It is not a proof of the genuine numerator moment or of the conditional analytic transfer premises.

With unchanged family/count/moment inputs the raw moment gate remains 64, even if the untilted saddle permits smaller local time parameters. The separate integrated-observable gate 662 cannot be substituted for raw beta. The conditional 473/6 figure belongs to the explicitly changed exceptional mask and requires its complete new-family good-side and contour transfer. No numerical changed-time count, good family, numerator moment, actual middle-energy gain, signed-main-term theorem, Lean certificate or final strict gap is established.
