/* ym_vortex_free_energy.c : the twist free energy of lattice gauge theory, Wilson action, gauge
 * group SU(2) or U(1), periodic lattice L^d with d = 4 or 5.
 *
 * The stack is the set of plaquettes (x; 0, 1) with x_0 = x_1 = 0, one in every (0,1)-plane, L^(d-2)
 * of them.  With every other plaquette at coupling beta and the stack at coupling b,
 *   Z(b) = int exp( beta sum_{p not in stack} Re tr U_p / N  +  b sum_{p in stack} Re tr U_p / N ).
 * Z(-beta) is the partition function with a twist through every (0,1)-plane: the centre element -1
 * for SU(2), a flux pi for U(1).  The twist free energy is
 *   F = -log Z(-beta) / Z(beta) = int_{-beta}^{beta} <E_stack>_b db,   E_stack = sum_{p in stack} Re tr U_p / N.
 * One run of this program measures <E_stack>_b at one value of b; ym_vortex_driver.py integrates.
 *
 * One sweep = one heat-bath pass (Kennedy-Pendleton/Creutz for SU(2), von Mises for U(1)) followed
 * by NOR overrelaxation passes over every link.
 *
 * build: cc -O3 -o ym_vortex_free_energy ym_vortex_free_energy.c -lm
 * usage: ym_vortex_free_energy su2|u1 d L beta b ntherm nmeas nor seed [hot]
 * output (one line): b  mean(E_stack)  binned standard error  mean plaquette Re tr U_p / N  nbins
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int D, L, V, isu2;
static double beta, bstack;
static int *up, *dn;      /* neighbour tables, [V*D] */
static char *onstack;     /* onstack[i]: site i has x_0 = x_1 = 0 */
static double *U;         /* SU(2): quaternions [V*D*4]; U(1): angles [V*D] */

/* ---- xoshiro256** ---- */
static uint64_t rs[4];
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t rnext(void) {
  uint64_t r = rotl(rs[1] * 5, 7) * 9, t = rs[1] << 17;
  rs[2] ^= rs[0]; rs[3] ^= rs[1]; rs[1] ^= rs[2]; rs[0] ^= rs[3]; rs[2] ^= t; rs[3] = rotl(rs[3], 45);
  return r;
}
static inline double urand(void) { return ((double)(rnext() >> 11) + 0.5) * 0x1.0p-53; } /* (0,1) */
static void seed_rng(uint64_t seed) {
  for (int i = 0; i < 4; i++) {
    uint64_t z = (seed += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    rs[i] = z ^ (z >> 31);
  }
}

/* ---- quaternions: q = a0 + i (a1 s1 + a2 s2 + a3 s3), s the Pauli matrices ---- */
typedef struct { double a0, a1, a2, a3; } quat;
static inline quat qmul(quat a, quat b) {
  quat c;
  c.a0 = a.a0 * b.a0 - a.a1 * b.a1 - a.a2 * b.a2 - a.a3 * b.a3;
  c.a1 = a.a0 * b.a1 + b.a0 * a.a1 - (a.a2 * b.a3 - a.a3 * b.a2);
  c.a2 = a.a0 * b.a2 + b.a0 * a.a2 - (a.a3 * b.a1 - a.a1 * b.a3);
  c.a3 = a.a0 * b.a3 + b.a0 * a.a3 - (a.a1 * b.a2 - a.a2 * b.a1);
  return c;
}
static inline quat qconj(quat a) { quat c = {a.a0, -a.a1, -a.a2, -a.a3}; return c; }
static inline quat getq(int i, int mu) { double *p = U + 4 * (D * i + mu); quat q = {p[0], p[1], p[2], p[3]}; return q; }
static inline void setq(int i, int mu, quat q) {
  double n = 1.0 / sqrt(q.a0 * q.a0 + q.a1 * q.a1 + q.a2 * q.a2 + q.a3 * q.a3);
  double *p = U + 4 * (D * i + mu); p[0] = q.a0 * n; p[1] = q.a1 * n; p[2] = q.a2 * n; p[3] = q.a3 * n;
}

static void build_neighbours(void) {
  up = malloc(sizeof(int) * V * D); dn = malloc(sizeof(int) * V * D); onstack = malloc(V);
  for (int i = 0; i < V; i++) {
    int x[5], r = i;
    for (int m = 0; m < D; m++) { x[m] = r % L; r /= L; }
    onstack[i] = x[0] == 0 && x[1] == 0;
    for (int m = 0; m < D; m++) {
      int y[5], j;
      memcpy(y, x, sizeof y); y[m] = (x[m] + 1) % L;
      j = 0; for (int n = D - 1; n >= 0; n--) j = j * L + y[n];
      up[D * i + m] = j;
      memcpy(y, x, sizeof y); y[m] = (x[m] + L - 1) % L;
      j = 0; for (int n = D - 1; n >= 0; n--) j = j * L + y[n];
      dn[D * i + m] = j;
    }
  }
}

/* coupling of the plaquette with corner i in the plane {mu, nu} */
static inline double coupling(int i, int mu, int nu) {
  return (mu + nu == 1 && onstack[i]) ? bstack : beta;
}

/* ---- SU(2) ---- */
/* the coupling-weighted staple sum S: the local weight of U_mu(i) is exp((U S)_0) */
static quat staple_su2(int i, int mu) {
  quat s = {0, 0, 0, 0};
  int ipm = up[D * i + mu];
  for (int nu = 0; nu < D; nu++) {
    if (nu == mu) continue;
    int ipn = up[D * i + nu], imn = dn[D * i + nu], ipmmn = dn[D * ipm + nu];
    double cf = coupling(i, mu, nu), cb = coupling(imn, mu, nu);
    quat a = qmul(qmul(getq(ipm, nu), qconj(getq(ipn, mu))), qconj(getq(i, nu)));
    quat b = qmul(qmul(qconj(getq(ipmmn, nu)), qconj(getq(imn, mu))), getq(imn, nu));
    s.a0 += cf * a.a0 + cb * b.a0; s.a1 += cf * a.a1 + cb * b.a1;
    s.a2 += cf * a.a2 + cb * b.a2; s.a3 += cf * a.a3 + cb * b.a3;
  }
  return s;
}
/* x0 with density proportional to sqrt(1-x0^2) exp(alpha x0) on [-1,1] */
static double sample_x0(double alpha) {
  if (alpha > 2.0) { /* Kennedy-Pendleton */
    for (;;) {
      double c = cos(2 * M_PI * urand());
      double X = -(log(urand()) + c * c * log(urand())) / alpha;
      double r = urand();
      if (r * r <= 1 - 0.5 * X) return 1 - X;
    }
  }
  if (alpha < 1e-8) {
    for (;;) { double x0 = 2 * urand() - 1; if (urand() <= sqrt(1 - x0 * x0)) return x0; }
  }
  for (;;) { /* Creutz */
    double y = exp(-2 * alpha) + urand() * (1 - exp(-2 * alpha));
    double x0 = 1 + log(y) / alpha;
    if (urand() <= sqrt(fmax(0.0, 1 - x0 * x0))) return x0;
  }
}
static void heatbath_su2(int i, int mu) {
  quat s = staple_su2(i, mu);
  double k = sqrt(s.a0 * s.a0 + s.a1 * s.a1 + s.a2 * s.a2 + s.a3 * s.a3);
  double x0, ct = 2 * urand() - 1, ph = 2 * M_PI * urand();
  if (k < 1e-12) { /* Haar */
    quat q = {sqrt(-2 * log(urand())) * cos(2 * M_PI * urand()), sqrt(-2 * log(urand())) * cos(2 * M_PI * urand()),
              sqrt(-2 * log(urand())) * cos(2 * M_PI * urand()), sqrt(-2 * log(urand())) * cos(2 * M_PI * urand())};
    setq(i, mu, q); return;
  }
  quat v = {s.a0 / k, s.a1 / k, s.a2 / k, s.a3 / k};
  x0 = sample_x0(k);
  double r = sqrt(fmax(0.0, 1 - x0 * x0)), st = sqrt(fmax(0.0, 1 - ct * ct));
  quat X = {x0, r * st * cos(ph), r * st * sin(ph), r * ct};
  setq(i, mu, qmul(X, qconj(v)));   /* U = X V^dagger, weight exp(k (U V)_0) */
}
static void overrelax_su2(int i, int mu) {
  quat s = staple_su2(i, mu);
  double k = sqrt(s.a0 * s.a0 + s.a1 * s.a1 + s.a2 * s.a2 + s.a3 * s.a3);
  if (k < 1e-12) return;
  quat vd = {s.a0 / k, -s.a1 / k, -s.a2 / k, -s.a3 / k};
  setq(i, mu, qmul(qmul(vd, qconj(getq(i, mu))), vd));   /* U -> V^+ U^+ V^+ */
}
static double retr_su2(int i, int mu, int nu) {   /* Re tr U_p / 2 */
  quat p = qmul(qmul(getq(i, mu), getq(up[D * i + mu], nu)),
                qmul(qconj(getq(up[D * i + nu], mu)), qconj(getq(i, nu))));
  return p.a0;
}

/* ---- U(1) ---- */
static void staple_u1(int i, int mu, double *re, double *im) {
  double sr = 0, si = 0;
  int ipm = up[D * i + mu];
  for (int nu = 0; nu < D; nu++) {
    if (nu == mu) continue;
    int ipn = up[D * i + nu], imn = dn[D * i + nu], ipmmn = dn[D * ipm + nu];
    double cf = coupling(i, mu, nu), cb = coupling(imn, mu, nu);
    double a = U[D * ipm + nu] - U[D * ipn + mu] - U[D * i + nu];
    double b = -U[D * ipmmn + nu] - U[D * imn + mu] + U[D * imn + nu];
    sr += cf * cos(a) + cb * cos(b); si += cf * sin(a) + cb * sin(b);
  }
  *re = sr; *im = si;
}
static double gauss(void) { return sqrt(-2 * log(urand())) * cos(2 * M_PI * urand()); }
static double vonmises(double kappa) {   /* density ~ exp(kappa cos t) on (-pi, pi] */
  double s;
  if (kappa < 1e-8) return M_PI * (2 * urand() - 1);
  if (kappa > 1e6) return fmod(gauss() / sqrt(kappa) + 3 * M_PI, 2 * M_PI) - M_PI;
  if (kappa < 1e-5) s = 1 / kappa + kappa;
  else { double r = 1 + sqrt(1 + 4 * kappa * kappa), rho = (r - sqrt(2 * r)) / (2 * kappa); s = (1 + rho * rho) / (2 * rho); }
  double W;
  for (;;) {
    double Z = cos(M_PI * urand());
    W = (1 + s * Z) / (s + Z);
    double Y = kappa * (s - W), Vv = urand();
    if ((Y * (2 - Y) - Vv >= 0) || (log(Y / Vv) + 1 - Y >= 0)) break;
  }
  double t = acos(fmax(-1.0, fmin(1.0, W)));
  return urand() < 0.5 ? -t : t;
}
static void heatbath_u1(int i, int mu) {
  double re, im; staple_u1(i, mu, &re, &im);
  double k = sqrt(re * re + im * im), arg = atan2(im, re);
  U[D * i + mu] = vonmises(k) - arg;   /* weight exp(k cos(theta + arg)) */
}
static void overrelax_u1(int i, int mu) {
  double re, im; staple_u1(i, mu, &re, &im);
  U[D * i + mu] = -2 * atan2(im, re) - U[D * i + mu];
}
static double retr_u1(int i, int mu, int nu) {   /* cos theta_p */
  return cos(U[D * i + mu] + U[D * up[D * i + mu] + nu] - U[D * up[D * i + nu] + mu] - U[D * i + nu]);
}

int main(int argc, char **argv) {
  if (argc < 10) { fprintf(stderr, "usage: ym_vortex_free_energy su2|u1 d L beta b ntherm nmeas nor seed [hot]\n"); return 1; }
  isu2 = strcmp(argv[1], "su2") == 0;
  D = atoi(argv[2]); L = atoi(argv[3]); beta = atof(argv[4]); bstack = atof(argv[5]);
  int ntherm = atoi(argv[6]), nmeas = atoi(argv[7]), nor = atoi(argv[8]);
  seed_rng(strtoull(argv[9], 0, 10));
  int hot = argc > 10 && strcmp(argv[10], "hot") == 0;
  if (D < 2 || D > 5) { fprintf(stderr, "need 2 <= d <= 5\n"); return 1; }
  V = 1; for (int m = 0; m < D; m++) V *= L;
  build_neighbours();
  U = calloc((size_t)V * D * (isu2 ? 4 : 1), sizeof(double));
  for (int i = 0; i < V; i++) for (int mu = 0; mu < D; mu++) {
    if (isu2) {
      quat q = {1, 0, 0, 0};
      if (hot) { q.a0 = gauss(); q.a1 = gauss(); q.a2 = gauss(); q.a3 = gauss(); }
      setq(i, mu, q);
    } else U[D * i + mu] = hot ? M_PI * (2 * urand() - 1) : 0.0;
  }
  const int nbins = 20;
  double *series = malloc(sizeof(double) * nmeas), psum = 0;
  for (int sweep = 0; sweep < ntherm + nmeas; sweep++) {
    for (int i = 0; i < V; i++) for (int mu = 0; mu < D; mu++) { if (isu2) heatbath_su2(i, mu); else heatbath_u1(i, mu); }
    for (int o = 0; o < nor; o++)
      for (int i = 0; i < V; i++) for (int mu = 0; mu < D; mu++) { if (isu2) overrelax_su2(i, mu); else overrelax_u1(i, mu); }
    if (sweep < ntherm) continue;
    double e = 0, p = 0;
    for (int i = 0; i < V; i++) {
      if (onstack[i]) e += isu2 ? retr_su2(i, 0, 1) : retr_u1(i, 0, 1);
      if ((sweep - ntherm) % 10 == 0)
        for (int mu = 0; mu < D; mu++) for (int nu = mu + 1; nu < D; nu++) p += isu2 ? retr_su2(i, mu, nu) : retr_u1(i, mu, nu);
    }
    series[sweep - ntherm] = e;
    if ((sweep - ntherm) % 10 == 0) psum += p / (V * D * (D - 1) / 2.0);
  }
  double mean = 0; for (int n = 0; n < nmeas; n++) mean += series[n]; mean /= nmeas;
  int bl = nmeas / nbins; double var = 0;
  for (int k = 0; k < nbins; k++) {
    double m = 0; for (int n = k * bl; n < (k + 1) * bl; n++) m += series[n]; m /= bl;
    var += (m - mean) * (m - mean);
  }
  double se = sqrt(var / (nbins * (nbins - 1.0)));
  int npl = (nmeas + 9) / 10;
  printf("%.10g %.10g %.10g %.10g %d\n", bstack, mean, se, psum / npl, nbins);
  return 0;
}
