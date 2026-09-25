/* ym_stopping_scale_mc.c : 4D lattice gauge theory Monte Carlo, Wilson action, gauge group SU(2) or U(1).
 *
 * One sweep = one heat-bath pass (Kennedy-Pendleton for SU(2), von Mises for U(1)) followed by
 * NOR overrelaxation passes over every link. After thermalization, each sweep records
 *   - the average plaquette energy  <1 - Re tr U_p / N>,
 *   - the energy of every block of 2^4 sites (sum over its sites x and planes mu<nu of
 *     1 - Re tr U_p(x) / N),
 *   - for every axis a used as time, the time-slice sums over spatial-plane plaquette energies.
 *
 * build: cc -O3 -o ym_stopping_scale_mc ym_stopping_scale_mc.c -lm
 * usage: ym_stopping_scale_mc su2|u1 L beta ntherm nmeas nor seed outfile [hot]
 * output (binary): int32 L, int32 group (2 = SU(2), 1 = U(1)), double beta, int32 nmeas,
 *   then per measurement: double plaq, double E[(L/2)^4], double O[4][L],
 *   and for U(1) also double Ph[24][L][2] (the transverse-photon operators, see below)
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int L, V, isu2;
static double beta;
static int *up, *dn;      /* neighbour tables, [V*4] */
static double *U;         /* SU(2): quaternions [V*4*4]; U(1): angles [V*4] */

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
static inline quat getq(int i, int mu) { double *p = U + 16 * i + 4 * mu; quat q = {p[0], p[1], p[2], p[3]}; return q; }
static inline void setq(int i, int mu, quat q) {
  double n = 1.0 / sqrt(q.a0 * q.a0 + q.a1 * q.a1 + q.a2 * q.a2 + q.a3 * q.a3);
  double *p = U + 16 * i + 4 * mu; p[0] = q.a0 * n; p[1] = q.a1 * n; p[2] = q.a2 * n; p[3] = q.a3 * n;
}

static void build_neighbours(void) {
  up = malloc(sizeof(int) * V * 4); dn = malloc(sizeof(int) * V * 4);
  for (int i = 0; i < V; i++) {
    int x[4], r = i;
    for (int m = 0; m < 4; m++) { x[m] = r % L; r /= L; }
    for (int m = 0; m < 4; m++) {
      int y[4];
      memcpy(y, x, sizeof y); y[m] = (x[m] + 1) % L;
      up[4 * i + m] = y[0] + L * (y[1] + L * (y[2] + L * y[3]));
      memcpy(y, x, sizeof y); y[m] = (x[m] + L - 1) % L;
      dn[4 * i + m] = y[0] + L * (y[1] + L * (y[2] + L * y[3]));
    }
  }
}

/* ---- SU(2) ---- */
static quat staple_su2(int i, int mu) {
  quat s = {0, 0, 0, 0};
  int ipm = up[4 * i + mu];
  for (int nu = 0; nu < 4; nu++) {
    if (nu == mu) continue;
    int ipn = up[4 * i + nu], imn = dn[4 * i + nu], ipmmn = dn[4 * ipm + nu];
    quat a = qmul(qmul(getq(ipm, nu), qconj(getq(ipn, mu))), qconj(getq(i, nu)));
    quat b = qmul(qmul(qconj(getq(ipmmn, nu)), qconj(getq(imn, mu))), getq(imn, nu));
    s.a0 += a.a0 + b.a0; s.a1 += a.a1 + b.a1; s.a2 += a.a2 + b.a2; s.a3 += a.a3 + b.a3;
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
  for (;;) { /* Creutz */
    double y = exp(-2 * alpha) + urand() * (1 - exp(-2 * alpha));
    double x0 = 1 + log(y) / alpha;
    if (urand() <= sqrt(fmax(0.0, 1 - x0 * x0))) return x0;
  }
}
static void heatbath_su2(int i, int mu) {
  quat s = staple_su2(i, mu);
  double k = sqrt(s.a0 * s.a0 + s.a1 * s.a1 + s.a2 * s.a2 + s.a3 * s.a3);
  quat v = {s.a0 / k, s.a1 / k, s.a2 / k, s.a3 / k};
  double x0 = sample_x0(beta * k);
  double ct = 2 * urand() - 1, ph = 2 * M_PI * urand(), r = sqrt(fmax(0.0, 1 - x0 * x0));
  double st = sqrt(fmax(0.0, 1 - ct * ct));
  quat X = {x0, r * st * cos(ph), r * st * sin(ph), r * ct};
  setq(i, mu, qmul(X, qconj(v)));   /* U = X V^dagger, weight exp(beta k (U V)_0) */
}
static void overrelax_su2(int i, int mu) {
  quat s = staple_su2(i, mu);
  double k = sqrt(s.a0 * s.a0 + s.a1 * s.a1 + s.a2 * s.a2 + s.a3 * s.a3);
  quat vd = {s.a0 / k, -s.a1 / k, -s.a2 / k, -s.a3 / k};
  setq(i, mu, qmul(qmul(vd, qconj(getq(i, mu))), vd));   /* U -> V^+ U^+ V^+ */
}
static double plaq_su2(int i, int mu, int nu) {
  quat p = qmul(qmul(getq(i, mu), getq(up[4 * i + mu], nu)),
                qmul(qconj(getq(up[4 * i + nu], mu)), qconj(getq(i, nu))));
  return 1 - p.a0;
}

/* ---- U(1) ---- */
static void staple_u1(int i, int mu, double *re, double *im) {
  double sr = 0, si = 0;
  int ipm = up[4 * i + mu];
  for (int nu = 0; nu < 4; nu++) {
    if (nu == mu) continue;
    int ipn = up[4 * i + nu], imn = dn[4 * i + nu], ipmmn = dn[4 * ipm + nu];
    double a = U[4 * ipm + nu] - U[4 * ipn + mu] - U[4 * i + nu];
    double b = -U[4 * ipmmn + nu] - U[4 * imn + mu] + U[4 * imn + nu];
    sr += cos(a) + cos(b); si += sin(a) + sin(b);
  }
  *re = sr; *im = si;
}
static double gauss(void) { return sqrt(-2 * log(urand())) * cos(2 * M_PI * urand()); }
static double vonmises(double kappa) {   /* density ~ exp(kappa cos t) on (-pi, pi]; numpy's method */
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
  U[4 * i + mu] = vonmises(beta * k) - arg;   /* weight exp(beta k cos(theta + arg)) */
}
static void overrelax_u1(int i, int mu) {
  double re, im; staple_u1(i, mu, &re, &im);
  U[4 * i + mu] = -2 * atan2(im, re) - U[4 * i + mu];
}
static double plaq_u1(int i, int mu, int nu) {
  return 1 - cos(U[4 * i + mu] + U[4 * up[4 * i + mu] + nu] - U[4 * up[4 * i + nu] + mu] - U[4 * i + nu]);
}

int main(int argc, char **argv) {
  if (argc < 9) { fprintf(stderr, "usage: ym_stopping_scale_mc su2|u1 L beta ntherm nmeas nor seed outfile [hot]\n"); return 1; }
  isu2 = strcmp(argv[1], "su2") == 0;
  L = atoi(argv[2]); beta = atof(argv[3]);
  int ntherm = atoi(argv[4]), nmeas = atoi(argv[5]), nor = atoi(argv[6]);
  seed_rng(strtoull(argv[7], 0, 10));
  int hot = argc > 9 && strcmp(argv[9], "hot") == 0;
  if (L % 2) { fprintf(stderr, "L must be even\n"); return 1; }
  V = L * L * L * L;
  build_neighbours();
  U = calloc((size_t)V * (isu2 ? 16 : 4), sizeof(double));
  for (int i = 0; i < V; i++) for (int mu = 0; mu < 4; mu++) {
    if (isu2) {
      quat q = {1, 0, 0, 0};
      if (hot) { q.a0 = gauss(); q.a1 = gauss(); q.a2 = gauss(); q.a3 = gauss(); }
      setq(i, mu, q);
    } else U[4 * i + mu] = hot ? M_PI * (2 * urand() - 1) : 0.0;
  }
  int Lb = L / 2, NB = Lb * Lb * Lb * Lb;
  FILE *out = fopen(argv[8], "wb");
  int32_t hdr[2] = {L, isu2 ? 2 : 1}; fwrite(hdr, 4, 2, out); fwrite(&beta, 8, 1, out);
  int32_t nm = nmeas; fwrite(&nm, 4, 1, out);
  double *E = malloc(sizeof(double) * NB), *O = malloc(sizeof(double) * 4 * L);
  double *Ph = malloc(sizeof(double) * 48 * L);
  int combo_index[4][4][4], nc = 0;
  for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = 0; c < 4; c++)
    combo_index[a][b][c] = (a != b && b != c && a != c) ? nc++ : -1;
  for (int sweep = 0; sweep < ntherm + nmeas; sweep++) {
    for (int i = 0; i < V; i++) for (int mu = 0; mu < 4; mu++) { if (isu2) heatbath_su2(i, mu); else heatbath_u1(i, mu); }
    for (int o = 0; o < nor; o++)
      for (int i = 0; i < V; i++) for (int mu = 0; mu < 4; mu++) { if (isu2) overrelax_su2(i, mu); else overrelax_u1(i, mu); }
    if (sweep < ntherm) continue;
    memset(E, 0, sizeof(double) * NB); memset(O, 0, sizeof(double) * 4 * L);
    double ptot = 0;
    for (int i = 0; i < V; i++) {
      int x[4], r = i;
      for (int m = 0; m < 4; m++) { x[m] = r % L; r /= L; }
      int b = x[0] / 2 + Lb * (x[1] / 2 + Lb * (x[2] / 2 + Lb * (x[3] / 2)));
      for (int mu = 0; mu < 4; mu++) for (int nu = mu + 1; nu < 4; nu++) {
        double p = isu2 ? plaq_su2(i, mu, nu) : plaq_u1(i, mu, nu);
        ptot += p; E[b] += p;
        for (int a = 0; a < 4; a++) if (a != mu && a != nu) O[a * L + x[a]] += p;
      }
    }
    double plaq = ptot / (6.0 * V);
    fwrite(&plaq, 8, 1, out); fwrite(E, 8, NB, out); fwrite(O, 8, 4 * L, out);
    if (!isu2) {
      /* transverse photon: for time axis a, momentum axis b, polarisation c (a, b, c distinct),
         Ph[a,b,c](t) = sum over x with x_a = t of exp(2 pi i x_b / L) sin theta_bc(x) */
      memset(Ph, 0, sizeof(double) * 48 * L);
      for (int i = 0; i < V; i++) {
        int x[4], r = i;
        for (int m = 0; m < 4; m++) { x[m] = r % L; r /= L; }
        for (int bb = 0; bb < 4; bb++) for (int cc = 0; cc < 4; cc++) {
          if (bb == cc) continue;
          double s = sin(U[4 * i + bb] + U[4 * up[4 * i + bb] + cc] - U[4 * up[4 * i + cc] + bb] - U[4 * i + cc]);
          double ph = 2 * M_PI * x[bb] / L, re = s * cos(ph), im = s * sin(ph);
          for (int aa = 0; aa < 4; aa++) {
            if (aa == bb || aa == cc) continue;
            int combo = combo_index[aa][bb][cc];
            Ph[(combo * L + x[aa]) * 2] += re; Ph[(combo * L + x[aa]) * 2 + 1] += im;
          }
        }
      }
      fwrite(Ph, 8, 48 * L, out);
    }
    if ((sweep - ntherm) % 500 == 0) { fprintf(stderr, "meas %d plaq %.8f\n", sweep - ntherm, plaq); fflush(out); }
  }
  fclose(out);
  return 0;
}
