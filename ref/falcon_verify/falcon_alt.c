#include <stddef.h>
#include <stdint.h>

#define PQCLEAN_FALCON512_CLEAN_CRYPTO_SECRETKEYBYTES   1281
#define PQCLEAN_FALCON512_CLEAN_CRYPTO_PUBLICKEYBYTES   897
#define PQCLEAN_FALCON512_CLEAN_CRYPTO_BYTES            690

extern uint16_t scaling_factors[];
extern uint16_t rev_mixed_powers_mont_table[];
extern uint16_t rev_omega_inv_powers_mont_table[];
#define BITREV512_NPAIRS 240
extern uint16_t bit_rev_table_512[BITREV512_NPAIRS][2];

/*
 * Required sizes of the temporary buffer (in bytes).
 *
 * This size is 28*2^9 bytes, except for degrees 2 and 4 (9 = 1
 * or 2) where it is slightly greater.
 */
/* ===================================================================== */
/*
 * Constants for NTT.
 *
 *   n = 2^9  (2 <= n <= 1024)
 *   phi = X^n + 1
 *   q = 12289
 *   q0i = -1/q mod 2^16
 *   R = 2^16 mod q
 *   R2 = 2^32 mod q
 */

#define Q     12289
#define Q0I   12287
#define R      4091
#define R2    10952

static void ntt512_bitrev_shuffle(uint16_t *a) {
  uint16_t i, j, k;
  uint16_t x;

  for (i=0; i< BITREV512_NPAIRS; i++) {
    j = bit_rev_table_512[i][0];
    k = bit_rev_table_512[i][1];
    x = a[j]; a[j] = a[k]; a[k] = x;
  }
}

/*
 * Addition modulo q. Operands must be in the 0..q-1 range.
 */
uint32_t
mq_add(uint32_t x, uint32_t y) {
    /*
     * We compute x + y - q. If the result is negative, then the
     * high bit will be set, and 'd >> 31' will be equal to 1;
     * thus '-(d >> 31)' will be an all-one pattern. Otherwise,
     * it will be an all-zero pattern. In other words, this
     * implements a conditional addition of q.
     */
    uint32_t d;

    d = x + y - Q;
    d += Q & -(d >> 31);
    return d;
}


/*
 * Subtraction modulo q. Operands must be in the 0..q-1 range.
 */
uint32_t
mq_sub(uint32_t x, uint32_t y) {
    /*
     * As in mq_add(), we use a conditional addition to ensure the
     * result is in the 0..q-1 range.
     */
    uint32_t d;

    d = x - y;
    d += Q & -(d >> 31);
    return d;
}


/*
 * Division by 2 modulo q. Operand must be in the 0..q-1 range.
 */
uint32_t
mq_rshift1(uint32_t x) {
    x += Q & -(x & 1);
    return (x >> 1);
}


/*
 * Subtract polynomial g from polynomial f.
 */
static void
mq_poly_sub(uint16_t *f, const uint16_t *g) {
    size_t u, n;

    n = (size_t)1 << 9;
    for (u = 0; u < n; u ++) {
        f[u] = (uint16_t)mq_sub(f[u], g[u]);
    }
}


/*
 * Montgomery multiplication modulo q. If we set R = 2^16 mod q, then
 * this function computes: x * y / R mod q
 * Operands must be in the 0..q-1 range.
 */
uint32_t
mq_montymul(uint32_t x, uint32_t y) {
    uint32_t z, w;

    /*
     * We compute x*y + k*q with a value of k chosen so that the 16
     * low bits of the result are 0. We can then shift the value.
     * After the shift, result may still be larger than q, but it
     * will be lower than 2*q, so a conditional subtraction works.
     */

    z = x * y;
    w = ((z * Q0I) & 0xFFFF) * Q;

    /*
     * When adding z and w, the result will have its low 16 bits
     * equal to 0. Since x, y and z are lower than q, the sum will
     * be no more than (2^15 - 1) * q + (q - 1)^2, which will
     * fit on 29 bits.
     */
    z = (z + w) >> 16;

    /*
     * After the shift, analysis shows that the value will be less
     * than 2q. We do a subtraction then conditional subtraction to
     * ensure the result is in the expected range.
     */
    z -= Q;
    z += Q & -(z >> 31);
    return z;
}


/*
 * Multiply two polynomials together (NTT representation, and using
 * a Montgomery multiplication). Result f*g is written over f.
 */
static void
mq_poly_montymul_ntt(uint16_t *f, const uint16_t *g) {
    size_t u, n;

    n = (size_t)1 << 9;
    for (u = 0; u < n; u ++) {
        f[u] = (uint16_t)mq_montymul(f[u], g[u]);
    }
}

static void
mq_poly_mul_ntt(uint16_t *f, const uint16_t *g) {
    size_t u, n;

    n = (size_t)1 << 9;
    for (u = 0; u < n; u ++) {
        uint16_t temp = mq_montymul(f[u], R2);
        f[u] = (uint16_t)mq_montymul(temp, g[u]);
    }
}

/*
 * Tell whether a given vector (2N coordinates, in two halves) is
 * acceptable as a signature. This compares the appropriate norm of the
 * vector with the acceptance bound. Returned value is 1 on success
 * (vector is short enough to be acceptable), 0 otherwise.
 */
static int
PQCLEAN_FALCON512_CLEAN_is_short(
    const int16_t *s1, const int16_t *s2) {
    /*
     * We use the l2-norm. Code below uses only 32-bit operations to
     * compute the square of the norm with saturation to 2^32-1 if
     * the value exceeds 2^31-1.
     */
    size_t n, u;
    uint32_t s, ng;

    n = (size_t)1 << 9;
    s = 0;
    ng = 0;
    for (u = 0; u < n; u ++) {
        int32_t z;

        z = s1[u];
        s += (uint32_t)(z * z);
        ng |= s;
        z = s2[u];
        s += (uint32_t)(z * z);
        ng |= s;
    }
    s |= -(ng >> 31);

    /*
     * Acceptance bound on the l2-norm is:
     *   1.2*1.55*sqrt(q)*sqrt(2*N)
     * Value 7085 is floor((1.2^2)*(1.55^2)*2*1024).
     */
    return s < (((uint32_t)7085 * (uint32_t)12289) >> (10 - 9));
}


void forward_ntt(uint16_t *a) {
  uint32_t j, s, t, u, d;
  uint32_t x, w;
  
  d = 512;
  for (t=1; t<512; t <<= 1) {
    d >>= 1;
    for (j=0, u=0; j<t; j++, u+=2*d) { // u = j * 2d
      w = rev_mixed_powers_mont_table[t + j]; // psi_t * w_t^bitrev(j)
      for (s=u; s<u+d; s++) {
        x = mq_montymul(a[s + d], w);
        a[s + d] = mq_sub(a[s], x);
        a[s] = mq_add(a[s], x);
      }
    }
  }
}

void inverse_ntt(uint16_t *a) {
  uint32_t j, s, t, u, d;
  uint32_t x, w;
  
  d = 512;
  for (t=1; t<512; t <<= 1) {
    d >>= 1;
    for (j=0, u=0; j<t; j++, u+=2*d) { // u = j * 2d
      w = rev_omega_inv_powers_mont_table[t + j]; // psi_t * w_t^bitrev(j)
      for (s=u; s<u+d; s++) {
        x = mq_montymul(a[s + d], w);
        a[s + d] = mq_sub(a[s], x);
        a[s] = mq_add(a[s], x);
      }
    }
  }
}



/* Internal signature verification code:
 *   c0[]      contains the hashed nonce+message
 *   s2[]      is the decoded signature
 *   h[]       contains the public key, in NTT + Montgomery format
 *   9      is the degree log
 *   tmp[]     temporary, must have at least 2*2^9 bytes
 * Returned value is 1 on success, 0 on error.
 *
 * tmp[] must have 16-bit alignment.
 */

int rv_falcon(const uint16_t *c0, const int16_t *s2,
                                   uint16_t *h, uint16_t *tmp) {
    size_t u, n;
    uint16_t *tt;

    n = (size_t)1 << 9;
    tt = tmp;
    
    /*
     * Reduce s2 elements modulo q ([0..q-1] range).
     */
    for (u = 0; u < n; u ++) {
        uint32_t w;

        w = (uint32_t)s2[u];
        w += Q & -(w >> 31);
        tt[u] = (uint16_t)w;
    }

    /*
     * Compute -s1 = s2*h - c0 mod phi mod q (in tt[]).
     */
    // print_uint16_array(stdout, h, 512);
    forward_ntt(h);
    forward_ntt(tt);
    mq_poly_mul_ntt(tt, h);

    // we need to shuffle the input
    ntt512_bitrev_shuffle(tt);
  
    inverse_ntt(tt);

    // shuffle the output
    ntt512_bitrev_shuffle(tt);
    // then scale the ouput
    mq_poly_montymul_ntt(tt, scaling_factors);

    // this should end up doing poly multiplication 
    // print_uint16_array(stdout, tt, 512);

    mq_poly_sub(tt, c0);

    /*
     * Normalize -s1 elements into the [-q/2..q/2] range.
     */
    for (u = 0; u < n; u ++) {
        int32_t w;

        w = (int32_t)tt[u];
        w -= (int32_t)(Q & -(((Q >> 1) - (uint32_t)w) >> 31));
        ((int16_t *)tt)[u] = (int16_t)w;
    }
    // print_uint16_array(tt);

    /*
     * Signature is valid if and only if the aggregate (-s1,s2) vector
     * is short enough.
     */
    return PQCLEAN_FALCON512_CLEAN_is_short((int16_t *)tt, s2);
}
