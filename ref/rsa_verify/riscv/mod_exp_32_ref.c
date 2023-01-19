/* 
 * 
 * 
 * 
 *
 * Derived from code in
 * https://****
 */

/**
 * Self-contained single-file example demonstrating RSA signature verification.
 * Pure SW implementation to be used on RV32IMC targets.
 * Contains an example public key with corresponding RR and d0inv.
 * Contains example signature created with corresponding private key.
 * Expected message is 0x5555...55555
 */

#include <stdio.h>
#include <stdint.h>

#define RSANUMWORDS 96 // 3072 = 96*32 bit

uint64_t mul32(uint32_t a, uint32_t b) {
  return (uint64_t)a*b;
}

uint64_t mula32(uint32_t a, uint32_t b, uint32_t c) {
  return (uint64_t)a*b+c;
}

uint64_t mulaa32(uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
  return (uint64_t)a*b+c+d;
}

/**
 * a[] -= mod
 */
void sub_mod(uint32_t *a, const uint32_t *n)
{
  int64_t A = 0;
  uint32_t i;
  for (i = 0; i < RSANUMWORDS; ++i) {
    A += (uint64_t)a[i] - n[i];
    a[i] = (uint32_t)A;
    A >>= 32;
  }
}

/**
 * Return a[] >= mod
 */
int ge_mod(const uint32_t *a, const uint32_t *n)
{
  uint32_t i;
  for (i = RSANUMWORDS; i;) {
    --i;
    if (a[i] < n[i])
      return 0;
    if (a[i] > n[i])
      return 1;
  }
  return 1;  /* equal */
}

/**
 * Montgomery c[] += a * b[] / R % mod
 */
void mont_mul_add(const uint32_t d0inv,
      uint32_t *c,
      const uint32_t a,
      const uint32_t *b,
      const uint32_t *n)
{
  uint64_t A = mula32(a, b[0], c[0]);
  uint32_t d0 = (uint32_t)A * d0inv;
  uint64_t B = mula32(d0, n[0], (uint32_t)A);
  uint32_t i;
  for (i = 1; i < RSANUMWORDS; ++i) {
    A = mulaa32(a, b[i], c[i], A >> 32);
    B = mulaa32(d0, n[i], (uint32_t)A, B >> 32);
    c[i - 1] = (uint32_t)B;
  }
  A = (A >> 32) + (B >> 32);
  c[i - 1] = (uint32_t)A;
  if (A >> 32)
    sub_mod(c, n);
}

/**
 * Montgomery c[] = a[] * b[] / R % mod
 */
void mont_mul(const uint32_t d0inv,
         uint32_t *c,
         const uint32_t *a,
         const uint32_t *b,
         const uint32_t *n)
{
  uint32_t i;
  for (i = 0; i < RSANUMWORDS; ++i)
    c[i] = 0;
  for (i = 0; i < RSANUMWORDS; ++i)
    mont_mul_add(d0inv, c, a[i], b, n);
}

/**
 * In-place public exponentiation.
 * Exponent depends is fixed to 65537
 *
 * @param rr		Precomputed constant, (R*R) mod n, considered part of key
 * @param d0inv Precomputed Montgomery constant,
 *                considered part of key d0inv=-n^(-1) mod R
 * @param n     Modulus of key
 * @param in		Input signature as little-endian array
 * @param out   Output message as little-endian array
 * @param workbuf32	Work buffer; caller must verify this is
 *			2 x RSANUMWORDS elements long.
 */
void mod_pow(const uint32_t d0inv,
        uint32_t *out,
        uint32_t *workbuf32,
        const uint32_t * rr,
        const uint32_t *n,
        uint32_t *in)
{
  uint32_t *a_r = workbuf32;
  uint32_t *aa_r = a_r + RSANUMWORDS;
  int i;

  /* Exponent 65537 */
  mont_mul(d0inv, a_r, in, rr, n);  /* a_r = a * RR / R mod M */
  for (i = 0; i < 16; i += 2) {
    mont_mul(d0inv, aa_r, a_r, a_r, n); /* aa_r = a_r * a_r / R mod M */
    mont_mul(d0inv, a_r, aa_r, aa_r, n);/* a_r = aa_r * aa_r / R mod M */
  }
  mont_mul(d0inv, out, a_r, in, n);  /* aaa = a_r * a / R mod M */

  /* Make sure aaa < mod; aaa is at most 1x mod too large. */
  if (ge_mod(out, n))
    sub_mod(out, n);
}