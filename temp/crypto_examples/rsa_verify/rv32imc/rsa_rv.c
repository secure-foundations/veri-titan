/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/main/common/rsa.c
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

/** Example Key (Modulus, RR, d0inv)
 * Public exponent is 65537
 * Private key is D = 0x6041730707bffad6947efef72cdaa80f6f3e7cb351f2434984bd1a5585ff1006f5d82e3e5a41dee37748ae0c48e91ae93280b58b2fc545335dedf7241d222a045232c1928e20154bc41587cba852eef02aac03ffe25a3638d08adbd2df239b2cd7db29e34097243f19b912be176965e51809b28f51c14c15f6f8cc01a1317052d21ff67343414a06b081276184e66f622d060e8bf987ff5bd36a6e38cc6dd5cb5cdb05a461d485c829c4d1b5352e82b36814f4f4debb08e7fab769ff7e40bb19514af9168c9b773570c58f2c3e177edfe43d4e29ae72329a25d7da234ce73407d2619e5072dffbec1d9601446417d968de1e8772ce4b46fd5224cc0a6ddc889aedec8247de9a6b93f166df6981c487dc111b4eb0ec7bc15782db65570158da4523eab41c7455bd70c72a52e015a7cba482581bed16fef89213158c94f15592482069a742973b55372ced7d20dc9312980ce4696fa4d5715098c927fc12ab013af8df4b83869ef22b53c176f4a83b89cab93ce7f6e619ae0c59d7e511bebf06e3
 */

uint32_t n[RSANUMWORDS] = {
  0x6a6a75e1,
  0xa018ddc5,
  0x687bb168,
  0x8e8205a5,
  0x7dbfffa7,
  0xc8722ac5,
  0xf84d21cf,
  0xe1312531,
  0x0ce3f8a3,
  0xa825f988,
  0x57f51964,
  0xb27e206a,
  0x8e1dd008,
  0x1c4fb8d7,
  0x824fb142,
  0x1c8be7b3,
  0x7b9d6366,
  0xc56ad0f2,
  0xef762d5b,
  0x4b1431e3,
  0x8ae28eb9,
  0xd41db7aa,
  0x43cccdf7,
  0x91b74a84,
  0x80183850,
  0x30e74d0d,
  0xb62ed015,
  0x235574d2,
  0x8c28f251,
  0x4f40def2,
  0x24e2efdb,
  0x9ebd1ff2,
  0xfa7b49ee,
  0x2819a938,
  0x6e66b8c8,
  0x24e41546,
  0x4d783a7c,
  0xd2947d3d,
  0x1ab269e9,
  0xfad39f16,
  0xaab78f7b,
  0x49d8b510,
  0x35bf0dfb,
  0xeb274754,
  0x069eccc9,
  0xc13c437e,
  0xe3bc0f60,
  0xc9e0e12f,
  0xc253ac43,
  0x89c240e0,
  0xc4aba4e5,
  0xedf34bc0,
  0x5402c462,
  0x4021b0bd,
  0x996b6241,
  0xc3d9945f,
  0xa137ac60,
  0xf0250bf5,
  0xc8c7100f,
  0xb70d6b88,
  0x78916a8c,
  0x33370e5d,
  0x3970dcb9,
  0xaf4c58b4,
  0x5f78cb0d,
  0xb02d90b7,
  0xeb6c3d05,
  0x04afc71a,
  0x45185f0f,
  0x987caa5b,
  0x33976249,
  0x565afdbc,
  0x80a85056,
  0x59e07655,
  0x9a29e77d,
  0x7a8dfb7f,
  0x782e0204,
  0x4d6713ff,
  0x131000ea,
  0xe18e1206,
  0x21f57f30,
  0xf24f038b,
  0x59cf874d,
  0x24c50525,
  0xb52f170d,
  0x46c9adde,
  0x90e82c73,
  0x1344ceaf,
  0x663209f2,
  0x24bd4fbf,
  0x5e4ed04d,
  0x0fce770a,
  0x81f78793,
  0xa792e13e,
  0xa6c7bf58,
  0xe1df9be8};

uint32_t rr[RSANUMWORDS] = {
  0xa3eb77fa,
  0x9db9a2ac,
  0x2c19d4ae,
  0xfb5be1e7,
  0xdd38f5fb,
  0xd0f4fdda,
  0xeb165cd3,
  0x546a7cfe,
  0xcd410c5c,
  0x73f5cf6b,
  0x1185bcae,
  0xda2e2103,
  0xbab5ae26,
  0x76e77aba,
  0xf49dd5f7,
  0x32318a29,
  0x689a85bc,
  0x8aa862a9,
  0x538c240e,
  0xb61eab77,
  0x9ccd73f2,
  0x6563c81a,
  0x6c65ac0e,
  0x90b209bf,
  0xe642e25e,
  0x7e351549,
  0x879a1830,
  0xc75cbb02,
  0xe0112362,
  0xebc2405f,
  0x01dc7990,
  0x3d3d07f3,
  0xc5b9a5be,
  0x98d8cc33,
  0xdd65e108,
  0xce301343,
  0x0dbdc0cb,
  0xc204b9ca,
  0xeabe1810,
  0x9849163a,
  0x234c8ff7,
  0x9bc14e3b,
  0x4b4c2226,
  0x079883be,
  0xba59c5f5,
  0xd9c77317,
  0x1ce689f5,
  0x05f49af5,
  0x7a83d42a,
  0xc509b5ca,
  0x0811a95f,
  0x093520a2,
  0x73649941,
  0xd9691ef5,
  0x6878ec0d,
  0x4043add6,
  0x7516d8b7,
  0x5c7070ff,
  0x4ce52e1d,
  0xf209e123,
  0xfe4319c4,
  0x9774620a,
  0x7a58d047,
  0x524b09b7,
  0x96cbf044,
  0x2a9044a2,
  0x514995dc,
  0xe4b83ed6,
  0xd21be300,
  0x2966d4f8,
  0xd9ee19c4,
  0xb60788f6,
  0xf8d074ab,
  0xa7e13295,
  0x93718edc,
  0xba9fc096,
  0x0ad2fbbc,
  0x9fe0c363,
  0x472a10b4,
  0xda9c946b,
  0x37276997,
  0x04e452fc,
  0xd19233b5,
  0xa277ef0e,
  0x49619ddd,
  0xb5822d56,
  0x6ca4d02f,
  0x7d0c0fc3,
  0xa29196e2,
  0xb6988a4f,
  0x785b7552,
  0xeaee3c24,
  0x87993424,
  0xfcb49693,
  0x21e64d84,
  0x9e2dcea8};

uint32_t d0inv = 0xf09b71df;

/* Example signature created with example key above, no padding */
uint32_t sig[RSANUMWORDS] = {
  0xceb7e983,
  0xe693b200,
  0xf9153989,
  0xcf899599,
  0x1ec09fae,
  0xf2f88007,
  0x2a24eed5,
  0x9c5b7c4e,
  0x21a153b2,
  0xaf7583ae,
  0x04fdd694,
  0x7550094b,
  0xb2a69ac4,
  0xe49d8022,
  0x7ed6f162,
  0x14bb3a1b,
  0xbb29d8dd,
  0x5c5815c2,
  0x7a80d848,
  0xb122f449,
  0x59dca808,
  0xbc1443e2,
  0xe304ff93,
  0xcc97ee4b,
  0x42ef6b57,
  0x1436839f,
  0xae860b45,
  0x6a843a17,
  0x2381fb91,
  0x09fd0635,
  0xa431aac3,
  0xd7220269,
  0xdf3e2697,
  0x35e2915e,
  0xedba6956,
  0x1d387448,
  0x930006df,
  0x961e5f00,
  0xf2a7e960,
  0x884e4add,
  0x7dfe76b1,
  0x4079aa79,
  0x1f3a378d,
  0x96c20697,
  0x268aea57,
  0x2c8569a4,
  0x0474f512,
  0x2388555c,
  0x58679953,
  0xe73da3a0,
  0x43431b9a,
  0x699f04d3,
  0xfc0be066,
  0xcce606f2,
  0xd94cdfa0,
  0x6c1ddca3,
  0xe96c11f6,
  0xfc635db4,
  0x3bdb4f69,
  0xa621c3e7,
  0x9f292111,
  0xb86e1e6b,
  0xb74f923b,
  0x592967a0,
  0xc412097f,
  0x8c1c8ca7,
  0x494fcdb6,
  0x87c5fe0f,
  0x50c01aee,
  0x8a26368e,
  0xeaf12232,
  0x7dade4d8,
  0x39eb2ac6,
  0x744f8aaa,
  0xf34908ca,
  0x1e0c656c,
  0xe96d4e29,
  0x8575d194,
  0xe439bd31,
  0xa74a77e3,
  0x0f465b88,
  0xf4e21152,
  0x80400ad8,
  0xe58501ec,
  0xa29d7536,
  0x55c19326,
  0x9ebbc63e,
  0x20c75aee,
  0xef6783d7,
  0x59ffdba5,
  0x879b937b,
  0x43a5c74c,
  0x82b8f825,
  0xfdf04b3a,
  0x8fc62fbe,
  0x114e6da5};


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
static void sub_mod(const uint32_t *n, uint32_t *a)
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
static int ge_mod(const uint32_t *n, const uint32_t *a)
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
static void mont_mul_add(const uint32_t d0inv, const uint32_t *n,
       uint32_t *c,
       const uint32_t a,
       const uint32_t *b)
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
    sub_mod(n, c);
}

/**
 * Montgomery c[] = a[] * b[] / R % mod
 */
static void mont_mul(const uint32_t d0inv, const uint32_t *n,
         uint32_t *c,
         const uint32_t *a,
         const uint32_t *b)
{
  uint32_t i;
  for (i = 0; i < RSANUMWORDS; ++i)
    c[i] = 0;
  for (i = 0; i < RSANUMWORDS; ++i)
    mont_mul_add(d0inv, n, c, a[i], b);
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
static void mod_pow(const uint32_t * rr, const uint32_t d0inv, const uint32_t *n,
         uint32_t *in,
         uint32_t *out,
         uint32_t *workbuf32)
{
  uint32_t *a_r = workbuf32;
  uint32_t *aa_r = a_r + RSANUMWORDS;
  int i;

  /* Exponent 65537 */
  mont_mul(d0inv, n, a_r, in, rr);  /* a_r = a * RR / R mod M */
  for (i = 0; i < 16; i += 2) {
    mont_mul(d0inv, n, aa_r, a_r, a_r); /* aa_r = a_r * a_r / R mod M */
    mont_mul(d0inv, n, a_r, aa_r, aa_r);/* a_r = aa_r * aa_r / R mod M */
  }
  mont_mul(d0inv, n, out, a_r, in);  /* aaa = a_r * a / R mod M */

  /* Make sure aaa < mod; aaa is at most 1x mod too large. */
  if (ge_mod(n, out))
    sub_mod(n, out);
}


int main(void) {
  uint32_t workbuf[2*RSANUMWORDS];
  uint32_t out[96];

  mod_pow(rr,d0inv,n,sig,out,workbuf);

  for (int i=0; i<(RSANUMWORDS); i++) {
    //printf("Limb %d: 0x%08lx\n", i, out[i]);
  }
}

