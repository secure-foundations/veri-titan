#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>

#define PQCLEAN_FALCON512_CLEAN_CRYPTO_SECRETKEYBYTES   1281
#define PQCLEAN_FALCON512_CLEAN_CRYPTO_PUBLICKEYBYTES   897
#define PQCLEAN_FALCON512_CLEAN_CRYPTO_BYTES            690

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
#define BITREV512_NPAIRS 240

const uint16_t bitrev512[BITREV512_NPAIRS][2] = {
    {     1,   256 }, {     2,   128 }, {     3,   384 }, {     4,    64 },
    {     5,   320 }, {     6,   192 }, {     7,   448 }, {     8,    32 },
    {     9,   288 }, {    10,   160 }, {    11,   416 }, {    12,    96 },
    {    13,   352 }, {    14,   224 }, {    15,   480 }, {    17,   272 },
    {    18,   144 }, {    19,   400 }, {    20,    80 }, {    21,   336 },
    {    22,   208 }, {    23,   464 }, {    24,    48 }, {    25,   304 },
    {    26,   176 }, {    27,   432 }, {    28,   112 }, {    29,   368 },
    {    30,   240 }, {    31,   496 }, {    33,   264 }, {    34,   136 },
    {    35,   392 }, {    36,    72 }, {    37,   328 }, {    38,   200 },
    {    39,   456 }, {    41,   296 }, {    42,   168 }, {    43,   424 },
    {    44,   104 }, {    45,   360 }, {    46,   232 }, {    47,   488 },
    {    49,   280 }, {    50,   152 }, {    51,   408 }, {    52,    88 },
    {    53,   344 }, {    54,   216 }, {    55,   472 }, {    57,   312 },
    {    58,   184 }, {    59,   440 }, {    60,   120 }, {    61,   376 },
    {    62,   248 }, {    63,   504 }, {    65,   260 }, {    66,   132 },
    {    67,   388 }, {    69,   324 }, {    70,   196 }, {    71,   452 },
    {    73,   292 }, {    74,   164 }, {    75,   420 }, {    76,   100 },
    {    77,   356 }, {    78,   228 }, {    79,   484 }, {    81,   276 },
    {    82,   148 }, {    83,   404 }, {    85,   340 }, {    86,   212 },
    {    87,   468 }, {    89,   308 }, {    90,   180 }, {    91,   436 },
    {    92,   116 }, {    93,   372 }, {    94,   244 }, {    95,   500 },
    {    97,   268 }, {    98,   140 }, {    99,   396 }, {   101,   332 },
    {   102,   204 }, {   103,   460 }, {   105,   300 }, {   106,   172 },
    {   107,   428 }, {   109,   364 }, {   110,   236 }, {   111,   492 },
    {   113,   284 }, {   114,   156 }, {   115,   412 }, {   117,   348 },
    {   118,   220 }, {   119,   476 }, {   121,   316 }, {   122,   188 },
    {   123,   444 }, {   125,   380 }, {   126,   252 }, {   127,   508 },
    {   129,   258 }, {   131,   386 }, {   133,   322 }, {   134,   194 },
    {   135,   450 }, {   137,   290 }, {   138,   162 }, {   139,   418 },
    {   141,   354 }, {   142,   226 }, {   143,   482 }, {   145,   274 },
    {   147,   402 }, {   149,   338 }, {   150,   210 }, {   151,   466 },
    {   153,   306 }, {   154,   178 }, {   155,   434 }, {   157,   370 },
    {   158,   242 }, {   159,   498 }, {   161,   266 }, {   163,   394 },
    {   165,   330 }, {   166,   202 }, {   167,   458 }, {   169,   298 },
    {   171,   426 }, {   173,   362 }, {   174,   234 }, {   175,   490 },
    {   177,   282 }, {   179,   410 }, {   181,   346 }, {   182,   218 },
    {   183,   474 }, {   185,   314 }, {   187,   442 }, {   189,   378 },
    {   190,   250 }, {   191,   506 }, {   193,   262 }, {   195,   390 },
    {   197,   326 }, {   199,   454 }, {   201,   294 }, {   203,   422 },
    {   205,   358 }, {   206,   230 }, {   207,   486 }, {   209,   278 },
    {   211,   406 }, {   213,   342 }, {   215,   470 }, {   217,   310 },
    {   219,   438 }, {   221,   374 }, {   222,   246 }, {   223,   502 },
    {   225,   270 }, {   227,   398 }, {   229,   334 }, {   231,   462 },
    {   233,   302 }, {   235,   430 }, {   237,   366 }, {   239,   494 },
    {   241,   286 }, {   243,   414 }, {   245,   350 }, {   247,   478 },
    {   249,   318 }, {   251,   446 }, {   253,   382 }, {   255,   510 },
    {   259,   385 }, {   261,   321 }, {   263,   449 }, {   265,   289 },
    {   267,   417 }, {   269,   353 }, {   271,   481 }, {   275,   401 },
    {   277,   337 }, {   279,   465 }, {   281,   305 }, {   283,   433 },
    {   285,   369 }, {   287,   497 }, {   291,   393 }, {   293,   329 },
    {   295,   457 }, {   299,   425 }, {   301,   361 }, {   303,   489 },
    {   307,   409 }, {   309,   345 }, {   311,   473 }, {   315,   441 },
    {   317,   377 }, {   319,   505 }, {   323,   389 }, {   327,   453 },
    {   331,   421 }, {   333,   357 }, {   335,   485 }, {   339,   405 },
    {   343,   469 }, {   347,   437 }, {   349,   373 }, {   351,   501 },
    {   355,   397 }, {   359,   461 }, {   363,   429 }, {   367,   493 },
    {   371,   413 }, {   375,   477 }, {   379,   445 }, {   383,   509 },
    {   391,   451 }, {   395,   419 }, {   399,   483 }, {   407,   467 },
    {   411,   435 }, {   415,   499 }, {   423,   459 }, {   431,   491 },
    {   439,   475 }, {   447,   507 }, {   463,   487 }, {   479,   503 },
};

// these are scaled by R so that montmul can be used
const uint16_t ntt512_inv_omega_powers_rev[512] = {
 0, 4091, 4091, 7888, 4091, 7888, 1229, 1081, 4091, 7888, 1229, 1081, 4342, 5329, 2530, 6275, 4091, 7888, 1229, 1081, 4342, 5329, 2530, 6275, 2812, 7023, 6399, 10698, 2579, 7538, 11703, 6464, 4091, 7888, 1229, 1081, 4342, 5329, 2530, 6275, 2812, 7023, 6399, 10698, 2579, 7538, 11703, 6464, 4615, 7099, 6442, 8546, 1711, 965, 5882, 1134, 9180, 2125, 1364, 10329, 4189, 10414, 1688, 10404, 4091, 7888, 1229, 1081, 4342, 5329, 2530, 6275, 2812, 7023, 6399, 10698, 2579, 7538, 11703, 6464, 4615, 7099, 6442, 8546, 1711, 965, 5882, 1134, 9180, 2125, 1364, 10329, 4189, 10414, 1688, 10404, 3412, 4431, 9460, 5831, 5664, 4042, 9725, 7144, 7506, 7882, 1549, 7072, 12172, 997, 79, 6049, 12275, 8417, 1690, 7446, 2181, 6308, 3569, 5719, 1237, 1538, 12189, 432, 8306, 4426, 1534, 4679, 4091, 7888, 1229, 1081, 4342, 5329, 2530, 6275, 2812, 7023, 6399, 10698, 2579, 7538, 11703, 6464, 4615, 7099, 6442, 8546, 1711, 965, 5882, 1134, 9180, 2125, 1364, 10329, 4189, 10414, 1688, 10404, 3412, 4431, 9460, 5831, 5664, 4042, 9725, 7144, 7506, 7882, 1549, 7072, 12172, 997, 79, 6049, 12275, 8417, 1690, 7446, 2181, 6308, 3569, 5719, 1237, 1538, 12189, 432, 8306, 4426, 1534, 4679, 6180, 2796, 10637, 10086, 1053, 3316, 11578, 7004, 10469, 489, 10787, 9438, 883, 8966, 9277, 6130, 1156, 10736, 900, 8401, 11269, 9322, 10772, 7045, 4949, 4673, 4746, 9974, 9368, 6720, 10270, 12163, 3403, 5453, 13, 5351, 11455, 4586, 9386, 4676, 9179, 3604, 8507, 2083, 3467, 9109, 9843, 4668, 10078, 1195, 1808, 4970, 1228, 2560, 2742, 12241, 1367, 5892, 5274, 3269, 3854, 2030, 10527, 730, 4091, 7888, 1229, 1081, 4342, 5329, 2530, 6275, 2812, 7023, 6399, 10698, 2579, 7538, 11703, 6464, 4615, 7099, 6442, 8546, 1711, 965, 5882, 1134, 9180, 2125, 1364, 10329, 4189, 10414, 1688, 10404, 3412, 4431, 9460, 5831, 5664, 4042, 9725, 7144, 7506, 7882, 1549, 7072, 12172, 997, 79, 6049, 12275, 8417, 1690, 7446, 2181, 6308, 3569, 5719, 1237, 1538, 12189, 432, 8306, 4426, 1534, 4679, 6180, 2796, 10637, 10086, 1053, 3316, 11578, 7004, 10469, 489, 10787, 9438, 883, 8966, 9277, 6130, 1156, 10736, 900, 8401, 11269, 9322, 10772, 7045, 4949, 4673, 4746, 9974, 9368, 6720, 10270, 12163, 3403, 5453, 13, 5351, 11455, 4586, 9386, 4676, 9179, 3604, 8507, 2083, 3467, 9109, 9843, 4668, 10078, 1195, 1808, 4970, 1228, 2560, 2742, 12241, 1367, 5892, 5274, 3269, 3854, 2030, 10527, 730, 7630, 8821, 625, 9589, 3388, 3060, 8846, 4551, 1730, 9731, 5344, 10340, 7871, 8763, 11911, 6057, 1467, 5460, 3736, 4506, 2320, 9640, 6101, 9036, 9948, 9130, 8723, 2133, 5680, 4956, 6038, 3901, 3585, 6633, 2621, 6865, 7680, 8605, 12145, 4063, 5387, 8188, 9807, 8756, 6090, 727, 2190, 5286, 10812, 9330, 6249, 11346, 2749, 1888, 1715, 7338, 1469, 2502, 1739, 8709, 3764, 12250, 2080, 8219, 673, 42, 10049, 7219, 6635, 5746, 4868, 1582, 4614, 8578, 1296, 300, 989, 11949, 1748, 7687, 11357, 2060, 8927, 7642, 2991, 351, 5858, 12052, 12126, 7586, 9143, 7692, 5204, 8487, 2053, 11285, 8780, 3853, 7516, 5381, 10325, 4552, 7103, 1758, 3698, 11552, 6536, 4699, 3243, 8602, 16, 914, 6375, 9327, 6409, 8197, 6664, 12011, 6634, 7225, 2895, 7156, 3402, 6932, 1060, 5252, 10733, 3281};

 const uint16_t ntt512_mixed_powers_rev[512] = {
  0, 4401, 11208, 11060, 6014, 9759, 6960, 7947, 5825, 586, 4751, 9710, 1591, 5890, 5266, 9477, 1885, 10601, 1875, 8100, 1960, 10925, 10164, 3109, 11155, 6407, 11324, 10578, 3743, 5847, 5190, 7674, 7610, 10755, 7863, 3983, 11857, 100, 10751, 11052, 6570, 8720, 5981, 10108, 4843, 10599, 3872, 14, 6240, 12210, 11292, 117, 5217, 10740, 4407, 4783, 5145, 2564, 8247, 6625, 6458, 2829, 7858, 8877, 11559, 1762, 10259, 8435, 9020, 7015, 6397, 10922, 48, 9547, 9729, 11061, 7319, 10481, 11094, 2211, 7621, 2446, 3180, 8822, 10206, 3782, 8685, 3110, 7613, 2903, 7703, 834, 6938, 12276, 6836, 8886, 126, 2019, 5569, 2921, 2315, 7543, 7616, 7340, 5244, 1517, 2967, 1020, 3888, 11389, 1553, 11133, 6159, 3012, 3323, 11406, 2851, 1502, 11800, 1820, 5285, 711, 8973, 11236, 2203, 1652, 9493, 6109, 9008, 1556, 7037, 11229, 5357, 8887, 5133, 9394, 5064, 5655, 278, 5625, 4092, 5880, 2962, 5914, 11375, 12273, 3687, 9046, 7590, 5753, 737, 8591, 10531, 5186, 7737, 1964, 6908, 4773, 8436, 3509, 1004, 10236, 3802, 7085, 4597, 3146, 4703, 163, 237, 6431, 11938, 9298, 4647, 3362, 10229, 932, 4602, 10541, 340, 11300, 11989, 10993, 3711, 7675, 10707, 7421, 6543, 5654, 5070, 2240, 12247, 11616, 4070, 10209, 39, 8525, 3580, 10550, 9787, 10820, 4951, 10574, 10401, 9540, 943, 6040, 2959, 1477, 7003, 10099, 11562, 6199, 3533, 2482, 4101, 6902, 8226, 144, 3684, 4609, 5424, 9668, 5656, 8704, 8388, 6251, 7333, 6609, 10156, 3566, 3159, 2341, 3253, 6188, 2649, 9969, 7783, 8553, 6829, 10822, 6232, 378, 3526, 4418, 1949, 6945, 2558, 10559, 7738, 3443, 9229, 8901, 2700, 11664, 3468, 4659, 11036, 2452, 9478, 8502, 10432, 6233, 728, 7569, 5200, 10175, 9410, 6242, 10492, 8950, 9817, 6034, 10438, 2818, 408, 1271, 11929, 8276, 6911, 9210, 5475, 11363, 2936, 4327, 6084, 2688, 7323, 4108, 1361, 9812, 9340, 1024, 9108, 1988, 5800, 478, 2806, 8681, 1911, 12188, 3374, 812, 292, 1753, 3619, 6786, 7707, 6750, 9826, 7056, 8470, 4639, 11344, 3291, 1244, 8815, 1071, 11017, 4325, 6395, 5150, 9959, 3884, 5473, 2356, 6737, 1333, 5267, 11277, 2510, 721, 9505, 4424, 5348, 5737, 5613, 105, 7827, 6689, 386, 12170, 8334, 10443, 10213, 4370, 11505, 8617, 850, 3240, 11539, 11535, 3133, 3488, 9661, 6501, 4981, 11613, 7894, 7379, 909, 40, 10004, 1963, 3073, 4051, 6686, 9245, 7987, 8399, 10231, 2650, 11448, 8505, 7248, 1093, 6688, 4296, 371, 4371, 695, 9878, 10230, 9793, 7405, 2609, 12254, 4225, 5963, 2778, 4136, 11597, 8808, 3835, 6736, 8476, 1224, 12039, 11209, 9237, 8444, 4933, 8530, 11361, 3856, 5879, 6718, 1871, 2184, 6342, 3311, 5852, 3652, 10017, 6898, 6476, 4873, 11603, 5393, 3816, 3213, 2416, 9454, 10422, 3732, 4220, 10857, 4328, 10832, 3410, 4900, 10661, 832, 7431, 4083, 9217, 3442, 6325, 2746, 10855, 5111, 10824, 8418, 303, 5733, 9853, 10122, 7030, 876, 2262, 2890, 2250, 9720, 2352, 821, 9739, 1273, 1097, 315, 11131, 7778, 11865, 11932, 6228, 6751, 6990, 3161, 8159, 11652, 4367, 7068, 8777, 3999, 4759, 9253, 8352, 2163, 8534, 983, 7739, 4922, 7488, 2363, 6177, 5056, 11176, 599, 10204, 824, 6174, 619, 2523, 7950, 2834, 937, 4514, 3279, 7884, 10464, 9635, 7214, 896, 10261, 9562, 9848, 6855, 120, 3070, 5889, 4520, 12153, 617, 3157
};

static void ntt512_bitrev_shuffle(uint16_t *a) {
  uint16_t i, j, k;
  uint16_t x;

  for (i=0; i< BITREV512_NPAIRS; i++) {
    j = bitrev512[i][0];
    k = bitrev512[i][1];
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

static void print_uint16_array(FILE *f, uint16_t *a, uint16_t n) {
  uint32_t i, k;
  fprintf(f, "[");

  k = 0;
  for (i=0; i<n; i++) {
    if (k == 0) fprintf(f, " ");
    fprintf(f, "%d", a[i]);
    k ++;
    if (k == 16) {
      fprintf(f, ",");
      k = 0;
    } else {
      fprintf(f, ", ");
    }
  }
//   if (k > 0) {
//     fprintf(f, "\n");
//   }
  fprintf(f, "]\n");
}

void forward_ntt(uint16_t *a) {
  uint32_t j, s, t, u, d;
  uint32_t x, w;
  
  d = 512;
  for (t=1; t<512; t <<= 1) {
    d >>= 1;
    for (j=0, u=0; j<t; j++, u+=2*d) { // u = j * 2d
      w = ntt512_mixed_powers_rev[t + j]; // psi_t * w_t^bitrev(j)
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
      w = ntt512_inv_omega_powers_rev[t + j]; // psi_t * w_t^bitrev(j)
      for (s=u; s<u+d; s++) {
        x = mq_montymul(a[s + d], w);
        a[s + d] = mq_sub(a[s], x);
        a[s] = mq_add(a[s], x);
      }
    }
  }
}


uint16_t factors[] = {128, 2034, 1215, 5674, 11437, 8735, 8426, 6012, 4135, 7527, 12272, 1458, 4351, 6351, 10482, 280, 12130, 4962, 1659, 7353, 9123, 7679, 10079, 5205, 336, 2267, 10870, 11822, 3908, 6032, 6757, 9637, 6246, 2861, 7636, 755, 6813, 12063, 12154, 735, 4191, 9953, 5891, 11621, 906, 3260, 9560, 12127, 882, 7487, 7028, 9527, 4114, 3545, 3912, 11472, 7179, 5974, 1611, 3518, 4059, 2479, 4254, 9610, 6393, 6157, 4711, 4391, 11595, 2413, 517, 2647, 11532, 2756, 15, 8111, 7727, 1625, 10269, 5536, 8092, 6465, 5765, 18, 12191, 1899, 1950, 9865, 9101, 2337, 7758, 6918, 7395, 4798, 12110, 2340, 11838, 1090, 7720, 4394, 3386, 8874, 842, 2243, 2808, 9290, 1308, 9264, 2815, 6521, 8191, 5926, 10065, 10743, 11148, 8943, 8659, 3378, 10283, 12287, 9569, 12078, 7976, 8462, 5816, 7933, 11427, 7424, 7371, 9025, 9578, 12029, 2781, 9437, 4604, 6339, 6451, 11303, 10830, 6578, 11977, 5795, 3951, 3067, 5149, 10199, 8648, 707, 2978, 6999, 6954, 7199, 8596, 3721, 9781, 5462, 5764, 10947, 5941, 5887, 6181, 484, 6923, 1906, 11470, 4459, 5763, 9587, 11980, 9875, 10412, 3392, 4745, 1475, 2893, 2000, 4131, 2087, 11850, 5121, 8986, 5694, 1770, 10845, 2400, 7415, 7420, 1931, 8603, 952, 4375, 2124, 725, 2880, 8898, 8904, 4775, 5408, 6058, 5250, 91, 870, 3456, 5762, 8227, 5730, 1574, 2354, 6300, 2567, 1044, 6605, 11830, 2499, 6876, 11720, 367, 7560, 7996, 11084, 7926, 1907, 541, 10709, 1775, 5356, 9072, 12053, 10843, 11969, 7204, 3107, 10393, 2130, 8885, 3513, 9548, 8096, 11905, 6187, 8644, 7556, 2556, 10662, 11589, 6542, 12173, 1997, 51, 7915, 11525, 5525, 5421, 11449, 477, 9692, 7312, 2519, 9498, 1541, 6630, 8963, 11281, 5488, 4257, 1401, 565, 6482, 4307, 7956, 5840, 3706, 1670, 10024, 4139, 678, 405, 10084, 12005, 7008, 6905, 2004, 9571, 2509, 8187, 486, 9643, 2117, 3494, 8286, 12236, 1654, 553, 2451, 3041, 6656, 7456, 1735, 112, 4852, 11816, 8037, 5399, 6107, 10445, 11405, 2082, 5050, 10738, 4348, 2271, 4021, 12244, 245, 1397, 7414, 6060, 7970, 302, 5183, 7283, 12235, 294, 6592, 6439, 7272, 9564, 5278, 1304, 3824, 2393, 10184, 537, 5269, 1353, 9019, 1418, 11396, 2131, 10245, 9763, 5560, 3865, 8997, 8365, 9075, 3844, 5015, 5, 6800, 6672, 4638, 3423, 10038, 10890, 2155, 6018, 6, 8160, 633, 650, 11481, 7130, 779, 2586, 2306, 2465, 9792, 8133, 780, 3946, 8556, 10766, 5561, 5225, 2958, 4377, 4844, 936, 7193, 436, 3088, 9131, 6270, 10923, 10168, 3355, 3581, 3716, 2981, 11079, 1126, 7524, 8192, 7286, 4026, 6755, 6917, 6035, 10837, 3809, 6571, 2457, 11201, 7289, 8106, 927, 7242, 5631, 2113, 10343, 7864, 3610, 6289, 12185, 6028, 1317, 9215, 9909, 7496, 6979, 4332, 5089, 2333, 2318, 6496, 11058, 9433, 11453, 5917, 10114, 3649, 10173, 10155, 10253, 8354, 6404, 8828, 12016, 9679, 1921, 7292, 12186, 7388, 7567, 5227, 5678, 4588, 9157, 4763, 1377, 4792, 3950, 1707, 11188, 1898, 590, 3615, 800, 6568, 10666, 4740, 6964, 8510, 9651, 708, 4338, 960, 2966, 2968, 5688, 5899, 10212, 1750, 8223, 290, 1152, 6017, 10935, 1910, 4621, 4881, 2100, 4952, 348, 6298, 12136, 833, 2292, 8003, 8315, 2520, 10858, 7791, 2642, 4732, 8373, 7666, 4688, 9978, 3024, 8114, 11807, 8086, 10594, 5132, 11657, 710, 7058, 1171, 7279, 6795};

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

int
PQCLEAN_FALCON512_CLEAN_verify_raw(const uint16_t *c0, const int16_t *s2,
                                   uint16_t *h, uint8_t *tmp) {
    size_t u, n;
    uint16_t *tt;

    n = (size_t)1 << 9;
    tt = (uint16_t *)tmp;
    
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
    // print_uint16_array(stdout, tt, 512);

    forward_ntt(h);
    forward_ntt(tt);
    mq_poly_mul_ntt(tt, h);

    // we need to shuffle the input
    ntt512_bitrev_shuffle(tt);
  
    inverse_ntt(tt);
    // shuffle the output
    ntt512_bitrev_shuffle(tt);
    // then scale the ouput
    mq_poly_montymul_ntt(tt, factors);
  
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



    /*
     * Signature is valid if and only if the aggregate (-s1,s2) vector
     * is short enough.
     */
    PQCLEAN_FALCON512_CLEAN_is_short((int16_t *)tt, s2);
}
