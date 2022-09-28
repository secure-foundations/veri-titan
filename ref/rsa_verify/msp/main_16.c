#include <stdint.h>
// #include <assert.h>
// #include <stdio.h>

extern void mod_pow(uint16_t *out,
        uint16_t *workbuf32,
        const uint16_t * rr,
        uint16_t *in);

#define RSANUMWORDS 192 // 3072 = 192*16 bit

uint16_t n[RSANUMWORDS] = {
  0x75e1,  0x6a6a,
  0xddc5,  0xa018,
  0xb168,  0x687b,
  0x05a5,  0x8e82,
  0xffa7,  0x7dbf,
  0x2ac5,  0xc872,
  0x21cf,  0xf84d,
  0x2531,  0xe131,
  0xf8a3,  0x0ce3,
  0xf988,  0xa825,
  0x1964,  0x57f5,
  0x206a,  0xb27e,
  0xd008,  0x8e1d,
  0xb8d7,  0x1c4f,
  0xb142,  0x824f,
  0xe7b3,  0x1c8b,
  0x6366,  0x7b9d,
  0xd0f2,  0xc56a,
  0x2d5b,  0xef76,
  0x31e3,  0x4b14,
  0x8eb9,  0x8ae2,
  0xb7aa,  0xd41d,
  0xcdf7,  0x43cc,
  0x4a84,  0x91b7,
  0x3850,  0x8018,
  0x4d0d,  0x30e7,
  0xd015,  0xb62e,
  0x74d2,  0x2355,
  0xf251,  0x8c28,
  0xdef2,  0x4f40,
  0xefdb,  0x24e2,
  0x1ff2,  0x9ebd,
  0x49ee,  0xfa7b,
  0xa938,  0x2819,
  0xb8c8,  0x6e66,
  0x1546,  0x24e4,
  0x3a7c,  0x4d78,
  0x7d3d,  0xd294,
  0x69e9,  0x1ab2,
  0x9f16,  0xfad3,
  0x8f7b,  0xaab7,
  0xb510,  0x49d8,
  0x0dfb,  0x35bf,
  0x4754,  0xeb27,
  0xccc9,  0x069e,
  0x437e,  0xc13c,
  0x0f60,  0xe3bc,
  0xe12f,  0xc9e0,
  0xac43,  0xc253,
  0x40e0,  0x89c2,
  0xa4e5,  0xc4ab,
  0x4bc0,  0xedf3,
  0xc462,  0x5402,
  0xb0bd,  0x4021,
  0x6241,  0x996b,
  0x945f,  0xc3d9,
  0xac60,  0xa137,
  0x0bf5,  0xf025,
  0x100f,  0xc8c7,
  0x6b88,  0xb70d,
  0x6a8c,  0x7891,
  0x0e5d,  0x3337,
  0xdcb9,  0x3970,
  0x58b4,  0xaf4c,
  0xcb0d,  0x5f78,
  0x90b7,  0xb02d,
  0x3d05,  0xeb6c,
  0xc71a,  0x04af,
  0x5f0f,  0x4518,
  0xaa5b,  0x987c,
  0x6249,  0x3397,
  0xfdbc,  0x565a,
  0x5056,  0x80a8,
  0x7655,  0x59e0,
  0xe77d,  0x9a29,
  0xfb7f,  0x7a8d,
  0x0204,  0x782e,
  0x13ff,  0x4d67,
  0x00ea,  0x1310,
  0x1206,  0xe18e,
  0x7f30,  0x21f5,
  0x038b,  0xf24f,
  0x874d,  0x59cf,
  0x0525,  0x24c5,
  0x170d,  0xb52f,
  0xadde,  0x46c9,
  0x2c73,  0x90e8,
  0xceaf,  0x1344,
  0x09f2,  0x6632,
  0x4fbf,  0x24bd,
  0xd04d,  0x5e4e,
  0x770a,  0x0fce,
  0x8793,  0x81f7,
  0xe13e,  0xa792,
  0xbf58,  0xa6c7,
  0x9be8,  0xe1df};

// 

const uint16_t d0inv = 0x71df;

/* Example signature created with example key above, no padding */
uint16_t sig[RSANUMWORDS] = {
    0xe983, 0xceb7,
    0xb200, 0xe693,
    0x3989, 0xf915,
    0x9599, 0xcf89,
    0x9fae, 0x1ec0,
    0x8007, 0xf2f8,
    0xeed5, 0x2a24,
    0x7c4e, 0x9c5b,
    0x53b2, 0x21a1,
    0x83ae, 0xaf75,
    0xd694, 0x04fd,
    0x094b, 0x7550,
    0x9ac4, 0xb2a6,
    0x8022, 0xe49d,
    0xf162, 0x7ed6,
    0x3a1b, 0x14bb,
    0xd8dd, 0xbb29,
    0x15c2, 0x5c58,
    0xd848, 0x7a80,
    0xf449, 0xb122,
    0xa808, 0x59dc,
    0x43e2, 0xbc14,
    0xff93, 0xe304,
    0xee4b, 0xcc97,
    0x6b57, 0x42ef,
    0x839f, 0x1436,
    0x0b45, 0xae86,
    0x3a17, 0x6a84,
    0xfb91, 0x2381,
    0x0635, 0x09fd,
    0xaac3, 0xa431,
    0x0269, 0xd722,
    0x2697, 0xdf3e,
    0x915e, 0x35e2,
    0x6956, 0xedba,
    0x7448, 0x1d38,
    0x06df, 0x9300,
    0x5f00, 0x961e,
    0xe960, 0xf2a7,
    0x4add, 0x884e,
    0x76b1, 0x7dfe,
    0xaa79, 0x4079,
    0x378d, 0x1f3a,
    0x0697, 0x96c2,
    0xea57, 0x268a,
    0x69a4, 0x2c85,
    0xf512, 0x0474,
    0x555c, 0x2388,
    0x9953, 0x5867,
    0xa3a0, 0xe73d,
    0x1b9a, 0x4343,
    0x04d3, 0x699f,
    0xe066, 0xfc0b,
    0x06f2, 0xcce6,
    0xdfa0, 0xd94c,
    0xdca3, 0x6c1d,
    0x11f6, 0xe96c,
    0x5db4, 0xfc63,
    0x4f69, 0x3bdb,
    0xc3e7, 0xa621,
    0x2111, 0x9f29,
    0x1e6b, 0xb86e,
    0x923b, 0xb74f,
    0x67a0, 0x5929,
    0x097f, 0xc412,
    0x8ca7, 0x8c1c,
    0xcdb6, 0x494f,
    0xfe0f, 0x87c5,
    0x1aee, 0x50c0,
    0x368e, 0x8a26,
    0x2232, 0xeaf1,
    0xe4d8, 0x7dad,
    0x2ac6, 0x39eb,
    0x8aaa, 0x744f,
    0x08ca, 0xf349,
    0x656c, 0x1e0c,
    0x4e29, 0xe96d,
    0xd194, 0x8575,
    0xbd31, 0xe439,
    0x77e3, 0xa74a,
    0x5b88, 0x0f46,
    0x1152, 0xf4e2,
    0x0ad8, 0x8040,
    0x01ec, 0xe585,
    0x7536, 0xa29d,
    0x9326, 0x55c1,
    0xc63e, 0x9ebb,
    0x5aee, 0x20c7,
    0x83d7, 0xef67,
    0xdba5, 0x59ff,
    0x937b, 0x879b,
    0xc74c, 0x43a5,
    0xf825, 0x82b8,
    0x4b3a, 0xfdf0,
    0x2fbe, 0x8fc6,
    0x6da5, 0x114e};

int ge_mod_wrap(const uint16_t *a)
{
  if (a[RSANUMWORDS] > 0) {
    return 1;
  }
  return ge_mod(a);
}

void sub_mod_ext(uint16_t *a)
{
  int32_t A = 0;
  uint16_t i;
  for (i = 0; i < RSANUMWORDS + 1; ++i) {
    if (i == RSANUMWORDS) {
      A += (uint32_t)a[i];
    } else {
      A += (uint32_t)a[i] - n[i];
    }
    a[i] = (uint16_t)A;
    A >>= 16;
  }
}

// void print_buff(char* name, const uint16_t* a, uint16_t len)
// {
//   printf("%s = to_nat(\"", name);
//   for (int i = 0; i < len; i++) {
//     printf("%04x", a[i]);  // endian reversed
//   }
//   printf("\")\n");
// }

void double_mod(uint16_t* a)
{
  uint32_t sum = 0;
  for (int i = 0; i < RSANUMWORDS+1; i ++)
  {
    sum += (uint32_t) a[i];
    sum += (uint32_t) a[i];
    a[i] = (uint16_t) sum;
    sum >>= 16;
  }
}

void compute_rr(uint16_t* a, uint16_t* workbuf)
{
  for (int i = 0; i < RSANUMWORDS; i ++) { a[i] = 0; }
  a[RSANUMWORDS] = 1;
  sub_mod_ext(a);

  for (int i = 0; i < 96; i ++) {
    double_mod(a);
    if (ge_mod_wrap(a)) {
      sub_mod_ext(a);
    }
  }

  mont_mul(workbuf, a, a);
  mont_mul(a, workbuf, workbuf);
  mont_mul(workbuf, a, a);
  mont_mul(a, workbuf, workbuf);
  mont_mul(workbuf, a, a);

  for (int i = 0; i < RSANUMWORDS; i ++) {
    a[i] = workbuf[i];
  }
}

int main(void) {
  uint16_t rr[RSANUMWORDS+1];
  uint16_t workbuf[2*RSANUMWORDS];
  uint16_t out[RSANUMWORDS];
  compute_rr(rr, workbuf);
  mod_pow(out,workbuf,rr,sig);
}

