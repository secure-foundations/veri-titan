include "../code/vale.dfy"
// include "../gen/modexp_var.dfy" 

module otbn_exe {
    import opened bv_ops
    import opened vt_ops
    import opened vt_vale
    // import opened mul256
    // import opened modexp_var

method ExecuteDemo()
{
    var state := state.init();

    var xmem := map[
        0 := 0x00000010,
        4 := 0x0000000C,
        8 := 0x00000280,
        12 := 0x000002c0,
        16 := 0x00000080,
        20 := 0x000004c0,
        24 := 0x000006c0,
        28 := 0x000008c0];

    var wmem := map[0x80 := 0xe1312531f84d21cfc8722ac57dbfffa78e8205a5687bb168a018ddc56a6a75e1,
    0xa0 := 0x1c8be7b3824fb1421c4fb8d78e1dd008b27e206a57f51964a825f9880ce3f8a3,
    0xc0 := 0x91b74a8443cccdf7d41db7aa8ae28eb94b1431e3ef762d5bc56ad0f27b9d6366,
    0xe0 := 0x9ebd1ff224e2efdb4f40def28c28f251235574d2b62ed01530e74d0d80183850,
    0x100 := 0xfad39f161ab269e9d2947d3d4d783a7c24e415466e66b8c82819a938fa7b49ee,
    0x120 := 0xc9e0e12fe3bc0f60c13c437e069eccc9eb27475435bf0dfb49d8b510aab78f7b,
    0x140 := 0xc3d9945f996b62414021b0bd5402c462edf34bc0c4aba4e589c240e0c253ac43,
    0x160 := 0xaf4c58b43970dcb933370e5d78916a8cb70d6b88c8c7100ff0250bf5a137ac60,
    0x180 := 0x565afdbc33976249987caa5b45185f0f04afc71aeb6c3d05b02d90b75f78cb0d,
    0x1a0 := 0xe18e1206131000ea4d6713ff782e02047a8dfb7f9a29e77d59e0765580a85056,
    0x1c0 := 0x1344ceaf90e82c7346c9addeb52f170d24c5052559cf874df24f038b21f57f30,
    0x1e0 := 0xe1df9be8a6c7bf58a792e13e81f787930fce770a5e4ed04d24bd4fbf663209f2,
    0x280 := 0x1dfc9779711cad8ba96ced374965995095d310b20b908e3bfd3e34f7f09b71df,
    0x2a0 := 0x7da9803aadf07cd11406fb58bda827cfc90a25828f25ef9512e25f1fcdf1cc06,
    0x2c0 := 0x546a7cfeeb165cd3d0f4fddadd38f5fbfb5be1e72c19d4ae9db9a2aca3eb77fa,
    0x2e0 := 0x32318a29f49dd5f776e77ababab5ae26da2e21031185bcae73f5cf6bcd410c5c,
    0x300 := 0x90b209bf6c65ac0e6563c81a9ccd73f2b61eab77538c240e8aa862a9689a85bc,
    0x320 := 0x3d3d07f301dc7990ebc2405fe0112362c75cbb02879a18307e351549e642e25e,
    0x340 := 0x9849163aeabe1810c204b9ca0dbdc0cbce301343dd65e10898d8cc33c5b9a5be,
    0x360 := 0x05f49af51ce689f5d9c77317ba59c5f5079883be4b4c22269bc14e3b234c8ff7,
    0x380 := 0x4043add66878ec0dd9691ef573649941093520a20811a95fc509b5ca7a83d42a,
    0x3a0 := 0x524b09b77a58d0479774620afe4319c4f209e1234ce52e1d5c7070ff7516d8b7,
    0x3c0 := 0xb60788f6d9ee19c42966d4f8d21be300e4b83ed6514995dc2a9044a296cbf044,
    0x3e0 := 0xda9c946b472a10b49fe0c3630ad2fbbcba9fc09693718edca7e13295f8d074ab,
    0x400 := 0x7d0c0fc36ca4d02fb5822d5649619ddda277ef0ed19233b504e452fc37276997,
    0x420 := 0x9e2dcea821e64d84fcb4969387993424eaee3c24785b7552b6988a4fa29196e2,
    0x4c0 := 0x9c5b7c4e2a24eed5f2f880071ec09faecf899599f9153989e693b200ceb7e983,
    0x4e0 := 0x14bb3a1b7ed6f162e49d8022b2a69ac47550094b04fdd694af7583ae21a153b2,
    0x500 := 0xcc97ee4be304ff93bc1443e259dca808b122f4497a80d8485c5815c2bb29d8dd,
    0x520 := 0xd7220269a431aac309fd06352381fb916a843a17ae860b451436839f42ef6b57,
    0x540 := 0x884e4addf2a7e960961e5f00930006df1d387448edba695635e2915edf3e2697,
    0x560 := 0x2388555c0474f5122c8569a4268aea5796c206971f3a378d4079aa797dfe76b1,
    0x580 := 0x6c1ddca3d94cdfa0cce606f2fc0be066699f04d343431b9ae73da3a058679953,
    0x5a0 := 0x592967a0b74f923bb86e1e6b9f292111a621c3e73bdb4f69fc635db4e96c11f6,
    0x5c0 := 0x7dade4d8eaf122328a26368e50c01aee87c5fe0f494fcdb68c1c8ca7c412097f,
    0x5e0 := 0xa74a77e3e439bd318575d194e96d4e291e0c656cf34908ca744f8aaa39eb2ac6,
    0x600 := 0x20c75aee9ebbc63e55c19326a29d7536e58501ec80400ad8f4e211520f465b88,
    0x620 := 0x114e6da58fc62fbefdf04b3a82b8f82543a5c74c879b937b59ffdba5ef6783d7];
    state := state.(xmem := xmem);
    state := state.(wmem := wmem);
    state := state.eval_code(va_code_modexp_var());

    state.dump_wmem(0x000008c0, 12);
}

// method ExecuteDemo()
// {
//     var state := state.init();
//     var code := va_Block(va_CCons(Ins32(ADD(GPR(8), GPR(0), GPR(0))),
//     va_CCons(Ins32(ADD(GPR(20), GPR(8), GPR(0))),
//     va_CCons(Ins32(ADDI(GPR(9), GPR(0), -1875)),
//     va_CCons(Ins32(ADD(GPR(27), GPR(9), GPR(9))),
//     va_CCons(Ins32(ADD(GPR(11), GPR(0), GPR(20))),
//     va_CCons(Ins32(ADD(GPR(5), GPR(27), GPR(9))),
//     va_CCons(Ins32(ADDI(GPR(22), GPR(0), 2)),
//     va_CCons(Ins256(BN_WSRR(WDR(30), 0)),
//     va_CCons(Ins256(BN_SUB(WDR(24), WDR(30), WDR(30), SFT(true, 8), 1)),
//     va_CCons(Ins32(ECALL()),
//     va_CNil())))))))))));

//     state := state.eval_code(code);
//     state.dump_regs();
// }


method Main()
{
    ExecuteDemo();
}

}
