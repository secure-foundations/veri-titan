barrett384:
    bn.rshi w20, w18, w31 >> 128
    bn.rshi w19, w17, w18 >> 128

    bn.add w19, w19, w8
    bn.addc w20, w20, w9

/*
    bn.add w19, w19, w24
    bn.addc w20, w20, w25

    bn.rshi w9, w20, w31 >> 1
    bn.rshi w8, w19, w20 >> 1
*/
