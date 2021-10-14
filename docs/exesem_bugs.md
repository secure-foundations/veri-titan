# Issues uncovered through RIG
 
## Our side (executable semantics):

## `BN.MULQACC.SO`

This instruction updates the flag, which was missing in our executable semantics. 

## `BN.MOVR`

The state update was written as the following (wrong):

```
    var di := read_reg32(grd);
    var si := read_reg32(grs);
    if di > 31 || si > 31 then 
        this.(ok := false)
    else
        write_reg32(grd, if grd_inc then di + 1 else di).
        write_reg32(grs, if grs_inc then si + 1 else si).
        write_reg256(WDR(di), read_reg256(WDR(si)))
```

This might be problematic when `grd == grs`. The second write will override the first write. Consider the following instruction:
```
bn.movr x3++,x3
```

The above will first increment `x3`, then revert it back into the old value. Note in our vale defintion we disallow `grd == grs`.

The current fix is:

```
    var di := read_reg32(grd);
    var si := read_reg32(grs);
    if di > 31 || si > 31 then 
        this.(ok := false)
    else
        var s := (if grd_inc then write_reg32(grd, di + 1) else this);
        var l := (if grs_inc then s.write_reg32(grs, si + 1) else s);
        l.write_reg256(WDR(di), read_reg256(WDR(si)))
```
We avoid writing when increment is not specified. 


## The other side (simlator):

## `X1 register`

Dumping the register value for `x1` seemingly always resutls in 0. However the simulator does not actually use 0 when operating. 

## `WRND register`

The resultant value is hard-coded (might be by design) to be 

`0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999`