module WideRegister {
    function method {:opaque} QB() : (r: int)
        ensures r >= 1;
    {
        18446744073709551616
    }

    type qword = i:int | 0 <= i < QB()

    datatype wide_register = wide_register(
        q0: qword,
        q1: qword,
        q2: qword,
        q3: qword
    )
}