module bv_ops_nl {

    lemma div_negative_one(a: nat)
      requires a > 1
      ensures -1 / a == -1
    {
    }

} // end module
